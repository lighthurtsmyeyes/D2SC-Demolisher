#!/usr/bin/env python3
"""
  /$$$$$$  /$$$$$$$  /$$$$$$$$ /$$   /$$  /$$$$$$  /$$   /$$  /$$$$$$  /$$   /$$  /$$$$$$  /$$$$$$$$ /$$$$$$$ 
 /$$__  $$| $$__  $$| $$_____/| $$$ | $$ /$$__  $$| $$  | $$ /$$__  $$| $$$ | $$ /$$__  $$| $$_____/| $$__  $$
| $$  \ $$| $$  \ $$| $$      | $$$$| $$| $$  \__/| $$  | $$| $$  \ $$| $$$$| $$| $$  \__/| $$      | $$  \ $$
| $$  | $$| $$$$$$$/| $$$$$   | $$ $$ $$| $$      | $$$$$$$$| $$$$$$$$| $$ $$ $$| $$ /$$$$| $$$$$   | $$$$$$$/
| $$  | $$| $$____/ | $$__/   | $$  $$$$| $$      | $$__  $$| $$__  $$| $$  $$$$| $$|_  $$| $$__/   | $$__  $$
| $$  | $$| $$      | $$      | $$\  $$$| $$    $$| $$  | $$| $$  | $$| $$\  $$$| $$  \ $$| $$      | $$  \ $$
|  $$$$$$/| $$      | $$$$$$$$| $$ \  $$|  $$$$$$/| $$  | $$| $$  | $$| $$ \  $$|  $$$$$$/| $$$$$$$$| $$  | $$
 \______/ |__/      |________/|__/  \__/ \______/ |__/  |__/|__/  |__/|__/  \__/ \______/ |________/|__/  |__/
                                                                                                                                                                                                         
                                                                                                              

Repair VPK packages tampered with by third-party skinchangers.

Observed tampering (sample: modified pak01_dir.vpk):
  1. Signature section filled with garbage; first int32 (publicKeySize) is
     negative -> ValvePak/VRF Source2Viewer crashes in ReadSignatureSection,
     vpkpp/VPKEdit dies on a huge allocation. The game never parses it.
  2. Every entry CRC32 XORed with a constant (0x155125E3 in the sample) so
     checksum verification fails for all files. The XOR key is planted as
     the "CRC" of zero-length decoy entries.
  3. Poison tree entries under the " " (extensionless) branch whose file
     names contain '"' (illegal in Windows paths) - decoys pointing at a
     watermark blob. Breaks naive parsers/extractors.
  4. Stale wholeFileChecksum. Tree MD5 is left VALID on purpose.
  5. Inside compiled resources (vtex_c/vpcf_c/vmat_c/...) the FourCC of the
     editor-only REDI block is overwritten with garbage ('YUYE'). The game
     skips unknown block types, but VRF/ValvePak constructs every block and
     dies with "Unrecognized block type".
  6. Compiled resources carry a ~20-char base32 watermark appended past the
     declared FileSize, tripping VRF's "File size does not match" check.

Fix: drop illegal entries, restore stamped REDI block descriptors (patching
a copy of the affected archive parts), strip trailing watermarks, recompute
every CRC32 from the restored data, rebuild the directory file with no
signature section and a fresh MD5 footer.

Usage:
    py -3 scripts/sanitize_vpk.py [path_to\_dir.vpk | folder] [-o OUTDIR]

Run without arguments (or double-click the file) to pick the *_dir.vpk in a
file dialog. A folder path also works if it contains exactly one *_dir.vpk.
Writes a clean copy (dir vpk + hardlinked archive parts) to OUTDIR
(default: <vpk folder>/sanitized_vpk). The original is left untouched.
"""

import argparse
import binascii
import hashlib
import os
import shutil
import struct
import sys
import webbrowser

VPK_SIGNATURE = 0x55AA1234
VPK_DIR_INDEX = 0x7FFF
VPK_ENTRY_TERM = 0xFFFF
ILLEGAL_CHARS = set('<>:"|?*')

TROLL_LINKS = (
    "https://discord.gg/AvEDbCThh5",
    "https://lighthurtsmyeyes.github.io/openchanger-website/",
)
TROLL_MESSAGE = "OWNED BY OPENCHANGER. EZ."


def print_owned_banner():
    os.system("")  # enable VT100 escape processing on the Windows console
    line = "=" * (len(TROLL_MESSAGE) + 8)
    print("\033[1;97;42m" + line)
    print("    " + TROLL_MESSAGE + "    ")
    print(line + "\033[0m")
    for url in TROLL_LINKS:
        print("\033[96m  " + url + "\033[0m")


def read_cstring(buf, off):
    end = buf.index(b"\x00", off)
    return buf[off:end].decode("ascii", "replace"), end + 1


class Entry:
    __slots__ = ("ext", "path", "name", "crc", "preload", "arch", "offset", "length")

    def __init__(self, ext, path, name, crc, preload, arch, offset, length):
        self.ext, self.path, self.name = ext, path, name
        self.crc, self.preload = crc, preload
        self.arch, self.offset, self.length = arch, offset, length

    @property
    def full_path(self):
        d = "" if self.path == " " else self.path
        n = self.name if self.ext == " " else f"{self.name}.{self.ext}"
        return f"{d}/{n}" if d else n


def is_poison(e):
    for s in (e.ext, e.path, e.name):
        if any(c in ILLEGAL_CHARS or ord(c) < 0x20 for c in s):
            return True
    return False


KNOWN_BLOCKS = {
    b"RERL", b"REDI", b"RED2", b"NTRO", b"DATA", b"VBIB", b"VXVS", b"SNAP",
    b"CTRL", b"MDAT", b"MBUF", b"AGRP", b"ASEQ", b"ANIM", b"CHIT", b"CSKG",
    b"INSG", b"LaCo", b"MRPH", b"PHYS", b"COLL", b"VCOL", b"SGMT", b"KEYV",
    b"FLCI", b"RDDI", b"AUX ", b"VSND", b"INOF", b"STBL", b"BITS",
}


def is_compiled_resource(payload):
    if len(payload) < 28:
        return False
    if struct.unpack_from("<H", payload, 4)[0] != 12:  # header version
        return False
    bcnt = struct.unpack_from("<I", payload, 12)[0]
    return 0 < bcnt <= 64 and 16 + bcnt * 12 <= len(payload)


def find_resource_stamps(payload):
    """Payload-relative offsets of garbage block-type stamps in a Source 2
    compiled resource. The competitor overwrites the editor-only REDI block's
    FourCC: the game skips unknown block types, but VRF constructs every
    block and dies with 'Unrecognized block type'."""
    if not is_compiled_resource(payload):
        return []
    bcnt = struct.unpack_from("<I", payload, 12)[0]
    types = [bytes(payload[16 + i * 12: 20 + i * 12]) for i in range(bcnt)]
    if not any(t in KNOWN_BLOCKS for t in types):
        return []
    return [16 + i * 12 for i, t in enumerate(types) if t not in KNOWN_BLOCKS]


BASE32 = frozenset(b"ABCDEFGHIJKLMNOPQRSTUVWXYZ234567")


def restore_redi(payload):
    """Rewrite stamped block-type FourCCs back to REDI. Length-preserving.
    Blocks whose content was replaced with a binary-KV3 template (identical
    GUID everywhere - the real edit info is destroyed) cannot be parsed by
    VRF's legacy-only REDI reader, so they are neutralized instead (size=0:
    both VRF and the game skip zero-size blocks). Returns (bytes, restored, dropped)."""
    stamps = find_resource_stamps(payload)
    if not stamps:
        return payload, 0, 0
    buf = bytearray(payload)
    restored = dropped = 0
    for pos in stamps:
        buf[pos:pos + 4] = b"REDI"
        rel = struct.unpack_from("<I", payload, pos + 4)[0]
        content = pos + 4 + rel
        readable = 0 <= content + 4 <= len(payload)
        magic = struct.unpack_from("<I", payload, content)[0] if readable else 0
        if not readable or (magic & 0xFFFFFF00) == 0x4B563300:  # binary KV3 magic ("3VK" + version)
            buf[pos + 8:pos + 12] = b"\x00\x00\x00\x00"
            dropped += 1
        else:
            restored += 1
    return bytes(buf), restored, dropped


def strip_watermark(payload):
    """Strip the trailing base32 watermark the packer appends past the
    declared FileSize (VRF verifies stream length against the in-file size)."""
    if not is_compiled_resource(payload):
        return payload, 0
    run = 0
    for i in range(len(payload) - 1, max(len(payload) - 65, -1), -1):
        if payload[i] in BASE32:
            run += 1
        else:
            break
    if 8 <= run <= 64:
        return payload[:len(payload) - run], run
    return payload, 0


def parse_dir(dir_file):
    data = open(dir_file, "rb").read()
    sig, ver, tree_size = struct.unpack_from("<III", data, 0)
    if sig != VPK_SIGNATURE:
        sys.exit(f"error: {dir_file} is not a VPK (bad signature {sig:#x})")
    hlen = 12
    header2 = (0, 0, 0, 0)
    if ver == 2:
        header2 = struct.unpack_from("<IIII", data, 12)
        hlen = 28
    elif ver != 1:
        sys.exit(f"error: unsupported VPK version {ver}")
    tree_off = hlen
    tree = data[tree_off:tree_off + tree_size]

    entries = []
    off = 0
    while True:
        ext, off = read_cstring(tree, off)
        if not ext:
            break
        while True:
            path, off = read_cstring(tree, off)
            if not path:
                break
            while True:
                name, off = read_cstring(tree, off)
                if not name:
                    break
                crc, pre, arch, eoff, elen, term = struct.unpack_from("<IHHIIH", tree, off)
                off += 18
                if term != VPK_ENTRY_TERM:
                    sys.exit(f"error: bad entry terminator {term:#x} at tree offset {off - 2:#x}")
                preload = tree[off:off + pre]
                off += pre
                entries.append(Entry(ext, path, name, crc, preload, arch, eoff, elen))
    if off != len(tree):
        print(f"warning: tree has {len(tree) - off} trailing bytes")

    data_base = tree_off + tree_size  # embedded (archiveIndex 0x7FFF) data lives here
    return data, ver, header2, entries, data_base


def read_entry_data(e, data, data_base, dir_folder, archives):
    chunks = [e.preload] if e.preload else []
    if e.length:
        if e.arch == VPK_DIR_INDEX:
            chunks.append(data[data_base + e.offset: data_base + e.offset + e.length])
        else:
            if e.arch not in archives:
                part = os.path.join(dir_folder, f"{base_name}_{e.arch:03d}.vpk")
                if not os.path.exists(part):
                    sys.exit(f"error: missing archive part {part}")
                archives[e.arch] = open(part, "rb").read()
            arc = archives[e.arch]
            chunks.append(arc[e.offset: e.offset + e.length])
    return b"".join(chunks)


def sanitize(dir_file, out_dir):
    global base_name
    dir_folder = os.path.dirname(os.path.abspath(dir_file))
    file_name = os.path.basename(dir_file)
    if not file_name.endswith("_dir.vpk"):
        sys.exit("error: expected a *_dir.vpk file")
    base_name = file_name[:-len("_dir.vpk")]

    data, ver, header2, entries, data_base = parse_dir(dir_file)
    print(f"input : {dir_file} (v{ver}, {len(entries)} entries)")

    kept, dropped = [], []
    seen = set()
    for e in entries:
        if is_poison(e):
            dropped.append(e)
        elif e.full_path.lower() in seen:
            dropped.append(e)
        else:
            seen.add(e.full_path.lower())
            kept.append(e)
    for e in dropped:
        print(f"drop  : [{e.ext!r}] {e.full_path!r} (crc={e.crc:#010x} len={e.length})")

    archives = {}
    arch_dirty = set()
    payloads = {}
    fixed, stamps_total, dropped_total, strip_total, strip_files = 0, 0, 0, 0, 0
    xor_keys = {}
    for e in kept:
        payload = read_entry_data(e, data, data_base, dir_folder, archives)
        destamped, nst, ndrop = restore_redi(payload)
        final, nstrip = strip_watermark(destamped)
        if (nst or ndrop) and e.arch != VPK_DIR_INDEX and e.length:
            # write the de-stamped data segment back (same length; the
            # watermark tail stays as unread slack beyond the new entry length)
            if e.arch not in arch_dirty:
                archives[e.arch] = bytearray(archives[e.arch])
                arch_dirty.add(e.arch)
            archives[e.arch][e.offset: e.offset + e.length] = destamped[len(e.preload):]
        if nst or ndrop or nstrip:
            stamps_total += nst
            dropped_total += ndrop
            strip_total += nstrip
            strip_files += 1 if nstrip else 0
            payloads[id(e)] = final
            if e.preload:
                e.preload = final[:len(e.preload)]
            e.length = len(final) - len(e.preload)
        actual = binascii.crc32(final) & 0xFFFFFFFF
        if actual != e.crc:
            fixed += 1
            xor_keys[e.crc ^ actual] = xor_keys.get(e.crc ^ actual, 0) + 1
            e.crc = actual
    if xor_keys:
        print(f"crc   : fixed {fixed} entr(y/ies); stored^actual keys: " +
              ", ".join(f"{k:#010x} x{n}" for k, n in sorted(xor_keys.items())))
    if stamps_total:
        print(f"data  : restored {stamps_total} stamped REDI block descriptor(s), "
              f"neutralized {dropped_total} KV3-template REDI block(s) in {len(arch_dirty)} archive part(s)")
    if strip_total:
        print(f"data  : stripped {strip_total} trailing watermark byte(s) from {strip_files} file(s)")

    # Re-embed any dir-resident payloads into a fresh file data section
    file_data = bytearray()
    for e in kept:
        if e.arch == VPK_DIR_INDEX and e.length:
            payload = payloads.get(id(e)) or read_entry_data(e, data, data_base, dir_folder, archives)
            e.offset = len(file_data)
            file_data += payload[len(e.preload):]

    # Serialize the tree: ext\0 (path\0 (name\0 entry)* \0)* \0 ... \0
    tree = bytearray()
    cur_ext = cur_path = None
    for e in sorted(kept, key=lambda x: (x.ext, x.path)):
        if e.ext != cur_ext:
            if cur_ext is not None:
                tree += b"\x00\x00"  # end names, end paths
            tree += e.ext.encode() + b"\x00"
            cur_ext, cur_path = e.ext, None
        if e.path != cur_path:
            if cur_path is not None:
                tree += b"\x00"      # end names
            tree += e.path.encode() + b"\x00"
            cur_path = e.path
        tree += e.name.encode() + b"\x00"
        tree += struct.pack("<IHHIIH", e.crc, len(e.preload), e.arch, e.offset, e.length, VPK_ENTRY_TERM)
        tree += e.preload
    tree += b"\x00\x00\x00"          # end names, end paths, end extensions

    out = bytearray()
    if ver == 2:
        out += struct.pack("<III", VPK_SIGNATURE, 2, len(tree))
        out += struct.pack("<IIII", len(file_data), 0, 48, 0)  # no archive md5, no signature
    else:
        out += struct.pack("<III", VPK_SIGNATURE, 1, len(tree))
    out += tree
    out += file_data
    if ver == 2:
        tree_md5 = hashlib.md5(bytes(tree)).digest()
        out += tree_md5
        out += hashlib.md5(b"").digest()          # archive md5 section checksum (empty section)
        out += hashlib.md5(bytes(out)).digest()   # whole-file checksum: md5 of everything up to this field

    os.makedirs(out_dir, exist_ok=True)
    out_file = os.path.join(out_dir, file_name)
    with open(out_file, "wb") as f:
        f.write(out)

    for arch in archives:
        src = os.path.join(dir_folder, f"{base_name}_{arch:03d}.vpk")
        dst = os.path.join(out_dir, f"{base_name}_{arch:03d}.vpk")
        if arch in arch_dirty:
            # dst may be a hardlink to the original from a previous run:
            # never write patched bytes through it - replace the file instead.
            if os.path.exists(dst):
                os.remove(dst)
            with open(dst, "wb") as f:
                f.write(archives[arch])
            print(f"patch : {dst} ({len(archives[arch])} bytes, de-stamped)")
        else:
            if not os.path.exists(dst):
                try:
                    os.link(src, dst)
                except OSError:
                    shutil.copy2(src, dst)
            print(f"link  : {dst}")

    print(f"output: {out_file} ({len(kept)} entries, {len(out)} bytes)")
    tampered = bool(dropped) or bool(xor_keys) or stamps_total > 0 or strip_total > 0 or header2[3] != 0
    return out_file, tampered


def verify(dir_file):
    dir_folder = os.path.dirname(os.path.abspath(dir_file))
    file_name = os.path.basename(dir_file)
    global base_name
    base_name = file_name[:-len("_dir.vpk")]
    data, ver, header2, entries, data_base = parse_dir(dir_file)
    archives = {}
    bad, stamped = 0, 0
    for e in entries:
        payload = read_entry_data(e, data, data_base, dir_folder, archives)
        if (binascii.crc32(payload) & 0xFFFFFFFF) != e.crc:
            print(f"  CRC MISMATCH: {e.full_path}")
            bad += 1
        elif find_resource_stamps(payload):
            print(f"  STILL STAMPED: {e.full_path}")
            stamped += 1
    if ver == 2:
        _, _, tree_size = struct.unpack_from("<III", data, 0)
        fds, amd5, omd5, ssz = struct.unpack_from("<IIII", data, 12)
        o = 28 + tree_size + fds + amd5
        ok_tree = hashlib.md5(data[28:28 + tree_size]).digest() == data[o:o + 16]
        ok_whole = hashlib.md5(data[:o + 32]).digest() == data[o + 32:o + 48]
        print(f"verify: treeMD5 {'OK' if ok_tree else 'BAD'}, wholeMD5 {'OK' if ok_whole else 'BAD'}, signatureSection={ssz}")
    print(f"verify: {len(entries)} entries, {bad} CRC mismatches, {stamped} stamped resources")
    return bad == 0 and stamped == 0


def pick_vpk_file():
    try:
        import tkinter as tk
        from tkinter import filedialog
        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        path = filedialog.askopenfilename(
            title="Select the *_dir.vpk to sanitize",
            filetypes=[("VPK directory", "*_dir.vpk"), ("VPK files", "*.vpk"), ("All files", "*.*")])
        root.destroy()
        return path
    except Exception:
        return input("Path to *_dir.vpk: ").strip()


def resolve_vpk_path(raw):
    path = os.path.abspath(raw.strip().strip('"').rstrip("\\/"))
    if os.path.isdir(path):
        dirs = [f for f in os.listdir(path) if f.lower().endswith("_dir.vpk")]
        if len(dirs) == 1:
            return os.path.join(path, dirs[0])
        if not dirs:
            sys.exit(f"error: no *_dir.vpk found in {path}")
        sys.exit(f"error: several *_dir.vpk in {path}, pick one: " + ", ".join(sorted(dirs)))
    return path


def main():
    ap = argparse.ArgumentParser(description="Repair tampered VPK directories (drop poison entries, fix CRCs, strip bad signature).")
    ap.add_argument("vpk", nargs="?", help="path to *_dir.vpk or a folder containing one (a file dialog opens if omitted)")
    ap.add_argument("-o", "--out", help="output folder (default: <vpk folder>/sanitized_vpk)")
    ap.add_argument("--no-pause", action="store_true", help="exit immediately when done (for scripting)")
    args = ap.parse_args()

    interactive = args.vpk is None
    raw = args.vpk if args.vpk else pick_vpk_file()
    if not raw:
        print("cancelled")
        return
    vpk = resolve_vpk_path(raw)
    out_dir = args.out or os.path.join(os.path.dirname(os.path.abspath(vpk)), "sanitized_vpk")

    code = 0
    tampered = False
    try:
        out_file, tampered = sanitize(vpk, out_dir)
        if not verify(out_file):
            print("error: verification failed")
            code = 1
    except SystemExit as e:
        if isinstance(e.code, str):
            print(e.code)
        code = e.code if isinstance(e.code, int) else 1
    except Exception as e:
        print(f"error: {e}")
        code = 1

    if code == 0 and tampered:
        print()
        print_owned_banner()
        for url in TROLL_LINKS:
            try:
                webbrowser.open(url)
            except Exception:
                pass

    if interactive:
        try:
            if code == 0:
                if input("\nOpen the output folder? [Y/n] ").strip().lower() not in ("n", "no", "н", "нет"):
                    os.startfile(out_dir)
            else:
                input("\nPress Enter to close...")
        except (EOFError, OSError):
            pass
    elif not args.no_pause:
        try:
            input("\nPress Enter to close...")
        except EOFError:
            pass
    sys.exit(code)


if __name__ == "__main__":
    main()
