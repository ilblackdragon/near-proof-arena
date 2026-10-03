#!/usr/bin/env python3
"""Emit a MALICIOUS tar to stdout for this archive-attack case. The e2e driver
uploads these bytes directly (not a tar of the directory). Uses Python tarfile
to write raw headers, so device/hardlink/symlink entries need no privilege and
the package is NOT nested under a subdirectory. No network.
"""
import io, os, sys, tarfile

HERE = os.path.dirname(os.path.abspath(__file__))
KIND = (sys.argv[1] if len(sys.argv) > 1
        else open(os.path.join(HERE, "archive-kind")).read().strip())

CANDIDATE = b"""schema = "arena-candidate-v1"
name = "archive-attack"
agent = "adversarial-suite"
challenge = "CHALLENGE_PLACEHOLDER"
backend_family = "archive"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 1 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
"""

def add_file(tar, name, data, mode=0o644):
    ti = tarfile.TarInfo(name)
    ti.size = len(data); ti.mode = mode; ti.mtime = 0
    tar.addfile(ti, io.BytesIO(data))

buf = io.BytesIO()
tar = tarfile.open(fileobj=buf, mode="w", format=tarfile.GNU_FORMAT)
# a well-formed package at the archive ROOT (not nested)
add_file(tar, "candidate.toml", CANDIDATE)
add_file(tar, "README.md", b"archive attack placeholder\n")
add_file(tar, "build-recipe/build.sh", b"#!/bin/sh\nmkdir -p out; : > out/verify\n", 0o755)
add_file(tar, "source/verify.c", b"int main(void){return 0;}\n")
add_file(tar, "dependency-locks/NONE", b"none\n")

if KIND == "zipslip":
    add_file(tar, "../../../../tmp/zipslip-escape", b"escaped\n")
elif KIND == "symlink":
    ti = tarfile.TarInfo("source/leak"); ti.type = tarfile.SYMTYPE
    ti.linkname = "/etc/passwd"; ti.mtime = 0; tar.addfile(ti)
elif KIND == "hardlink":
    ti = tarfile.TarInfo("source/hard"); ti.type = tarfile.LNKTYPE
    ti.linkname = "/etc/passwd"; ti.mtime = 0; tar.addfile(ti)
elif KIND == "device":
    ti = tarfile.TarInfo("source/dev0"); ti.type = tarfile.CHRTYPE
    ti.devmajor = 1; ti.devminor = 3; ti.mode = 0o666; ti.mtime = 0; tar.addfile(ti)
elif KIND == "bomb":
    # one large all-zeros entry: compresses to almost nothing, so the
    # decompressed/compressed ratio blows past the archive guard (>200 after
    # 16 MiB). 128 MiB is plenty and cheap to build in RAM.
    big = 128 * 1024 * 1024
    ti = tarfile.TarInfo("source/zeros"); ti.size = big; ti.mode = 0o644; ti.mtime = 0
    tar.addfile(ti, io.BytesIO(bytes(big)))
else:
    sys.stderr.write("unknown kind %s\n" % KIND); sys.exit(2)

tar.close()
data = buf.getvalue()
if KIND == "bomb":
    import subprocess
    p = subprocess.run(["zstd", "-19", "-c"], input=data, stdout=subprocess.PIPE)
    data = p.stdout
sys.stdout.buffer.write(data)
