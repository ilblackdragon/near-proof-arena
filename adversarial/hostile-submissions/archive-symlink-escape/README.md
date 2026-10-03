# Hostile case: archive-symlink-escape

**Attack family:** archive-attack

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** ARCHIVE_UNSAFE

## What this proves about the judge

The archive contains a symlink pointing outside the root (or a symlink then a write through it). Symlinks are rejected outright by the archive policy (ARCHIVE_UNSAFE).

## Notes

Hostile payload is the ARCHIVE ENCODING, not a directory. The e2e driver runs make-archive.sh to produce the malicious tar and uploads THOSE bytes. The directory package here is a well-formed placeholder for documentation and the local loader.
