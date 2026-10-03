# Hostile case: archive-bomb

**Attack family:** archive-attack

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** ARCHIVE_UNSAFE

## What this proves about the judge

A decompression bomb: the archive expands far beyond the 2 GiB / 100k-entry expansion limits. Extraction must stop at the cap (ARCHIVE_UNSAFE / RESOURCE_LIMIT), not exhaust disk.

## Notes

Hostile payload is the ARCHIVE ENCODING, not a directory. The e2e driver runs make-archive.sh to produce the malicious tar and uploads THOSE bytes. The directory package here is a well-formed placeholder for documentation and the local loader.
