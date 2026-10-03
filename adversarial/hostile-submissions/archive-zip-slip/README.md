# Hostile case: archive-zip-slip

**Attack family:** archive-attack

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** ARCHIVE_UNSAFE

## What this proves about the judge

The archive contains an entry whose path escapes the extraction root via `../` (zip-slip). Extraction must refuse: path traversal is rejected before any file is written (ARCHIVE_UNSAFE).

## Notes

Hostile payload is the ARCHIVE ENCODING, not a directory. The e2e driver runs make-archive.sh to produce the malicious tar and uploads THOSE bytes. The directory package here is a well-formed placeholder for documentation and the local loader.
