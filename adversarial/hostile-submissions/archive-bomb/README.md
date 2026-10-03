# Hostile case: archive-bomb

**Attack family:** archive-attack

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** ARCHIVE_UNSAFE

## What this proves about the judge

A decompression bomb that expands far beyond the expansion / ratio limits. Extraction must stop at the cap, not exhaust disk. The payload is the archive ENCODING, so the directory package here is a well-formed placeholder and make-archive.py emits the malicious tar; the driver uploads that.

## Notes

make-archive.py writes raw tar headers with Python's tarfile so device/hardlink/symlink entries do not need privilege and the package is not nested under a subdir.
