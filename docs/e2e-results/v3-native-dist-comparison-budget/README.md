Actual distribute comparator budget
===================================

Strict single-file Lean checks and four exact axiom guards pass. The theorem unfolds the actual Gen.distRows generator: two shard loops contribute at most 2*n and the grid contributes at most n*n. No supplied comparison inventory is assumed. Consequently each successful n<=64 run contributes at most 4224 comparisons; any supplied list of at most32 such actual runs contributes at most135168.

This proves counts, not CmpOk or physical traffic. The list has explicit actual generator success, n<=64, and length<=32 premises; native accepted-call list instantiation and actual Run.cmps budget remain separate. No active constraints or acceptance domain changed.
