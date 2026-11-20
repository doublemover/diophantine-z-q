# Immutable source-only regulated factor successor, exact reviewer findings

The r1 archive and papers remain unchanged. Only the two proof lines change.
In residue_factor's first calculation the listed simp lemmas already push
the division into each summand; keep the outer finite sum for sum_congr.
In root_hit use pinned ZMod.natCast_zmod_val (not natCast_val, which states
the more general cast result). No theorem or definition is changed.
