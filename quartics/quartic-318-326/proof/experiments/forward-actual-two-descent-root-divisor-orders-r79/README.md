# Squarefree normalization, CRT and centered roots

Two independent native-only modules are added. LegendreSquarefreeCRT318 constructs signed squarefree coefficient decomposition with nonincrease of size, assembles prime modular roots by CRT, and proves exact multiplicity1 of a prime divisor of a squarefree integer. LegendreCenteredRoot318 constructs t,c with t²-a=b*c and2|t|≤|b| from an actual modular root modulo|b|, using native valMinAbs.

All1333 predecessor sources and relative order remain byte-identical, including checked modular-root73, checked Qp77, actual125 and the pending affine78 leaf. Each new module has one experiment-root closure; their union has two. No complete ternary induction or affine-transfer/strict-bound module is included in this packet.

Source/math/API review is not Lean acceptance. No local Lean was run. These constructions do not select a global auxiliary value or establish the original quaternary local-global principle or four elliptic realizations. Strict hosted checks remain required.
