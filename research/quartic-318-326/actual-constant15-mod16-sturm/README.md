# A fixed-level modulo-16 certificate for the literal conductor-15 coefficient

For the unchanged original a=0 scalar the signed Waldspurger coefficient
is divisible by sixteen. Its integer value, nonvanishing, and the rank
or rational-point status of the twist are not established.

- [Exact paper](high-hom-1120/heegner-compressed-trace/original-constant15-actual-mod16-lift-r2/ACTUAL-CONSTANT15-FIXED-LEVEL-MOD16.md)
- [Full mod-16 Sturm transcript](high-hom-1120/heegner-compressed-trace/original-constant15-actual-mod16-lift-r2/EXACT-RAW-WEIGHT-TWO-MOD16.txt)
- [Signed independent review](review/INDEPENDENT-ACTUAL-CONSTANT15-MOD16-STURM-REVIEW.md)

Run sh verify.sh with Python 3, a C++17 compiler, sha256sum, and cmp.
The three exact replays use only the enclosed source, build into a
temporary directory, and do not expand or factor the literal twist.
Mathematical antecedents are included at their original relative paths.
The exact review also records the historical display-unsafe r1; only
the rendering-corrected r2 and its unchanged replay are packaged here.
