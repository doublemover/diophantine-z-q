# Exact ideal relation at 53 for the actual one-I mirror field

This is a source-only arithmetic packet for the actual historical one-I
base \(d=2811626664334219040035976315\). It proves the relation

    eξ[q53] + 4eξ[q3] + eξ[q5303] + eξ[I_C] = 0

in the projected ordinary class group, with the degree-13 q53 prime,
all visible factors, and the unfactored 2,940-digit-norm ideal I_C
specified exactly. The latter does not reduce to the 150-million
factor base **in this principal row**. This is not a bound on the
class quotient, Selmer dimension or rational rank and does not
exclude some other relative ideal reduction.

- [Exact q53 chart and depth](actual-one-I-ordinary-q53-ideal-r1/EXACT-ORDINARY-Q53-PRINCIPAL-CHART.md)
- [Signed norm and the two projected small factors](actual-one-I-q53-global-norm-r1/EXACT-PARTIAL-PRINCIPAL-REDUCTION-OF-MIRROR-Q53.md)
- [Complete factor-free composite divisor](actual-one-I-q53-relative-gaussian-r1/EXACT-FACTOR-FREE-MIRROR-Q53-CLASS-RELATION.md)
- [Bounded smoothness replay](actual-one-I-q53-factor-base-smoothness-r1/EXACT-Q53-PRINCIPAL-ROW-NOT-SMALL-SMOOTH.md)
- [Signed independent review](independent-q53-review/INDEPENDENT-REVIEW.md)

The exact ordinary-class predecessor and inputs are included. Its
GRH comparison is conditional; none of the arithmetic above uses
GRH. The independent reviewer checked all five authored arithmetic
outputs and separately rebuilt signed norm residues using finite
elliptic additions.

From this folder, run:

    bash replay.sh

Needs Python 3 with SymPy and a C++17 compiler with GMP headers/libraries.
The replay builds only a disposable standalone arithmetic executable.
