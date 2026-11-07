# Actual bicanonical section chart producer

Strict kernel PASS: two modules, 25 public theorems and 41 recursively audited declarations. Only standard axiom roots occur.

The actual coefficient functions are q0(t)=1/P(t) and q1(t)=t/P(t), with P(t)=product(t−a_i) and the literal four finite contacts0,32,76832,−343. They represent the sections q0(dt)² and q1(dt)², not ordinary differential coefficients.

`BicanonicalCharts318` proves the exact contact-polynomial changes under t=a_i+z² and t=1/z². Multiplication by the square of the actual complex derivative gives the finite-branch coefficients4/product_{j≠i}(a_i−a_j+z²), and (a_i+z²) times that coefficient. At infinity it gives4z²/product(1−a_i z²) and4/product(1−a_i z²). These are exact punctured equalities, including the factor four and squared Jacobian, not only limits.

The rational ratio is preserved exactly in the original and finite-branch trivializations. The infinity identity Q0=z²Q1 is valid even at zero; away from zero the ratio is exactly1/z². At infinity the two values are(0,4), not an undefined affine ratio assigned a value.

`BicanonicalHolomorphy318` proves complex differentiability on the actual open complement of each denominator divisor, with literal open neighborhoods of every finite branch and of infinity. The denominators are actual polynomials and their center values are proved nonzero. The first section is nowhere zero on each finite-branch neighborhood and off the branch divisor; the second is nowhere zero near infinity. This supplies local holomorphy and no-common-zero without either property as an input.

## Geometric boundary

The actual covering curve must supply the order-two branch coordinates and identify t as its rational quotient coordinate. Away from the branch locus its unramified t-coordinate is a local coordinate. Those named geometric facts make the checked coefficient functions into the actual global bicanonical sections. This packet does not construct the algebraic curve, line bundle or chart gluing in Lean, and does not by itself prove vertical integrality on the arithmetic model. The separate relative-DVR derivation producer is the next step toward that integrality.

## Reproduction

Run `bash converse-work/bicanonical-sections/verify.sh`. It strictly compiles both modules and the exhaustive audit. Upstream frozen smooth-metric definitions are imported without modification. No repository or Git operation was performed.
