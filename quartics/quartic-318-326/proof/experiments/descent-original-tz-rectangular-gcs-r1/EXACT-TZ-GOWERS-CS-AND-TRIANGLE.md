# Exact finite signed Gowers Cauchy–Schwarz and triangle

Scope: isolated source-only proof drafts for original 318/326. No
Lean/build/push or analogue of the nonlinear analytic theorem.

**Smallest testable leaf:** ActualTZReflectionIteration318 is Mathlib-only,
one authored module, no baseline project imports. It proves the finite
iteration of one-axis Cauchy–Schwarz in full generality at the actual
type Fin a → Bool. ActualTZRectangularGCS318 adds exactly one authored
module and is an independent 2/0 cohort; it proves the one-axis
Cauchy–Schwarz itself and the unnormalized full multilinear bound.
The next two modules use the prior exact actual finite-box/pointed
packet, not a claim of a small independent complete hosted closure.

## Reflection and actual box

Write b_i∈{0,1}. In a general finite rectangle, choose paired digits
(u_i,v_i) independently, and insert the point y_i=u_i if b_i=1,
y_i=v_i otherwise. A shared finite parameter x may appear in all
functions and is retained. Split at ANY fixed j by Fin.insertNthEquiv
for both digits and all vertices. For each fixed x and other pairs the
box product factors into A_s B_t; summing the two j digits gives
(sum_s A_s)(sum_t B_t). The j=true/false reflections replace the function
index bit j in every vertex but do not change the spatial selection.
Their exact finite sums are respectively the sum of (sum_s A_s)^2
and the sum of (sum_t B_t)^2 over the same retained variables. Thus one
ordinary finite Cauchy–Schwarz over those retained variables gives
|Mix F|²≤|Mix reflected_true|·|Mix reflected_false|. This works for
signed real values by using squares, not assuming Mixed F≥0.

Splice the first m direction bits from a fixed assignment. Use Fin.snoc
at its 0-based next direction m, and the corresponding equivalence to
split products over all assignments of length m+1. Induction raises the
next one-axis inequality to 2^m and applies the old 2^m bound to both
reflections. Once all a directions have been reflected, the leaf is
exactly the diagonal of a single original vertex function. This yields
the unnormalized power inequality
    |Mix F|^(2^a) ≤ ∏_ω |Mix(const F_ω)|.
There is no root estimation or nondegeneracy hypothesis in this step.

In the actual cyclic box use
    F̃_ω(x,y)=F_ω(x+∑_i axis_i y_i mod n).
With both original digit tuples u,v fixed, the rectangular evaluation
has offset ∑ axis_i v_i + ∑_{ω_i=1} axis_i (u_i−v_i). Translating by
the common first sum is a permutation of Fin n at that fixed pair;
this identifies the two UNNORMALIZED mixed sums exactly. Each original
axis retains its full paired difference multiplicity, including for
zero/nonunit slopes, n=1, or repeated wrapped vertices. No use of a
uniform distribution of differences.

Divide the power Cauchy–Schwarz by (n L^(2a))^(2^a); the right side
counts exactly 2^a copies of that normalization. The strict actual
seminorm uses a>0: use the prior independently derived diagonal
boxPower_nonneg and remove max(0,·) via boxNorm_is_power. Apply the
positive real 2^a-root; the finite product root identity uses only
nonnegative inputs. The result is normalized_gcs, with original
parameters and functions, for arbitrary signed real mixed inputs.
A totalized L=0 is harmless in this finite identity; the actual
analytic hierarchy still requires genuine nonempty scales.

The exact triangle expands the mixed multilinear product over all
subsets of the FULL Boolean vertex set using Fintype.prod_add.
Apply normalized_gcs term by term, then recombine via the same
expansion to (‖f‖+‖g‖)^(2^a). The old diagonal nonnegativity and
boxNorm_le_of_abs_power finish. localAverage_add is just summing these
triangles with the unchanged fine digits and original M^D denominator.

ActualTZTriangleForPointedPacket318.globalTriangle is an optional small
consumer that supplies the exact earlier GlobalTriangle field for
all q at the old J. It does not mutate or weaken the old Packet.

## Remaining native analytic boundary

No DenseModel, BoundedConcatenation, PointedPET, primitive-majorant
moment bounds, affine/Frei–Tinková estimates, ray reciprocity, or
actual prime lower mass are proved here. Their original typed inputs,
coefficients and common diagonal remain as before. This closes only
the finite GCS/triangle auxiliary field at source level. It does not
assert Lean admission or remove the independent deep hypotheses.

Control: exact signed rectangular/cyclic identities, every
one-coordinate reflected inequality, the full normalized integer
power comparison, and all finite multilinearity terms. Includes
empty finite L=0, n=1, arbitrary signs/nonunits, and distinct
functions for different vertices. This is not a prime search.
