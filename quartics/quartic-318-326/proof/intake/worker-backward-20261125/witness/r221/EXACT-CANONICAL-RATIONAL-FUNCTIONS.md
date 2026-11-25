# From the actual four named rational functions, not a field-isomorphism input

Status: exact source-only candidate. This removes an algebraic input from
R220, not representability of the true PEL group. R219 classical argument
provides the field M of the genuine quaternionic coarse curve over its
true Atkin–Lehner quotient K=Q(T), its degree 16, and actual four eigenfunctions.
Each eigenfunction may initially be given by z_i²=d_i(T−b_i); if R219 computes
d_i=c_i u_i² in Q*, use y_i=z_i/u_i. This is an actual rational operation on
M, not an independently chosen square root or a complex evaluation. Its
coefficient b, and T, must be the named old ones.

The native-ready source constructs the unique tensor evaluator sending the
four old generators to these functions, proves injectivity from the old
actual field, proves surjectivity by matching the actual degree, and proves
the map intertwines each supplied actual labelled deck arrow. The e in R220
then uses the same K comparison restricted over U. This final restriction
only asks the actual chart's U-to-field map to agree with T on Q[T], after
which localization uniqueness gives agreement throughout U. No PEL
representer, canonical coarse curve, named CM anchors or functions are
constructed by this leaf.

Direct imports: FourRootAutomorphisms318, FourRootSignBaseChange318,
SourceTwistArithmetic318 (historical), and stock
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas. Five recursive audit roots
are embedded in the source.
