# Full-order invariant and native bound chain

The preceding packet constructs the full native integer ring, not merely a quadratic suborder. Its ring equivalence is promoted to an integer algebra equivalence using map_intCast. The integral basis is the actual native QuadraticAlgebra basis, with both basis vectors explicitly unfolded in the matrix computations. Multiplication by r+s*theta has matrix [[r,-210s],[s,r]]. The native algebra trace is 2r. The trace Gram matrix of the full integer basis is diag(2,-420), determinant -840.

Map this basis along the actual full integer algebra equivalence. Native discriminant invariance under algebra equivalence and NumberField.discr_eq_discr identify the field discriminant with -840. This avoids assuming the order is maximal or inferring the field discriminant from an arbitrary rank-two lattice.

The actual quadratic algebra has native rational finrank two. The native relation r1+2r2=2 leaves r2=0 or1. NumberField.sign_discr rules out r2=0 because the already constructed field discriminant is negative. Therefore r2=1 and r1=0.

Substitute these actual values into NumberField.exists_ideal_in_class_of_norm_le. Its real bound simplifies to 2sqrt(840)/pi. The exact native sqrt identity gives sqrt(840)<29; Real.pi_gt_d2 gives pi>3.14, hence 2sqrt(840)<19pi. For each native class, the native theorem supplies an actual nonzero integral ideal I with norm at most that bound. Its natural norm is less than19, hence at most18. No enumeration of ideals or binary forms is used in this proof, and no class-group exhaustion is asserted.

The old lost native class-number eight chain is a reconstruction guide only. These five sources have new hashes and need fresh independent source review and hosted elaboration. The audit-repair investigation remains separate; no frozen inherited source is silently changed here.
