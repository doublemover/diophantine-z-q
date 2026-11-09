# Actual cusp assignment and analytic uniformizers

Status: frozen. Seventeen sources passed fresh strict replay and a private-inclusive
recursive audit of 378 declarations. Distinct non-author review is pending.

This packet identifies the actual source cusps with the two rational parameter
cusps. In the genuine identity-cusp q coordinate, the original T has order -1;
its reciprocal extends analytically by zero with derivative exactly 1. In the
genuine S-cusp width-three q coordinate, T has order 1, extends analytically by
zero, and has nonzero derivative. These are actual source-cusp uniformizers,
not only the pole orders of an independently specified rational target function.

Thirteen predecessor sources are unchanged. Four new modules compare the exact
meromorphic orders, normalize the identity-cusp leading coefficient, and use
actual global injectivity and disjoint cusp neighborhoods to select the other
cusp's zero rather than its initially possible pole.

## Exact application contract

1. Source object and germ. The functions are exactly qParameter g from the prior
   packet: the original full quotient T evaluated in the inverse genuine width-q
   cusp homeomorphism. Their established meromorphy and nonvanishing on punctured
   discs imply finite integer meromorphic order. Their arbitrary total value at
   zero is explicitly zero, and analyticity at zero is proved only when justified
   by positive order. The reciprocal is the same function's field inverse.
2. All rotations and order comparison. For every integral rotation, the exact
   identity J(T(q))=G(q^w)/q^w gives source j-order -w with w positive. Orders of
   multiplication, division and powers are applied to actual meromorphic germs.
   If T has negative order m, adding either nonzero constant leaves order m, so
   J(T) has order m. If m is positive, both numerator factors have order zero,
   so J(T) has order -3m. If m=0, both numerator orders are nonnegative, which
   contradicts the negative source j-order. Infinite order is excluded by actual
   punctured nonvanishing. Thus every rotation is covered without assuming a
   branch, derivative or cusp assignment.
3. Exact width specialization. The already proved widths are 1 at the identity
   rotation and 3 at S. The positive-order option is arithmetically impossible
   at width 1, giving T order -1 there. At S the order calculation initially
   permits -3 or 1; the subsequent global argument is required and supplied,
   rather than choosing the desired alternative by the target pole labels.
4. Reciprocal normalization. The identity cusp reciprocal H=1/T has positive
   order 1 and actual value zero, hence is analytic at the origin. Substituting
   into the literal reciprocal J formula gives H(q)=q U(q), where
   U=(1+27H)(1+243H)^3/G(q). The genuine q-j normalization has G(0)=1, so U is
   analytic and U(0)=1. Eventual equality on the punctured neighborhood is extended
   using continuity of both germs. Differentiation yields H'(0)=1 exactly.
5. Local inverse and source coverage. The actual analytic inverse of H near zero
   exists by that derivative and fixes zero. Its eventual right-inverse identity
   and continuity ensure small target reciprocals map inside the actual identity
   cusp disc. A nonzero reciprocal cannot map to the disc origin. If T had a pole
   at S, its reciprocal would tend to zero, so every sufficiently small nonzero
   S-cusp q would have the same T-value as an actual point of the identity cusp
   neighborhood. All these local domains are explicitly intersected before use.
6. Identity of the global consumer. Equality of those two T-values is converted
   to equality of their original quotient points by the previously proved full
   quotient parameter injectivity. Both points lie in the original identity and
   S rotated height-two neighborhoods, proved disjoint independently. This gives
   the contradiction excluding S-order -3. No abstract two-point end set,
   target compactification, or new topology replaces the source neighborhoods.
7. Actual uniformizers. The remaining S-order is 1. Since the original total
   function's value at zero is zero, positive order proves its analytic extension.
   A general order-one analytic germ is factored as q times an analytic unit;
   continuity extends that factorization to the full germ and differentiation
   gives nonzero derivative. Thus T is a genuine local analytic coordinate at S,
   and 1/T is one at infinity. No unsupported inverse-analytic conclusion is
   deduced merely from topological bijectivity.
8. Dependencies and historical scope. All thirteen preceding sources are
   byte-identical, including actual meromorphy, actual global homeomorphism and
   actual cusp orbit/width proofs. The original rational reciprocal formula,
   Mathlib meromorphic-order conventions, local analytic inverse theorem and
   actual source-neighborhood disjointness are used as stated. Existing historical
   target branch orders and high-level quotient atlases remain unchanged; the new
   result supplies the missing application to actual source-cusp germs.
9. Verification and remaining consumers. Seventeen exact sources are freshly
   replayed serially with Lean 4.35.0 and kernel checking enabled. The recursive
   audit includes all private declarations and allows only propext,
   Classical.choice and Quot.sound. Exact baseline pins and producer hashes bind
   the packet. Distinct review is required before admission. A global map out of
   the actual simultaneous filling, full analytic atlas compatibility, compact
   biholomorphism, arithmetic analytification, PEL identification and final height
   theorem are not inferred or claimed here.

## Remaining boundary

The actual two cusp assignments and their local analytic uniformizers are now
proved. The global filled map and full quotient/filled complex-analytic structure
still need their explicit constructions and compatibility proofs. The PEL,
arithmetic model and FiveContact49Height/sourceArithmetic endpoints remain open.
