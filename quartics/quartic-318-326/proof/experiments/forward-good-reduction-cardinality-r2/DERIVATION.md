# Same-model good reduction and actual order comparison

## Historical and actual source comparison

Read the actual COMPLETENESS-ASSEMBLY.md section6 and the original BranchHalving.explicit_half/from_roots argument, not just earlier acceptance summaries. That route uses the precise original R, its inclusion in the doubling image under additional Gaussian ray hypotheses, the finite curve cardinality d, and the factor d/4. Existing GlobalReductionCounts counts concrete residue models but does not identify the actual Qp formal quotient. Existing CompactLocalPointCoding proves finiteness for the actual quotient, even at bad reduction, but contains no cardinality comparison. This packet supplies the good-reduction cardinality bridge. The historical finite-curve/doubling route is already present; incorporation of its actual quotient comparison is advanced here, while Gaussian counting and the additional halving factor remain pending.

## 1. Actual residue map and unit derivative

The reduction map is the pinned PadicInt.toZMod ring homomorphism from Zp to ZMod p. Its kernel is the actual maximal ideal. The pinned maximalIdeal_eq_span_p and norm_lt_one_iff_dvd identify zero reduction with norm<1. Hence equal residues mean difference norm<1, and nonzero reduction means norm1, using the actual integral norm bound.

For a residue curve y²=x³−D*x, assume p odd and D has nonzero reduction. The exact discriminant polynomial identity4D³=(4D−3x²)(3x²−D)²+27y⁴ proves that2y and3x²−D cannot both vanish. The proof is over an arbitrary field of characteristic different from2, including characteristic3, not an illicit characteristic-zero argument in ZMod p. Transporting this through the same reduction map gives one actual unit derivative at each integral point of the original model.

## 2. Genuine residue-preserving Hensel lifting

The helper hensel_same_residue keeps all necessary conclusions of the pinned hensels_lemma. A zero residue gives residual norm<1 and a nonzero derivative residue gives derivative norm1. Thus the strict Hensel inequality holds. The returned actual zero b has distance from the chosen representative strictly below the derivative norm1, so its residue equals the original representative's residue.

For an arbitrary actual residue point, choose canonical natural representatives x,y. If2y is nonzero modulo p, apply Hensel to Y²−(x³−Dx), varying only y. Otherwise use the unit derivative3x²−D and X³−DX−y², varying only x. Both cases return an actual integral point with the exact original two residues. No singular residual points are omitted, since good reduction plus the discriminant identity ensures one chart works. Characteristic3 is covered by the abscissa chart when needed.

## 3. Both directions of the actual coset relation

An integral point is mapped to the original Mathlib affine point with explicitly produced nonsingularity; no unrelated curve or substitute group law appears. Its formal subgroup is precisely the existing AlgebraicFormalSubgroup, whose carrier is zero or an x-coordinate pole of norm>1.

Equal residue coordinates have both differences of norm<1. The derivative-unit result supplies the actual ordinate or abscissa chart required by LocalPointDifference.close_points. That producer retains secants, equality, and the same-x inverse/tangent branch, so it proves membership of the actual difference in the original formal subgroup. QuotientAddGroup.eq_zero_iff then gives equality of their actual classes.

For the converse, distinct integral residue coordinates give a unit coordinate difference. If x1 differs from x2 and their difference is a unit, the original slope(y1+y2)/(x1−x2) is integral. If only y2−y1 is a unit, the exact curve subtraction identity gives the alternate slope−(x1²+x1x2+x2²−D)/(y2−y1), also integral. Both yield integral actual difference abscissa, not a formal pole.

If x1=x2, the original curve equations force y2=y1 or y2=−y1. Distinct residues rule out equality and force2y1 a unit in the inverse case. The actual difference is then the actual double of P, whose tangent slope(3x1²−D)/(2y1) is integral. Its abscissa remains integral. In every branch the two points are distinct, excluding the zero-point alternative in the formal subgroup. This proves different residue coordinates cannot give the same actual coset, including all exceptional secant/tangent cases.

## 4. Bijection and exact cardinality

For every residue point choose the actual Hensel lift and send it to its original formal quotient class; send the extra infinity code to zero. Integral affine points are not formal, so no affine code equals infinity. The converse coset result proves injectivity of the code, and the lift residue identities recover the original labels.

Every original quotient class has an actual point representative. If formal it is the infinity code. Otherwise the original x-coordinate is integral, and the original ordinate-integral lemma makes y integral. Reduce those exact coordinates, lift their residue, and use the same-residue direction to recover the same class. This proves surjectivity. Equiv.ofBijective therefore constructs an actual equivalence of the formal quotient with Option of the literal residue equation solutions. Nat.card_congr and the finite Option cardinality formula give exactly1 plus the affine count. No reduction group homomorphism is assumed or claimed; the set bijection suffices for cardinality.

## 5. Original selected coefficient and all15 actual orders

The integral coefficient is exactly the original embedding of D, with its actual integral bound. The existing norm49/conjugate argument gives valuation0 away from7, and the actual p-adic norm/valuation formula gives norm1. The selected rho is integral; reducing its exact equation gives rho_bar²=2. Reducing the exact coefficient identity gives D_bar=(3−rho_bar)². Thus the resulting count is of the literal finite curve y²=x³−(3−rho_bar)²x.

The generic formal subgroup specializes definitionally to SelectedQuotientOrders.subgroup, and the point whose order is consumed is its original generator: the original half-point R class, not P=2R. The exact quotient cardinality theorem and the pinned additive Lagrange theorem give actual_order_dvd for this full finite-curve count. For every Fin3×Fin5 position and its exact negative-root opposite, the original actual order divides its literal count. dvd_lcm and the existing actual-modulus consumer then prove both constructed actual LCMs divide the all15 corresponding full-count LCMs. Duplicate prime positions and arbitrary orientation choices remain represented.

## 6. Validation and deliberately retained stronger boundary

203 predecessor files are unchanged; the five new files have finite1M budgets. Static closure is208 modules and220 baseline dependencies. Pinned primary APIs include PadicInt.toZMod and kernel/norm equivalences, the full Hensel output including closeness, actual Point secant/tangent constructors, Nat.card_congr, and orderOf_dvd_natCard with its generated additive form. The exact checker retains all203 source tests and adds2,900 ordinate-chart and296 abscissa-chart modular lifts through p³, exact discriminant/secant polynomial identities, and12 literal finite-curve counts and original R orders.

The checker records a critical negative control: p17,rho6 has full count20 and R order10; similar controls occur at other split primes. Therefore divisibility by the full count does not imply divisibility by count/4 under the hypotheses used here. The historical stronger Gaussian ray/root/halving calculation must still supply that step, followed by the actual CM count and prime/order separation. The new bijection is not advertised as a group isomorphism; this proof uses only its exact cardinality and Lagrange in the already existing original quotient group.

Finite checks and source closure are not kernel proofs. Hosted elaboration/recursive axiom audit and independent bounded source review remain separate. Four rational TwoTwist Realizations, the global rational-anchor implication and compatible prime-pattern production remain unchanged global inputs; the literal source polynomial and all fixed signs are untouched.
