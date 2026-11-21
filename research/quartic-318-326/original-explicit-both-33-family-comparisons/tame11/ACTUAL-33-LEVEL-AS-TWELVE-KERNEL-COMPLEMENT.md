# Produce the actual full-33 comparison from the full-3 universal family

## Exact input and scope

Work over S = Spec Z[1/33]. Retain the actual discriminant-210 maximal quaternionic order O and prescribed polarization element μ²=−210. Restrict Yuan's fine U(3) scheme X₃ and its universal abelian surface A₃/X₃ to S. The sole moduli representability input of the following construction is this genuine **fine** level-three model with its universal object. For identification with Yuan's existing name X₃₃, use that it represents the full principal-33 problem, not an independently specified forgetful morphism or universal-family comparison. This is no construction at residue characteristics 3 or 11, no replacement by a coarse twist and no change to the original t or its marked point.

At principal level the congruence subgroup acts trivially on O/3 and O/33 respectively, so a full principal marking is the descended O-linear frame of the corresponding prime-to-residue-characteristic torsion. No symplectic or determinant-fixed condition is added. [Yuan v2, §2.1](https://arxiv.org/html/2205.11334v2#S2.SS1) supplies the fine moduli scheme, determinant condition on Lie, and unique compatible principal polarization. For the explicit full-frame convention at the tame prime 11, see [Buzzard §1, Definition 1.1](https://www.ma.ic.ac.uk/~buzzard/maths/research/papers/shimura.pdf#page=3); his later representability results with prime-to-discriminant levels are not used at bad primes here.

## Construct the new finite scheme inside the actual old family

Put V=A₃[11]. It is a finite étale group scheme of degree 11⁴: multiplication by 11 on any abelian scheme over this base is étale by the invertible differential and smooth group translations; it is proper and fibrewise finite, hence finite, with degree checked on geometric abelian-surface fibres ([Stacks 39.9.8–9](https://stacks.math.columbia.edu/tag/0BF9)). Taking its kernel is base change along the actual zero.

Choose once a splitting O/11 O ≅ M₂(F₁₁), available because 11 does not divide 210 and O is maximal at 11. This concerns the acting ring, not a new trivialization of the selected surface's torsion. Each geometric fibre V is four-dimensional over F₁₁, with its actual M₂-action; the two complementary idempotents split it into two equal-dimensional summands, with inverse off-diagonal maps between them. It is therefore the regular left M₂-module, including over 2, 5, 7 on this base. This is not a semisimplicity claim about O/3.

For t∈F₁₁ use the rank-one operator whose first row is (1,t) and second row is zero. Add the rank-one operator with first row (0,1). Let K_t ⊂ V be the kernel group scheme of each of these 12 operators. These are open and closed finite étale subschemes: their defining equality is equality with the zero map into a finite étale separated scheme, whose diagonal is open and closed. Define the actual scheme

    R = V minus the union of these twelve K_t.

This is a finite étale open-and-closed subscheme of the one actual torsion scheme, not an application of the representability theorem for the 33 moduli problem. Fibrewise after any O-linear identification V ≅ M₂, a matrix P fails to be left cyclic precisely when its two columns have a nonzero annihilating row; every such row direction occurs among the twelve. Each K_t has exactly 11² points on a geometric fibre; distinct kernels meet exactly at zero because their independent rows kill both columns. Thus R has degree 11⁴−1−12(11²−1)=13200. The condition is independent of which splitting of O/11 was used, because it is exactly left cyclicity.

An O-linear map from the constant regular left module O/11 to V over an arbitrary base T→X₃ is determined by P=η₁₁(1): its value at a is aP. It is a full marking iff it is a fibrewise isomorphism of finite étale group schemes. This is equivalent to the T-point P factoring through the open-and-closed complement R. Hence R represents **adding** the 11-mark to the actual existing 3-mark. Its universal P is the universal 11-frame by this formula. This proof may replace the more general representability of finite locally constant sheaves, [Stacks 59.64.4](https://stacks.math.columbia.edu/tag/03RV).

## Exact one cartesian square and preservation of the given mark

On R keep the base-changed actual A₃, O-action, determinant condition, zero and polarization. Combine the already retained η₃ with this η₁₁ to get η₃₃ by the addition map on the two torsion kernels. Conversely the projectors [22] and [12] recover η₃ and η₁₁, with the unchanged original sign of η₃. These are equalities of group functors, natural over S. Full level 3 is already fine; there is accordingly no second quotient by ±1 and no automorphism ambiguity in identifying the polarized families. The unique μ-compatible polarization is transported unchanged.

Thus R canonically represents the full principal-33 problem and is the same X₃₃ by Yoneda. Its forgetful map to X₃ is induced by the actual structure R→X₃, not prescribed as input. Its universal abelian scheme over R is the constructed R×ₓ₃ A₃, with the actual Cartesian square and section. On the chosen generic point over L, the section of R is literally P=η₁₁(1) on the already fixed same A; adding the marks recovers the fixed full-33 point rather than another level branch. There is no assumption of a separate universal-family isomorphism for this one square.

## A cheaper exact integral extension on this overlap

If y₃ is already prolonged to Spec O_L[1/3], restrict it to T=Spec O_L[1/33]. Its pullback of R is finite over T. Write it as Spec B, with B finite over A=O_L[1/33]. The designated generic P gives an actual A-algebra map β:B→L. Every β(b) is integral over A and A is integrally closed, so β lands in A. Injectivity A→L makes the extension unique. Hence on this overlap the full 33-mark can be prolonged **from the known 3-section and chosen generic 11-mark**, without a second valuative extension argument for X₃₃. If used with the earlier proper X₃₃ extension, the two are equal by uniqueness on the same normal base.

The small independent Lean source in this packet formalizes precisely this last extension step for a genuine finite algebra section (more generally integral algebra); it does not construct A₃, A₃[11], the kernels, the moduli representation, or the Cartier/KS lines in Lean. The first mathematical proof here is independent of that native port. The 33→11 comparison involving the discarded ramified level 3 is not needed for this one constructed square and is not claimed by the matrix enumeration.
