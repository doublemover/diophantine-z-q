# Exact original local-sieve vanishing density

## Historical source and scope

Read the actual finite-field-count lemma, formula(eq:v5-local-g), and proof in quartics/quartic-318-326/docs/sources/quartic_v10.tex lines16547–16590. The preceding245-source packet constructs the literal primitive quadric, norm fibers and forbidden adjacent-norm estimates. This successor constructs the remaining exact coefficient-vanishing density on that same quadric, not a density hypothesis.

All245 inherited Lean sources remain byte-identical. Four new modules cover indexed vanishing loci, exact fibers, the full primitive ratio, and the original integer-coefficient residue application. This still does not prove the analytic prime-pattern existence theorem.

## Nonzero w: preserve and separate every coefficient

Locus(κ,γ,w) is the literal four-coordinate norm-difference fiber with the additional condition that some original norm-plus-γ_iw² vanishes. For w nonzero and injectiveγ, it is equivalent to the disjoint union over every original indexi of NormFiber(−γ_iw²)×NormFiber(−(γ_i+κ)w²). The forward map uses the actual pairs. Injectivity is proved by recovering the coefficient from its norm and cancelling the nonzero w²; surjectivity uses the original existential vanishing witness.

The two distinguished coefficients0 and−κ are distinct becauseκ is nonzero. Each gives one zero norm fiber and one nonzero norm fiber. Every other index gives two nonzero norm fibers. Writingν0=q+(q−1)epsilon and n=q−epsilon, epsilon=chi(−1), each nonzero-w fiber consequently has cardinality2ν0n+(k−2)n². A complete finite indicator sum, not an assumed count of special indices, supplies the factor2 and k−2.

## Zero w: do not count the same locus k times

At w0 every coefficient equation becomes the same zero-norm condition. A separate equivalence identifies this locus with NormFiber0×NormFiber0 using one actual index. Its cardinality isν0², not kν0². The exact original five-coordinate locus is then the disjoint union over allw, giving(q−1)[2ν0n+(k−2)n²]+ν0².

## Original primitive locus and density

The literal zero vector belongs to the total vanishing locus. Remove exactly this one vector. The numerator is therefore

(q−1)(q−epsilon)[2ν0+(k−2)(q−epsilon)]+ν0²−1.

The denominator is the already constructed q⁴−1 nonzero points of the same original quadric. Both natural-to-integer/rational subtractions check the relevant cardinality is positive. Their ratio is the actual definition of density.

For k2 and inert epsilon−1, the complete formula gives exactly2/(q²+1), not zero. The zero-w and distinguished-coefficient corrections are retained throughout.

## Actual integer coefficient application

The residue map is injective on the full original index type when the prime divides none of the named nonzero coefficient differences. This is proved using the exact ZMod integer-cast equality/divisibility theorem, in its correct subtraction direction. The separate exclusion p not dividingκ gives a nonzero residueκ. With p not2, original integer equations γ_i0=0 andγ_i1=−κ map to the same distinguished residues. OriginalSieveResidueDensity318.original_density applies the count with these inputs, not an assumed residue-injectivity assertion.

## Validation

Exact tests cover1128 coefficient systems,13360w-fibers,7552 literal primitive bad points and18 two-form inert cases. Repeated coefficients give a genuine overcounting negative control. Inherited finite checks, static dependency/placeholder/hash checks and audit-history self-test remain separate from hosted Lean acceptance. No local Lean was run. The analytic weighted count, fixed-field prime/Artin inputs, sieve tail and diagonal choice remain open formal producers.

## Hosted proof-boundary successor

The four new density sources remain exact copies. The sole predecessor change is the exact FormalPoleCoherentChart318 hosted-boundary repair documented in HOSTED-REPAIR.md.248 other Lean sources are identical to density249r1; original failure evidence is preserved.
