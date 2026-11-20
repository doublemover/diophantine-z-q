# Constructive actual real Brauer invariant, source-only

Pinned project 558a130e12a461d9b380b44510d457f0d3d8a29d, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, Lean 4.35.0. No Lean, push or hosted launch. SOURCE-CLOSURE.json gives exact input owners and source hashes.

- CTCyclicTwoBar318 (1/0/2): in ordinary unnormalized additive C₂ bar notation, with conjugation/action s, compute c(1,g)=c(1,1), c(g,1)=g·c(1,1); the normalized value x=c(s,s)-s·c(1,1) is s-fixed. If c=db then x=N_s(b(s)-b(1)). Conversely if N_s u=x take b(g)=c(1,1)+[g=s]u. Every fixed x occurs via the cochain x at (s,s), zero elsewhere. No normalization requirement on input. Exact integer canary checks all surviving cycle rows on four independent actions on Z/8.
- CTComplexUnitNorm318 (1/0/2): in literal ℂ×, Norm u = conj(u)u = normSq(u)>0; every positive real r is a norm via its nonzero real square root. These are exact coefficient statements, not assumptions about unspecified local classes.
- CTRealClosureConjugation318 (1/0/4): one actual ℝ-algebra equivalence AlgebraicClosure ℝ≃ℂ from FTA and finite dimension, actual absolute Galois group has identity and transported conjugation only. Krull discreteness is on the same group, via the open stabilizer of the preimage of i. It is not an alternate topology placed on the cochains.
- CTRealNativeBar318 (8/0/15): same native d₁ and d₂ action and signs, under tuple↔pair cochain identifications. Discreteness implies all bar one-cochains used in the boundary criterion are genuine locally constant one-cochains. Computes native ContH2 zero iff realized norm, not quotient by arbitrary cochains in general.
- CTRealNativeNormClass318 (10/0/17): transported complex unit via the same ℝ-algebra equiv, actual conjugation intertwining, exact normalized class vanishes iff a positive real. Sign multiplies on sums; explicit (s,s)=-1 Hamilton cycle has sign -1.
- CTRealNativeInvariant318 (12/0/19): the exact native invariant is a hom into ℚ/ℤ sending positive to 0, negative to 1/2. Proves it factors through literal continuous boundaries, is injective with image all (ℚ/ℤ)[2], and gives the additive equivalence. No local arithmetic theorem supplied as an assumption. This is a draft formal proof, not an accepted result.
- CTActualRealInvariantSupplier318 (15/0/22): discharges only the real member of the earlier actual-global-value input and leaves the p-adic actual invariant equivalences external. It also leaves the p-adic canonical arithmetic Frobenius orientation, ABHN, global H³, actual elliptic representative descent, and alternating/dual radical outside. It is not a Cassels–Tate proof.

Exact API pins: Complex algebra/hom/conjugation Mathlib/LinearAlgebra/Complex/Module.lean 57b2542a8bb51865cf6e6e09bdbfddb60f4f9412 L250–274; FTA Mathlib/Analysis/Complex/Polynomial/Basic.lean da59eb616eebae98107a02ab0aa7ec7b7ba16a91 L50–60; algebraic closure equivalence Mathlib/FieldTheory/IsAlgClosed/Basic.lean e2a382ab7779e0c17a5482ec828ce3645bcdeee4 L397ff; actual absolute group df9d6df96b4d2d74ee22d9125c6f685f7101066d L42 and AlgEquiv.autCongr 0897ffa92fc5db60f3e5106e5f494f126933ba5a L683ff. Real coefficient identities Mathlib/Basic/Complex/Basic.lean 0bd1c511d5e6483c9819496d644820b6d4b0545a L492, L520, L544, L564; positive sqrt a38cafe76a6bd18c19a323bc8d5d8d50801c9c29 L174, L272. Pinned bar differentials d8d0c75f895b029378093024a0fdac434d83ae1b L124–151; tuple contraction 4d5246282f7e36c96532dde9af94095503270871 L1270ff; finite product discreteness d02d2f98e431656118c192638682887d73b13a19 L1213 and IsLocallyConstant.of_discrete 536041ba7dad518f8597cf36de33f0b4cf83a8d3 L64. Exact torsion lemma AddCircle.nsmul_eq_zero_iff at ff91ca21a74cd801caaeda5809cd73823accba0b L625ff.

Primary normalization: [Milne, Class Field Theory IV.4, the real numbers](https://jmilne.org/math/CourseNotes/CFT.pdf) identifies H² with ℝ×/Nm(ℂ×), and its nonzero Hamilton class has cocycle -1 at the two conjugations. The paper formula here uses c(s,s)-s·c(1,1) to justify matching an arbitrary native unnormalized cochain to that computation. Neither the checked reference nor an exact small arithmetic enumeration is being used as a formal substitute for hosted verification.

## r2 source visibility and notation only

The immutable parent has intake 80e678b29419fba106f44887aff6c44adb89e1a0438228eeb3427209fe97bbc0.
Independent cold review found the pinned operation is the scoped notation conj for starRingEnd, not the
constant Complex.conj. r2 uses the exact starRingEnd ℂ function at every such term, retaining all named
Complex.conj_* proof lemmas. The actual absolute group is publicly imported where its RealGal abbrev is
exported. The proof-only C2 bar definally equal evaluation head is accessible via import all in the native
Bar owner. The 4 changed files are ComplexUnitNorm, RealClosureConjugation, RealNativeBar, RealNativeNormClass.
No arithmetic signs, hypotheses, endpoints, other source bytes, or selector counts changed.
