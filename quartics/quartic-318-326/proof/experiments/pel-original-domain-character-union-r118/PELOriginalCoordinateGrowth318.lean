module
public import PELOriginalSectionRingDomain318
public import PELOriginalSectionDegreeZero318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace PELOriginalCoordinateGrowth318
open PELOriginalGradedSectionRing318 PELOriginalSectionMultiplication318
open PELOriginalCubicRelationIdeal318 PELOriginalWholeHZeroDimension318
open PELOriginalLevelTheta318
variable (τ:ℂ)(hτ:0<τ.im)
/-- The exact first-isomorphism identification of the ACTUAL coordinate
quotient with its evaluated subalgebra. Thus the graded image pieces below
are pieces of this very quotient, not an unrelated ring. -/
@[expose] def coordinateEquivalence:
    (Equations⧸relations τ hτ)≃ₐ[ℂ](presentation τ hτ).range:=
  Ideal.quotientKerEquivRange (presentation τ hτ)
/-- The degree-n piece of the ACTUAL cubic coordinate image: homogeneous
polynomials of degree n evaluated in the SAME original section ring.
The degree corresponds to original power L^(3n), not L^n. -/
@[expose] def degreePiece(n:ℕ):Submodule ℂ (Ring τ hτ):=
  (MvPolynomial.homogeneousSubmodule (Label 3) ℂ n).map (presentation τ hτ).toLinearMap
@[expose] def sectionCoefficient(n:ℕ):Ring τ hτ→ₗ[ℂ]homogeneous τ hτ (3*n) where
  toFun p:=⟨p.val.coeff (3*n),p.property _⟩
  map_add' p q:=by apply Subtype.ext;exact Polynomial.coeff_add _ _ _
  map_smul' c p:=by apply Subtype.ext;exact Polynomial.coeff_smul _ _ _
@[expose] def intoOriginalHZero(n:ℕ):degreePiece τ hτ n→ₗ[ℂ]homogeneous τ hτ (3*n):=
  (sectionCoefficient τ hτ n).comp (degreePiece τ hτ n).subtype
/-- The actual image piece has precisely one formal degree. Extracting
its genuine original H0 coefficient and reinserting that degree is an
exact inverse, not a dimension assumption. -/
theorem reconstruct(n:ℕ)(a:degreePiece τ hτ n):
    includeDegree τ hτ (3*n) (intoOriginalHZero τ hτ n a)=a.val:=by
  obtain ⟨p,hp,hpa⟩:=a.property
  apply Subtype.ext
  change Polynomial.monomial (3*n) (a.val.val.coeff (3*n))=a.val.val
  rw [←hpa,underlying_presentation,CubicHomogeneousMarker318.homogeneous_marker _ _ p n hp,
    Polynomial.coeff_monomial_same]
theorem intoOriginalHZero_injective(n:ℕ):Function.Injective (intoOriginalHZero τ hτ n):=by
  intro a b h
  apply Subtype.ext
  rw [←reconstruct τ hτ n a,←reconstruct τ hτ n b,h]

instance pieceFinite(n:ℕ):FiniteDimensional ℂ (degreePiece τ hτ n):=by
  by_cases hn:n=0
  · subst n
    exact FiniteDimensional.of_injective (intoOriginalHZero τ hτ 0)
      (intoOriginalHZero_injective τ hτ 0)
  · letI:NeZero (3*n):=⟨Nat.mul_ne_zero (by decide) hn⟩
    exact FiniteDimensional.of_injective (intoOriginalHZero τ hτ n)
      (intoOriginalHZero_injective τ hτ n)
/-- Rigorous growth bound for the ACTUAL coordinate image, derived from
injection into all original holomorphic sections. It is not yet an
algebraic dimension calculation, a Hilbert polynomial equality, or
normal generation. -/
theorem whole_growth_bound(n:ℕ):
    Module.finrank ℂ (degreePiece τ hτ n)≤if n=0 then 1 else 9*n^2:=by
  by_cases hn:n=0
  · subst n
    have h:=LinearMap.finrank_le_finrank_of_injective (intoOriginalHZero_injective τ hτ 0)
    simpa only [Nat.mul_zero,PELOriginalSectionDegreeZero318.whole_hilbert_function,
      if_pos rfl] using h
  · letI:NeZero (3*n):=⟨Nat.mul_ne_zero (by decide) hn⟩
    have h:=LinearMap.finrank_le_finrank_of_injective (intoOriginalHZero_injective τ hτ n)
    rw [PELOriginalSectionDegreeZero318.whole_hilbert_function,
      if_neg (Nat.mul_ne_zero (by decide) hn)] at h
    rw [if_neg hn]
    convert h using 1 <;> ring
end PELOriginalCoordinateGrowth318
