module
public import SelectedOriginalGenericChartClosures318
public import IntegralClosureSquare318
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.Integral
public section
noncomputable section

open Polynomial
open scoped LaurentPolynomial
open SelectedOriginalGenericChartClosures318
namespace SelectedOriginalGenericClosureOverlap318

abbrev Laurent := LaurentPolynomial ℚ

variable (K : Type) [Field K] [Algebra JField K]

/-- The coordinate unit for a chart: J on chart 1 and J⁻¹ on chart 0. -/
@[expose] def unitAt (i : Fin 2) : Kˣ :=
  if i = 0 then (Units.mk0 (coordinate K) (coordinate_ne_zero K))⁻¹
  else Units.mk0 (coordinate K) (coordinate_ne_zero K)

theorem unitAt_value (i : Fin 2) : (unitAt K i : K) = polynomial K i X := by
  fin_cases i
  · simp [unitAt,polynomial_X₀,Units.val_inv_eq_inv_val]
  · simp [unitAt,polynomial_X₁]

variable [aK : Algebra ℚ K] [hTower : IsScalarTower ℚ JField K]

/-- The overlap Laurent ring evaluates in the SAME field, for each
of the genuine projective coordinate conventions. -/
@[expose] def evaluation (i : Fin 2) : Laurent →+* K :=
  LaurentPolynomial.eval₂ (algebraMap ℚ K) (unitAt K i)

include hTower in
theorem evaluation_polynomial (i : Fin 2) (p : ℚ[X]) :
    evaluation K i (algebraMap ℚ[X] Laurent p) = polynomial K i p := by
  rw [evaluation,LaurentPolynomial.algebraMap_eq_toLaurent,LaurentPolynomial.eval₂_toLaurent,
    unitAt_value]
  have he := congrArg (fun f : ℚ[X] →+* K => f p) (polynomial_eq_aeval K i)
  simpa only [Polynomial.aeval_def,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using he.symm

abbrev Order (i : Fin 2) :=
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  integralClosure ℚ[X] K

abbrev OverlapOrder (i : Fin 2) :=
  letI : Algebra Laurent K := (evaluation K i).toAlgebra
  integralClosure Laurent K

/-- The element inverted in each normalization chart is its own
original base polynomial coordinate, pulled into the integral closure. -/
@[expose] def parameter (i : Fin 2) : Order K i := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  exact algebraMap ℚ[X] (Order K i) X

include hTower in
@[expose] def restrictOrder (i : Fin 2) : Order K i →+* OverlapOrder K i := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : Algebra Laurent K := (evaluation K i).toAlgebra
  have he : (algebraMap Laurent K).comp (algebraMap ℚ[X] Laurent) =
      (RingHom.id K).comp (algebraMap ℚ[X] K) :=
    RingHom.ext (evaluation_polynomial K i)
  exact
    { toFun := fun x => ⟨(x : K),
        IsIntegral.map_of_comp_eq (algebraMap ℚ[X] Laurent) (RingHom.id K) he x.property⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

include hTower in
theorem restrictOrder_val (i : Fin 2) (x : Order K i) :
    ((restrictOrder K i x : OverlapOrder K i) : K) = x := rfl

include hTower in
/-- Exact localization of each actual chart order into the Laurent
integral closure. The proof clears powers of that chart's own X
and keeps the element in the original generic field K. -/
theorem restrict_isLocalization (i : Fin 2) :
    letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
    IsLocalization.Away (parameter K i) (OverlapOrder K i) := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  letI : Algebra Laurent K := (evaluation K i).toAlgebra
  letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
  letI : IsScalarTower ℚ[X] Laurent K :=
    IsScalarTower.of_algebraMap_eq (fun p => (evaluation_polynomial K i p).symm)
  apply IsLocalization.Away.mk
  · have h : algebraMap (Order K i) (OverlapOrder K i) (parameter K i) =
        algebraMap Laurent (OverlapOrder K i) (algebraMap ℚ[X] Laurent X) := by
      apply Subtype.ext
      exact (evaluation_polynomial K i X).symm
    rw [h]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Laurent) (X : ℚ[X])).map
      (algebraMap Laurent (OverlapOrder K i))
  · intro z
    obtain ⟨⟨_,n,rfl⟩,hn⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (M := Submonoid.powers (X : ℚ[X])) (Rₘ := Laurent) (z : K) z.property
    refine ⟨n,⟨(X : ℚ[X])^n • (z : K),hn⟩,?_⟩
    apply Subtype.ext
    change (z : K) * (polynomial K i X)^n = (X : ℚ[X])^n • (z : K)
    have hX : algebraMap ℚ[X] K (X : ℚ[X]) = polynomial K i X := rfl
    rw [Algebra.smul_def,map_pow,hX,mul_comm]
  · intro x y h
    have hh : restrictOrder K i x = restrictOrder K i y := h
    have hv := congrArg (fun z : OverlapOrder K i => (z : K)) hh
    have hxy : x = y := Subtype.ext
      ((restrictOrder_val K i x).symm.trans (hv.trans (restrictOrder_val K i y)))
    exact ⟨0,by simpa only [pow_zero,one_mul] using hxy⟩

include hTower in
@[expose] def restrictIso (i : Fin 2) :
    letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
    Localization.Away (parameter K i) ≃ₐ[Order K i] OverlapOrder K i := by
  letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
  letI : IsLocalization.Away (parameter K i) (OverlapOrder K i) := restrict_isLocalization K i
  exact IsLocalization.algEquiv (Submonoid.powers (parameter K i)) _ _

theorem evaluation_inversion :
    (evaluation K 1).comp LaurentPolynomial.invert.toRingHom = evaluation K 0 := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : ℚ[X]))
  apply Polynomial.ringHom_ext
  · intro r
    change evaluation K 1 (LaurentPolynomial.invert (algebraMap ℚ[X] Laurent (C r))) =
      evaluation K 0 (algebraMap ℚ[X] Laurent (C r))
    simp [evaluation,LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_C]
  · change evaluation K 1 (LaurentPolynomial.invert (algebraMap ℚ[X] Laurent X)) =
      evaluation K 0 (algebraMap ℚ[X] Laurent X)
    rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    rw [LaurentPolynomial.invert_T]
    have h := LaurentPolynomial.eval₂_T_neg_n (algebraMap ℚ K) (unitAt K 1) 1
    have h' := LaurentPolynomial.eval₂_T_n (algebraMap ℚ K) (unitAt K 0) 1
    simp only [pow_one,Nat.cast_one] at h h'
    have hu : (↑((unitAt K 1)⁻¹) : K) = (unitAt K 0 : K) := by simp [unitAt]
    exact h.trans (hu.trans h'.symm)

/-- On the overlap the two coordinate names are reciprocal; equality
of elements is still equality IN the original whole field K. -/
@[expose] def invertOverlap : OverlapOrder K 0 ≃+* OverlapOrder K 1 := by
  letI : Algebra Laurent K := (evaluation K 0).toAlgebra
  -- Use explicit source and target algebra parameters: the carrier K is
  -- equal, but the two Laurent actions must not be unified.
  exact @IntegralClosureSquare318.closureEquiv Laurent K Laurent K _ _ _ _
    (evaluation K 0).toAlgebra (evaluation K 1).toAlgebra
    LaurentPolynomial.invert.toRingEquiv (RingEquiv.refl K)
    (by
      change (evaluation K 1).comp LaurentPolynomial.invert.toRingHom =
        (RingHom.id K).comp (evaluation K 0)
      rw [RingHom.id_comp]
      exact evaluation_inversion K)

theorem invertOverlap_val (z : OverlapOrder K 0) :
    ((invertOverlap K z : OverlapOrder K 1) : K) = z := rfl

include hTower in
@[expose] def overlapIso :
    Localization.Away (parameter K 0) ≃+* Localization.Away (parameter K 1) := by
  letI : Algebra (Order K 0) (OverlapOrder K 0) := (restrictOrder K 0).toAlgebra
  letI : Algebra (Order K 1) (OverlapOrder K 1) := (restrictOrder K 1).toAlgebra
  exact (restrictIso K 0).toRingEquiv.trans
    ((invertOverlap K).trans (restrictIso K 1).symm.toRingEquiv)

end SelectedOriginalGenericClosureOverlap318

#print axioms SelectedOriginalGenericClosureOverlap318.restrict_isLocalization
#print axioms SelectedOriginalGenericClosureOverlap318.invertOverlap_val
#print axioms SelectedOriginalGenericClosureOverlap318.overlapIso
