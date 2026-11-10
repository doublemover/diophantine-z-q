module
public import ContactInfinityPrincipalParts318
public import ReciprocalInfinityNormalization318
public import SourceInfinityOverlap318

public section
noncomputable section
namespace ContactInfinityRegularFractions318
attribute [-instance] DivisionRing.toRatAlgebra
open Polynomial InfinityFieldCoordinates318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev Base := InfinityOpenChart318.OpenBase c
abbrev InfinityRing := InfinityOpenChart318.OpenOrder c
abbrev OverlapRing := ContactKummerOrder318.OpenOrder c
abbrev D := InfinityOpenChart318.denominator c
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

@[expose] def baseEmbedding : Base c →+* L c :=
  (InfinityOpenFractionField318.openEmbedding c).comp (algebraMap (Base c) (InfinityRing c))

theorem baseEmbedding_polynomial (P : ℚ[X]) :
    baseEmbedding c (algebraMap ℚ[X] (Base c) P) = aeval (u c) P :=
  ReciprocalInfinityNormalization318.openEmbedding_on_polynomial c P

theorem baseEmbedding_inverse :
    baseEmbedding c (IsLocalization.Away.invSelf (D c)) = (aeval (u c) (D c))⁻¹ := by
  have h := congrArg (baseEmbedding c) (IsLocalization.Away.mul_invSelf (S:=Base c) (D c))
  rw [map_mul,map_one,baseEmbedding_polynomial] at h
  apply mul_left_cancel₀ (ContactInfinityPrincipalParts318.denominator_at_u_ne_zero c)
  rw [h,mul_inv_cancel₀ (ContactInfinityPrincipalParts318.denominator_at_u_ne_zero c)]

/-- A regular fraction as an actual element of the original infinity base ring. -/
@[expose] def regularCoefficient (P : ℚ[X]) (m : ℕ) : Base c :=
  algebraMap ℚ[X] (Base c) P * (IsLocalization.Away.invSelf (D c))^m

theorem regularCoefficient_embedding (P : ℚ[X]) (m : ℕ) :
    baseEmbedding c (regularCoefficient c P m) =
      aeval (u c) P / (aeval (u c) (D c))^m := by
  simp only [regularCoefficient,map_mul,map_pow,baseEmbedding_polynomial,
    baseEmbedding_inverse,div_eq_mul_inv,inv_pow]

/-- Every actual localized infinity coefficient has such an original fraction representation. -/
theorem coefficient_fraction (a : Base c) :
    ∃ m : ℕ, ∃ P : ℚ[X], baseEmbedding c a =
      aeval (u c) P / (aeval (u c) (D c))^m := by
  obtain ⟨m,P,hP⟩ := IsLocalization.Away.surj (D c) a
  refine ⟨m,P,(eq_div_iff (pow_ne_zero m
    (ContactInfinityPrincipalParts318.denominator_at_u_ne_zero c))).mpr ?_⟩
  have h := congrArg (baseEmbedding c) hP
  simpa only [map_mul,map_pow,baseEmbedding_polynomial] using h

@[expose] def inverseU : OverlapRing c :=
  (((SourceInfinityOverlap318.u_unit c).unit⁻¹ : (OverlapRing c)ˣ) : OverlapRing c)

/-- The principal term is also an actual element of the original overlap ring. -/
@[expose] def principalTerm (P : ℚ[X]) (n : ℕ) : OverlapRing c :=
  InfinityOverlapLocalization318.toOpen c
    (algebraMap (Base c) (InfinityRing c) (algebraMap ℚ[X] (Base c) P)) *
      (inverseU c)^n

theorem inverse_u_embedding :
    SourceOpenFractionField318.openEmbedding c (inverseU c) =
      (u c)⁻¹ := by
  have hu : (((SourceInfinityOverlap318.u_unit c).unit : (OverlapRing c)ˣ) : OverlapRing c) =
      SourceInfinityOverlap318.u c := (SourceInfinityOverlap318.u_unit c).unit_spec
  have huinv : SourceInfinityOverlap318.u c * inverseU c = 1 := by
    rw [← hu]
    exact (SourceInfinityOverlap318.u_unit c).unit.mul_inv
  have h := congrArg (SourceOpenFractionField318.openEmbedding c) huinv
  simp only [Units.val_mul,Units.val_one,map_mul,map_one,hu,SourceInfinityOverlap318.u_embedding] at h
  apply mul_left_cancel₀ (u_ne_zero c)
  rw [h,mul_inv_cancel₀ (u_ne_zero c)]

theorem principalTerm_embedding (P : ℚ[X]) (n : ℕ) :
    SourceOpenFractionField318.openEmbedding c (principalTerm c P n) =
      aeval (u c) P / (u c)^n := by
  simp only [principalTerm,map_mul,map_pow,InfinityOverlapLocalization318.toOpen_embedding,
    ReciprocalInfinityNormalization318.openEmbedding_on_polynomial,
    inverse_u_embedding,div_eq_mul_inv,inv_pow]

/-- The infinity-regular remainder is constructed in its actual ring, not only in the field. -/
theorem principal_reduction (P : ℚ[X]) (n m : ℕ) :
    ∃ R : ℚ[X], ∃ b : InfinityRing c, R.degree < (n : WithBot ℕ) ∧
      aeval (u c) P / ((u c)^n * (aeval (u c) (D c))^m) =
        SourceOpenFractionField318.openEmbedding c (principalTerm c R n) +
          InfinityOpenFractionField318.openEmbedding c b := by
  obtain ⟨R,S,hR,h⟩ := ContactInfinityPrincipalParts318.fraction_decomposition c P n m
  refine ⟨R,algebraMap (Base c) (InfinityRing c) (regularCoefficient c S m),hR,?_⟩
  rw [principalTerm_embedding]
  change _ = _ + baseEmbedding c (regularCoefficient c S m)
  rw [regularCoefficient_embedding]
  exact h


/-- Every original infinity-base coefficient, after a pole at u=0, reduces
inside the actual overlap ring to a bounded principal term plus an actual
infinity-regular ring element. -/
theorem coefficient_principal_reduction (a : Base c) (n : ℕ) :
    ∃ R : ℚ[X], ∃ b : InfinityRing c, R.degree < (n : WithBot ℕ) ∧
      InfinityOverlapLocalization318.toOpen c (algebraMap (Base c) (InfinityRing c) a) *
          (inverseU c)^n =
        principalTerm c R n + InfinityOverlapLocalization318.toOpen c b := by
  obtain ⟨m,P,hP⟩ := coefficient_fraction c a
  obtain ⟨R,b,hR,h⟩ := principal_reduction c P n m
  refine ⟨R,b,hR,?_⟩
  apply SourceOpenFractionField318.openEmbedding_injective c
  simp only [map_mul,map_pow,map_add,InfinityOverlapLocalization318.toOpen_embedding,
    inverse_u_embedding]
  change baseEmbedding c a * ((u c)⁻¹)^n = _
  rw [hP]
  calc
    aeval (u c) P / (aeval (u c) (D c))^m * ((u c)⁻¹)^n =
        aeval (u c) P / ((u c)^n * (aeval (u c) (D c))^m) := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    _ = _ := h

end ContactInfinityRegularFractions318
