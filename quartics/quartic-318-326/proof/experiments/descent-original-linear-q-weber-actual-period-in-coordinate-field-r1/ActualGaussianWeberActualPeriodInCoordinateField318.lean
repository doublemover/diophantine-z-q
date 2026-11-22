module
public import ActualGaussianWeberTorsionAlgebraicByOrigin318
public import ActualLSGOriginalFullUniformization318
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public section
noncomputable section

namespace ActualGaussianWeberActualPeriodInCoordinateField318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberPlaceEquivariance318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberTorsionAlgebraicByOrigin318
open ActualGaussianComplexTorusKernel318 ActualLSGOriginalFullUniformization318

attribute [local instance] Classical.decEq

private theorem reflects_zero {A F : Type*} [Field A] [Field F]
    (f : A→+*F) (hF : (2:F)≠0) (P : WP A)
    (h : coordinateHom f hF P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    change onCurvePoint f hF (Point.some x y hxy)=(0:WP F) at h
    rw [point_some f hF hxy] at h
    exact False.elim (Point.some_ne_zero _ h)

/-- One supplied, already designated algebraic-closure map, not
an independently chosen complex embedding. -/
private theorem lift_integral_through_named_embedding
    {K A F : Type*} [Field K] [Field A] [Field F] [Algebra K A] [Algebra K F]
    [IsAlgClosed A] (e : A→ₐ[K]F) (x : F) (hx : IsIntegral K x) :
    ∃ z : A, e z=x := by
  let R := e.fieldRange
  let g : A≃ₐ[K]R := AlgEquiv.ofInjectiveField e
  have h0 : ((minpoly K x).map (algebraMap K A)).Splits := IsAlgClosed.splits _
  have hh := h0.map g.toRingEquiv.toRingHom
  rw [Polynomial.map_map] at hh
  have hEq : g.toRingEquiv.toRingHom.comp (algebraMap K A)=algebraMap K R :=
    RingHom.ext fun z => g.commutes z
  rw [hEq] at hh
  have hm : x∈R := hx.mem_intermediateField_of_minpoly_splits hh
  obtain ⟨z,hz⟩ := hm
  exact ⟨z,hz⟩

/-- The literal defining set of the original full-coordinate field,
with both coordinates of each true stock n-division point. -/
@[expose] def divisionCoordinates (A : Type*) [Field A] (n : ℕ) : Set A :=
  {z | ∃ (a b : A), ∃ hab : (curve A).toAffine.Nonsingular a b,
    n • Point.some a b hab=0 ∧ (z=a ∨ z=b)}

/-- Existence of the same specified division point over the exact
existing coordinate-generated subfield. The equality of that field
with the displayed adjoin is a definitional interface, not a second
choice of field or an existence assumption about a point. -/
theorem lift_named_torsion_into_exact_coordinate_field
    (K A F : Type*) [Field K] [CharZero K] [Field A] [Field F]
    [Algebra K A] [Algebra K F] [IsAlgClosed A]
    (e : A→ₐ[K]F) (hK : (2:K)≠0) (hF : (2:F)≠0)
    (n : ℕ) (hn : 0<n)
    (D : IntermediateField K A) (hD : D=IntermediateField.adjoin K (divisionCoordinates A n))
    (Q : WP F) (hQ : n • Q=0) :
    ∃ P : WP D, n • P=0 ∧
      coordinateHom (e.toRingHom.comp (algebraMap D A)) hF P=Q := by
  let hA : (2:A)≠0 := by
    intro h
    exact hF (by simpa only [map_ofNat,map_zero] using congrArg e h)
  let i : D→+*A := algebraMap D A
  let h₂ : (2:D)≠0 := by
    intro h
    exact hA (by simpa only [map_ofNat,map_zero] using congrArg i h)
  let H := coordinateHom (e.toRingHom.comp i) hF
  cases Q with
  | zero =>
    refine ⟨0,nsmul_zero n,?_⟩
    change H 0=0
    exact H.map_zero
  | some x y hxy =>
    obtain ⟨hx,hy⟩ := torsion_integral_coordinates_of_positive_level K F hK hF n hn x y hxy hQ
    obtain ⟨a,ha⟩ := lift_integral_through_named_embedding e x hx
    obtain ⟨b,hb⟩ := lift_integral_through_named_embedding e y hy
    have hEqA : b^2=a^3-a := by
      apply e.injective
      simpa only [map_pow,map_sub,ha,hb] using (literal_equation x y).mp hxy.1
    let hAb := nonsing_of_equation hA hEqA
    let R := Point.some a b hAb
    let G := coordinateHom e.toRingHom hF
    have hG : G R=Point.some x y hxy := by
      change onCurvePoint e.toRingHom hF (Point.some a b hAb)=_
      rw [point_some]
      exact some_congr ha hb
    have hR : n • R=0 := by
      apply reflects_zero e.toRingHom hF
      change G (n • R)=0
      rw [map_nsmul,hG,hQ]
    have haD : a∈D := by
      rw [hD]
      exact IntermediateField.subset_adjoin K _ ⟨a,b,hAb,hR,Or.inl rfl⟩
    have hbD : b∈D := by
      rw [hD]
      exact IntermediateField.subset_adjoin K _ ⟨a,b,hAb,hR,Or.inr rfl⟩
    let aD : D := ⟨a,haD⟩
    let bD : D := ⟨b,hbD⟩
    have hiA : i aD=a := rfl
    have hiB : i bD=b := rfl
    have habD : bD^2=aD^3-aD := by
      apply i.injective
      simpa only [map_pow,map_sub,hiA,hiB] using hEqA
    let hPD := nonsing_of_equation h₂ habD
    let P := Point.some aD bD hPD
    have hIm : H P=Point.some x y hxy := by
      change onCurvePoint (e.toRingHom.comp i) hF (Point.some aD bD hPD)=_
      rw [point_some]
      exact some_congr
        ((congrArg e hiA).trans ha) ((congrArg e hiB).trans hb)
    refine ⟨P,?_,hIm⟩
    apply reflects_zero (e.toRingHom.comp i) hF
    change H (n • P)=0
    rw [map_nsmul,hIm,hQ]

/-- The actual accepted positive square-period point at [1/n] is
lifted through the already designated complex embedding. That
specific analytic point, not another n-division point, is retained. -/
theorem actual_positive_period_lifts
    (A : Type*) [Field A] [Algebra Base A] [IsAlgClosed A]
    (e : A→+*ℂ) (he : e.comp (algebraMap Base A)=complexEmbedding)
    (n : ℕ) (hn : 1<n) (D : IntermediateField Base A)
    (hD : D=IntermediateField.adjoin Base (divisionCoordinates A n)) :
    ∃ P : WP D, n • P=0 ∧
      coordinateHom (e.comp (algebraMap D A)) (by norm_num : (2:ℂ)≠0) P=
        uniformization.point (V ((1:ℂ)/(n:ℂ))) := by
  letI : CharZero Base := ⟨fun a b h =>
    Nat.cast_injective (R := ℂ) (by
      simpa only [map_natCast] using congrArg complexEmbedding h)⟩
  letI : Algebra Base ℂ := complexEmbedding.toAlgebra
  let f : A→ₐ[Base]ℂ :=
    { e with commutes' := fun x => DFunLike.congr_fun he x }
  have hn₀ : 0<n := Nat.zero_lt_one.trans hn
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hn₀.ne'
  have hT : n • V ((1:ℂ)/(n:ℂ))=0 := by
    rw [←map_nsmul,nsmul_eq_mul,mul_div_assoc,mul_one,div_self hnC]
    exact (QuotientAddGroup.eq_zero_iff (N:=lattice) _).mpr ⟨1,map_one iota⟩
  have hQ : n • uniformization.point (V ((1:ℂ)/(n:ℂ)))=0 := by
    rw [←map_nsmul,hT,map_zero]
  have hBase : (2:Base)≠0 := by
    intro h
    exact (by norm_num : (2:ℂ)≠0)
      (by simpa only [map_ofNat,map_zero] using congrArg complexEmbedding h)
  exact lift_named_torsion_into_exact_coordinate_field Base A ℂ f hBase (by norm_num)
    n hn₀ D hD _ hQ

end ActualGaussianWeberActualPeriodInCoordinateField318
