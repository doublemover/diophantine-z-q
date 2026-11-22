module
public import ActualGaussianWeberOriginalFieldFoundation318
public import ActualGaussianWeberBaseNumberField318
public import ActualGaussianWeberLiteralComplexTorsion318
public import ActualLSGOriginalFullUniformization318
public import ActualGaussianWeberStockCoordinateHom318
public import Mathlib.FieldTheory.Minpoly.Field
public section
noncomputable section

namespace ActualGaussianWeberNamedFullFieldFiniteness318

open NumberField WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberPlaceEquivariance318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberFullTorsionInertia318 ActualGaussianWeberFullCoordinateField318
open ActualGaussianWeberAlgebraicClosureTorsion318 ActualGaussianWeberLiteralComplexTorsion318

attribute [local instance] Classical.decEq

private def affX (K : Type*) [CommRing K] : WP K→K
  | .zero => 0
  | .some x _ _ => x

private def affY (K : Type*) [CommRing K] : WP K→K
  | .zero => 0
  | .some _ y _ => y

private theorem named_embedding_points_injective :
    Function.Injective (coordinateHom chosenClosureEmbedding (by norm_num : (2:ℂ)≠0)) := by
  let f := chosenClosureEmbedding
  let hC : (2:ℂ)≠0 := by norm_num
  intro P Q h
  change onCurvePoint f hC P=onCurvePoint f hC Q at h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hxy =>
      rw [point_some f hC hxy] at h
      cases h
  | some x y hxy =>
    rw [point_some f hC hxy] at h
    cases Q with
    | zero => cases h
    | some u v huv =>
      rw [point_some f hC huv] at h
      have hx : f x=f u := congrArg (affX ℂ) h
      have hy : f y=f v := congrArg (affY ℂ) h
      exact some_congr (f.injective hx) (f.injective hy)

private theorem finite_named_closure_torsion (n : ℕ) (hn : 0<n) :
    Finite {P : WP Ω // n • P=0} := by
  letI : Finite {Q : WP ℂ // n • Q=0} :=
    literal_complex_torsion_finite ActualLSGOriginalFullUniformization318.uniformization n hn
  let f := coordinateHom chosenClosureEmbedding (by norm_num : (2:ℂ)≠0)
  let F : {P : WP Ω // n • P=0}→{Q : WP ℂ // n • Q=0} :=
    fun P => ⟨f P,by rw [←map_nsmul,P.property,map_zero]⟩
  apply Finite.of_injective F
  intro P Q h
  apply Subtype.ext
  exact named_embedding_points_injective (congrArg Subtype.val h)

private theorem finite_named_coordinates (n : ℕ) (hn : 0<n) :
    (torsionCoordinates Ω n).Finite := by
  let T := {P : WP Ω // n • P=0}
  letI : Finite T := finite_named_closure_torsion n hn
  let X : T→Ω := fun P => affX Ω P
  let Y : T→Ω := fun P => affY Ω P
  apply ((Set.finite_range X).union (Set.finite_range Y)).subset
  rintro _ ⟨x,y,hxy,hT,rfl|rfl⟩
  · exact Or.inl ⟨⟨Point.some x y hxy,hT⟩,rfl⟩
  · exact Or.inr ⟨⟨Point.some x y hxy,hT⟩,rfl⟩

/-- The exact original coordinate adjoin is finite; the same fixed
closure embedding identifies its finite torsion source. No normality,
primitive point or legacy arithmetic proof is an input. -/
theorem old_fullField_finite (n : ℕ) (hn : 0<n) :
    FiniteDimensional Base (fullField Ω n) := by
  letI : Finite (torsionCoordinates Ω n) := (finite_named_coordinates n hn).to_subtype
  change FiniteDimensional Base (IntermediateField.adjoin Base (torsionCoordinates Ω n))
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R:=Base) x).isIntegral)

/-- Install NumberField on the same original coordinate carrier
used by the actual local place and not on an isomorphic substitute. -/
theorem old_fullField_numberField (n : ℕ) (hn : 0<n) :
    NumberField (fullField Ω n) := by
  letI : NumberField Base := ActualGaussianWeberBaseNumberField318.actual_gaussian_number_field
  letI : FiniteDimensional Base (fullField Ω n) := old_fullField_finite n hn
  exact NumberField.of_module_finite Base (fullField Ω n)

end ActualGaussianWeberNamedFullFieldFiniteness318
