module
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Localization
public section
noncomputable section
namespace FiniteFlatGenericRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The actual local rank of an affine finite flat domain algebra agrees
with the degree of the specified compatible fraction fields. -/
theorem affine_rank_eq_fraction_degree
    (A B K L : Type u) [CommRing A] [CommRing B] [IsDomain A]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite A B] [Module.Flat A B] (p : PrimeSpectrum A) :
    (Spec.algebraMap A B).finrank p = Module.finrank K L := by
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq,
    Ideal.finrank_fiber_eq_finrank]
  exact (IsFractionRing.finrank_eq A K B L).symm

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [Flat f]

/-- Rank of the actual finite-flat morphism equals its actual generic-stalk
field degree at every target point. The scalar action is the literal
DominantFunctionField318.map pullback, not a selected abstract field inclusion.
No local-finite-presentation premise is needed for this integral-base statement. -/
theorem finrank_eq_generic_degree (y : Y) :
    letI : Algebra Y.functionField X.functionField :=
      (DominantFunctionField318.map f).hom.toAlgebra
    f.finrank y = Module.finrank Y.functionField X.functionField := by
  letI : Algebra Y.functionField X.functionField :=
    (DominantFunctionField318.map f).hom.toAlgebra
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  have hy : y ∈ U := Y.affineCover.covers y
  letI : Nonempty U := ⟨⟨y, hy⟩⟩
  let V : X.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  letI : Nonempty V := DominantFunctionField318.preimage_nonempty f U
  let A := Γ(Y, U)
  let B := Γ(X, V)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A X.functionField :=
    ((algebraMap Y.functionField X.functionField).comp
      (algebraMap A Y.functionField)).toAlgebra
  letI : IsScalarTower A Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower A B X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact congrArg (fun g : Γ(Y, U) ⟶ X.functionField => g a)
      (DominantFunctionField318.map_germ f U)
  letI : IsFractionRing A Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  letI : IsFractionRing B X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  letI : Module.Finite A B := f.finite_app U hU
  letI : Module.Flat A B := by
    change (f.app U).hom.Flat
    have hf := f.flat_appLE hU hV le_rfl
    simpa only [V, Scheme.Hom.appLE_eq_app] using hf
  have hsquare : IsPullback (Spec.map (f.app U)) hV.fromSpec hU.fromSpec f := by
    apply IsOpenImmersion.isPullback
    · simpa only [V, Scheme.Hom.appLE_eq_app] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
    · rw [hU.opensRange_fromSpec, hV.opensRange_fromSpec]
  let p : PrimeSpectrum A := hU.primeIdealOf ⟨y, hy⟩
  have hr : (Spec.map (f.app U)).finrank p = f.finrank y := by
    have he := Scheme.Hom.finrank_of_isPullback hV.fromSpec
      (Spec.map (f.app U)) f hU.fromSpec hsquare.flip p
    simpa only [p, hU.fromSpec_primeIdealOf] using he
  rw [← hr]
  change (Spec.algebraMap A B).finrank p = Module.finrank Y.functionField X.functionField
  exact affine_rank_eq_fraction_degree A B Y.functionField X.functionField p

end FiniteFlatGenericRank318
