module
public import VaryingSourceWordOpen318
public import VaryingSourceWordQuotient318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace VaryingSourceUniversalQuotient318
open AlgebraicGeometry CategoryTheory
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "H" => VaryingSourceWordOpen318.ring R A ι w

@[expose] def chartData : VaryingSourceWordOpen318.Point R A ι H w :=
  VaryingSourceWordOpen318.toPoint R A ι H w (AlgHom.id R H)
@[expose] def chartAction : Action R A ι H :=
  action R A ι H (chartData R A ι w).val
lemma chart_unit : IsUnit (VaryingMatrixWords318.determinant
    (point R A ι H (chartAction R A ι w)).val w) := by
  have h : point R A ι H (chartAction R A ι w)=(chartData R A ι w).val :=
    (actionPoints R A ι H).symm_apply_apply (chartData R A ι w).val
  rw [h]
  exact (chartData R A ι w).property

abbrev parameter : Scheme := Spec (CommRingCat.of (VaryingSourceActionParameter318.ring R A ι))
abbrev chart : Scheme := Spec (CommRingCat.of H)
@[expose] def intoParameter : chart R A ι w ⟶ parameter R A ι :=
  Spec.map (CommRingCat.ofHom (algebraMap (VaryingSourceActionParameter318.ring R A ι) H))
instance chart_open : IsOpenImmersion (intoParameter R A ι w) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway (VaryingSourceWordOpen318.delta R A ι w)

/-- The universal quotient is a closed subscheme of the literal original
base-changed affine source over this represented word chart. -/
abbrev family : Scheme :=
  CyclicQuotientFiniteFlat318.scheme (linearAction R A ι H (chartAction R A ι w))
    (chartAction R A ι w).marked
abbrev intoSource : family R A ι w ⟶ Spec (CommRingCat.of (H ⊗[R] A)) :=
  CyclicQuotientFiniteFlat318.into (linearAction R A ι H (chartAction R A ι w))
    (chartAction R A ι w).marked
abbrev projection : family R A ι w ⟶ chart R A ι w :=
  CyclicQuotientFiniteFlat318.projection (linearAction R A ι H (chartAction R A ι w))
    (chartAction R A ι w).marked
instance family_closed : IsClosedImmersion (intoSource R A ι w) := inferInstance
instance family_finite : IsFinite (projection R A ι w) :=
  VaryingSourceWordQuotient318.finite R A ι H (chartAction R A ι w) w (chart_unit R A ι w)
instance family_flat : Flat (projection R A ι w) :=
  VaryingSourceWordQuotient318.flat R A ι H (chartAction R A ι w) w (chart_unit R A ι w)
end VaryingSourceUniversalQuotient318
