module
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace FiniteEtaleFieldPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (F C:Type) [Field F] [IsAlgClosed F] [CommRing C] [Algebra F C]
variable [Module.Finite F C] [Algebra.Etale F C]
local instance : IsFinite (Spec.algebraMap F C):=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap F C))).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
@[expose] def Points:={p:Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of C) //
  p ≫ Spec.algebraMap F C=𝟙 _}
@[expose] def closedPointEquiv : closedPoints (Spec (CommRingCat.of C)) ≃ PrimeSpectrum C:=by
  letI:IsArtinianRing C:=isArtinian_of_tower F inferInstance
  exact {
    toFun := fun p => p.val
    invFun := fun p => ⟨p,(PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr inferInstance⟩
    left_inv := fun p => rfl
    right_inv := fun p => rfl }
/-- Actual base-preserving Scheme points, not an arbitrary chosen labeling,
correspond to prime points through their residue-field lifts. -/
@[expose] def pointEquiv : Points F C ≃ PrimeSpectrum C:=
  (pointEquivClosedPoint (Spec.algebraMap F C)).trans (closedPointEquiv F C)
/-- Finite etale splitting is used only for the actual fiber cardinality,
not to transport addition along unproved labels. -/
theorem card_spectrum : Nat.card (PrimeSpectrum C)=Module.finrank F C:=by
  letI:IsArtinianRing C:=isArtinian_of_tower F inferInstance
  letI:Fintype (PrimeSpectrum C):=Fintype.ofFinite _
  have h:Module.finrank F C=Module.finrank F (PrimeSpectrum C→F):=
    (Algebra.FormallyEtale.equivPiOfIsSepClosed F C).toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa only [Nat.card_eq_fintype_card] using h.symm
theorem card_points : Nat.card (Points F C)=Module.finrank F C:=
  (Nat.card_congr (pointEquiv F C)).trans (card_spectrum F C)
end FiniteEtaleFieldPoints318
