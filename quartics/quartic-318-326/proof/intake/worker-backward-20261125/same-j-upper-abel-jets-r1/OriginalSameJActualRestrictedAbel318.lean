module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import OriginalCyclicDivisorRetainedSchemeRead318

@[expose] public section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace OriginalSameJActualRestrictedAbel318

universe u

variable {X J : Scheme.{u}} (α : X ⟶ J)
variable {U : X.Opens} {V : J.Opens}
variable (hU : IsAffineOpen U) (x : X)
variable (hx : x ∈ U) (hαx : α x ∈ V)

include hU hx hαx in
/-- A genuine smaller basic open of the original ordinary curve
chart, still at x and in the inverse image of the same J chart. -/
theorem basic_inside :
    ∃ t : Γ(X,U), X.basicOpen t ≤ U ⊓ α ⁻¹ᵁ V ∧ x ∈ X.basicOpen t := by
  let W : X.Opens := U ⊓ α ⁻¹ᵁ V
  have hw : x ∈ W := ⟨hx,hαx⟩
  exact hU.exists_basicOpen_le (⟨x,hw⟩ : W) hx

variable {W : X.Opens} (haW : IsAffineOpen W) (haV : IsAffineOpen V)
variable (hle : W ≤ α ⁻¹ᵁ V)

abbrev ring : Γ(J,V) ⟶ Γ(X,W) := α.appLE V W hle

/-- Equality of the actual Scheme arrows over both chart inclusions,
not equality of the values of a single coordinate. -/
theorem returned_arrow :
    Spec.map (ring α hle) ≫ haV.fromSpec = haW.fromSpec ≫ α := by
  apply (cancel_epi haW.isoSpec.hom).mp
  change W.toSpecΓ ≫ (Spec.map (ring α hle) ≫ haV.fromSpec) =
    W.toSpecΓ ≫ (haW.fromSpec ≫ α)
  calc
    _ = (W.toSpecΓ ≫ Spec.map (α.appLE V W hle)) ≫ haV.fromSpec :=
      (Category.assoc _ _ _).symm
    _ = (α.resLE V W hle ≫ V.toSpecΓ) ≫ haV.fromSpec := by
      rw [Scheme.Opens.toSpecΓ_SpecMap_appLE]
    _ = α.resLE V W hle ≫ V.ι := by
      rw [Category.assoc, haV.toSpecΓ_fromSpec]
    _ = W.ι ≫ α := α.resLE_comp_ι hle
    _ = _ := by rw [← Category.assoc, haW.toSpecΓ_fromSpec]

variable {k : Type u} [Field k]
variable (P : Spec (CommRingCat.of k) ⟶ X) (O : Spec (CommRingCat.of k) ⟶ J)
variable (based : P ≫ α = O)
variable (pHits : Set.range P ⊆ Set.range haW.fromSpec)
variable (oHits : Set.range O ⊆ Set.range haV.fromSpec)

open OriginalCyclicDivisorRetainedSchemeRead318 in
include based in
theorem whole_augmentations :
    (ringRead haW.fromSpec P pHits).comp (ring α hle).hom =
      ringRead haV.fromSpec O oHits := by
  let f : Γ(J,V) ⟶ Γ(X,W) := ring α hle
  let z : Γ(X,W) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (ringRead haW.fromSpec P pHits)
  let y : Γ(J,V) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (ringRead haV.fromSpec O oHits)
  have H : f ≫ z = y := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    apply (cancel_mono haV.fromSpec).mp
    calc
      (Spec.map z ≫ Spec.map f) ≫ haV.fromSpec =
          Spec.map z ≫ (haW.fromSpec ≫ α) := by
        rw [Category.assoc, returned_arrow α haW haV hle]
      _ = P ≫ α := by
        rw [← Category.assoc, same_arrow haW.fromSpec P pHits]
      _ = O := based
      _ = Spec.map y ≫ haV.fromSpec := (same_arrow haV.fromSpec O oHits).symm
  exact congrArg (fun q : Γ(J,V) ⟶ CommRingCat.of k => q.hom) H

end OriginalSameJActualRestrictedAbel318

#print axioms OriginalSameJActualRestrictedAbel318.basic_inside
#print axioms OriginalSameJActualRestrictedAbel318.returned_arrow
#print axioms OriginalSameJActualRestrictedAbel318.whole_augmentations
