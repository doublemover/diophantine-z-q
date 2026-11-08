module
public import UniversalSheafDifferentials318
public section
noncomputable section
namespace IntrinsicUniversalComparison318
open AlgebraicGeometry CategoryTheory
open PresheafOfModulesOfCommRing
universe u
variable {X : Scheme.{u}} {S : X.Opensᵒᵖ ⥤ CommRingCat.{u}}
    (φ : S ⟶ X.presheaf)
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Universal property for an actual sheaf and an actual sheaf derivation. The
quantifier ranges over all O-module sheaves, not a chosen set of local frames. -/
@[expose] def IsUniversal {L : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' L.val φ) : Prop :=
  ∀ (M : X.Modules) (δ : PresheafOfModulesOfCommRing.Derivation' M.val φ),
    ∃! f : L ⟶ M, d.postcomp f.val = δ

/-- The intrinsic object has this full universal property. -/
theorem intrinsic_isUniversal : IsUniversal φ (UniversalSheafDifferentials318.D φ) :=
  fun _ δ => UniversalSheafDifferentials318.existsUnique_desc φ δ

/-- Canonical comparison to any genuinely universal global sheaf derivation.
This is an isomorphism theorem, with the universal-property input explicit. -/
@[expose] def isoOfUniversal {L : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' L.val φ)
    (hd : IsUniversal φ d) : UniversalSheafDifferentials318.omega φ ≅ L := by
  unfold IsUniversal at hd
  let f := UniversalSheafDifferentials318.desc φ d
  let g := Classical.choose (hd _ (UniversalSheafDifferentials318.D φ))
  have hg := (Classical.choose_spec (hd _ (UniversalSheafDifferentials318.D φ))).1
  refine ⟨f,g,?_,?_⟩
  · apply UniversalSheafDifferentials318.hom_ext φ
    change ((UniversalSheafDifferentials318.D φ).postcomp (f.val ≫ g.val)) =
      UniversalSheafDifferentials318.D φ
    rw [←UniversalSheafDifferentials318.postcomp_comp,
      UniversalSheafDifferentials318.desc_fac, hg]
  · obtain ⟨k, hk, hku⟩ := hd L d
    apply (hku _ ?_).trans (hku _ ?_).symm
    · change d.postcomp (g.val ≫ f.val) = d
      rw [←UniversalSheafDifferentials318.postcomp_comp, hg,
        UniversalSheafDifferentials318.desc_fac]
    · rfl

/-- The comparison carries the intrinsic differential to the specified actual
one, so its normalization cannot be chosen independently. -/
theorem isoOfUniversal_fac {L : X.Modules} (d : PresheafOfModulesOfCommRing.Derivation' L.val φ)
    (hd : IsUniversal φ d) :
    (UniversalSheafDifferentials318.D φ).postcomp (isoOfUniversal φ d hd).hom.val = d :=
  UniversalSheafDifferentials318.desc_fac φ d
end IntrinsicUniversalComparison318
