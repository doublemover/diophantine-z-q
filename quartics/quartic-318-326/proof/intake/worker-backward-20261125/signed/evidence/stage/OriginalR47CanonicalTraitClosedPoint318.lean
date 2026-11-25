module
public import OriginalR47TraitRoundKernel318
public section
noncomputable section

namespace OriginalR47CanonicalTraitClosedPoint318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime] [p.IsMaximal]
variable {X : Scheme.{u}} (s : X ⟶ base (R:=R))

/-- Descend closedness along the *actual* localization. The closure
of the old image stays over the original closed base point; the
strict lift-at-prime and preimmersion read every point in that
closure in the same trait. Localization itself is not assumed
locally finite type or a closed morphism. -/
theorem descend (v : restricted p s)
    (hv : toTrait p s v = IsLocalRing.closedPoint (Localization.AtPrime p))
    (hclosed : IsClosed ({v} : Set (restricted p s))) :
    IsClosed ({forgetMap p s v} : Set X) := by
  let z : PrimeSpectrum R := ⟨p,inferInstance⟩
  have hz : IsClosed ({z} : Set (base (R:=R))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).2 inferInstance
  have hs : s (forgetMap p s v) = z := by
    have H : forgetMap p s ≫ s = toTrait p s ≫ brace p := pullback.condition
    have he := congrArg (fun f : restricted p s ⟶ base (R:=R) => f v) H
    rw [Scheme.Hom.comp_apply,Scheme.Hom.comp_apply,hv,brace_closedPoint p] at he
    exact he
  letI : IsPreimmersion (forgetMap p s) := forgetMap_preimmersion p s
  apply isClosed_of_closure_subset
  intro x hx
  have hk : closure ({forgetMap p s v} : Set X) ⊆ s ⁻¹' ({z} : Set (base (R:=R))) :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mpr hs))
      (hz.preimage s.continuous)
  have hxs : s x = z := Set.mem_singleton_iff.mp (hk hx)
  obtain ⟨w,hw⟩ := (lift_at_prime p s x hxs).exists
  have hwc : w ∈ closure ({v} : Set (restricted p s)) := by
    rw [(forgetMap p s).isEmbedding.closure_eq_preimage_closure_image,Set.image_singleton]
    change forgetMap p s w ∈ closure ({forgetMap p s v} : Set X)
    rw [hw.1]
    exact hx
  rw [hclosed.closure_eq] at hwc
  exact Set.mem_singleton_iff.mpr (hw.1.symm.trans
    (congrArg (forgetMap p s) (Set.mem_singleton_iff.mp hwc)))

end OriginalR47CanonicalTraitClosedPoint318

#print axioms OriginalR47CanonicalTraitClosedPoint318.descend
