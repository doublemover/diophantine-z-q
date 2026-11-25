module
public import OriginalUpperActualFibreComponents318

public section
noncomputable section
namespace OriginalUpperActualFibreIntersectionScheme318

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open OriginalUpperActualFibreComponents318 (C ambientIdeal ambientSupport curve ι embedded_ker component_closed_embedding)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Z : Scheme.{u}} (s : X ⟶ Z) (p : Z) (E F : C s p)
local notation "I" => ambientIdeal s p E
local notation "J" => ambientIdeal s p F

/-- Genuine scheme-theoretic intersection, retaining the nonreduced
structure of the sum of embedded ideals. -/
abbrev crossing : Scheme := (I ⊔ J).subscheme

abbrev intoX : crossing s p E F ⟶ X := (I ⊔ J).subschemeι
abbrev first : crossing s p E F ⟶ I.subscheme := inclusion le_sup_left
abbrev second : crossing s p E F ⟶ J.subscheme := inclusion le_sup_right

theorem actual_support : Set.range (intoX s p E F) =
    (ambientSupport s p E : Set X) ∩ (ambientSupport s p F : Set X) := by
  simp only [intoX, range_subschemeι, support_sup, ambientIdeal,
    TopologicalSpace.Closeds.coe_inf, coe_support_vanishingIdeal]

/-- The natural closed subscheme is the intersection in schemes, not
the reduced intersection and not simply the intersection of sets. -/
theorem cartesian : IsPullback (first s p E F) (second s p E F) I.subschemeι J.subschemeι := by
  refine ⟨by simp [first,second], ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro T
    let h := T.fst ≫ I.subschemeι
    have hI : I ≤ h.ker := by
      rw [←I.ker_subschemeι]
      exact T.fst.le_ker_comp _
    have hJ : J ≤ h.ker := by
      rw [show h = T.snd ≫ J.subschemeι from T.condition,← J.ker_subschemeι]
      exact T.snd.le_ker_comp _
    exact h.toImage ≫ inclusion (sup_le hI hJ)
  · intro T
    apply (cancel_mono I.subschemeι).mp
    simp [first,Category.assoc]
  · intro T
    apply (cancel_mono J.subschemeι).mp
    simpa [second,Category.assoc] using T.condition
  · intro T k hk _
    apply (cancel_mono ((I ⊔ J).subschemeι)).mp
    rw [←inclusion_subschemeι (h := (le_sup_left : I ≤ I ⊔ J)),←Category.assoc]
    change (k ≫ first s p E F) ≫ I.subschemeι = _
    rw [hk]
    simp [Category.assoc]

/-- No change to the component chosen inside the actual fibre: its
ambient image is isomorphic to its true fibre subscheme, over X. -/
def embeddedCurve (closed : IsClosed ({p} : Set Z)) :
    curve s p E ≅ I.subscheme :=
  letI := component_closed_embedding s p closed E
  asIso (ι s p E).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (embedded_ker s p E))

theorem embeddedCurve_over (closed : IsClosed ({p} : Set Z)) :
    (embeddedCurve s p E closed).hom ≫ I.subschemeι = ι s p E := by
  simp only [embeddedCurve,Iso.trans_hom,Category.assoc]
  have compatible (K L : X.IdealSheafData) (h : K = L) :
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ L.subschemeι = K.subschemeι := by
    subst L
    simp
  rw [compatible]
  exact (ι s p E).toImage_imageι

end OriginalUpperActualFibreIntersectionScheme318

#print axioms OriginalUpperActualFibreIntersectionScheme318.actual_support
#print axioms OriginalUpperActualFibreIntersectionScheme318.cartesian
#print axioms OriginalUpperActualFibreIntersectionScheme318.embeddedCurve_over
