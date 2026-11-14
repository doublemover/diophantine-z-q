module
public import OriginalPointSheafSectionValues318
public import OriginalAllPlaceFrameCoherence318
public section
noncomputable section
namespace OriginalGlobalFrameTransport318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalPointSheafSectionValues318 ContactBicanonicalPointHeight318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i j : Fin 4)
local notation "ΓK" => Γ(Spec (CommRingCat.of (K c t)),⊤)
local notation "C" => (Scheme.ΓSpecIso (CommRingCat.of (K c t))).inv

/-- The transition of the GENUINE original whole-point sheaf frames is
exactly the earlier original arithmetic frame scalar. A nonzero actual
global q0 fixes the full line morphism; no all-section transition is assumed. -/
theorem pointFrame_transition :
    (pointFrame c t hn i).inv≫(pointFrame c t hn j).hom=
      ClutchedModule318.multiply (C (frameScalar c t hn i j)) := by
  haveI : IsIso (ClutchedModule318.multiply (C (a0 c t hn i))) :=
    ClutchedModule318.multiply_isIso _ ((isUnit_iff_ne_zero.mpr (a0_ne c t hn i)).map C.hom)
  apply (cancel_epi (ClutchedModule318.multiply (C (a0 c t hn i)))).1
  have hleft : ClutchedModule318.multiply (C (a0 c t hn i))≫
      (pointFrame c t hn i).inv≫(pointFrame c t hn j).hom=
        ClutchedModule318.multiply (C (a0 c t hn j)) := by
    rw [show ClutchedModule318.multiply (C (a0 c t hn i))=
      pulledSection c t (ContactScaledBicanonicalPoint318.scaledQ0 c)≫(pointFrame c t hn i).hom
      from (pulledSection_frame c t hn i _).symm]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    exact pulledSection_frame c t hn j _
  have hright : ClutchedModule318.multiply (C (a0 c t hn i))≫
      ClutchedModule318.multiply (C (frameScalar c t hn i j))=
        ClutchedModule318.multiply (C (a0 c t hn j)) := by
    apply ModuleTopExt318.ext
    change (ClutchedModule318.multiply (C (frameScalar c t hn i j))).app ⊤
      ((ClutchedModule318.multiply (C (a0 c t hn i))).app ⊤ (1:ΓK))=_
    rw [ClutchedModule318.multiply_top,ClutchedModule318.multiply_top,
      ClutchedModule318.multiply_top,one_mul,one_mul,←map_mul,frameScalar_a0 c t hn i j]
    congr 1
    exact mul_comm _ _
  exact hleft.trans hright.symm

/-- Every true global intrinsic bicanonical section, not just q0/q1,
obeys the same original frame transition at the SAME whole point. -/
theorem value_transition (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    ContactBicanonicalPointValue318.value c t hn j s=
      frameScalar c t hn i j*ContactBicanonicalPointValue318.value c t hn i s := by
  have h : ClutchedModule318.multiply (C (ContactBicanonicalPointValue318.value c t hn i s))≫
      ClutchedModule318.multiply (C (frameScalar c t hn i j))=
        ClutchedModule318.multiply (C (ContactBicanonicalPointValue318.value c t hn j s)) := by
    rw [←pointFrame_transition c t hn i j,←pulledSection_frame c t hn i s]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    exact pulledSection_frame c t hn j s
  have hv := congrArg (fun φ => φ.app ⊤ (1:ΓK)) h
  change (ClutchedModule318.multiply (C (frameScalar c t hn i j))).app ⊤
      ((ClutchedModule318.multiply (C (ContactBicanonicalPointValue318.value c t hn i s))).app ⊤ (1:ΓK))=_ at hv
  simp only [ClutchedModule318.multiply_top,one_mul,←map_mul] at hv
  have hv' := (ConcreteCategory.bijective_of_isIso C).1 hv
  exact hv'.symm.trans (mul_comm _ _)
end OriginalGlobalFrameTransport318
