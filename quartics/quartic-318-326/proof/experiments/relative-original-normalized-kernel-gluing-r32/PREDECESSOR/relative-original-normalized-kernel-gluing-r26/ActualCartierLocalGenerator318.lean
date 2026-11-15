module
public import ActualCartierKernelFrameNaturality318
public import OriginalOpenTopSection318
public section
noncomputable section
namespace ActualCartierLocalGenerator318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318 ActualCartierKernelFrames318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j] (c : A)
  (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
  (hc : ∀ a : A,a*c=0 → a=0)
local notation "U" => (chartOpen A j).1
local notation "M" => ActualClosedIdealModule318.object p

/-- The ORIGINAL Cartier generator inside the actual global kernel sheaf. -/
@[expose] def section : Γ(M,U) := frame p A j c z hs hc (chartOpen A j) le_rfl 1

/-- A genuine sheaf morphism on the whole actual Cartier open. -/
@[expose] def hom : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι :=
  OriginalOpenTopSection318.map M U (section p A j c z hs hc)

@[expose] def imageAffine (V : U.toScheme.affineOpens) : X.affineOpens :=
  ⟨U.ι ''ᵁ V.1,V.2.image_of_isOpenImmersion U.ι⟩
lemma image_le (V : U.toScheme.affineOpens) : imageAffine A j V≤chartOpen A j :=
  OriginalOpenTopSection318.image_le U V.1

/-- On EVERY affine subopen, the actual map is the previously constructed
kernel frame, with the exact open-immersion scalar comparison. -/
lemma hom_formula (V : U.toScheme.affineOpens) (a : Γ(U.toScheme,V.1)) :
    (M.restrictAppIso U.ι V.1).hom ((hom p A j c z hs hc).app V.1 a)=
      frame p A j c z hs hc (imageAffine A j V) (image_le A j V)
        ((U.ι.appIso V.1).inv a) := by
  rw [hom,OriginalOpenTopSection318.map_formula]
  have hr := ActualCartierKernelFrameNaturality318.frame_restrict p A j c z hs hc
    (chartOpen A j) (imageAffine A j V) le_rfl (image_le A j V) 1
  simp only [map_one] at hr
  rw [section,hr]
  simpa only [smul_eq_mul,mul_one] using
    ((frame p A j c z hs hc (imageAffine A j V) (image_le A j V)).map_smul
      ((U.ι.appIso V.1).inv a) 1).symm

lemma hom_bijective (V : U.toScheme.affineOpens) :
    Function.Bijective ((hom p A j c z hs hc).app V.1) := by
  have hf : Function.Bijective (fun a : Γ(U.toScheme,V.1) =>
      (M.restrictAppIso U.ι V.1).hom ((hom p A j c z hs hc).app V.1 a)) := by
    have he : (fun a : Γ(U.toScheme,V.1) =>
        (M.restrictAppIso U.ι V.1).hom ((hom p A j c z hs hc).app V.1 a)) =
        (fun a => frame p A j c z hs hc (imageAffine A j V) (image_le A j V)
          ((U.ι.appIso V.1).inv a)) := funext (hom_formula p A j c z hs hc V)
    rw [he]
    exact (frame p A j c z hs hc (imageAffine A j V) (image_le A j V)).bijective.comp
      (ConcreteCategory.bijective_of_isIso (U.ι.appIso V.1).inv)
  have hi := (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι V.1).hom).1
  constructor
  · intro a b h
    exact hf.1 (congrArg (fun t => (M.restrictAppIso U.ι V.1).hom t) h)
  · intro b
    obtain ⟨a,ha⟩ := hf.2 ((M.restrictAppIso U.ι V.1).hom b)
    exact ⟨a,hi ha⟩
end ActualCartierLocalGenerator318
