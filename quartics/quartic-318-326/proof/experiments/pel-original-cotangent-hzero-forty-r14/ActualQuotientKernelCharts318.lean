module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
/- Minimal kernel-chart extraction from AffineQuotientKernelSections318.
The original quotient_kernel and original_kernel proofs are retained;
no unrelated actual-module-kernel closure is imported. -/
namespace ActualQuotientKernelCharts318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : CommRingCat.{u}) (J : Ideal A)
@[expose] def quotientMap : A ⟶ CommRingCat.of (A ⧸ J) :=
  CommRingCat.ofHom (Ideal.Quotient.mk J)

/-- The actual Spec quotient kernel, transported by the canonical Gamma
comparison, is the original ideal itself, without taking its radical. -/
lemma quotient_kernel :
    ((Spec.map (quotientMap A J)).ker.ideal ⟨⊤,isAffineOpen_top (Spec A)⟩).comap
      (Scheme.ΓSpecIso A).inv.hom=J := by
  rw [Scheme.Hom.ker_apply]
  ext a
  change (Spec.map (quotientMap A J)).appTop ((Scheme.ΓSpecIso A).inv a)=0 ↔ a∈J
  have he := congrArg (fun k => k a) (Scheme.ΓSpecIso_inv_naturality (quotientMap A J))
  change (Scheme.ΓSpecIso (CommRingCat.of (A⧸J))).inv (Ideal.Quotient.mk J a)=
    (Spec.map (quotientMap A J)).appTop ((Scheme.ΓSpecIso A).inv a) at he
  rw [← he]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (A⧸J))).inv).1]
  exact Ideal.Quotient.eq_zero_iff_mem

variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (j : Spec A ⟶ X) [IsOpenImmersion j]
  (k : Spec (CommRingCat.of (A⧸J)) ⟶ Z)
  (hs : IsPullback (Spec.map (quotientMap A J)) k j p)

/-- The affine-open image of the actual chart, with no choice of a
replacement affine scheme or discarded boundary points. -/
abbrev chartOpen : X.affineOpens :=
  ⟨j ''ᵁ ⊤,(isAffineOpen_top (Spec A)).image_of_isOpenImmersion j⟩

/-- Native A coefficients enter the original chart section ring through
the actual Gamma-Spec isomorphism and actual open-immersion appIso. -/
@[expose] def coefficient : A ⟶ Γ(X,(chartOpen A j).1) :=
  (Scheme.ΓSpecIso A).inv ≫ (j.appIso ⊤).inv

/-- The SAME global closed-map kernel, viewed on its actual chart, is
exactly the original quotient ideal after the explicit coefficient map. -/
include hs in
lemma original_kernel : (p.ker.ideal (chartOpen A j)).comap (coefficient A j).hom=J := by
  have he := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion p (Spec.map (quotientMap A J)) k j hs
    ⟨⊤,isAffineOpen_top (Spec A)⟩
  change (p.ker.ideal (chartOpen A j)).comap
    ((j.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso A).inv.hom)=J
  rw [← Ideal.comap_comap,← he]
  exact quotient_kernel A J

end ActualQuotientKernelCharts318
