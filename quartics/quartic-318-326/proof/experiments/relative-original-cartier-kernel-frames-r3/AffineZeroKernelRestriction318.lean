module
public import AffineQuotientKernelSections318
public section
noncomputable section
namespace AffineZeroKernelRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : CommRingCat.{u}) (J : Ideal A) {Z X : Scheme.{u}}
  (p : Z ⟶ X) [QuasiCompact p] (j : Spec A ⟶ X) [IsOpenImmersion j]
  (k : Spec (CommRingCat.of (A⧸J)) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) k j p)

lemma coefficient_bijective : Function.Bijective (coefficient A j) :=
  (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).inv).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)

/-- Undoing the actual coefficient isomorphism gives an equality of
ideals INSIDE the original ambient chart section ring. -/
lemma chart_kernel : (p.ker.ideal (chartOpen A j))=Ideal.map (coefficient A j).hom J := by
  rw [← original_kernel A J p j k hs]
  exact (Ideal.map_comap_of_surjective (coefficient A j).hom
    (coefficient_bijective A j).2 _).symm

variable (V : X.affineOpens) (hV : V≤chartOpen A j)

/-- Actual original coefficient restriction to the specified affine
subopen. No new coordinate or arbitrary localization map is introduced. -/
@[expose] def restrictedCoefficient : A ⟶ Γ(X,V.1) :=
  coefficient A j ≫ X.presheaf.map (homOfLE hV).op

/-- Every affine subopen of the WHOLE actual chart has the original
section-zero kernel obtained by exact extension of the literal quotient
ideal. This is the affine-basis producer needed for global kernel descent. -/
lemma restricted_kernel : RingHom.ker (p.app V.1).hom =
    Ideal.map (restrictedCoefficient A j V hV).hom J := by
  rw [← p.ker_apply V]
  calc
    p.ker.ideal V = Ideal.map (X.presheaf.map (homOfLE hV).op).hom
        (p.ker.ideal (chartOpen A j)) := (p.ker.map_ideal hV).symm
    _ = Ideal.map (X.presheaf.map (homOfLE hV).op).hom
        (Ideal.map (coefficient A j).hom J) := by rw [chart_kernel A J p j k hs]
    _ = _ := by rw [Ideal.map_map]; rfl
end AffineZeroKernelRestriction318
