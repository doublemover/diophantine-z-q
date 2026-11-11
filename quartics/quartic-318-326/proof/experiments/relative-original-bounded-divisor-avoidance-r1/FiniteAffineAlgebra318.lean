module
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace FiniteAffineAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (p : Z ⟶ Spec R) [IsFinite p]
abbrev ring (_p : Z ⟶ Spec R) : CommRingCat.{u} := Γ(Z,⊤)
/-- The coefficient map of the SAME entire finite family, obtained from
its canonical affine comparison rather than a selected open chart. -/
@[expose] def coefficient : R ⟶ ring R p := Spec.preimage (Z.isoSpec.inv ≫ p)
@[expose] instance algebra : Algebra R (ring R p) := (coefficient R p).hom.toAlgebra
lemma spec_coefficient : Spec.map (coefficient R p)=Z.isoSpec.inv ≫ p := Spec.map_preimage _
@[reassoc] lemma iso_projection : Z.isoSpec.hom ≫ Spec.map (coefficient R p)=p := by
  rw [spec_coefficient,← Category.assoc,Iso.hom_inv_id,Category.id_comp]
instance finite : Module.Finite R (ring R p) := by
  have h : IsFinite (Spec.map (coefficient R p)) := by rw [spec_coefficient]; infer_instance
  exact IsFinite.SpecMap_iff.mp h
instance flat [Flat p] : Module.Flat R (ring R p) := by
  have h : Flat (Spec.map (coefficient R p)) := by rw [spec_coefficient]; infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)
instance algebraFinitePresentation [LocallyOfFinitePresentation p] : Algebra.FinitePresentation R (ring R p) := by
  have h : LocallyOfFinitePresentation (Spec.map (coefficient R p)) := by
    rw [spec_coefficient]
    infer_instance
  exact LocallyOfFinitePresentation.SpecMap_iff.mp h
end FiniteAffineAlgebra318
