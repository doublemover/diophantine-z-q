module
public import VaryingLocalFreeFamilyPresentation318
public import FiniteProjectiveDualFrame318
public section
noncomputable section
namespace VaryingLocalFreeModuleProjective318
open AlgebraicGeometry CategoryTheory
open VaryingLocalFreeQuotientEquiv318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : LocalIdeal R A ι S)
abbrev quotient := (S ⊗[R] A) ⧸ I.val
/-- Native coefficient projection of the same quotient algebra. -/
lemma spec_coefficient : Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A ι S I)))=
    VaryingWholeIdealFamily318.projection R A S I.val := by
  change Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A ι S I)))=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.val)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
  rw [← Spec.map_comp]
  rfl
instance finite : Module.Finite S (quotient R A ι S I) := by
  have h : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A ι S I)))) := by
    rw [spec_coefficient]; infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h)
instance flat : Module.Flat S (quotient R A ι S I) := by
  have h : Flat (Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A ι S I)))) := by
    rw [spec_coefficient]; infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)
instance algebraPresentation : Algebra.FinitePresentation S (quotient R A ι S I) := by
  have h : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap S (quotient R A ι S I)))) := by
    rw [spec_coefficient]; infer_instance
  exact RingHom.finitePresentation_algebraMap.mp (LocallyOfFinitePresentation.SpecMap_iff.mp h)
/-- The missing module-presentation hypothesis is proved before invoking
flat projectivity. This includes non-Noetherian coefficient rings. -/
instance modulePresentation : Module.FinitePresentation S (quotient R A ι S I) :=
  Module.FinitePresentation.of_finite_of_finitePresentation S _
instance projective : Module.Projective S (quotient R A ι S I) :=
  FiniteProjectiveDualFrame318.projective_of_finitePresentation_flat S _
lemma dual_frame : Nonempty (FiniteProjectiveDualFrame318.Frame S (quotient R A ι S I)) :=
  FiniteProjectiveDualFrame318.nonempty_frame S _
end VaryingLocalFreeModuleProjective318
