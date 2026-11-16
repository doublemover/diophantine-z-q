module
public import WholeFrameClassifierInverse318
public section
noncomputable section
namespace ContactFrameAffineCoefficient318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) [Algebra ℚ R] (S : CommRingCat.{0})
  (b : Spec S ⟶ Spec R)
/-- Canonical rational coefficient structure induced by the ACTUAL affine
scheme map. This avoids restricting the tests to separately chosen algebras. -/
@[expose] def algebra : Algebra ℚ S :=
  ((Spec.preimage b).hom.comp (algebraMap ℚ R)).toAlgebra
@[expose] def hom : letI := algebra R S b; R →ₐ[ℚ] S := by
  letI := algebra R S b
  exact { __ := (Spec.preimage b).hom, commutes' := fun _ => rfl }
lemma spec_hom : letI := algebra R S b;
    Spec.map (CommRingCat.ofHom (hom R S b).toRingHom)=b := Spec.map_preimage b
lemma preimage_map (f : R ⟶ S) : Spec.preimage (Spec.map f)=f := by
  apply Spec.map_injective
  exact Spec.map_preimage (Spec.map f)
variable (T : CommRingCat.{0}) (g : Spec T ⟶ Spec S) (a : Spec T ⟶ Spec R) (hg : g ≫ b=a)
lemma ring_comp : Spec.preimage b ≫ Spec.preimage g=Spec.preimage a := by
  apply Spec.map_injective
  simpa only [Spec.map_comp,Spec.map_preimage] using hg
@[expose] def arrow : letI := algebra R S b; letI := algebra R T a; S →ₐ[ℚ] T := by
  letI := algebra R S b
  letI := algebra R T a
  exact { __ := (Spec.preimage g).hom, commutes' := fun z =>
    congrArg (fun k : R ⟶ T => k.hom (algebraMap ℚ R z)) (ring_comp R S b T g a hg) }
lemma arrow_spec : letI := algebra R S b; letI := algebra R T a;
    Spec.map (CommRingCat.ofHom (arrow R S b T g a hg).toRingHom)=g := Spec.map_preimage g
lemma arrow_comp : letI := algebra R S b; letI := algebra R T a;
    (arrow R S b T g a hg).comp (hom R S b)=hom R T a := by
  letI := algebra R S b
  letI := algebra R T a
  apply AlgHom.ext
  intro z
  exact congrArg (fun k : R ⟶ T => k.hom z) (ring_comp R S b T g a hg)
end ContactFrameAffineCoefficient318
