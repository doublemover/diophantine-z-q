module
public import LocalSectionCotangentComparison318
public section
noncomputable section
namespace LocalSectionCotangentImageTransport318
open AlgebraicGeometry CategoryTheory AffineSectionCotangentImage318
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {g : Spec (CommRingCat.of R) ⟶ X}
  (A B : LocalSectionAffineChart318.Data f g)
  (F : Type u) [Field F] [Algebra R F]
  (e : Cotangent A ≃ₗ[R] Cotangent B)

/-- Extend the ACTUAL integral comparison, rather than choose a
possibly rescaled generic isomorphism. -/
@[expose] def generic : GenericCotangent A F ≃ₗ[F] GenericCotangent B F :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F) e

@[simp] theorem generic_toGeneric (x : Cotangent A) :
    generic A B F e (toGeneric A F x) = toGeneric B F (e x) := by
  simp only [generic,toGeneric,TensorProduct.mk_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply]

/-- The complete embedded integral images correspond, including all
relations and any integral cotangent torsion. No freeness is assumed. -/
theorem image_iff (x : GenericCotangent A F) :
    x ∈ integralImage A F ↔ generic A B F e x ∈ integralImage B F := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨e y,(generic_toGeneric A B F e y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨e.symm y,?_⟩
    apply (generic A B F e).injective
    rw [generic_toGeneric,LinearEquiv.apply_symm_apply]
    exact hy

/-- Exact transport of the full image, not only preservation of its
rank or the norm of one selected generator. -/
theorem image_range :
    Set.image (generic A B F e) (integralImage A F : Set (GenericCotangent A F)) =
      (integralImage B F : Set (GenericCotangent B F)) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (image_iff A B F e x).mp hx
  · intro hy
    obtain ⟨x,rfl⟩ := (generic A B F e).surjective y
    exact ⟨x,(image_iff A B F e x).mpr hy,rfl⟩
end LocalSectionCotangentImageTransport318
