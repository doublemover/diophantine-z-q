module
public import RelativeLaurentGeneratorBound318
public import OriginalTwoImageBoundary318
public section
noncomputable section
namespace RelativeShiftedDifference318
open LaurentPolynomial RelativeLaurentScalar318
universe u v w z
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable {A : Type w} [AddCommGroup A] [Module R A]
  {B : Type z} [AddCommGroup B] [Module R B] (f : A →ₗ[R] M) (g : B →ₗ[R] M)

lemma mem_iff (d : ℤ) (x : M) :
    x ∈ RelativeLaurentGeneratorBound318.boundary R M f.range g.range d ↔
      ∃ a b, f a - (T d : LaurentPolynomial R) • g b = x := by
  have he : ((shift R M d).comp g).range = g.range.map (shift R M d) := by
    ext y
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨g b,⟨b,rfl⟩,rfl⟩
    · rintro ⟨z,⟨b,rfl⟩,rfl⟩
      exact ⟨b,rfl⟩
  have h := OriginalTwoImageBoundary318.mem_iff f ((shift R M d).comp g) x
  simpa only [RelativeLaurentGeneratorBound318.boundary,he,LinearMap.comp_apply,shift] using h
end RelativeShiftedDifference318
