module
public import AlgebraEqualizerConjugacy318
public section
noncomputable section
namespace FlatBinarySectionAlgebra318
open scoped TensorProduct
universe u
variable {R C D E : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing E]
  [Algebra R C] [Algebra R D] [Algebra R E]
variable (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
variable (f : C →ₐ[R] E) (g : D →ₐ[R] E)
abbrev pairs := AlgHom.equalizer (f.comp (AlgHom.fst R C D)) (g.comp (AlgHom.snd R C D))
open TensorAlgebraBaseChange318
lemma left_square (z : A ⊗[R] (C×D)) :
    map A (f.comp (AlgHom.fst R C D)) z=
      map A f (TensorBinaryAlgebraProducts318.equivalence A z).1 := by
  rw [TensorBinaryAlgebraProducts318.fst_value,composition] <;> rfl
lemma right_square (z : A ⊗[R] (C×D)) :
    map A (g.comp (AlgHom.snd R C D)) z=
      map A g (TensorBinaryAlgebraProducts318.equivalence A z).2 := by
  rw [TensorBinaryAlgebraProducts318.snd_value,composition] <;> rfl
/-- Tensor the FULL compatible-section ring and identify it with the
compatible pairs on the actual two tensor charts. Flatness is the only
exactness input; neither difference-map surjectivity nor a splitting is used. -/
def equivalence : A ⊗[R] pairs f g ≃ₐ[A] pairs (map A f) (map A g) :=
  (FlatAlgebraEqualizerBaseChange318.equivalence A
    (f.comp (AlgHom.fst R C D)) (g.comp (AlgHom.snd R C D))).trans
      (AlgebraEqualizerConjugacy318.equivalence _ _ _ _
        (TensorBinaryAlgebraProducts318.equivalence A) (AlgEquiv.refl _ _)
        (left_square A f) (right_square A g))
@[simp] lemma pure_value (a : A) (z : pairs f g) :
    (equivalence A f g (a ⊗ₜ[R] z)).val=(a ⊗ₜ[R] z.val.1,a ⊗ₜ[R] z.val.2) := rfl
end FlatBinarySectionAlgebra318
