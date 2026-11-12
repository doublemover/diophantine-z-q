module
public import TensorBinaryAlgebraProducts318
public section
noncomputable section
namespace AlgebraEqualizerConjugacy318
universe u
variable {R C D C' D' : Type u} [CommRing R] [CommRing C] [CommRing D]
  [CommRing C'] [CommRing D'] [Algebra R C] [Algebra R D] [Algebra R C'] [Algebra R D']
variable (f g : C →ₐ[R] D) (f' g' : C' →ₐ[R] D')
  (e : C ≃ₐ[R] C') (d : D ≃ₐ[R] D')
  (hf : ∀ z, d (f z)=f' (e z)) (hg : ∀ z, d (g z)=g' (e z))
def map : AlgHom.equalizer f g →ₐ[R] AlgHom.equalizer f' g' :=
  (e.toAlgHom.comp (AlgHom.equalizer f g).val).codRestrict _ (fun z => by
    change f' (e z)=g' (e z)
    rw [←hf,←hg,z.property])
include hf hg in
lemma inverse_mem (z : AlgHom.equalizer f' g') : f (e.symm z.val)=g (e.symm z.val) := by
  apply d.injective
  rw [hf,hg,e.apply_symm_apply,z.property]
/-- Exact full equalizer conjugacy, retaining both original arrows. -/
def equivalence : AlgHom.equalizer f g ≃ₐ[R] AlgHom.equalizer f' g' :=
  AlgEquiv.ofBijective (map f g f' g' e d hf hg) ⟨(by
    intro x y h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)),(by
    intro z
    refine ⟨⟨e.symm z.val,inverse_mem f g f' g' e d hf hg z⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply z.val)⟩
@[simp] lemma value (z : AlgHom.equalizer f g) :
    (equivalence f g f' g' e d hf hg z).val=e z.val := rfl
end AlgebraEqualizerConjugacy318
