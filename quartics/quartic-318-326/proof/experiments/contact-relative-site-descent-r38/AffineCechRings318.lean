module
public import AffineModuleMate318
public section
noncomputable section
namespace AffineCechRings318
open CategoryTheory TensorProduct AffineModuleBaseChange318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]
abbrev double : CommRingCat.{u} := ring R S S
abbrev triple : CommRingCat.{u} := CommRingCat.of (S ⊗[R] (S ⊗[R] S))
abbrev map12 : double R S ⟶ triple R S :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R S)
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)).toRingHom
abbrev map13 : double R S ⟶ triple R S :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R S)
    (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)).toRingHom
abbrev map23 : double R S ⟶ triple R S :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
    S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)).toRingHom
abbrev vertex1 : S ⟶ triple R S := CommRingCat.ofHom (algebraMap S _)
abbrev vertex2 : S ⟶ triple R S := leftMap R S S ≫ map23 R S
abbrev vertex3 : S ⟶ triple R S := rightMap R S S ≫ map23 R S

lemma map12_tmul (a b : S) : map12 R S (a ⊗ₜ[R] b) = a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S)) := rfl
lemma map13_tmul (a b : S) : map13 R S (a ⊗ₜ[R] b) = a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] b) := rfl
lemma map23_tmul (a b : S) : map23 R S (a ⊗ₜ[R] b) = (1 : S) ⊗ₜ[R] (a ⊗ₜ[R] b) := rfl

lemma map12_left : (map12 R S).hom.comp (leftMap R S S).hom = (vertex1 R S).hom := by
  ext s
  change s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S)) = s ⊗ₜ[R] (1 : S ⊗[R] S)
  rw [Algebra.TensorProduct.one_def]
lemma map12_right : (map12 R S).hom.comp (rightMap R S S).hom = (vertex2 R S).hom := by
  ext s
  rfl
lemma map13_left : (map13 R S).hom.comp (leftMap R S S).hom = (vertex1 R S).hom := by
  ext s
  change s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (1 : S)) = s ⊗ₜ[R] (1 : S ⊗[R] S)
  rw [Algebra.TensorProduct.one_def]
lemma map13_right : (map13 R S).hom.comp (rightMap R S S).hom = (vertex3 R S).hom := by
  ext s
  rfl
lemma map23_left : (map23 R S).hom.comp (leftMap R S S).hom = (vertex2 R S).hom := rfl
lemma map23_right : (map23 R S).hom.comp (rightMap R S S).hom = (vertex3 R S).hom := rfl
end AffineCechRings318
