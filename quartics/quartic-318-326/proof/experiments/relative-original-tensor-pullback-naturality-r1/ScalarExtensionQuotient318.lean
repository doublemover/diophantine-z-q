module
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Isomorphisms
public section
noncomputable section
namespace ScalarExtensionQuotient318
open TensorProduct
universe u v w
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The genuine S-linear image, not the R-linear image with an assumed
S action. No flatness of S over R is required. -/
abbrev image (P : Submodule R M) : Submodule S (S ⊗[R] M) :=
  (P.subtype.baseChange S).range

lemma kernel (P : Submodule R M) : (P.mkQ.baseChange S).ker = image S P := by
  ext x
  exact SetLike.ext_iff.mp (lTensor_mkQ S P) x

/-- Right exactness with the actual S action and a representative formula. -/
@[expose] def equivalence (P : Submodule R M) :
    ((S ⊗[R] M) ⧸ image S P) ≃ₗ[S] S ⊗[R] (M ⧸ P) :=
  (Submodule.quotEquivOfEq _ _ (kernel S P).symm).trans
    ((P.mkQ.baseChange S).quotKerEquivOfSurjective
      (LinearMap.baseChange_surjective S P.mkQ_surjective))

lemma equivalence_mk (P : Submodule R M) (s : S) (m : M) :
    equivalence S P ((image S P).mkQ (s ⊗ₜ[R] m)) = s ⊗ₜ[R] P.mkQ m := by
  simp [equivalence,Submodule.mkQ_apply]

lemma image_mono {P Q : Submodule R M} (h : P ≤ Q) : image S P ≤ image S Q := by
  rintro _ ⟨t,rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul s p =>
      exact ⟨s ⊗ₜ[R] (⟨p.1,h p.2⟩ : Q),rfl⟩
  | add x y hx hy =>
      simpa only [map_add] using (image S Q).add_mem hx hy

lemma image_sup (P Q : Submodule R M) : image S (P ⊔ Q) = image S P ⊔ image S Q := by
  apply le_antisymm
  · rintro _ ⟨t,rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul s p =>
        obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp p.2
        change s ⊗ₜ[R] p.1 ∈ image S P ⊔ image S Q
        rw [← hab,tmul_add]
        exact Submodule.add_mem _
          (Submodule.mem_sup_left ⟨s ⊗ₜ[R] (⟨a,ha⟩ : P),rfl⟩)
          (Submodule.mem_sup_right ⟨s ⊗ₜ[R] (⟨b,hb⟩ : Q),rfl⟩)
    | add x y hx hy =>
        simpa only [map_add] using (image S P ⊔ image S Q).add_mem hx hy
  · exact sup_le (image_mono S le_sup_left) (image_mono S le_sup_right)

lemma image_range {A : Type*} [AddCommGroup A] [Module R A] (f : A →ₗ[R] M) :
    image S f.range = (f.baseChange S).range := by
  ext x
  exact (SetLike.ext_iff.mp (LinearMap.lTensor_range S (g := f)) x).symm

/-- In a two-affine Cech presentation, the image sum, not either kernel,
commutes with arbitrary scalar extension. This is the right-exact step. -/
@[expose] def twoImageEquivalence (P Q : Submodule R M) :
    S ⊗[R] (M ⧸ (P ⊔ Q)) ≃ₗ[S]
      ((S ⊗[R] M) ⧸ (image S P ⊔ image S Q)) :=
  (equivalence S (P ⊔ Q)).symm.trans
    (Submodule.quotEquivOfEq _ _ (image_sup S P Q))

lemma twoImageEquivalence_tmul (P Q : Submodule R M) (s : S) (m : M) :
    twoImageEquivalence S P Q (s ⊗ₜ[R] (P ⊔ Q).mkQ m) =
      (image S P ⊔ image S Q).mkQ (s ⊗ₜ[R] m) := by
  change Submodule.quotEquivOfEq _ _ (image_sup S P Q)
    ((equivalence S (P ⊔ Q)).symm (s ⊗ₜ[R] (P ⊔ Q).mkQ m)) = _
  rw [← equivalence_mk S (P ⊔ Q),LinearEquiv.symm_apply_apply]
  rfl
end ScalarExtensionQuotient318
