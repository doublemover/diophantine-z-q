module
public import FlatPrincipalCoefficientRegular318
public section
noncomputable section
namespace VaryingSourceTensorCollapse318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
/-- The actual original coefficient tensor source, with its entire
nested base change collapsed by the native algebra equivalence. -/
abbrev equivalence : T ⊗[S] (S ⊗[R] A) ≃ₐ[T] T ⊗[R] A :=
  Algebra.TensorProduct.cancelBaseChange R S T T A
lemma source (z : S ⊗[R] A) : equivalence R A S T ((1 : T) ⊗ₜ[S] z)=VaryingWholeQuotientTensor318.source R A S T z := by
  induction z using TensorProduct.inductionOn with
  | tmul s a => simp only [Algebra.TensorProduct.cancelBaseChange_tmul,Algebra.smul_def,mul_one,
      VaryingWholeQuotientTensor318.source,Algebra.TensorProduct.rTensor,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,Algebra.ofId_apply]
  | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,hx,hy]
lemma source_hom : (equivalence R A S T).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom=
    (VaryingWholeQuotientTensor318.source R A S T).toRingHom := by
  ext z
  exact source R A S T z
lemma ideal (I : Ideal (S ⊗[R] A)) : Ideal.map (equivalence R A S T).toRingHom
    (FlatQuotientIdealTensor318.extended S (S ⊗[R] A) T I)=VaryingWholeQuotientTensor318.ideal R A S T I := by
  rw [FlatQuotientIdealTensor318.extended,Ideal.map_map,source_hom]
  rfl
end VaryingSourceTensorCollapse318
