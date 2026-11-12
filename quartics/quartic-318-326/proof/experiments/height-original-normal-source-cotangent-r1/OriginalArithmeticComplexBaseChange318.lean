module
public import OriginalArithmeticTensorFiber318
public import OriginalArchimedeanNormedFiber318
public section
noncomputable section
namespace OriginalArithmeticComplexBaseChange318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalArchimedeanCotangentFiber318 OriginalArchimedeanSectionCoefficient318
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i : Fin 4)

/-- Extend the SAME genuine arithmetic fiber through the actual infinite
place embedding, instead of introducing an independent complex line. -/
abbrev complexFiber := (ModuleCat.extendScalars w.embedding).obj
  (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn i))
@[expose] def coefficientFrame : complexFiber c t hn w i ≃ₗ[ℂ] ℂ := by
  letI : Algebra (K c t) ℂ := w.embedding.toAlgebra
  exact ScalarExtensionTensor318.tensorEquiv (T:=ℂ)
    (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn i)) ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
        (OriginalArithmeticTensorFiber318.frame c t hn i) ≪≫ₗ
          AlgebraTensorModule.rid (K c t) ℂ ℂ
lemma coefficientFrame_tmul (z : ℂ) (x : OriginalArithmeticTensorFiber318.fiber c t hn i) :
    coefficientFrame c t hn w i (z ⊗ₜ[K c t,w.embedding] x)=
      z*w.embedding (OriginalArithmeticTensorFiber318.frame c t hn i x) := by
  letI : Algebra (K c t) ℂ := w.embedding.toAlgebra
  change AlgebraTensorModule.rid (K c t) ℂ ℂ
    (AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
      (OriginalArithmeticTensorFiber318.frame c t hn i)
      (ScalarExtensionTensor318.tensorEquiv (T:=ℂ)
        (ModuleCat.of (K c t) (OriginalArithmeticTensorFiber318.fiber c t hn i))
        (z ⊗ₜ[K c t,w.embedding] x)))=_
  rw [ScalarExtensionTensor318.tensorEquiv_tmul,AlgebraTensorModule.congr_tmul,
    AlgebraTensorModule.rid_tmul]
  simp only [LinearEquiv.refl_apply,Algebra.smul_def]

/-- Entire analytic tensor functional is the coefficient evaluation of
this SAME arithmetic tensor, times the proved actual derivative square. -/
lemma tensor_coefficient (θ : OriginalArithmeticTensorFiber318.square c i) :
    OriginalArchimedeanIntrinsicTensor318.tensor c t hn w i θ=
      w.embedding (OriginalArithmeticTensorFiber318.point c t hn i
        (OriginalArchimedeanComplexFiber318.squareFrame c i θ))*branchDerivative c t w i^2 := by
  induction θ using TensorProduct.induction_on with
  | zero => simp
  | tmul ω η =>
    rw [OriginalArchimedeanIntrinsicTensor318.tensor_pure,
      OriginalArchimedeanComplexFiber318.squareFrame_pure,map_mul,map_mul]
    simp only [OriginalArchimedeanCotangentFiber318.differential,
      OriginalArchimedeanCotangentFiber318.point,OriginalArithmeticTensorFiber318.point,
      RingHom.comp_apply]
    ring
  | add θ ψ hθ hψ => simp only [map_add,hθ,hψ,add_mul]

/-- Genuine both-inverse complex-linear scalar-extension comparison.
The following whole nested-pure identity pins it to the actual tensor
associativity/base square, not just an abstract dimension-one isomorphism. -/
@[expose] def comparison : complexFiber c t hn w i ≃ₗ[ℂ]
    OriginalArchimedeanComplexFiber318.fiber c t hn w i :=
  coefficientFrame c t hn w i ≪≫ₗ
    LinearEquiv.smulOfUnit (Units.mk0 (branchDerivative c t w i^2)
      (pow_ne_zero _ (branchDerivative_ne c t hn w i))) ≪≫ₗ
        (OriginalArchimedeanComplexFiber318.frame c t hn w i).symm

lemma comparison_nested (z : ℂ) (a : K c t) (θ : OriginalArithmeticTensorFiber318.square c i) :
    comparison c t hn w i
      (z ⊗ₜ[K c t,w.embedding]
        (a ⊗ₜ[A c i,OriginalArithmeticTensorFiber318.point c t hn i] θ))=
    (z*w.embedding a) ⊗ₜ[A c i,OriginalArchimedeanCotangentFiber318.point c t hn w i] θ := by
  apply (OriginalArchimedeanComplexFiber318.frame c t hn w i).injective
  change OriginalArchimedeanComplexFiber318.frame c t hn w i
    ((OriginalArchimedeanComplexFiber318.frame c t hn w i).symm
      (branchDerivative c t w i^2*coefficientFrame c t hn w i _))=_
  rw [LinearEquiv.apply_symm_apply,coefficientFrame_tmul,
    OriginalArithmeticTensorFiber318.frame_tmul,map_mul,
    OriginalArchimedeanComplexFiber318.frame_tmul,tensor_coefficient]
  ring

/-- The SAME actual global section fiber commutes with scalar extension
for EVERY proper-curve global section, not only the two bounded sections. -/
lemma comparison_global (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    comparison c t hn w i
      ((1:ℂ) ⊗ₜ[K c t,w.embedding] OriginalArithmeticTensorFiber318.globalFiber c t hn i s)=
        OriginalArchimedeanComplexFiber318.globalFiber c t hn w i s := by
  unfold OriginalArithmeticTensorFiber318.globalFiber OriginalArchimedeanComplexFiber318.globalFiber
  rw [comparison_nested,map_one,mul_one]
end OriginalArithmeticComplexBaseChange318
