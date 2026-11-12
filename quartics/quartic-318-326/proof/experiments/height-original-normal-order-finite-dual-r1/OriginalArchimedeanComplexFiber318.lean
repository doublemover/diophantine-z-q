module
public import OriginalArchimedeanIntrinsicNorm318
public import ScalarExtensionTensor318
public section
noncomputable section
namespace OriginalArchimedeanComplexFiber318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanSectionCoefficient318
open OriginalArchimedeanCotangentFiber318 OriginalArchimedeanIntrinsicTensor318
open CategoryTheory TensorProduct AlgebraicGeometry
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i : Fin 4)
abbrev square := Omega c i ⊗[A c i] Omega c i
@[expose] def squareFrame : square c i ≃ₗ[A c i] A c i :=
  TensorProduct.congr (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i) ≪≫ₗ TensorProduct.lid (A c i) (A c i)
lemma squareFrame_pure (ω η : Omega c i) : squareFrame c i (ω ⊗ₜ[A c i] η)=
    ContactDifferentialFrames318.sourceLocalizationFrame c i ω*
      ContactDifferentialFrames318.sourceLocalizationFrame c i η := by
  simp only [squareFrame,LinearEquiv.trans_apply,TensorProduct.congr_tmul,TensorProduct.lid_tmul,smul_eq_mul]

/-- The ACTUAL complex scalar fiber uses the original branch-point ring
map, not a separately specified complex line. -/
abbrev fiber := (ModuleCat.extendScalars (point c t hn w i)).obj (ModuleCat.of (A c i) (square c i))

/-- Both-inverse complex-linear frame of the genuine scalar fiber. The
last unit scaling is exactly the proved analytic derivative square. -/
@[expose] def frame : fiber c t hn w i ≃ₗ[ℂ] ℂ := by
  letI : Algebra (A c i) ℂ := (point c t hn w i).toAlgebra
  exact ScalarExtensionTensor318.tensorEquiv (T:=ℂ) (ModuleCat.of (A c i) (square c i)) ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) (squareFrame c i) ≪≫ₗ
      AlgebraTensorModule.rid (A c i) ℂ ℂ ≪≫ₗ
        LinearEquiv.smulOfUnit (Units.mk0 (branchDerivative c t w i^2)
          (pow_ne_zero _ (branchDerivative_ne c t hn w i)))

/-- Every pure tensor in the genuine complex fiber has the expected
balanced value. This pins the frame to the WHOLE original cotangent
map, including its actual scalar map, before any section norm is used. -/
lemma frame_pure (z : ℂ) (ω η : Omega c i) :
    frame c t hn w i (z ⊗ₜ[A c i,point c t hn w i] (ω ⊗ₜ[A c i] η))=
      z*tensor c t hn w i (ω ⊗ₜ[A c i] η) := by
  letI : Algebra (A c i) ℂ := (point c t hn w i).toAlgebra
  change branchDerivative c t w i^2 *
    (AlgebraTensorModule.rid (A c i) ℂ ℂ
      (AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) (squareFrame c i)
        (ScalarExtensionTensor318.tensorEquiv (T:=ℂ) (ModuleCat.of (A c i) (square c i))
          (z ⊗ₜ[A c i,point c t hn w i] (ω ⊗ₜ[A c i] η)))))=_
  rw [ScalarExtensionTensor318.tensorEquiv_tmul,AlgebraTensorModule.congr_tmul,
    AlgebraTensorModule.rid_tmul,squareFrame_pure,tensor_pure]
  simp only [LinearEquiv.refl_apply,Algebra.smul_def,map_mul,differential]
  ring

lemma frame_tmul (z : ℂ) (θ : square c i) :
    frame c t hn w i (z ⊗ₜ[A c i,point c t hn w i] θ)=z*tensor c t hn w i θ := by
  induction θ using TensorProduct.induction_on with
  | zero => simp
  | tmul ω η => exact frame_pure c t hn w i z ω η
  | add θ ψ hθ hψ => simp only [tmul_add,map_add,hθ,hψ,mul_add]

/-- The literal complex fiber of ANY original proper-curve global
section, with no restriction to the displayed q0/q1 pair. -/
@[expose] def globalFiber (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : fiber c t hn w i :=
  (1:ℂ) ⊗ₜ[A c i,point c t hn w i] (ContactTrueGlobalTensorPullback318.chartTensor c i s)
lemma frame_globalFiber (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    frame c t hn w i (globalFiber c t hn w i s)=globalValue c t hn w i s := by
  rw [globalFiber,frame_tmul,one_mul]
  rfl

lemma frame_left_inverse (v : fiber c t hn w i) : (frame c t hn w i).symm (frame c t hn w i v)=v :=
  (frame c t hn w i).symm_apply_apply v
lemma frame_right_inverse (z : ℂ) : frame c t hn w i ((frame c t hn w i).symm z)=z :=
  (frame c t hn w i).apply_symm_apply z
end OriginalArchimedeanComplexFiber318
