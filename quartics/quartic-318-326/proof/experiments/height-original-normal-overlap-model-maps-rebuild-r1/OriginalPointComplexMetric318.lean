module
public import OriginalIntrinsicPointModule318
public import OriginalIntrinsicAdelicSectionNorms318
public section
noncomputable section
namespace OriginalPointComplexMetric318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalIntrinsicPointModule318 OriginalArchimedeanSectionCoefficient318
open OriginalArchimedeanFrameNorm318 PELOriginalManuscriptNormalization318
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t))

/-- Complex scalar extension of the SAME original whole-point K-module
that carries every finite integral lattice. No branch occurs in this object. -/
abbrev complexModule := (ModuleCat.extendScalars w.embedding).obj (pointModule c t)
@[expose] def coefficientFrame (i : Fin 4) : complexModule c t w ≃ₗ[ℂ] ℂ := by
  letI : Algebra (K c t) ℂ := w.embedding.toAlgebra
  exact ScalarExtensionTensor318.tensorEquiv (T:=ℂ) (pointModule c t) ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) (frame c t hn i) ≪≫ₗ
      AlgebraTensorModule.rid (K c t) ℂ ℂ
lemma coefficientFrame_tmul (i : Fin 4) (z : ℂ) (x : pointModule c t) :
    coefficientFrame c t hn w i (z ⊗ₜ[K c t,w.embedding] x)=z*w.embedding (frame c t hn i x) := by
  letI : Algebra (K c t) ℂ := w.embedding.toAlgebra
  change AlgebraTensorModule.rid (K c t) ℂ ℂ
    (AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) (frame c t hn i)
      (ScalarExtensionTensor318.tensorEquiv (T:=ℂ) (pointModule c t)
        (z ⊗ₜ[K c t,w.embedding] x)))=_
  rw [ScalarExtensionTensor318.tensorEquiv_tmul,AlgebraTensorModule.congr_tmul,AlgebraTensorModule.rid_tmul]
  simp only [LinearEquiv.refl_apply,Algebra.smul_def]

@[expose] def tangentFrame (i : Fin 4) : complexModule c t w ≃ₗ[ℂ] ℂ :=
  coefficientFrame c t hn w i ≪≫ₗ
    LinearEquiv.smulOfUnit (Units.mk0 (branchDerivative c t w i^2)
      (pow_ne_zero _ (branchDerivative_ne c t hn w i)))
lemma tangentFrame_tmul (i : Fin 4) (z : ℂ) (x : pointModule c t) :
    tangentFrame c t hn w i (z ⊗ₜ[K c t,w.embedding] x)=
      z*w.embedding (frame c t hn i x)*branchDerivative c t w i^2 := by
  change branchDerivative c t w i^2*coefficientFrame c t hn w i _=_
  rw [coefficientFrame_tmul]
  ring

/-- Equality of the WHOLE complex tangent frames on one fixed scalar
fiber follows from the actual point-frame transition and derivative
transition, not from agreement on only the two bounded sections. -/
theorem tangentFrame_independent (i j : Fin 4) :
    tangentFrame c t hn w i=tangentFrame c t hn w j := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    rw [tangentFrame_tmul,tangentFrame_tmul,frame_transition c t hn i j x,map_mul,
      OriginalArchimedeanIntrinsicNorm318.derivative_frame_transition c t hn w i j]
    ring
  | add x y hx hy => simp only [map_add,hx,hy]

variable (hλ : lambda=2401) (hμ : mu= -343/32)
@[expose] def metricFrame (i : Fin 4) : complexModule c t w ≃ₗ[ℂ] ℂ :=
  tangentFrame c t hn w i ≪≫ₗ LinearEquiv.smulOfUnit
    (Units.mk0 (OriginalArchimedeanNormedFiber318.metricScale hλ hμ c t w:ℂ)
      (Complex.ofReal_ne_zero.mpr (OriginalArchimedeanNormedFiber318.metricScale_pos hλ hμ c t w).ne'))
lemma metricFrame_independent (i j : Fin 4) :
    metricFrame c t hn w hλ hμ i=metricFrame c t hn w hλ hμ j := by
  unfold metricFrame
  rw [tangentFrame_independent c t hn w i j]

/-- Canonical norm on the actual original point-line complexification.
The fixed index0 is immaterial by the full frame equality just proved. -/
@[expose] def normedGroup : NormedAddCommGroup (complexModule c t w) :=
  NormedAddCommGroup.induced _ ℂ (metricFrame c t hn w hλ hμ 0).toAddMonoidHom
    (metricFrame c t hn w hλ hμ 0).injective
@[expose] def normedSpace :
    letI := normedGroup c t hn w hλ hμ
    NormedSpace ℂ (complexModule c t w) := by
  letI := normedGroup c t hn w hλ hμ
  refine { norm_smul_le := ?_ }
  intro a x
  change ‖metricFrame c t hn w hλ hμ 0 (a • x)‖≤‖a‖*‖metricFrame c t hn w hλ hμ 0 x‖
  rw [map_smul,norm_smul]

lemma norm_frame (i : Fin 4) (x : complexModule c t w) :
    letI := normedGroup c t hn w hλ hμ
    ‖x‖=PeterssonSectionNorm318.quadraticNorm (density hλ hμ c t w) (tangentFrame c t hn w i x) := by
  change ‖metricFrame c t hn w hλ hμ 0 x‖=_
  rw [metricFrame_independent c t hn w hλ hμ 0 i]
  change ‖(OriginalArchimedeanNormedFiber318.metricScale hλ hμ c t w:ℂ)*tangentFrame c t hn w i x‖=_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (OriginalArchimedeanNormedFiber318.metricScale_pos hλ hμ c t w)]
  unfold OriginalArchimedeanNormedFiber318.metricScale PeterssonSectionNorm318.quadraticNorm
  ring

@[expose] def globalElement (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : complexModule c t w :=
  (1:ℂ) ⊗ₜ[K c t,w.embedding] OriginalIntrinsicPointModule318.globalElement c t s

/-- The true canonical global point element has the previously produced
arithmetic/Poincare norm in EVERY branch frame. -/
lemma global_norm (i : Fin 4) (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    letI := normedGroup c t hn w hλ hμ
    ‖globalElement c t w s‖=
      w (ContactBicanonicalPointValue318.value c t hn i s)*frameNorm hλ hμ c t w i := by
  rw [norm_frame c t hn w hλ hμ i,globalElement,tangentFrame_tmul,one_mul,frame_global]
  exact (scalar_norm hλ hμ c t w i _).symm
end OriginalPointComplexMetric318
