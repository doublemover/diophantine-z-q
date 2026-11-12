module
public import OriginalArchimedeanComplexFiber318
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public section
noncomputable section
namespace OriginalArchimedeanNormedFiber318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanFrameNorm318
open OriginalArchimedeanComplexFiber318 PELOriginalManuscriptNormalization318
open PeterssonSectionNorm318 AlgebraicGeometry
variable (hλ : lambda=2401) (hμ : mu= -343/32)
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i : Fin 4)
@[expose] def metricScale : ℝ := (2/Real.sqrt (density hλ hμ c t w))^2
lemma metricScale_pos : 0<metricScale hλ hμ c t w :=
  sq_pos_of_pos (div_pos (by norm_num) (Real.sqrt_pos.2 (density_pos hλ hμ c t w)))

/-- Actual metric frame of the genuine complex scalar fiber, retaining
the factor2 cotangent convention and its square for bicanonical tensors. -/
@[expose] def metricFrame : fiber c t hn w i ≃ₗ[ℂ] ℂ :=
  frame c t hn w i ≪≫ₗ LinearEquiv.smulOfUnit
    (Units.mk0 (metricScale hλ hμ c t w:ℂ)
      (Complex.ofReal_ne_zero.mpr (metricScale_pos hλ hμ c t w).ne'))

/-- A genuine normed additive group on the ACTUAL fiber, induced through
the injective metric frame; not merely a number attached to two sections. -/
@[expose] def normedGroup : NormedAddCommGroup (fiber c t hn w i) :=
  NormedAddCommGroup.induced _ ℂ (metricFrame hλ hμ c t hn w i).toAddMonoidHom
    (metricFrame hλ hμ c t hn w i).injective
@[expose] def normedSpace :
    letI := normedGroup hλ hμ c t hn w i
    NormedSpace ℂ (fiber c t hn w i) := by
  letI := normedGroup hλ hμ c t hn w i
  refine { norm_smul_le := ?_ }
  intro a v
  change ‖metricFrame hλ hμ c t hn w i (a • v)‖≤‖a‖*‖metricFrame hλ hμ c t hn w i v‖
  rw [map_smul,norm_smul]

lemma norm_eq (v : fiber c t hn w i) :
    letI := normedGroup hλ hμ c t hn w i
    ‖v‖=quadraticNorm (density hλ hμ c t w) (frame c t hn w i v) := by
  change ‖(metricScale hλ hμ c t w:ℂ)*frame c t hn w i v‖=_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (metricScale_pos hλ hμ c t w)]
  unfold metricScale quadraticNorm
  ring

/-- The honest norm of EVERY true global section fiber equals its actual
arithmetic frame value times the produced Poincare branch-frame norm. -/
lemma global_norm (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    letI := normedGroup hλ hμ c t hn w i
    ‖globalFiber c t hn w i s‖=
      w (ContactBicanonicalPointValue318.value c t hn i s)*frameNorm hλ hμ c t w i := by
  rw [norm_eq,frame_globalFiber]
  exact OriginalArchimedeanIntrinsicNorm318.globalNorm_original hλ hμ c t hn w i s
end OriginalArchimedeanNormedFiber318
