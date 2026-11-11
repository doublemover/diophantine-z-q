module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public section
noncomputable section
namespace SplitHolomorphicImage318
open Filter Topology Set
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E]
  [FiniteDimensional ℂ F]

/-- An actual continuous complex-linear left inverse of an injective
finite-dimensional derivative, not a hypothesis that the image splits. -/
@[expose] def projection (A:E→L[ℂ]F):F→L[ℂ]E:=
  A.toLinearMap.leftInverse.toContinuousLinearMap
lemma projection_left (A:E→L[ℂ]F) (hA:Function.Injective A) (v:E):
    projection A (A v)=v:=
  LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hA) v
lemma projection_comp (A:E→L[ℂ]F) (hA:Function.Injective A):
    (projection A).comp A=ContinuousLinearMap.id ℂ E:=by
  ext v
  exact projection_left A hA v

variable (f:E→F) (x:E) (hf:ContDiffAt ℂ 1 f x)
  (hinj:Function.Injective (fderiv ℂ f x))
@[expose] def projected:E→E:=fun z=>projection (fderiv ℂ f x) (f z)
lemma projected_contDiff:ContDiffAt ℂ 1 (projected f x) x:=
  (projection (fderiv ℂ f x)).contDiff.contDiffAt.comp x hf
lemma projected_hasFDerivAt:
    HasFDerivAt (projected f x) ((ContinuousLinearEquiv.refl ℂ E):E→L[ℂ]E) x:=by
  have h:=(projection (fderiv ℂ f x)).hasFDerivAt.comp x
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [projection_comp _ hinj] using h

/-- The projected map is genuinely locally biholomorphic. Its source
remains an actual open subset of the ORIGINAL coordinate space. -/
@[expose] def chart:OpenPartialHomeomorph E E:=
  (projected_contDiff f x hf).toOpenPartialHomeomorph (projected f x)
    (projected_hasFDerivAt f x hf hinj) (by norm_num)
lemma chart_apply (z:E):chart f x hf hinj z=projected f x z:=rfl
lemma center_mem:x∈(chart f x hf hinj).source:=
  (projected_contDiff f x hf).mem_toOpenPartialHomeomorph_source
    (projected_hasFDerivAt f x hf hinj) (by norm_num)
lemma inverse_center:(chart f x hf hinj).symm (projected f x x)=x:=
  (chart f x hf hinj).left_inv (center_mem f x hf hinj)
lemma inverse_contDiff:
    ContDiffAt ℂ 1 (chart f x hf hinj).symm (projected f x x):=
  (projected_contDiff f x hf).to_localInverse
    (projected_hasFDerivAt f x hf hinj) (by norm_num)

@[expose] def graph:E→F:=fun w=>f ((chart f x hf hinj).symm w)
lemma graph_center:graph f x hf hinj (projected f x x)=f x:=by
  rw [graph,inverse_center]
lemma graph_contDiff:ContDiffAt ℂ 1 (graph f x hf hinj) (projected f x x):=by
  have h:ContDiffAt ℂ 1 f ((chart f x hf hinj).symm (projected f x x)):=by
    rw [inverse_center]
    exact hf
  exact h.comp _ (inverse_contDiff f x hf hinj)
lemma graph_projected (w:E) (hw:w∈(chart f x hf hinj).target):
    projection (fderiv ℂ f x) (graph f x hf hinj w)=w:=
  (chart f x hf hinj).right_inv hw
lemma graph_original (z:E) (hz:z∈(chart f x hf hinj).source):
    graph f x hf hinj (projected f x z)=f z:=by
  rw [graph,←chart_apply f x hf hinj z,(chart f x hf hinj).left_inv hz]

/-- A genuine open parameter neighborhood on which the graph is
holomorphic, with an exact image identity and linear inverse projection.
In particular this is more than injectivity of a derivative at one point. -/
theorem exists_holomorphic_graph (U:Set E) (hU:IsOpen U) (hx:x∈U):
    ∃W:Set E,IsOpen W ∧ projected f x x∈W ∧ W⊆(chart f x hf hinj).target ∧
      DifferentiableOn ℂ (graph f x hf hinj) W ∧
      (∀w∈W,(chart f x hf hinj).symm w∈U) ∧
      (∀w∈W,projection (fderiv ℂ f x) (graph f x hf hinj w)=w) ∧
      f '' ((chart f x hf hinj).source ∩ projected f x ⁻¹' W)=
        graph f x hf hinj '' W:=by
  have hg:= (graph_contDiff f x hf hinj).eventually (by norm_num)
  have ht:(chart f x hf hinj).target∈𝓝 (projected f x x):=
    (chart f x hf hinj).open_target.mem_nhds
      ((chart f x hf hinj).map_source (center_mem f x hf hinj))
  have hu:∀ᶠw in 𝓝 (projected f x x),(chart f x hf hinj).symm w∈U:=by
    have hi:=(inverse_contDiff f x hf hinj).continuousAt
    apply hi.eventually
    rw [inverse_center]
    exact hU.mem_nhds hx
  obtain ⟨W,hW,hWo,hWx⟩:=mem_nhds_iff.mp (inter_mem ht (inter_mem hg hu))
  refine ⟨W,hWo,hWx,fun w hw=>(hW hw).1,?_,?_,?_,?_⟩
  · intro w hw
    exact ((hW hw).2.1.differentiableAt (by norm_num)).differentiableWithinAt
  · intro w hw
    exact (hW hw).2.2
  · intro w hw
    exact graph_projected f x hf hinj w (hW hw).1
  · ext y
    constructor
    · rintro ⟨z,⟨hz,hzw⟩,rfl⟩
      exact ⟨projected f x z,hzw,graph_original f x hf hinj z hz⟩
    · rintro ⟨w,hw,rfl⟩
      refine ⟨(chart f x hf hinj).symm w,⟨?_,?_⟩,rfl⟩
      · exact (chart f x hf hinj).map_target (hW hw).1
      · change projected f x ((chart f x hf hinj).symm w)∈W
        rw [←chart_apply f x hf hinj,(chart f x hf hinj).right_inv (hW hw).1]
        exact hw
end SplitHolomorphicImage318
