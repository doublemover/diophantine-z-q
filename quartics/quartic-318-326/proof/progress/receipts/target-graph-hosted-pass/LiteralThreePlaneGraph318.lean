module
public import LiteralThreePlaneImmersion318
public import AnalyticImplicitGraph318
public import Mathlib.Analysis.Analytic.Linear
public section
noncomputable section
open Filter
open scoped Topology
namespace LiteralThreePlaneGraph318
open LiteralThreeBaseEvaluation318 LiteralThreePlanePoints318 LiteralThreePlaneImmersion318
set_option maxHeartbeats 0

lemma Q_analyticAt (p : ℂ × ℂ) : AnalyticAt ℂ (fun v : ℂ × ℂ => Q v.1 v.2) p := by
  have hf : AnalyticAt ℂ (fun v : ℂ × ℂ => v.1) p := analyticAt_fst
  have hs : AnalyticAt ℂ (fun v : ℂ × ℂ => v.2) p := analyticAt_snd
  have h1 : AnalyticAt ℂ (fun v : ℂ × ℂ => (v.1-1728)^2*v.2^4) p :=
    ((hf.sub analyticAt_const).pow 2).mul (hs.pow 4)
  have h2 : AnalyticAt ℂ (fun v : ℂ × ℂ => 6*v.1*(v.1-1728)*v.2^2) p :=
    ((analyticAt_const.mul hf).mul (hf.sub analyticAt_const)).mul (hs.pow 2)
  have h3 : AnalyticAt ℂ (fun v : ℂ × ℂ => 8*v.1*(v.1-1728)*v.2) p :=
    ((analyticAt_const.mul hf).mul (hf.sub analyticAt_const)).mul hs
  have h4 : AnalyticAt ℂ (fun v : ℂ × ℂ => 3*v.1^2) p :=
    analyticAt_const.mul (hf.pow 2)
  exact ((h1.sub h2).sub h3).sub h4

/-- An independent holomorphic graph of the literal quartic through every
actual plane point. Its local uniqueness is proved by the implicit function theorem,
using the nonzero partial already obtained from the actual algebraic cubic unit. -/
theorem exists_graph (p : Plane) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p.val.1.val ∧ g p.val.1.val=p.val.2 ∧
      (∀ᶠ z in 𝓝 p.val.1.val, Q z (g z)=0) ∧
      (∀ᶠ v in 𝓝 (p.val.1.val,p.val.2), Q v.1 v.2=0 ↔ g v.1=v.2) := by
  have h := AnalyticImplicitGraph318.exists_graph (Q_analyticAt (p.val.1.val,p.val.2))
    (hasDerivAt_Q p.val.1.val p.val.2) (plane_partialX_ne_zero p)
  simpa only [p.property] using h

@[expose] def graph (p : Plane) : ℂ → ℂ := (exists_graph p).choose

lemma graph_spec (p : Plane) : AnalyticAt ℂ (graph p) p.val.1.val ∧
    graph p p.val.1.val=p.val.2 ∧
    (∀ᶠ z in 𝓝 p.val.1.val, Q z (graph p z)=0) ∧
    (∀ᶠ v in 𝓝 (p.val.1.val,p.val.2), Q v.1 v.2=0 ↔ graph p v.1=v.2) :=
  (exists_graph p).choose_spec

end LiteralThreePlaneGraph318
