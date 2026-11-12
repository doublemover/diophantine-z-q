module
public import LocalizedPrimitiveRootChart318
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public section
noncomputable section
namespace LocalizedPrimitiveOpenRootChart318
open Set Filter Polynomial
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- The entire source and target of the root chart stay in the original
principal base open. This is the form needed for later covering-sheet
arguments; the total extension outside D(d) cannot enter these charts. -/
theorem exists_open_root_chart (hs : Q.Separable)
    (p : AnalyticParameterizedRootChart318.ZeroLocus
      (LocalizedPrimitiveRootChart318.equation d Q))
    (hp : MvPolynomial.eval p.val.1 d ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (AnalyticParameterizedRootChart318.ZeroLocus
          (LocalizedPrimitiveRootChart318.equation d Q)) (ι → ℂ),
      p ∈ e.source ∧ (∀ q, e q = q.val.1) ∧
      (∀ q ∈ e.source, MvPolynomial.eval q.val.1 d ≠ 0) ∧
      (∀ w ∈ e.target, MvPolynomial.eval w d ≠ 0) ∧
      AnalyticOnNhd ℂ (fun w => (e.symm w).val) e.target := by
  obtain ⟨e,he,hbase,han⟩ := LocalizedPrimitiveRootChart318.exists_root_chart d Q hs p hp
  let U : Set (AnalyticParameterizedRootChart318.ZeroLocus
      (LocalizedPrimitiveRootChart318.equation d Q)) :=
    {q | MvPolynomial.eval q.val.1 d ≠ 0}
  have hU : IsOpen U := by
    have hd : Continuous (fun v : ι → ℂ => MvPolynomial.eval v d) :=
      continuous_iff_continuousAt.mpr (fun v =>
        ((AnalyticOnNhd.eval_mvPolynomial d) v (Set.mem_univ v)).continuousAt)
    have hc : Continuous (fun q : AnalyticParameterizedRootChart318.ZeroLocus
        (LocalizedPrimitiveRootChart318.equation d Q) => MvPolynomial.eval q.val.1 d) :=
      hd.comp (continuous_fst.comp continuous_subtype_val)
    exact isOpen_ne hc continuous_const
  let f := e.restrOpen U hU
  refine ⟨f,⟨he,hp⟩,hbase,fun q hq => hq.2,?_,?_⟩
  · intro w hw
    have hu : MvPolynomial.eval (f.symm w).val.1 d ≠ 0 := (f.map_target hw).2
    have hb : (f.symm w).val.1 = w := (hbase (f.symm w)).symm.trans (f.right_inv hw)
    rwa [hb] at hu
  · intro w hw
    exact han w hw.1
end LocalizedPrimitiveOpenRootChart318
