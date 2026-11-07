module
public import HolomorphicProjection318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318 HolomorphicCharts318
open Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicInverse318
set_option maxHeartbeats 0

/-- Every genuine local inverse sheet of the quotient covering is holomorphic
on its actual source, for the constructed complex analytic structure. -/
theorem inverse_holomorphic (N:ℕ) (hN:5≤N)
    (e:OpenPartialHomeomorph (Base (image N)) UpperHalfPlane)
    (he:(e.symm:UpperHalfPlane→Base (image N))=quotientMap N) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source := by
  letI:=complexChartedSpace N hN
  intro q hq
  apply ContMDiffAt.contMDiffWithinAt
  apply _root_.contMDiffAt_iff.mpr
  refine ⟨e.continuousAt hq,?_⟩
  let b:UpperHalfPlane:=(quotient_surjective N q).choose
  have hb:quotientMap N b=q := (quotient_surjective N q).choose_spec
  have hbsource:quotientMap N b∈e.source := by rw [hb];exact hq
  have han:=InverseCoordinate318.analytic_local_inverse N hN e he b hbsource
  simp only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id]
  change ContDiffWithinAt ℂ ω (fun w:ℂ => (e ((localChart N hN b).symm w):ℂ))
    Set.univ (localChart N hN b q)
  have hc:localChart N hN b q=(b:ℂ) := by
    rw [localChart_apply,←hb,(quotient_localHomeomorph N hN).localInverseAt_apply_self]
  simp only [localChart_symm_apply,hc]
  exact han.contDiffAt.contDiffWithinAt

theorem localInverseAt_holomorphic (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω ((quotient_localHomeomorph N hN).localInverseAt a)
      ((quotient_localHomeomorph N hN).localInverseAt a).source :=
  inverse_holomorphic N hN _ ((quotient_localHomeomorph N hN).localInverseAt_symm a)
end HolomorphicInverse318
