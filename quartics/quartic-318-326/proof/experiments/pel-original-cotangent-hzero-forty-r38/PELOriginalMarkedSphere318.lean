module
public import PELOriginalAnalyticSphere318
public import PELOriginalDirectBranchEnumeration318
public import ComplexSphereFourPointNormalization318
public section
noncomputable section
namespace PELOriginalMarkedSphere318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELOriginalFiniteRamification318 PELOriginalDirectBranchEnumeration318
open PELStabilizerLocusInvariant318 ComplexSphereCharts318
open ComplexSphereFourPointNormalization318
set_option maxHeartbeats 2800000
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The original five labels remain in their original order 30,42,70,105,210. -/
@[expose] def branchPoint (i:Fin 5) : MaximalBase:=(displayed i).val

theorem branchPoint_injective : Function.Injective branchPoint := by
  intro i j h
  exact displayed_injective (Subtype.ext h)

theorem branchImage_eq_range : branchImage=range branchPoint := by
  ext q
  constructor
  · intro hq
    obtain ⟨i,hi⟩:=displayed_surjective ⟨q,hq⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  · rintro ⟨i,rfl⟩
    exact (displayed i).property

/-- The ACTUAL original marked quotient admits a normalized analytic
coordinate with branch labels30,42,70 at infinity,0,1 respectively.
The remaining original105/210 coordinates are constructed complex moduli
lam,mu, with exact distinctness, NOT assumed to equal published rational
values. Identifying those moduli is a separate arithmetic comparison. -/
theorem original_normalized_five_branch_points :
    ∃(H:MaximalBase≃ₜOnePoint ℂ)(lam mu:ℂ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
      H (branchPoint 0)=∞ ∧ H (branchPoint 1)=(0:ℂ) ∧ H (branchPoint 2)=(1:ℂ) ∧
      H (branchPoint 3)=(lam:OnePoint ℂ) ∧ H (branchPoint 4)=(mu:OnePoint ℂ) ∧
      lam≠0 ∧ lam≠1 ∧ mu≠0 ∧ mu≠1 ∧ lam≠mu ∧
      H '' branchImage=({∞,(0:ℂ),(1:ℂ),(lam:ℂ),(mu:ℂ)}:Set (OnePoint ℂ)) := by
  obtain ⟨G,hG,hGI,_⟩:=PELOriginalAnalyticSphere318.original_analytic_sphere
  let points:Fin 4→OnePoint ℂ:=fun i=>G (branchPoint i.castSucc)
  have hp:Function.Injective points := by
    intro i j h
    have hij:=branchPoint_injective (G.injective h)
    exact Fin.ext (congrArg Fin.val hij)
  let N:=normalization points hp
  have hN:= (normalization_biholomorphic points hp).1
  have hNI:= (normalization_biholomorphic points hp).2
  have h0:N (G (branchPoint 0))=∞:=normalization_zero points hp
  have h1:N (G (branchPoint 1))=(0:ℂ):=normalization_one points hp
  have h2:N (G (branchPoint 2))=(1:ℂ):=normalization_two points hp
  let H:=G.trans N
  have hH:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H:=hN.comp hG
  have hHI:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm:=hGI.comp hNI
  have hB:Function.Injective (fun i:Fin 5=>H (branchPoint i)):=H.injective.comp branchPoint_injective
  have h30:H (branchPoint 3)≠∞ := by
    intro h
    have he:=hB (h.trans h0.symm)
    norm_num at he
  have h40:H (branchPoint 4)≠∞ := by
    intro h
    have he:=hB (h.trans h0.symm)
    norm_num at he
  obtain ⟨lam,hlam⟩:=OnePoint.ne_infty_iff_exists.mp h30
  obtain ⟨mu,hmu⟩:=OnePoint.ne_infty_iff_exists.mp h40
  have hlam0:lam≠0 := by
    intro h
    have he:=hB (hlam.symm.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans h1.symm))
    norm_num at he
  have hlam1:lam≠1 := by
    intro h
    have he:=hB (hlam.symm.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans h2.symm))
    norm_num at he
  have hmu0:mu≠0 := by
    intro h
    have he:=hB (hmu.symm.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans h1.symm))
    norm_num at he
  have hmu1:mu≠1 := by
    intro h
    have he:=hB (hmu.symm.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans h2.symm))
    norm_num at he
  have hlammu:lam≠mu := by
    intro h
    have he:=hB (hlam.symm.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans hmu))
    norm_num at he
  refine ⟨H,lam,mu,hH,hHI,h0,h1,h2,hlam.symm,hmu.symm,hlam0,hlam1,hmu0,hmu1,hlammu,?_⟩
  rw [branchImage_eq_range,←range_comp]
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp only [Function.comp_apply] <;> simp [h0,h1,h2,←hlam,←hmu]
  · intro hp
    simp only [mem_insert_iff,mem_singleton_iff] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · exact ⟨0,h0⟩
    · exact ⟨1,h1⟩
    · exact ⟨2,h2⟩
    · exact ⟨3,hlam.symm⟩
    · exact ⟨4,hmu.symm⟩
end PELOriginalMarkedSphere318
