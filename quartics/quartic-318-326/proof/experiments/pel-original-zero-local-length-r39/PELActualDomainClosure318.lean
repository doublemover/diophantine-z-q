module
public import PELMaximalActualJordanDomain318
public section
noncomputable section
namespace PELActualDomainClosure318
open Set Metric Filter
open scoped Topology
open PELMaximalActualComplexDomain318 PELMaximalActualJordanDomain318
set_option maxHeartbeats 2400000

/-- The entire actual closed half-cut, including all original vertices,
is the closure of its genuine complex interior. -/
theorem closure_openDomain : closure openDomain=closedDomain := by
  let S : Set ReflectedDiskJoukowski318.Disk := {w | ‖w.val‖<1}
  have hS : (Subtype.val : ReflectedDiskJoukowski318.Disk → ℂ) '' S=ball (0:ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa only [mem_ball,dist_zero_right] using hw
    · intro hz
      exact ⟨⟨z,ball_subset_closedBall hz⟩,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  have hdense : closure S=Set.univ := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hS,closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)]
    ext w
    simp only [mem_preimage,mem_univ,iff_true]
    exact w.property
  let F : ReflectedDiskJoukowski318.Disk → ℂ := fun w => (actualClosedDisk.symm w).val
  have hF : Continuous F := continuous_subtype_val.comp actualClosedDisk.symm.continuous
  have hFi : F '' S=openDomain := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      apply (openDomain_iff_disk_interior _).mpr
      rw [Homeomorph.apply_symm_apply]
      exact hw
    · intro hz
      let q : closedDomain := ⟨z,openDomain_subset hz⟩
      refine ⟨actualClosedDisk q,(openDomain_iff_disk_interior q).mp hz,?_⟩
      change (actualClosedDisk.symm (actualClosedDisk q)).val=z
      rw [Homeomorph.symm_apply_apply]
      rfl
  have hFc : F '' Set.univ=closedDomain := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (actualClosedDisk.symm w).property
    · intro hz
      refine ⟨actualClosedDisk ⟨z,hz⟩,Set.mem_univ _,?_⟩
      change (actualClosedDisk.symm (actualClosedDisk ⟨z,hz⟩)).val=z
      rw [Homeomorph.symm_apply_apply]
  rw [←hFi,hF.isClosedMap.closure_image_eq_of_continuous hF,hdense,hFc]

theorem actual_frontier : frontier openDomain=closedDomain\openDomain := by
  rw [←closure_sdiff_interior,closure_openDomain,openDomain_open.interior_eq]

end PELActualDomainClosure318
