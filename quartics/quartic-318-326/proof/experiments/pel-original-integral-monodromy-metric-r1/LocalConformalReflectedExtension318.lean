module
public import LocalConformalEdgeExtension318
public section
noncomputable section
namespace LocalConformalReflectedExtension318
open Set Filter Metric
open scoped Topology ComplexConjugate
open HolomorphicRectanglePrimitive318
open RealSeamNeighborhood318 ConformalBoundaryModulus318
set_option maxHeartbeats 3200000

/-- Construct an actual analytic extension at a geodesic edge from a
GENUINE interior disk homeomorphism and its holomorphy. Neither complex
boundary values nor a boundary extension of that homeomorphism are inputs.
The local source chart and its upper-side identity are explicit inputs
supplied by the six original geodesic chart producers. -/
theorem local_extension_with_reflection (D:Set ℂ) (hD:IsOpen D)
    (disk:D≃ₜUnitDisk) (f:ℂ→ℂ) (hf:∀q:D,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f D)
    (e:OpenPartialHomeomorph ℂ ℂ)
    (hea:AnalyticOnNhd ℂ e e.source) (hia:AnalyticOnNhd ℂ e.symm e.target)
    {z:ℂ} (hz:z∈e.source) (hreal:(e z).im=0)
    (hhalf:∀ᶠw in 𝓝 (e z),e.symm w∈D ↔ 0<w.im) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ F=ᶠ[𝓝[D] z] f ∧ ‖F z‖=1 ∧
      ∀ᶠy in 𝓝 z,(e y).im<0 →
        F y=(conj (f (e.symm (conj (e y)))))⁻¹ := by
  have hw:e z∈e.target := e.map_source hz
  have hback:e.symm (e z)=z := e.left_inv hz
  have hfront:z∈frontier D := by
    simpa only [hback] using chart_seam_frontier D hD e hw hreal hhalf
  have hlow : ∀ᶠy in 𝓝 z,y∈D → (1/2:ℝ)<‖f y‖ :=
    eventually_nhdsWithin_iff.mp (boundary_norm_lower D hD disk f hf z hfront (1/2) (by norm_num))
  have hsym:Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    simpa only [hback] using (e.continuousAt_symm hw).tendsto
  let S:Set ℂ := {w | e.symm w∈D ↔ 0<w.im}
  let T:Set ℂ := {w | e.symm w∈D → (1/2:ℝ)<‖f (e.symm w)‖}
  let V:Set ℂ := e.target∩(interior S∩interior T)
  have hV:IsOpen V := e.open_target.inter (isOpen_interior.inter isOpen_interior)
  have hwV:e z∈V := ⟨hw,mem_interior_iff_mem_nhds.mpr hhalf,
    mem_interior_iff_mem_nhds.mpr (hsym.eventually hlow)⟩
  let x:ℝ := (e z).re
  have hx:e z=(x:ℂ) := by apply Complex.ext <;> simp [x,hreal]
  have hVx:V∈𝓝 (x:ℂ) := by simpa only [←hx] using hV.mem_nhds hwV
  obtain ⟨r,hr,hrect⟩ := rectangle_in_neighborhood x V hVx
  let U:Set ℂ := openRectangle (x-r) (x+r) 0 r
  let W:Set ℂ := openRectangle (x-r) (x+r) (-r) r
  have hab:x-r<x+r := by linarith
  have hxmid:x∈Ioo (x-r) (x+r) := by constructor <;> linarith
  have upper_full : U⊆W := by
    intro w hw'
    exact ⟨hw'.1,⟨by linarith [hw'.2.1],hw'.2.2⟩⟩
  have hUtarget : U⊆e.target := fun w hw'=>(hrect (upper_full hw')).1
  have hUD : ∀w∈U,e.symm w∈D := by
    intro w hw'
    have hs : e.symm w∈D ↔ 0<w.im := interior_subset ((hrect (upper_full hw')).2.1)
    exact hs.mpr hw'.2.1
  have hfnorm (y:ℂ) (hy:y∈D) : ‖f y‖<1 := by
    rw [hf ⟨y,hy⟩]
    simpa only [UnitDisk,mem_ball,dist_zero_right] using (disk ⟨y,hy⟩).property
  let g:ℂ→ℂ := fun w=>f (e.symm w)
  have hg:DifferentiableOn ℂ g U := by
    intro w hw'
    exact ((hfa _ (hUD w hw')).comp (hia _ (hUtarget hw'))).differentiableAt.differentiableWithinAt
  have hlo : ∀w∈U,(1/2:ℝ)≤‖g w‖ := by
    intro w hw'
    have ht : e.symm w∈D → (1/2:ℝ)<‖f (e.symm w)‖ :=
      interior_subset ((hrect (upper_full hw')).2.2)
    exact (ht (hUD w hw')).le
  have hhi : ∀w∈U,‖g w‖≤1 := fun w hw'=>(hfnorm _ (hUD w hw')).le
  have hmod : ∀y∈Ioo (x-r) (x+r),Tendsto (fun w=>‖g w‖) (𝓝[U] (y:ℂ)) (𝓝 1) := by
    intro y hy
    have hyW:(y:ℂ)∈W := by
      change (y:ℂ).re∈Ioo (x-r) (x+r) ∧ (y:ℂ).im∈Ioo (-r) r
      simpa using And.intro hy (And.intro (neg_lt_zero.mpr hr) hr)
    have hyV:=hrect hyW
    have hyhalf:∀ᶠw in 𝓝 (y:ℂ),e.symm w∈D ↔ 0<w.im :=
      mem_of_superset (isOpen_interior.mem_nhds hyV.2.1) interior_subset
    have hyfront:=chart_seam_frontier D hD e hyV.1 (by simp) hyhalf
    have hto:Tendsto e.symm (𝓝[U] (y:ℂ)) (𝓝[D] (e.symm (y:ℂ))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(e.continuousAt_symm hyV.1).tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      exact self_mem_nhdsWithin.mono (fun w hw'=>hUD w hw')
    exact (boundary_norm_tendsto_one D hD disk f hf _ hyfront).comp hto
  obtain ⟨G,hG,hag,hlower⟩ := ModulusSchwarzExtension318.extension_of_modulus
    g hab hr hg hlo hhi hmod
  have hxW:(x:ℂ)∈W := by
    change (x:ℂ).re∈Ioo (x-r) (x+r) ∧ (x:ℂ).im∈Ioo (-r) r
    simpa using And.intro hxmid (And.intro (neg_lt_zero.mpr hr) hr)
  have heW:e z∈W := by simpa only [hx] using hxW
  have hGA:AnalyticAt ℂ G (e z) :=
    hG.analyticOnNhd (openRectangle_open _ _ _ _) _ heW
  refine ⟨fun y=>G (e y),hGA.comp (hea z hz),?_,?_,?_⟩
  · have hnearW : ∀ᶠy in 𝓝 z,e y∈W :=
      (e.continuousAt hz).eventually ((openRectangle_open _ _ _ _).mem_nhds heW)
    have hnearHalf := (e.continuousAt hz).tendsto.eventually hhalf
    filter_upwards [nhdsWithin_le_nhds hnearW,nhdsWithin_le_nhds hnearHalf,
      nhdsWithin_le_nhds (e.open_source.mem_nhds hz),self_mem_nhdsWithin] with y hyW hyHalf hyS hyD
    have hiy:0<(e y).im := hyHalf.mp (by simpa only [e.left_inv hyS] using hyD)
    have hyU:e y∈U := ⟨hyW.1,⟨hiy,hyW.2.2⟩⟩
    change G (e y)=f y
    rw [hag _ hyU]
    change f (e.symm (e y))=f y
    rw [e.left_inv hyS]
  · rw [hx]
    exact ModulusSchwarzExtension318.seam_norm_one g G hr hG hag hmod hxmid
  · have hnearW : ∀ᶠy in 𝓝 z,e y∈W :=
      (e.continuousAt hz).eventually ((openRectangle_open _ _ _ _).mem_nhds heW)
    filter_upwards [hnearW] with y hyW hyNeg
    have hyL:e y∈openRectangle (x-r) (x+r) (-r) 0 :=
      ⟨hyW.1,⟨hyW.2.1,hyNeg⟩⟩
    exact hlower (e y) hyL
end LocalConformalReflectedExtension318
