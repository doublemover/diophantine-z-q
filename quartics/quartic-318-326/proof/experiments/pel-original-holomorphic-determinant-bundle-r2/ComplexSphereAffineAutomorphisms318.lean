module
public import ComplexCurveHomeomorphInverse318
public import ComplexCurveRemovablePoints318
public section
noncomputable section
namespace ComplexSphereAffineAutomorphisms318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ComplexSphereCharts318 SphereInversion318
set_option maxHeartbeats 2800000
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

@[expose] def complexAffine (a b:ℂ) (ha:a≠0) : ℂ≃ₜℂ where
  toFun z:=a*z+b
  invFun w:=(w-b)/a
  left_inv z:=by field_simp [ha];ring
  right_inv w:=by field_simp [ha];ring
  continuous_toFun:=by fun_prop
  continuous_invFun:=by fun_prop

@[expose] def affineSphere (a b:ℂ) (ha:a≠0) : OnePoint ℂ≃ₜOnePoint ℂ :=
  (complexAffine a b ha).onePointCongr

theorem affineSphere_coe (a b:ℂ) (ha:a≠0) (z:ℂ) :
    affineSphere a b ha (z:OnePoint ℂ)=(a*z+b:ℂ) := rfl

theorem affineSphere_infty (a b:ℂ) (ha:a≠0) : affineSphere a b ha ∞=∞ := rfl

theorem coe_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω ((↑):ℂ→OnePoint ℂ) := by
  intro z
  exact contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩))
    (by rw [affine_target];exact mem_univ z)

/-- Holomorphy in the actual finite source chart, without changing the
standard sphere complex structure. -/
theorem of_affine_pullback (F:OnePoint ℂ→OnePoint ℂ) (z:ℂ)
    (h:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w:ℂ=>F (w:OnePoint ℂ)) z) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (z:OnePoint ℂ) := by
  have hA:=contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩))
    (affine_mem z)
  have h':ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w:ℂ=>F (w:OnePoint ℂ)) (affine (z:OnePoint ℂ)) := by rw [affine_coe];exact h
  apply (h'.comp (z:OnePoint ℂ) hA).congr_of_eventuallyEq
  filter_upwards [affine.open_source.mem_nhds (affine_mem z)] with q hq
  exact congrArg F (affine.left_inv hq).symm

theorem affineSphere_holomorphic (a b:ℂ) (ha:a≠0) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (affineSphere a b ha) := by
  apply ComplexCurveRemovablePoints318.holomorphic_of_finite_exception
    _ (affineSphere a b ha).continuous {∞} (Set.finite_singleton _)
  intro p hp
  induction p using OnePoint.rec with
  | infty => exact False.elim (hp (mem_singleton _))
  | coe z =>
    apply of_affine_pullback _ z
    exact (coe_holomorphic (a*z+b)).comp z
      (contMDiffAt_iff_contDiffAt.mpr ((analyticAt_const.mul analyticAt_id).add analyticAt_const).contDiffAt)

/-- Standard inversion is holomorphic including zero and infinity. The
existing genuine homeomorphism supplies continuity at both points and
actual complex removable-singularity theorems finish the finite exceptions. -/
theorem inversion_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω inversionHomeomorph := by
  apply ComplexCurveRemovablePoints318.holomorphic_of_finite_exception
    _ inversionHomeomorph.continuous ({∞,(0:ℂ)}:Set (OnePoint ℂ)) (by simp)
  intro p hp
  induction p using OnePoint.rec with
  | infty => exact False.elim (hp (by simp))
  | coe z =>
    have hz:z≠0 := by intro he;subst z;exact hp (by simp)
    apply of_affine_pullback _ z
    have h:(ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w:ℂ=>(w⁻¹:OnePoint ℂ)) z) :=
      (coe_holomorphic z⁻¹).comp z
        (contMDiffAt_iff_contDiffAt.mpr (analyticAt_id.inv hz).contDiffAt)
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact inversion_coe hw
end ComplexSphereAffineAutomorphisms318
