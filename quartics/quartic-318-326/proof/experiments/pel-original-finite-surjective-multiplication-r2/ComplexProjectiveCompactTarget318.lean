module
public import ComplexProjectiveHermitianProjector318
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Compactness.Compact
public section
noncomputable section
namespace ComplexProjectiveCompactTarget318
open Set Topology Metric
open ComplexProjectiveQuotientTopology318
variable (ι:Type*) [Fintype ι]
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι
local instance projectiveHausdorff:T2Space (Space ι):=
  ComplexProjectiveHermitianProjector318.hausdorff ι
abbrev UnitSphere:=sphere (0:V ι) 1
lemma sphere_nonzero(v:UnitSphere ι):v.val≠0:=by
  have hn:‖v.val‖=1:=by simpa only [mem_sphere,dist_zero_right] using v.property
  intro hz
  rw [hz,norm_zero] at hn
  exact zero_ne_one hn
@[expose] def sphereProjection(v:UnitSphere ι):Space ι:=
  Projectivization.mk ℂ v.val (sphere_nonzero ι v)
lemma sphereProjection_continuous:Continuous (sphereProjection ι):=
  continuous_mk ι Subtype.val continuous_subtype_val (sphere_nonzero ι)

/-- Every actual projective line has a unit-norm representative. This
normalizes a representative only to prove surjectivity; no continuous
choice of representative or new projective topology is assumed. -/
lemma sphereProjection_surjective:Function.Surjective (sphereProjection ι):=by
  intro p
  let v:V ι:=Projectivization.rep p
  have hv:v≠0:=Projectivization.rep_nonzero p
  have hn:0<‖v‖:=norm_pos_iff.mpr hv
  let a:ℂ:=(‖v‖⁻¹:ℝ)
  have ha:a≠0:=Complex.ofReal_ne_zero.mpr (inv_ne_zero (ne_of_gt hn))
  have hunit:‖a • v‖=1:=by
    rw [norm_smul]
    dsimp only [a]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ (ne_of_gt hn)]
  let s:UnitSphere ι:=⟨a • v,by simpa only [mem_sphere,dist_zero_right] using hunit⟩
  refine ⟨s,?_⟩
  have he:Projectivization.mk ℂ (a • v) (sphere_nonzero ι s)=
      Projectivization.mk ℂ v hv:=by
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a,rfl⟩
  exact he.trans (Projectivization.mk_rep p)

theorem compact:CompactSpace (Space ι):=
  Function.Surjective.compactSpace (sphereProjection_continuous ι)
    (sphereProjection_surjective ι)
local instance projectiveCompact:CompactSpace (Space ι):=compact ι

/-- The actual independent target is identified with its compact closed
rank-one-projector image. This does NOT assert that any theta map is
injective, an immersion, or a projective embedding. -/
theorem projector_closedEmbedding:
    IsClosedEmbedding (ComplexProjectiveHermitianProjector318.projector ι):=
  (ComplexProjectiveHermitianProjector318.continuous_projector ι).isClosedEmbedding
    (ComplexProjectiveHermitianProjector318.projector_injective ι)
theorem projector_image_compact:
    IsCompact (Set.range (ComplexProjectiveHermitianProjector318.projector ι)):=
  isCompact_range (ComplexProjectiveHermitianProjector318.continuous_projector ι)
end ComplexProjectiveCompactTarget318
