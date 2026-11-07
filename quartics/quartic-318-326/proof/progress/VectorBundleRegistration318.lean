module
public import FiberLinearStructure318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 DependentFiberBundle318
open FiberLinearStructure318 Filter Topology Bundle
namespace VectorBundleRegistration318
set_option maxHeartbeats 0

/-- For rank-one complex fibers, actual joint chart continuity gives operator-norm
continuity of the linear coordinate changes. -/
theorem rank_one_coordChange_continuous {B:Type*} [TopologicalSpace B]
    {E:B→Type*} [∀b,AddCommMonoid (E b)] [∀b,Module ℂ (E b)]
    [TopologicalSpace (Bundle.TotalSpace ℂ E)]
    (e e':Trivialization ℂ (Bundle.TotalSpace.proj (F:=ℂ) (E:=E)))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] :
    ContinuousOn (fun b=>e.coordChangeL ℂ e' b : B→ℂ→L[ℂ]ℂ)
      (e.baseSet∩e'.baseSet) := by
  have hc:ContinuousOn (fun b=>(e' (e.toOpenPartialHomeomorph.symm (b,1))).2)
      (e.baseSet∩e'.baseSet) := by
    apply ContinuousOn.snd
    apply e'.continuousOn.comp (e.continuousOn_symm_prodMk_left.mono Set.inter_subset_left)
    intro b hb
    apply e'.mem_source.mpr
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
  have hd:=((ContinuousLinearMap.smulRightL ℂ ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)).continuous.comp_continuousOn hc
  apply hd.congr
  intro b hb
  apply ContinuousLinearMap.ext
  intro z
  change e.coordChangeL ℂ e' b z=z * (e' (e.toOpenPartialHomeomorph.symm (b,1))).2
  rw [←e.coordChangeL_apply' (R:=ℂ) e' hb 1]
  have hh: e.coordChangeL ℂ e' b (z • (1:ℂ))=z • e.coordChangeL ℂ e' b 1 := map_smul _ z 1
  simpa only [smul_eq_mul,mul_one] using hh

instance dependentFiberBundle (N:ℕ) [hN:Fact (5≤N)] : FiberBundle ℂ (fibers N) :=
  DependentFiberBundle318.fiberBundle N hN.out

instance chart_mem_atlas (N:ℕ) [hN:Fact (5≤N)] (a:UpperHalfPlane) :
    MemTrivializationAtlas (dependentTrivialization N hN.out a) := ⟨⟨a,rfl⟩⟩

/-- The actual quotient differential fibers form a genuine complex line bundle. -/
instance vectorBundle (N:ℕ) [hN:Fact (5≤N)] : VectorBundle ℂ ℂ (fibers N) where
  trivialization_linear' e he := by
    obtain ⟨a,rfl⟩:=he.out
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨a,rfl⟩:=he.out
    obtain ⟨c,rfl⟩:=he'.out
    exact rank_one_coordChange_continuous _ _

end VectorBundleRegistration318
