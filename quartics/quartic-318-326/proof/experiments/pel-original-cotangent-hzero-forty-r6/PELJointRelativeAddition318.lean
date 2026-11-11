module
public import PELArithmeticInversion318
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public section
noncomputable section
namespace PELJointRelativeAddition318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELComplexPeriodSurface318 PELHolomorphicFamilyProjection318 PELOriginalHolomorphicFibers318
open PELArithmeticZeroSection318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000

/-- Its intended domain is the actual same-base fiber product. No
holomorphy claim is made for arbitrary pairs with different parameters. -/
@[expose] def relativeAdd (p q : Total) : Total := (p.1,p.2+q.2)
@[expose] def sumCoordinates (z w : Ambient) : Ambient := (z.1,z.2+w.2)

@[expose] def sumLinear : Ambient × Ambient →ₗ[ℂ] Ambient where
  toFun p := sumCoordinates p.1 p.2
  map_add' p q := by
    apply Prod.ext rfl
    change (p.1.2+q.1.2)+(p.2.2+q.2.2)=(p.1.2+p.2.2)+(q.1.2+q.2.2)
    abel
  map_smul' c p := by
    apply Prod.ext rfl
    change c • p.1.2+c • p.2.2=c • (p.1.2+p.2.2)
    exact (smul_add c p.1.2 p.2.2).symm

theorem projection_add (τ : HalfPlane) (z w : ComplexVectors) :
    relativeAdd (familyProjection (τ,z)) (familyProjection (τ,w))=
      familyProjection (τ,z+w) := by
  rw [projection_fiber,projection_fiber,projection_fiber]
  change (τ,fiberEquiv τ (QuotientAddGroup.mk' (Periods τ) z)+
    fiberEquiv τ (QuotientAddGroup.mk' (Periods τ) w))=
    (τ,fiberEquiv τ (QuotientAddGroup.mk' (Periods τ) (z+w)))
  rw [map_add,map_add]

theorem projection_add_same_base (a b : Cover) (hab : a.1=b.1) :
    relativeAdd (familyProjection a) (familyProjection b)=
      familyProjection (a.1,a.2+b.2) := by
  rcases a with ⟨τ,z⟩
  rcases b with ⟨σ,w⟩
  change τ=σ at hab
  subst σ
  exact projection_add τ z w

theorem inverse_projection (a : Cover) (p : Total) (hp : p∈(familyChart a).source) :
    familyProjection (inverseChart a p)=p := by
  have h := (inverseChart a).left_inv ((familyChart_source a p).mp hp)
  rwa [inverseChart_symm] at h

/-- On every full same-base chart intersection, addition is literally
addition of the original period coordinates before the same quotient map. -/
theorem chart_add_square (a b c : Cover) (p q : Total) (hbase : p.1=q.1)
    (hp : p∈(familyChart a).source) (hq : q∈(familyChart b).source) :
    relativeAdd p q=(familyChart c).symm
      (sumCoordinates (familyChart a p) (familyChart b q)) := by
  let u := inverseChart a p
  let v := inverseChart b q
  have hu : familyProjection u=p := inverse_projection a p hp
  have hv : familyProjection v=q := inverse_projection b q hq
  have huv : u.1=v.1 := by
    calc
      _ = p.1 := congrArg Prod.fst hu
      _ = q.1 := hbase
      _ = v.1 := (congrArg Prod.fst hv).symm
  have hc : (familyChart c).symm
      (sumCoordinates (familyChart a p) (familyChart b q))=
        familyProjection (u.1,u.2+v.2) := by
    rw [familyChart_symm]
    apply congrArg familyProjection
    change ambientChart.symm (ambientChart (u.1,u.2+v.2))=(u.1,u.2+v.2)
    exact ambientChart.left_inv (ambientChart_source _)
  rw [hc,←hu,←hv]
  exact projection_add_same_base u v huv

local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

/-- Full joint holomorphy on the relative fiber product, expressed by its
universal test-map criterion: ANY two holomorphic maps with identical base
have a holomorphic original sum. This does not choose a fiber-product atlas. -/
theorem relativeAdd_holomorphicAt {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ,E) ω N]
    (f g : N → Total) (x : N) (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω f x)
    (hg : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω g x)
    (hbase : ∀ᶠ y in 𝓝 x,(f y).1=(g y).1) :
    ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω (fun y => relativeAdd (f y) (g y)) x := by
  obtain ⟨a,ha⟩ := familyProjection_surjective (f x)
  obtain ⟨b,hb⟩ := familyProjection_surjective (g x)
  have hfa : f x∈(familyChart a).source := ha ▸ familyChart_center a
  have hgb : g x∈(familyChart b).source := hb ▸ familyChart_center b
  have hfc := (contMDiffAt_of_mem_maximalAtlas (familyChart_maximal a) hfa).comp x hf
  have hgc := (contMDiffAt_of_mem_maximalAtlas (familyChart_maximal b) hgb).comp x hg
  let H : N → Ambient := fun y => sumCoordinates (familyChart a (f y)) (familyChart b (g y))
  have hH : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω H x := by
    have hs : ContMDiffAt 𝓘(ℂ,Ambient × Ambient) 𝓘(ℂ,Ambient) ω sumLinear
        (familyChart a (f x),familyChart b (g x)) :=
      contMDiffAt_iff_contDiffAt.mpr sumLinear.toContinuousLinearMap.contDiff.contDiffAt
    exact hs.comp x (hfc.prodMk_space hgc)
  let c : Cover := (a.1,a.2+b.2)
  have hHx : H x=ambient c := by
    change sumCoordinates (familyChart a (f x)) (familyChart b (g x))=ambient c
    rw [←ha,←hb,familyChart_at_center,familyChart_at_center]
    all_goals rfl
  have ht : H x∈(familyChart c).target := by
    rw [hHx]
    have h := (familyChart c).map_source (familyChart_center c)
    rwa [familyChart_at_center] at h
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (familyChart_maximal c) ht
  apply (hi.comp x hH).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually ((familyChart a).open_source.mem_nhds hfa),
    hg.continuousAt.eventually ((familyChart b).open_source.mem_nhds hgb),hbase] with y hyf hyg hybase
  exact chart_add_square a b c (f y) (g y) hybase hyf hyg
/-- In particular, addition preserves every pair of holomorphic test maps
into the actual same-base fiber product. -/
theorem relativeAdd_holomorphic {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ,E) ω N]
    (f g : N → Total) (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω f)
    (hg : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω g) (hbase : ∀ x,(f x).1=(g x).1) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω (fun x => relativeAdd (f x) (g x)) :=
  fun x => relativeAdd_holomorphicAt f g x (hf x) (hg x) (Filter.Eventually.of_forall hbase)
end PELJointRelativeAddition318
