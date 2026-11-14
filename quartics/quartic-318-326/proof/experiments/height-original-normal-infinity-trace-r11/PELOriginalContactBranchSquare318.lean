module
public import PELOriginalCommonContactBase318
public import PELOriginalMaximalCharts318
public import ComplexCurvePartialInverse318
public section
noncomputable section
namespace PELOriginalContactBranchSquare318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELCoarseInertiaCoordinate318 PELInertiaSquaredCoordinate318
open PELOriginalManuscriptNormalization318 ComplexSphereCharts318
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold
local instance : ChartedSpace ℂ MaximalBase:=PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=PELMaximalComplexAtlas318.maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The SAME original genus-five source and manuscript marked base. -/
@[expose] def normalizedMap : UnlevelledBase→OnePoint ℂ:=
  coordinate ∘ PELOriginalMaximalQuotient318.projection
lemma holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω normalizedMap:=
  biholomorphic.1.comp PELMaximalComplexAtlas318.maximal_projection_holomorphic
lemma continuous : Continuous normalizedMap:=holomorphic.continuous

/-- Actual z² local model at EVERY original ramification point of the
full sixteen-cover, including all eight points over each branch value.
The source is UnlevelledBase, NOT any elliptic character quotient. -/
theorem branch_square (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus) :
    ∃(e:OpenPartialHomeomorph UnlevelledBase ℂ)
      (b:OpenPartialHomeomorph (OnePoint ℂ) ℂ),
      p∈e.source ∧ normalizedMap p∈b.source ∧ e p=0 ∧ b (normalizedMap p)=0 ∧
      (∀x∈e.source,normalizedMap x∈b.source ∧ b (normalizedMap x)=(e x)^2) ∧
      (∀x∈e.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e x) ∧
      (∀z∈e.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm z) ∧
      (∀x∈b.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b x) ∧
      (∀z∈b.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b.symm z) := by
  obtain ⟨j,hj⟩:=(original_locus_union p).mp hp
  obtain ⟨τ,rfl⟩:=PELUnlevelledComplexBase318.projection_surjective p
  obtain ⟨U,b₀,hU,hpU,hbs,hmodel,hbLift⟩:=
    PELMaximalTopologicalAtlas318.exists_branch_chart j τ hj
  let E:=inertiaChart τ
  let e:=E.restrOpen U hU
  let b:OpenPartialHomeomorph (OnePoint ℂ) ℂ:=coordinate.symm.toOpenPartialHomeomorph.trans b₀
  have hpe:PELUnlevelledComplexBase318.projection τ∈e.source:=⟨chart_center_source τ,hpU⟩
  have he0:e (PELUnlevelledComplexBase318.projection τ)=0:=chart_center τ
  have hbOriginal:PELMaximalTopologicalAtlas318.OriginalChart b₀:=⟨U,hU,hbs,hbLift⟩
  have hc (x:UnlevelledBase):coordinate.symm (normalizedMap x)=
      PELOriginalMaximalQuotient318.projection x:=coordinate.symm_apply_apply _
  have hnew:∀x∈e.source,normalizedMap x∈b.source ∧ b (normalizedMap x)=(e x)^2:=by
    intro x hx
    constructor
    · refine ⟨mem_univ _,?_⟩
      change coordinate.symm (normalizedMap x)∈b₀.source
      rw [hc,hbs]
      exact ⟨x,hx.2,rfl⟩
    · change b₀ (coordinate.symm (normalizedMap x))=(e x)^2
      rw [hc,hmodel x hx.2]
      rfl
  have hehol:∀x∈e.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e x:=
    fun x hx=>chart_holomorphic τ x hx.1
  have hbhol:∀x∈b.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b x:=by
    intro x hx
    exact (PELOriginalMaximalCharts318.original_chart_holomorphic b₀ hbOriginal
      (coordinate.symm x) hx.2).comp x (biholomorphic.2 x)
  refine ⟨e,b,hpe,(hnew _ hpe).1,he0,?_,hnew,hehol,?_,hbhol,?_⟩
  · rw [(hnew _ hpe).2,he0,zero_pow (by decide : 2≠0)]
  · intro z hz
    have h:=ComplexCurvePartialInverse318.inverse_at e (e.symm z) (e.map_target hz)
      (hehol _ (e.map_target hz))
    simpa only [e.right_inv hz] using h
  · intro z hz
    have h:=ComplexCurvePartialInverse318.inverse_at b (b.symm z) (b.map_target hz)
      (hbhol _ (b.map_target hz))
    simpa only [b.right_inv hz] using h
end PELOriginalContactBranchSquare318
