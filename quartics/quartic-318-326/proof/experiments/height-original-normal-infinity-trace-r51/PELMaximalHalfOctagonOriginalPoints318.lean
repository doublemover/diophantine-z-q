module
public import PELMaximalHalfOctagonCoordinates318
public import PELNormalizerOctagonReduction318
public import PELOriginalMaximalQuotient318
public import PELActualOriginalSideGluing318
public section
noncomputable section
namespace PELMaximalHalfOctagonOriginalPoints318
open Set
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELMaximalHalfOctagonCoordinates318 PELNormalizerOctagonAffine318
open PELDirichletOriginalUnits318 PELActualPolygonHomeomorph318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELOriginalVertexStratum318 PELUnlevelledNormalizerAction318
open PELOriginalElementaryAction318 PELNormOneBaseAction318
set_option maxHeartbeats 2400000

/-- The literal half-octagon is contained in the full normalizer octagon. -/
theorem cut_in_octagon (P : ℝ × ℝ) (hP : P∈upperCut) : inequalities P.1 P.2 := by
  obtain ⟨hb0,hb1,ha0,ha1,hs,ht⟩ := hP
  exact ⟨by linarith,hb1,ha0,ha1,by linarith,hs,by linarith,by linarith⟩

/-- Every real point of the new octagon lies in the original norm-one
polygon. This is a full real affine argument, not only a vertex inclusion. -/
theorem octagon_in_original (A B : ℝ) (h : inequalities A B) :
    PELOriginalDirichletPolygon318.inequalities A B := by
  intro j ε δ
  have hh := whole_octagon 0 (-(rowFirst j:ℝ)*(sign ε:ℝ))
    (-(rowSecond j:ℝ)*(sign δ:ℝ)) (rowConstant j:ℝ) A B h (by
      intro v
      fin_cases j <;> cases ε <;> cases δ <;> fin_cases v <;>
        norm_num [rowFirst,rowSecond,rowConstant,sign,PELNormalizerOctagonVertices318.vertex])
  linarith

@[expose] def cutPoint (P : upperCut) : HalfPlane :=
  (polygonInverse ⟨P.val,octagon_in_original _ _ (cut_in_octagon P.val P.property)⟩).val

theorem cutPoint_coordinates (P : upperCut) :
    (scaledFirst (cutPoint P),scaledSecond (cutPoint P))=P.val :=
  Prod.ext (inverse_scaled _).1 (inverse_scaled _).2

theorem cutPoint_continuous : Continuous cutPoint :=
  continuous_subtype_val.comp (continuous_polygonInverse.comp
    (continuous_subtype_val.subtype_mk _))

theorem cutPoint_recovers (τ : HalfPlane) (hτ : (scaledFirst τ,scaledSecond τ)∈upperCut) :
    cutPoint ⟨(scaledFirst τ,scaledSecond τ),hτ⟩=τ :=
  PELActualOriginalSideGluing318.scaled_injective (cutPoint_coordinates _)

/-- The unchanged two-stage arithmetic projection of the actual half-plane. -/
@[expose] def maximalProjection (τ : HalfPlane) : PELOriginalMaximalQuotient318.MaximalBase :=
  PELOriginalMaximalQuotient318.projection (PELUnlevelledComplexBase318.projection τ)

theorem maximalProjection_continuous : Continuous maximalProjection :=
  PELOriginalMaximalQuotient318.projection_continuous.comp
    PELUnlevelledComplexBase318.projection_holomorphic.continuous

theorem maximalProjection_surjective : Function.Surjective maximalProjection :=
  PELOriginalMaximalQuotient318.projection_surjective.comp
    PELUnlevelledComplexBase318.projection_surjective

/-- Exact full-normalizer orbit relation already underlying the ORIGINAL
maximal quotient, retaining the norm-one unit adjustment of a coarse lift. -/
theorem maximalProjection_eq_iff (τ σ : HalfPlane) : maximalProjection τ=maximalProjection σ ↔
    ∃ g : positiveNormalizer,baseAction g σ=τ := by
  rw [maximalProjection,maximalProjection,
    PELOriginalMaximalQuotient318.full_normalizer_orbit_iff]
  constructor
  · rintro ⟨g,hg⟩
    change PELUnlevelledComplexBase318.projection (baseAction g σ)=
      PELUnlevelledComplexBase318.projection τ at hg
    obtain ⟨u,hu⟩ := (projection_eq_iff_unit τ (baseAction g σ)).mp hg.symm
    refine ⟨originalNormalizer u*g,?_⟩
    rw [baseAction_mul,normalizer_action]
    exact hu
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    change PELUnlevelledComplexBase318.projection (baseAction g σ)=
      PELUnlevelledComplexBase318.projection τ
    rw [hg]

theorem maximalProjection_invariant (g : positiveNormalizer) (τ : HalfPlane) :
    maximalProjection (baseAction g τ)=maximalProjection τ :=
  (maximalProjection_eq_iff _ _).mpr ⟨g,rfl⟩

@[expose] def cutProjection : upperCut → PELOriginalMaximalQuotient318.MaximalBase :=
  maximalProjection ∘ cutPoint

theorem cutProjection_continuous : Continuous cutProjection :=
  maximalProjection_continuous.comp cutPoint_continuous

instance cutCompact : CompactSpace upperCut := by
  apply isCompact_univ_iff.mp
  rw [←Set.range_eq_univ.mpr upperCutCenter.symm.surjective,←Set.image_univ]
  exact isCompact_univ.image upperCutCenter.symm.continuous
end PELMaximalHalfOctagonOriginalPoints318
