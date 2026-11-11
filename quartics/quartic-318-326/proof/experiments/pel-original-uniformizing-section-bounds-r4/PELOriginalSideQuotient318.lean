module
public import PELActualPolygonHomeomorph318
public import PELOriginalBaseCompact318
public import Mathlib.Logic.Relation
public section
noncomputable section
namespace PELOriginalSideQuotient318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELDirichletOriginalUnits318
open PELOriginalDirichletPolygon318 PELActualPolygonHomeomorph318
open PELUnlevelledComplexBase318 PELOriginalBaseCompact318
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ HalfPlane := PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- Height ties are exactly the original rational side equations in the
scaled Klein coordinates; the boundary relation retains the actual unit. -/
theorem side_height_iff (j : Fin 8) (ε δ : Bool) (τ : HalfPlane) :
    height (testUnit j ε δ • τ)=height τ ↔
      (rowFirst j:ℝ)*((sign ε:ℝ)*scaledFirst τ)+
      (rowSecond j:ℝ)*((sign δ:ℝ)*scaledSecond τ)=(rowConstant j:ℝ) := by
  have h := original_energy j ε δ τ
  constructor
  · intro he
    rw [he] at h
    simp only [sub_self,mul_zero,zero_div] at h
    linarith
  · intro he
    have hz : (rowConstant j:ℝ)-(rowFirst j:ℝ)*(sign ε:ℝ)*scaledFirst τ-
        (rowSecond j:ℝ)*(sign δ:ℝ)*scaledSecond τ=0 := by linarith
    rw [hz] at h
    have hm := (div_eq_iff (height_pos τ).ne').mp h
    nlinarith

/-- Only actual side moves are imposed: both endpoints lie in the literal
polygon and the ORIGINAL unit preserves the height there. This relation is
not defined by equality in the final arithmetic quotient. -/
@[expose] def sideRelation (x y : originalDomain) : Prop :=
  ∃ (j : Fin 8) (ε δ : Bool),y.val=testUnit j ε δ • x.val ∧ height y.val=height x.val
@[expose] def sideSetoid : Setoid originalDomain := Relation.EqvGen.setoid sideRelation
abbrev PairedPolygon := Quotient sideSetoid
@[expose] def polygonProjection : originalDomain → PairedPolygon := Quotient.mk _

theorem side_projection_eq (x y : originalDomain) (h : sideRelation x y) :
    projection x.val=projection y.val := by
  obtain ⟨j,ε,δ,hy,_⟩ := h
  rw [hy]
  exact (projection_unit (testUnit j ε δ) x.val).symm

theorem generated_projection_eq (x y : originalDomain) (h : Relation.EqvGen sideRelation x y) :
    projection x.val=projection y.val := by
  induction h with
  | rel x y h => exact side_projection_eq x y h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A genuine continuous comparison from the side-paired compact polygon
onto the unchanged original arithmetic curve. Injectivity/local covering,
vertex fans and a fundamental-polygon theorem are NOT assumed here. -/
@[expose] def arithmeticComparison : PairedPolygon → UnlevelledBase :=
  Quotient.lift (fun x : originalDomain => projection x.val) generated_projection_eq

theorem comparison_square (x : originalDomain) :
    arithmeticComparison (polygonProjection x)=projection x.val := rfl

theorem arithmeticComparison_continuous : Continuous arithmeticComparison :=
  (projection_holomorphic.continuous.comp continuous_subtype_val).quotient_lift generated_projection_eq

theorem arithmeticComparison_surjective : Function.Surjective arithmeticComparison := by
  intro x
  obtain ⟨τ,rfl⟩ := projection_surjective x
  obtain ⟨u,hu⟩ := original_polygon_reduction τ
  exact ⟨polygonProjection ⟨u • τ,hu⟩,projection_unit u τ⟩

instance pairedPolygonCompact : CompactSpace PairedPolygon := by
  apply isCompact_univ_iff.mp
  have hs : Function.Surjective polygonProjection := Quotient.mk_surjective
  rw [← Set.range_eq_univ.mpr hs,← Set.image_univ]
  exact isCompact_univ.image continuous_quot_mk

/-- The actual comparison is proper because its source is genuinely compact
and the original arithmetic target is Hausdorff. This does not promote it
to a homeomorphism or a finite covering. -/
theorem arithmeticComparison_proper : IsProperMap arithmeticComparison := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨arithmeticComparison_continuous,?_,?_⟩
  · intro S hS
    exact (hS.isCompact.image arithmeticComparison_continuous).isClosed
  · intro y
    exact (isClosed_singleton.preimage arithmeticComparison_continuous).isCompact
end PELOriginalSideQuotient318
