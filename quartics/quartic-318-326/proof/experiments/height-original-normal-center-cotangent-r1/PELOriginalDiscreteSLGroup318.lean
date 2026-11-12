module
public import PELPrincipalThreeFreeAction318
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public section
noncomputable section
namespace PELOriginalDiscreteSLGroup318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicUnitPeriodTransport318
open QuaternionicJointPeriodTopology318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPrincipalThreeFreeAction318 PELComplexPeriodSurface318
open scoped MatrixGroups
set_option maxHeartbeats 1400000

/-- Faithful image of the ORIGINAL principal-three units in the standard
real special linear group; no abstract discrete subgroup is supplied. -/
@[expose] def specialLinear : principalThree →* SL(2,ℝ) where
  toFun u := ⟨unitMatrix representation order u.val,determinant u⟩
  map_one' := by apply Subtype.ext; simp [unitMatrix]
  map_mul' u v := by
    apply Subtype.ext
    exact QuaternionicPeriodAutomorphy318.unitMatrix_mul representation order u.val v.val

theorem specialLinear_injective : Function.Injective specialLinear := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact representation_injective (congrArg (fun M : SL(2,ℝ) => M.val) h)

@[expose] def imageGroup : Subgroup SL(2,ℝ) := specialLinear.range
@[expose] def intoImage : principalThree →* imageGroup := specialLinear.rangeRestrict

theorem intoImage_injective : Function.Injective intoImage := by
  intro u v h
  exact specialLinear_injective (congrArg Subtype.val h)

theorem intoImage_surjective : Function.Surjective intoImage := by
  rintro ⟨g,u,hu⟩
  exact ⟨u,Subtype.ext hu⟩

@[expose] def imageEquiv : principalThree ≃* imageGroup :=
  MulEquiv.ofBijective intoImage ⟨intoImage_injective,intoImage_surjective⟩

local instance : DiscreteTopology (Periods basePoint) :=
  PELOriginalPeriodLattice318.original_discrete basePoint basePoint.property

@[expose] def periodGauge (g : imageGroup) : Periods basePoint :=
  ⟨fixedPeriod g.val.val,by
    obtain ⟨u,hu⟩ := g.property
    change period (basePoint:ℂ) g.val.val∈Periods basePoint
    rw [←hu]
    exact ⟨((u.val:order):PELQuaternionAlgebra318.B),(u.val:order).property,rfl⟩⟩

theorem periodGauge_continuous : Continuous periodGauge :=
  (fixedPeriod.toLinearMap.toContinuousLinearMap.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem periodGauge_injective : Function.Injective periodGauge := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact fixedPeriod.injective (congrArg Subtype.val he)

/-- Discreteness is deduced from the SAME original order period lattice,
not assumed as an arithmetic-group property. -/
instance imageGroup_discrete : DiscreteTopology imageGroup :=
  DiscreteTopology.of_continuous_injective periodGauge_continuous periodGauge_injective

/-- The pinned upper-half-plane proper-action theorem now applies to this
concrete image subgroup with all of its hypotheses constructed. -/
instance imageGroup_proper : ProperlyDiscontinuousSMul imageGroup UpperHalfPlane := inferInstance
end PELOriginalDiscreteSLGroup318
