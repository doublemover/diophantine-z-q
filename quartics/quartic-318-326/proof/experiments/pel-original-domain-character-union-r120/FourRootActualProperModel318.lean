module
public import FourRootProjectiveFiniteDescent318
public import FourRootWholeSchemeGeometry318
public import FourRootProjectivePointComparison318
public import FourRootCenteredFiniteBase318
public import FourRootSquaredInfinityBase318
public section
noncomputable section
namespace FourRootActualProperModel318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootCoordinateOverlap318 FourRootProjectiveProjection318
variable (b:Fin 4→ℂ)

/-- The actual centered finite base action, not an unrelated canonical
polynomial scalar structure, supplies finiteness of the exact ring map. -/
theorem finite_base:(finiteCoordinate b).toRingHom.Finite:=by
  letI:Algebra (Polynomial ℂ) (Affine b):=(finiteCoordinate b).toAlgebra
  exact RingHom.finite_algebraMap.mpr (FourRootCenteredFiniteBase318.finite_free b).1
/-- The actual reciprocal base v=u² has rank16, not the rank8 of the
intermediate u-base. Its exact scalar map is consumed here. -/
theorem infinity_base:(infinityCoordinate b).toRingHom.Finite:=by
  letI:Algebra (Polynomial ℂ) (Infinity b):=(infinityCoordinate b).toAlgebra
  exact RingHom.finite_algebraMap.mpr (FourRootSquaredInfinityBase318.finite_free b).1

theorem projection_finite:IsFinite (FourRootProjectiveProjection318.projection b):=
  FourRootProjectiveFiniteDescent318.projection_finite b (finite_base b) (infinity_base b)
theorem proper:IsProper (structureMap b):=
  FourRootProjectiveFiniteDescent318.structure_proper b (finite_base b) (infinity_base b)

/-- The SAME independently glued contact Scheme is a genuine smooth,
proper, integral complex model, normal at every actual stalk and finite
over the exact marked projective base. All premises except distinct
branch values have been constructed internally. -/
theorem model (hb:Function.Injective b):
    IsIntegral (scheme b) ∧ Smooth (structureMap b) ∧ IsProper (structureMap b) ∧
      IsFinite (FourRootProjectiveProjection318.projection b) ∧
        ∀p:scheme b,IsIntegrallyClosed ((scheme b).presheaf.stalk p):=
  ⟨FourRootWholeSchemeGeometry318.integral b hb,
    FourRootWholeSchemeGeometry318.smooth b hb,proper b,projection_finite b,
    FourRootWholeSchemeGeometry318.normal_stalk b hb⟩

/-- This exact model carries the already constructed whole original
source comparison and original deck action; numerical λ,μ remain separate. -/
theorem actual_original_model:
    IsIntegral (scheme PELOriginalCommonContactBase318.branches) ∧
      Smooth (structureMap PELOriginalCommonContactBase318.branches) ∧
      IsProper (structureMap PELOriginalCommonContactBase318.branches) ∧
      IsFinite (FourRootProjectiveProjection318.projection PELOriginalCommonContactBase318.branches) ∧
      ∀p:scheme PELOriginalCommonContactBase318.branches,
        IsIntegrallyClosed ((scheme PELOriginalCommonContactBase318.branches).presheaf.stalk p):=
  model _ PELOriginalCommonContactBase318.branches_injective
end FourRootActualProperModel318
