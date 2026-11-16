module
public import PELOriginalWholeCharacterOrders318
public import ThreeBranchLegendreAffineIso318
public import PELOriginalOrderedLegendreInvariants318
public section
noncomputable section
namespace PELOriginalOrderedCharacterSchemeMaps318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalActualCharacterFields318
open PELOriginalWholeCharacterOrders318

@[expose] def branch (i:Fin 4) (j:Fin 3):ℂ:=
  branches (SourceTwistArithmetic318.complement i j)
lemma branch_injective (i:Fin 4):Function.Injective (branch i):=by
  apply branches_injective.comp
  fin_cases i <;> decide
lemma first_difference (i:Fin 4):branch i 1≠branch i 0:=
  (branch_injective i).ne (by decide)

/-- The coordinate change uses the SAME ordered parameter appearing in
original character invariants, not a permutation-equivalent j parameter. -/
lemma parameter_eq (i:Fin 4):
    ThreeBranchLegendrePolynomial318.parameter (branch i 0) (branch i 1) (branch i 2)=
      PELOriginalOrderedCharacterCoordinate318.parameter i:=by
  rw [PELOriginalOrderedCharacterCoordinate318.parameter_formula]
  fin_cases i <;>
    simp [ThreeBranchLegendrePolynomial318.parameter,branch,
      PELOriginalCommonContactBase318.branches,SourceTwistArithmetic318.complement]

lemma polynomial_eq (i:Fin 4):
    FourRootCharacterPolynomialOrder318.radicand branches (omitted i)=
      ThreeBranchLegendrePolynomial318.cubic (branch i 0) (branch i 1) (branch i 2):=by
  rw [cubic_equation]
  simp [Fin.prod_univ_succ,ThreeBranchLegendrePolynomial318.cubic,branch]
  <;> ring

/-- Actual whole cubic character rings are isomorphic to the exact affine
models whose invariants are consumed by the original four-row solver. -/
@[expose] def coordinateEquiv (i:Fin 4):Cubic i≃ₐ[ℂ]
    ShortAffineJacobian318.Ring
      (NormalizedLegendreProjectiveModel318.A (PELOriginalOrderedCharacterCoordinate318.parameter i))
      (NormalizedLegendreProjectiveModel318.B (PELOriginalOrderedCharacterCoordinate318.parameter i)):=by
  let e: Cubic i≃ₐ[ℂ]ThreeBranchLegendreAffineIso318.Cubic (branch i 0) (branch i 1) (branch i 2):=
    (ContactGenericFiber318.rootParameterEquiv (polynomial_eq i)).restrictScalars ℂ
  simpa only [parameter_eq] using e.trans
    (ThreeBranchLegendreAffineIso318.coordinateEquiv _ _ _ (first_difference i))

@[expose] def mapOnRings (i:Fin 4):
    ShortAffineJacobian318.Ring
      (NormalizedLegendreProjectiveModel318.A (PELOriginalOrderedCharacterCoordinate318.parameter i))
      (NormalizedLegendreProjectiveModel318.B (PELOriginalOrderedCharacterCoordinate318.parameter i))→ₐ[ℂ]
    FourRootAffineCoordinateRing318.Ring branches:=
  (FourRootCharacterAffineScheme318.coordinateMap branches branches_injective
    (omitted i) (omitted_nonempty i)).comp (coordinateEquiv i).symm.toAlgHom

lemma injective (i:Fin 4):Function.Injective (mapOnRings i):=
  (FourRootCharacterWholeAffineMap318.injective branches branches_injective _ _).comp
    (coordinateEquiv i).symm.injective
lemma finite_ring (i:Fin 4):(mapOnRings i).toRingHom.Finite:=
  (FourRootCharacterWholeAffineMap318.finite branches branches_injective _ _).comp
    (RingHom.Finite.of_surjective _ (coordinateEquiv i).symm.surjective)

/-- A genuine finite scheme morphism from the ENTIRE original finite
contact chart to its correctly ordered independent Legendre chart. -/
@[expose] def morphism (i:Fin 4):FourRootGluedScheme318.finiteScheme branches⟶
    ShortAffineScheme318.scheme
      (NormalizedLegendreProjectiveModel318.A (PELOriginalOrderedCharacterCoordinate318.parameter i))
      (NormalizedLegendreProjectiveModel318.B (PELOriginalOrderedCharacterCoordinate318.parameter i)):=
  Spec.map (CommRingCat.ofHom (mapOnRings i).toRingHom)
theorem finite (i:Fin 4):IsFinite (morphism i):=
  (IsFinite.SpecMap_iff _).mpr (finite_ring i)
lemma over_complex (i:Fin 4):morphism i≫
    ShortAffineScheme318.structureMap
      (NormalizedLegendreProjectiveModel318.A (PELOriginalOrderedCharacterCoordinate318.parameter i))
      (NormalizedLegendreProjectiveModel318.B (PELOriginalOrderedCharacterCoordinate318.parameter i))=
    FourRootGluedScheme318.finiteBase branches:=by
  rw [morphism,ShortAffineScheme318.structureMap,FourRootGluedScheme318.finiteBase,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (mapOnRings i).commutes z
end PELOriginalOrderedCharacterSchemeMaps318
