module
public import GlobalDifferentialFunctor318
public import InfinityGlobalFormCompatibility318
public import FiniteGlobalFormCompatibility318
public section
noncomputable section
namespace ActualDifferentialTriple318
open AlgebraicGeometry CategoryTheory KaehlerDifferential WeierstrassOverlap318
open DifferentialChartMaps318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

abbrev FI (A B : R) := ActualDifferentialOverlap318.CommonRing A B
abbrev XY (A B : R) := FiniteInvariantDifferential318.CommonRing A B
@[expose] def extraMinor (A B : R) : FI A B :=
  finiteBaseMap A B (ShortAffineJacobian318.presentation A B 0).jacobian
/-- Actual common localization of all three differential charts. -/
abbrev Triple (A B : R) := Localization.Away (extraMinor A B)
@[expose] def fromFI (A B : R) : FI A B →ₐ[R] Triple A B :=
  Algebra.algHom R (FI A B) (Triple A B)
@[expose] def base (A B : R) : Affine A B →ₐ[R] Triple A B :=
  (fromFI A B).comp (finiteBaseMap A B)

theorem base_x_unit (A B : R) :
    IsUnit (base A B (ShortAffineJacobian318.presentation A B 0).jacobian) := by
  exact IsLocalization.Away.algebraMap_isUnit (R:=FI A B) (S:=Triple A B) (extraMinor A B)

theorem base_y_unit (A B : R) :
    IsUnit (base A B (ShortAffineJacobian318.presentation A B 1).jacobian) := by
  change IsUnit (fromFI A B (finiteBaseMap A B _))
  rw [finiteBaseMap_jacobian]
  apply IsUnit.map
  exact IsUnit.of_mul_eq_one_right (ActualDifferentialOverlap318.finiteInverse A B)
    (by rw [mul_comm,ActualDifferentialOverlap318.finite_inverse])

@[expose] def fromXY (A B : R) : XY A B →ₐ[R] Triple A B :=
  IsLocalization.Away.liftAlgHom (S:=XY A B) (P:=Triple A B) (f:=base A B)
    ((ShortAffineJacobian318.presentation A B 0).jacobian *
      (ShortAffineJacobian318.presentation A B 1).jacobian)
    (by rw [map_mul]; exact (base_x_unit A B).mul (base_y_unit A B))

@[simp] theorem fromXY_integral (A B : R) (s : Affine A B) :
    fromXY A B (algebraMap (Affine A B) (XY A B) s)=base A B s := by
  simp [fromXY,IsLocalization.Away.liftAlgHom_apply]

/-- The concrete two routes from the finite y-chart to the triple overlap agree. -/
theorem y_diamond (A B : R) :
    (fromFI A B).comp (finiteChartMap A B)=
      (fromXY A B).comp (FiniteInvariantDifferential318.yMap A B) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (ShortAffineJacobian318.presentation A B 1).jacobian)
  apply AlgHom.ext
  intro s
  change fromFI A B (finiteChartMap A B (algebraMap (Affine A B) (FiniteChart A B) s))=
    fromXY A B (FiniteInvariantDifferential318.yMap A B (algebraMap (Affine A B) (FiniteChart A B) s))
  rw [finiteChartMap_integral]
  simp only [FiniteInvariantDifferential318.yMap,ProductLocalization318.rightMap_integral,
    fromXY_integral,base,AlgHom.comp_apply]

@[expose] def fromX (A B : R) : FiniteInvariantDifferential318.XChart A B →ₐ[R] Triple A B := (fromXY A B).comp (FiniteInvariantDifferential318.xMap A B)
@[expose] def fromY (A B : R) : FiniteChart A B →ₐ[R] Triple A B := (fromFI A B).comp (finiteChartMap A B)
@[expose] def fromInfinity (A B : R) : InfinityChart A B →ₐ[R] Triple A B := (fromFI A B).comp (infinityChartMap A B)

/-- Literal invariant differentials from all three charts agree on their actual common ring. -/
theorem triple_forms (A B : R) :
    AlgHomDifferential318.map (T:=Triple A B) (fromX A B) (FiniteInvariantDifferential318.xForm A B)=
      AlgHomDifferential318.map (T:=Triple A B) (fromY A B) (InvariantChartForms318.finite A B) ∧
    AlgHomDifferential318.map (T:=Triple A B) (fromY A B) (InvariantChartForms318.finite A B)=
      AlgHomDifferential318.map (T:=Triple A B) (fromInfinity A B) (InvariantChartForms318.infinity A B) := by
  constructor
  · rw [fromX,fromY,y_diamond,DifferentialFunctor318.map_comp_apply,DifferentialFunctor318.map_comp_apply]
    exact congrArg (AlgHomDifferential318.map (T:=Triple A B) (fromXY A B))
      (FiniteInvariantDifferential318.invariant_overlap A B).symm
  · rw [fromY,fromInfinity,DifferentialFunctor318.map_comp_apply,DifferentialFunctor318.map_comp_apply]
    exact congrArg (AlgHomDifferential318.map (T:=Triple A B) (fromFI A B))
      (InvariantChartForms318.invariant_overlap A B)

/-- Genuine transported global sections satisfy the exact three-chart cocycle. -/
theorem triple_global_sections (A B : R) :
    GlobalDifferentialFunctor318.map (T:=Triple A B) (fromX A B)
      ((tilde.isoTop (R:=CommRingCat.of (FiniteInvariantDifferential318.XChart A B))
        (ModuleCat.of _ (KaehlerDifferential R (FiniteInvariantDifferential318.XChart A B)))).hom
          (FiniteInvariantDifferential318.xForm A B))=
    GlobalDifferentialFunctor318.map (T:=Triple A B) (fromInfinity A B)
      ((tilde.isoTop (R:=CommRingCat.of (InfinityChart A B))
        (ModuleCat.of _ (KaehlerDifferential R (InfinityChart A B)))).hom
          (InvariantChartForms318.infinity A B)) := by
  rw [GlobalDifferentialFunctor318.map_section,GlobalDifferentialFunctor318.map_section,
    (triple_forms A B).1,(triple_forms A B).2]
end ActualDifferentialTriple318
