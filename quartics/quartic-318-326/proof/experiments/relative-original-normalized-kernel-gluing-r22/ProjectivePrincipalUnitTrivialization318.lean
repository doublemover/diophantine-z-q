module
public import ProjectiveParameterPrincipalNormalization318
public section
noncomputable section
namespace ProjectivePrincipalUnitTrivialization318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i : Fin F.size) (S : CommRingCat.{0}) [Algebra R S]

@[expose] def forward (a : H i →ₐ[R] S) : ProjectiveParameterUnitSlice318.ChartPoint R P S i where
  point := a.comp (ProjectiveParameterPrincipalNormalization318.point R P i)
  coordinateUnit := Units.map a.toMonoidHom (ProjectiveParameterPrincipalNormalization318.unit R P i)
  coordinate_eq := rfl
@[expose] def backward (a : ProjectiveParameterUnitSlice318.ChartPoint R P S i) : H i →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (x i) (show IsUnit (a.point (x i)) from by
    rw [a.coordinate_eq]
    exact a.coordinateUnit.isUnit)
lemma backward_include (a : ProjectiveParameterUnitSlice318.ChartPoint R P S i) (z : A) :
    backward R P i S a (algebraMap A (H i) z)=a.point z :=
  IsLocalization.Away.lift_eq _ _ z

private lemma point_ext {a b : ProjectiveParameterUnitSlice318.ChartPoint R P S i}
    (hp : a.point=b.point) (hu : a.coordinateUnit=b.coordinateUnit) : a=b := by
  cases a
  cases b
  cases hp
  cases hu
  rfl

/-- The ACTUAL away-localization represents the full unit-coordinate
chart functor on arbitrary coefficient rings. No merely geometric-point
or nonzero-to-unit inference is used. -/
@[expose] def points : (H i →ₐ[R] S) ≃ ProjectiveParameterUnitSlice318.ChartPoint R P S i where
  toFun := forward R P i S
  invFun := backward R P i S
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (x i))
    apply RingHom.ext
    intro z
    exact backward_include R P i S (forward R P i S a) z
  right_inv a := by
    apply point_ext R P i S
    · apply AlgHom.ext
      intro z
      exact backward_include R P i S a z
    · apply Units.ext
      change backward R P i S a (algebraMap A (H i) (x i))=(a.coordinateUnit:S)
      rw [backward_include,a.coordinate_eq]

/-- A genuine local unit-torsor classification of points of the ACTUAL
principal chart: a test-ring unit and a point of the ORIGINAL normalized
slice. Both directions use quotient and localization universal properties. -/
@[expose] def trivialization : (H i →ₐ[R] S) ≃ Sˣ × (B i →ₐ[R] S) :=
  (points R P i S).trans (ProjectiveParameterSliceAlgebra318.chartPoints R P i S)
end ProjectivePrincipalUnitTrivialization318
