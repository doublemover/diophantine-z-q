module
public import ProjectiveParameterUnitAction318
public section
noncomputable section
namespace ProjectiveParameterUnitSlice318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (S : Type w) [CommRing S] [Algebra R S] (i : Fin F.size)

/-- An actual point on a principal coordinate chart: the selected literal
coordinate is a unit, not merely nonzero in a possibly nonreduced ring. -/
structure ChartPoint where
  point : A →ₐ[R] S
  coordinateUnit : Sˣ
  coordinate_eq : point (x i)=(coordinateUnit:S)

abbrev SlicePoint := {a : A →ₐ[R] S // a (x i)=1}

lemma scale_coordinate (s : S) (a : A →ₐ[R] S) :
    ProjectiveParameterUnitAction318.pointScale R P S s a (x i)=s*a (x i) :=
  ProjectiveParameterUnitAction318.pointScale_generator R P S s a _

/-- Divide by the ACTUAL invertible chosen coordinate. This remains valid
over arbitrary rings with nilpotents and with a finite projective module. -/
@[expose] def normalize (a : ChartPoint R P S i) : SlicePoint R P S i :=
  ⟨ProjectiveParameterUnitAction318.pointScale R P S ((a.coordinateUnit⁻¹:Sˣ):S) a.point,by
    rw [scale_coordinate,a.coordinate_eq,Units.inv_mul]⟩
@[expose] def denormalize (a : Sˣ × SlicePoint R P S i) : ChartPoint R P S i :=
  ⟨ProjectiveParameterUnitAction318.pointScale R P S (a.1:S) a.2.val,a.1,by
    rw [scale_coordinate,a.2.property,mul_one]⟩

/-- Explicit principal-chart trivialization of the relative unit action.
The residual slice has coordinate exactly one; the discarded factor is
an actual test-ring unit, not an arbitrary nonzero scalar. -/
@[expose] def trivialization : ChartPoint R P S i ≃ Sˣ × SlicePoint R P S i where
  toFun a := (a.coordinateUnit,normalize R P S i a)
  invFun := denormalize R P S i
  left_inv a := by
    rcases a with ⟨a,u,hu⟩
    have he : ProjectiveParameterUnitAction318.pointScale R P S (u:S)
      (ProjectiveParameterUnitAction318.pointScale R P S ((u⁻¹:Sˣ):S) a)=a := by
      rw [ProjectiveParameterUnitAction318.pointScale_mul,Units.mul_inv,
        ProjectiveParameterUnitAction318.pointScale_one]
    simp only [denormalize,normalize,he]
  right_inv a := by
    rcases a with ⟨u,a,ha⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ProjectiveParameterUnitAction318.pointScale R P S ((u⁻¹:Sˣ):S)
        (ProjectiveParameterUnitAction318.pointScale R P S (u:S) a)=a
      rw [ProjectiveParameterUnitAction318.pointScale_mul,Units.inv_mul,
        ProjectiveParameterUnitAction318.pointScale_one]

/-- Scalar normalization is UNIQUE on this chart: a scalar preserving
the slice coordinate must be one. This rules out hidden unit stabilizers. -/
lemma slice_scalar_unique (u : Sˣ) (a : SlicePoint R P S i)
    (h : ProjectiveParameterUnitAction318.pointScale R P S (u:S) a.val (x i)=1) : u=1 := by
  rw [scale_coordinate,a.property,mul_one] at h
  exact Units.ext h

lemma action_free (a : ChartPoint R P S i) (u : Sˣ)
    (h : ProjectiveParameterUnitAction318.pointScale R P S (u:S) a.point=a.point) : u=1 := by
  have hi := DFunLike.congr_fun h (x i)
  rw [scale_coordinate,a.coordinate_eq] at hi
  have hi' := congrArg (fun s : S => s*((a.coordinateUnit⁻¹:Sˣ):S)) hi
  apply Units.ext
  simpa only [mul_assoc,Units.mul_inv,mul_one] using hi'
end ProjectiveParameterUnitSlice318
