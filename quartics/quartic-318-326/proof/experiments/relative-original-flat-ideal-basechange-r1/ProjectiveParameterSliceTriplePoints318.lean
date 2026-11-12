module
public import ProjectiveParameterSliceOverlapPoints318
public import Mathlib.Tactic.Group
public section
noncomputable section
namespace ProjectiveParameterSliceTriplePoints318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (S : Type w) [CommRing S] [Algebra R S]
local notation "scale" => ProjectiveParameterUnitAction318.pointScale R P S

/-- Three actual normalized slice coordinates, with both overlap
coordinates invertible in the entire test ring. -/
structure Point (i j k : Fin F.size) where
  point : A →ₐ[R] S
  first_eq : point (x i)=1
  secondUnit : Sˣ
  second_eq : point (x j)=(secondUnit:S)
  thirdUnit : Sˣ
  third_eq : point (x k)=(thirdUnit:S)

@[ext] lemma point_ext {i j k : Fin F.size} {a b : Point R P S i j k}
    (hp : a.point=b.point) (hj : a.secondUnit=b.secondUnit) (hk : a.thirdUnit=b.thirdUnit) : a=b := by
  cases a
  cases b
  cases hp
  cases hj
  cases hk
  rfl

@[expose] def rotate (i j k : Fin F.size) (a : Point R P S i j k) : Point R P S j k i where
  point := scale ((a.secondUnit⁻¹:Sˣ):S) a.point
  first_eq := by rw [ProjectiveParameterUnitSlice318.scale_coordinate,a.second_eq,Units.inv_mul]
  secondUnit := a.secondUnit⁻¹*a.thirdUnit
  second_eq := by rw [ProjectiveParameterUnitSlice318.scale_coordinate,a.third_eq,Units.val_mul]
  thirdUnit := a.secondUnit⁻¹
  third_eq := by rw [ProjectiveParameterUnitSlice318.scale_coordinate,a.first_eq,mul_one]

private lemma unit_comp (u v : Sˣ) (a : A →ₐ[R] S) :
    scale (u:S) (scale (v:S) a)=scale ((u*v:Sˣ):S) a :=
  ProjectiveParameterUnitAction318.pointScale_mul R P S (u:S) (v:S) a

/-- Exact cyclic triple-overlap cocycle on ALL coefficient tests. The
successive units are the actual ratios of the original three coordinates. -/
lemma rotate_three (i j k : Fin F.size) (a : Point R P S i j k) :
    rotate R P S k i j (rotate R P S j k i (rotate R P S i j k a))=a := by
  apply point_ext
  · change scale (((((a.secondUnit⁻¹*a.thirdUnit)⁻¹*a.secondUnit⁻¹)⁻¹):Sˣ):S)
      (scale ((((a.secondUnit⁻¹*a.thirdUnit)⁻¹):Sˣ):S)
        (scale ((a.secondUnit⁻¹:Sˣ):S) a.point))=a.point
    rw [unit_comp,unit_comp]
    have h : (((a.secondUnit⁻¹*a.thirdUnit)⁻¹*a.secondUnit⁻¹)⁻¹)*
      ((a.secondUnit⁻¹*a.thirdUnit)⁻¹)*a.secondUnit⁻¹=1 := by group
    rw [h]
    exact ProjectiveParameterUnitAction318.pointScale_one R P S a.point
  · change (((a.secondUnit⁻¹*a.thirdUnit)⁻¹*a.secondUnit⁻¹)⁻¹)*
      ((a.secondUnit⁻¹*a.thirdUnit)⁻¹)=a.secondUnit
    group
  · change (((a.secondUnit⁻¹*a.thirdUnit)⁻¹*a.secondUnit⁻¹)⁻¹)=a.thirdUnit
    group

@[expose] def firstOverlap (i j k : Fin F.size) (a : Point R P S i j k) :
    ProjectiveParameterSliceOverlap318.Point R P S i j :=
  ⟨a.point,a.first_eq,a.secondUnit,a.second_eq⟩
@[expose] def secondOverlap (i j k : Fin F.size) (a : Point R P S i j k) :
    ProjectiveParameterSliceOverlap318.Point R P S i k :=
  ⟨a.point,a.first_eq,a.thirdUnit,a.third_eq⟩

/-- Rotation on a triple restricts to the already constructed actual
pairwise transition on its second overlap leg. -/
lemma rotation_leg (i j k : Fin F.size) (a : Point R P S i j k) :
    secondOverlap R P S j k i (rotate R P S i j k a)=
      ProjectiveParameterSliceOverlap318.transition R P S i j (firstOverlap R P S i j k a) := rfl
@[expose] def map {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (i j k : Fin F.size) (a : Point R P S i j k) : Point R P T i j k where
  point := g.comp a.point
  first_eq := by change g (a.point (x i))=1; rw [a.first_eq,map_one]
  secondUnit := Units.map g.toMonoidHom a.secondUnit
  second_eq := by change g (a.point (x j))=g (a.secondUnit:S); rw [a.second_eq]
  thirdUnit := Units.map g.toMonoidHom a.thirdUnit
  third_eq := by change g (a.point (x k))=g (a.thirdUnit:S); rw [a.third_eq]

lemma rotate_natural {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (i j k : Fin F.size) (a : Point R P S i j k) :
    map R P S g j k i (rotate R P S i j k a)=
      rotate R P T i j k (map R P S g i j k a) := by
  apply point_ext
  · change g.comp (scale ((a.secondUnit⁻¹:Sˣ):S) a.point)=
      ProjectiveParameterUnitAction318.pointScale R P T
        (((Units.map g.toMonoidHom a.secondUnit)⁻¹:Tˣ):T) (g.comp a.point)
    rw [ProjectiveParameterUnitAction318.pointScale_natural]
    rfl
  · apply Units.ext
    exact map_mul g _ _
  · apply Units.ext
    rfl

lemma map_comp {T U : Type*} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
    (g : S →ₐ[R] T) (h : T →ₐ[R] U) (i j k : Fin F.size) (a : Point R P S i j k) :
    map R P T h i j k (map R P S g i j k a)=map R P S (h.comp g) i j k a := by
  apply point_ext
  · rfl
  · apply Units.ext; rfl
  · apply Units.ext; rfl

end ProjectiveParameterSliceTriplePoints318
