module
public import ProjectiveParameterSliceAlgebra318
public section
noncomputable section
namespace ProjectiveParameterSliceOverlap318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
variable (S : Type w) [CommRing S] [Algebra R S]
local notation "scale" => ProjectiveParameterUnitAction318.pointScale R P S

/-- Literal overlap of two normalized coordinate slices: the first
coordinate is one and the second is an actual coefficient unit. -/
structure Point (i j : Fin F.size) where
  point : A →ₐ[R] S
  first_eq : point (x i)=1
  secondUnit : Sˣ
  second_eq : point (x j)=(secondUnit:S)

@[ext] lemma point_ext {i j : Fin F.size} {a b : Point R P S i j}
    (hp : a.point=b.point) (hu : a.secondUnit=b.secondUnit) : a=b := by
  cases a
  cases b
  cases hp
  cases hu
  rfl

@[expose] def transition (i j : Fin F.size) (a : Point R P S i j) : Point R P S j i where
  point := scale ((a.secondUnit⁻¹:Sˣ):S) a.point
  first_eq := by
    rw [ProjectiveParameterUnitSlice318.scale_coordinate,a.second_eq,Units.inv_mul]
  secondUnit := a.secondUnit⁻¹
  second_eq := by
    rw [ProjectiveParameterUnitSlice318.scale_coordinate,a.first_eq,mul_one]

/-- Transition in the opposite direction uses precisely the reciprocal
unit and returns the original point, retaining the whole algebra map. -/
lemma transition_transition (i j : Fin F.size) (a : Point R P S i j) :
    transition R P S j i (transition R P S i j a)=a := by
  rcases a with ⟨a,hi,u,hj⟩
  have he : scale (u:S) (scale ((u⁻¹:Sˣ):S) a)=a := by
    rw [ProjectiveParameterUnitAction318.pointScale_mul,Units.mul_inv,
      ProjectiveParameterUnitAction318.pointScale_one]
  simp only [transition,inv_inv,he]

@[expose] def equivalence (i j : Fin F.size) : Point R P S i j ≃ Point R P S j i where
  toFun := transition R P S i j
  invFun := transition R P S j i
  left_inv := transition_transition R P S i j
  right_inv := transition_transition R P S j i

/-- The original algebra map normalized at coordinate j then at k equals
its direct k-normalization. The second normalizing unit is the ACTUAL
transformed coordinate u⁻¹v, so this is a genuine triple-overlap equation. -/
lemma triple (a : A →ₐ[R] S) (u v : Sˣ) :
    scale ((((u⁻¹*v)⁻¹:Sˣ)):S) (scale ((u⁻¹:Sˣ):S) a)=
      scale ((v⁻¹:Sˣ):S) a := by
  rw [ProjectiveParameterUnitAction318.pointScale_mul]
  congr 1
  simp only [mul_inv_rev,inv_inv,Units.val_mul,mul_assoc,Units.mul_inv,mul_one]

lemma transformed_coordinate (a : A →ₐ[R] S) (j : Fin F.size) (u v : Sˣ)
    (h : a (x j)=(v:S)) :
    scale ((u⁻¹:Sˣ):S) a (x j)=((u⁻¹*v:Sˣ):S) := by
  rw [ProjectiveParameterUnitSlice318.scale_coordinate,h,Units.val_mul]

/-- Every affine coefficient map transports these literal normalized
points and units. No reducedness, field, or flatness assumption enters. -/
@[expose] def map {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (i j : Fin F.size) (a : Point R P S i j) : Point R P T i j where
  point := g.comp a.point
  first_eq := by change g (a.point (x i))=1; rw [a.first_eq,map_one]
  secondUnit := Units.map g.toMonoidHom a.secondUnit
  second_eq := by change g (a.point (x j))=g (a.secondUnit:S); rw [a.second_eq]

lemma transition_natural {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (i j : Fin F.size) (a : Point R P S i j) :
    map R P S g j i (transition R P S i j a)=
      transition R P T i j (map R P S g i j a) := by
  apply point_ext
  · change g.comp (scale ((a.secondUnit⁻¹:Sˣ):S) a.point)=
      ProjectiveParameterUnitAction318.pointScale R P T
        (((Units.map g.toMonoidHom a.secondUnit)⁻¹:Tˣ):T) (g.comp a.point)
    rw [ProjectiveParameterUnitAction318.pointScale_natural]
    rfl
  · apply Units.ext
    rfl
end ProjectiveParameterSliceOverlap318
