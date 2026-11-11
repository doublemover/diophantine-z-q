module
public import ProjectiveParameterSliceTriplePoints318
public section
noncomputable section
namespace ProjectiveParameterSliceTripleAlgebra318
open ProjectiveParameterSliceLocalization318
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
variable (i j k : Fin F.size)

/-- Actual second localization of the same original slice algebra,
inverting BOTH original overlap coordinates rather than their support. -/
@[expose] def coordinate : O i j := ProjectiveParameterSliceLocalization318.point R P i j (x k)
abbrev algebra := Localization.Away (coordinate R P i j k)
local notation "T" => algebra R P i j k
instance baseAlgebra : Algebra R T :=
  ((algebraMap (O i j) T).comp (algebraMap R (O i j))).toAlgebra
instance baseTower : IsScalarTower R (O i j) T := IsScalarTower.of_algebraMap_eq' rfl

@[expose] def overlapMap : O i j →ₐ[R] T := IsScalarTower.toAlgHom R (O i j) T
@[expose] def point : A →ₐ[R] T :=
  (overlapMap R P i j k).comp (ProjectiveParameterSliceLocalization318.point R P i j)
@[expose] def secondUnit : Tˣ :=
  Units.map (overlapMap R P i j k).toMonoidHom (ProjectiveParameterSliceLocalization318.unit R P i j)
@[expose] def thirdUnit : Tˣ where
  val := algebraMap (O i j) T (coordinate R P i j k)
  inv := IsLocalization.Away.invSelf (coordinate R P i j k)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]

/-- The universal triple point lives in the actual iterated localization.
Its two invertible coordinates are explicitly constructed, not assumed. -/
@[expose] def universal : ProjectiveParameterSliceTriplePoints318.Point R P T i j k where
  point := point R P i j k
  first_eq := by
    change overlapMap R P i j k (ProjectiveParameterSliceLocalization318.point R P i j (x i))=1
    rw [ProjectiveParameterSliceLocalization318.first,map_one]
  secondUnit := secondUnit R P i j k
  second_eq := by
    change overlapMap R P i j k (ProjectiveParameterSliceLocalization318.point R P i j (x j))=
      overlapMap R P i j k (ProjectiveParameterSliceLocalization318.unit R P i j : O i j)
    rw [ProjectiveParameterSliceLocalization318.unit_val]
  thirdUnit := thirdUnit R P i j k
  third_eq := rfl

/-- Maps from the actual triple localization are determined by the SAME
original symmetric generators. Both localization inverses are forced. -/
lemma hom_ext {S : Type*} [CommRing S] [Algebra R S] {f g : T →ₐ[R] S}
    (h : ∀ a : A,f (point R P i j k a)=g (point R P i j k a)) : f=g := by
  have ho : f.comp (overlapMap R P i j k)=g.comp (overlapMap R P i j k) := by
    apply ProjectiveParameterSliceLocalizationIso318.hom_ext R P i j
    intro a
    exact h a
  have he : f.toRingHom=g.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinate R P i j k))
    apply RingHom.ext
    intro a
    exact DFunLike.congr_fun ho a
  exact AlgHom.ext (fun a => DFunLike.congr_fun he a)
end ProjectiveParameterSliceTripleAlgebra318
