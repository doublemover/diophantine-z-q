module
public import ProjectiveParameterSliceLocalizationIso318
public section
noncomputable section
namespace ProjectiveParameterSliceOverlapPoints318
open ProjectiveParameterSliceLocalization318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i j : Fin F.size) (S : Type w) [CommRing S] [Algebra R S]
local notation "O" => algebra R P i j
local notation "Q" => ProjectiveParameterSliceOverlap318.Point R P S i j

@[expose] def forward (a : O →ₐ[R] S) : Q where
  point := a.comp (point R P i j)
  first_eq := by change a (point R P i j (x i))=1; rw [first,map_one]
  secondUnit := Units.map a.toMonoidHom (unit R P i j)
  second_eq := by change a (point R P i j (x j))=a (unit R P i j:O); rw [unit_val]

@[expose] def sliceMap (a : Q) : B i →ₐ[R] S :=
  (ProjectiveParameterSliceAlgebra318.points R P i S).symm ⟨a.point,a.first_eq⟩
lemma sliceMap_mk (a : Q) (z : A) :
    sliceMap R P i j S a (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) z)=a.point z := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ z)=_
  rw [Ideal.Quotient.lift_mk]

lemma sliceMap_coordinate (a : Q) : sliceMap R P i j S a (coordinate R P i j)=(a.secondUnit:S) := by
  rw [coordinate,sliceMap_mk,a.second_eq]

/-- The inverse point construction uses BOTH actual universal properties:
the coordinate-one quotient and localization at the coordinate unit. -/
@[expose] def backward (a : Q) : O →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (coordinate R P i j)
    (show IsUnit (sliceMap R P i j S a (coordinate R P i j)) from by
      rw [sliceMap_coordinate]
      exact a.secondUnit.isUnit)
lemma backward_point (a : Q) (z : A) : backward R P i j S a (point R P i j z)=a.point z := by
  change backward R P i j S a (algebraMap (B i) O
    (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) z))=_
  rw [backward,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,sliceMap_mk]

/-- The previously constructed ACTUAL overlap algebra represents the
full normalized overlap functor on arbitrary coefficient tests. Hence
point-level normalization identities can be applied to all algebra maps,
not merely to geometric points. -/
@[expose] def points : (O →ₐ[R] S) ≃ Q where
  toFun := forward R P i j S
  invFun := backward R P i j S
  left_inv a := by
    apply ProjectiveParameterSliceLocalizationIso318.hom_ext R P i j
    intro z
    rw [backward_point]
    rfl
  right_inv a := by
    apply ProjectiveParameterSliceOverlap318.point_ext
    · apply AlgHom.ext
      intro z
      exact backward_point R P i j S a z
    · apply Units.ext
      change backward R P i j S a (unit R P i j:O)=(a.secondUnit:S)
      rw [unit_val,backward_point,a.second_eq]

/-- Represented overlap points commute with every actual coefficient map. -/
lemma natural {T : Type*} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) (a : O →ₐ[R] S) :
    forward R P i j T (g.comp a)=ProjectiveParameterSliceOverlap318.map R P S g i j
      (forward R P i j S a) := by
  apply ProjectiveParameterSliceOverlap318.point_ext
  · rfl
  · apply Units.ext
    rfl
end ProjectiveParameterSliceOverlapPoints318
