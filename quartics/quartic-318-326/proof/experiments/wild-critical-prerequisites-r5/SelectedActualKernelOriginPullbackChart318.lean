module
public import SelectedCanonicalFiniteAffine318
public import SelectedGeneralizedInstallOriginOpen318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedGeneralizedGluedCarrier318 SelectedGeneralizedInstallOriginOpen318
open SelectedGeneralizedInfinityCartier318

namespace SelectedActualKernelOriginPullbackChart318

universe u
variable {R : Type u} [CommRing R]
variable (d : Rˣ) (m : Carrier d ⟶ Carrier d)

abbrev U := pullback m (install d)
abbrev p : U d m ⟶ OriginOpen d := pullback.snd m (install d)
abbrev fromCarrier : U d m ⟶ Carrier d := pullback.fst m (install d)
abbrev Z := pullback m (identitySection d)
abbrev proj : Z d m ⟶ Base R := pullback.snd m (identitySection d)

def intoOpen : Z d m ⟶ U d m :=
  pullback.lift (pullback.fst m (identitySection d)) (proj d m≫originLift d) (by
    rw [Category.assoc,originLift_install]
    exact pullback.condition)

theorem into_carrier :
    intoOpen d m≫fromCarrier d m=pullback.fst m (identitySection d) := pullback.lift_fst _ _ _
theorem into_origin_open :
    intoOpen d m≫p d m=proj d m≫originLift d := pullback.lift_snd _ _ _

/-- The actual zero fibre is the actual pullback of the small
origin atlas, globally along the original endomorphism. This
really factors every kernel point scheme-theoretically. -/
theorem origin_atlas_square :
    IsPullback (intoOpen d m) (proj d m) (p d m) (originLift d) := by
  have large : IsPullback (proj d m) (intoOpen d m≫fromCarrier d m)
      (originLift d≫install d) m := by
    rw [into_carrier,originLift_install]
    exact (IsPullback.of_hasPullback m (identitySection d)).flip
  exact (large.of_bot (into_origin_open d m).symm (IsPullback.of_hasPullback m (install d)).flip).flip

variable [IsFinite m]

theorem finite_preimage : IsFinite (p d m) := inferInstance

abbrev B := SelectedCanonicalFiniteAffine318.coord (U d m)

/-- Coefficients of the actual preimage of the identity affine chart. -/
def atlasAlgebra : Algebra (OpenRing d) (B d m) := by
  letI : IsFinite (p d m) := finite_preimage d m
  exact SelectedCanonicalFiniteAffine318.coefficients (p d m)

def model : Spec (B d m) ≅ U d m := by
  letI : IsFinite (p d m) := finite_preimage d m
  exact SelectedCanonicalFiniteAffine318.model (p d m)

theorem model_over_atlas :
    letI := atlasAlgebra d m
    (model d m).hom≫p d m=Spec.algebraMap (OpenRing d) (B d m) := by
  letI : IsFinite (p d m) := finite_preimage d m
  exact SelectedCanonicalFiniteAffine318.model_over (p d m)

def fromBase : Algebra R (B d m) := by
  letI := atlasAlgebra d m
  exact ((algebraMap (OpenRing d) (B d m)).comp (algebraMap R (OpenRing d))).toAlgebra

/-- The equation is the actual pullback of the named original
uniformizer t, not an arbitrary regular or chosen scalar. -/
def equation : B d m := by
  letI := atlasAlgebra d m
  exact algebraMap (OpenRing d) (B d m) (localT d)

theorem model_over_base (hm : m≫overBase d=overBase d) :
    letI := fromBase d m
    ((model d m).hom≫fromCarrier d m)≫overBase d=Spec.algebraMap R (B d m) := by
  letI := atlasAlgebra d m
  have h := congrArg (fun f : U d m ⟶ Carrier d => f≫overBase d)
    (pullback.condition : fromCarrier d m≫m=p d m≫install d)
  simp only [Category.assoc,hm,install_over] at h
  rw [Category.assoc,h,←Category.assoc,model_over_atlas]
  unfold Spec.algebraMap
  rw [←Spec.map_comp] <;> rfl

/-- The preimage affine algebra, as an actual open subchart of the
original smooth curve, is flat over the old base. No flatness of
the finite [M] is assumed in this ambient step. -/
theorem ambient_flat [Flat (overBase d)] (hm : m≫overBase d=overBase d) :
    letI := fromBase d m
    Module.Flat R (B d m) := by
  letI := fromBase d m
  apply RingHom.flat_algebraMap_iff.mp
  apply Flat.SpecMap_iff.mp
  change Flat (Spec.algebraMap R (B d m))
  rw [←model_over_base d m hm]
  letI : IsOpenImmersion (fromCarrier d m) := inferInstance
  infer_instance

end SelectedActualKernelOriginPullbackChart318

#print axioms SelectedActualKernelOriginPullbackChart318.origin_atlas_square
#print axioms SelectedActualKernelOriginPullbackChart318.ambient_flat
