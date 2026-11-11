module
public import VaryingWordTriplePoints318
public section
noncomputable section
namespace VaryingWordTripleAlgebra318
open VaryingNormalizedWordOverlap318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "H" => VaryingNormalizedWordOverlap318.ring R A ι w v
@[expose] def coordinate : H := algebraMap N H (delta R A ι w u)
abbrev ring := Localization.Away (coordinate R A ι w v u)
local notation "K" => ring R A ι w v u
instance baseAlgebra : Algebra R K :=
  ((algebraMap H K).comp (algebraMap R H)).toAlgebra
instance baseTower : IsScalarTower R H K := IsScalarTower.of_algebraMap_eq' rfl
@[expose] def inclusion : H →ₐ[R] K := IsScalarTower.toAlgHom R H K
@[expose] def coordinateUnit : Kˣ where
  val := algebraMap H K (coordinate R A ι w v u)
  inv := IsLocalization.Away.invSelf (coordinate R A ι w v u)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]

variable (S : Type u) [CommRing S] [Algebra R S]
lemma coordinate_forward (a : H →ₐ[R] S) :
    a (coordinate R A ι w v u)=VaryingMatrixWords318.determinant
      (VaryingNormalizedWordOverlap318.toPoint R A ι w S v a).val.val.val u :=
  VaryingNormalizedWordOverlap318.determinant_forward R A ι w S
    (a.comp (VaryingNormalizedWordOverlap318.inclusion R A ι w v)) u

@[expose] def toPoint (a : K →ₐ[R] S) : VaryingWordTriplePoints318.Point R A ι w v u S :=
  ⟨VaryingNormalizedWordOverlap318.toPoint R A ι w S v
    (a.comp (inclusion R A ι w v u)),by
    rw [← coordinate_forward]
    exact (coordinateUnit R A ι w v u).isUnit.map a.toMonoidHom⟩
@[expose] def fromPoint (d : VaryingWordTriplePoints318.Point R A ι w v u S) : K →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (coordinate R A ι w v u)
    (show IsUnit (VaryingNormalizedWordOverlap318.fromPoint R A ι w S v d.val
      (coordinate R A ι w v u)) from by
      rw [coordinate_forward]
      change IsUnit (VaryingMatrixWords318.determinant
        ((pointsOnOpen R A ι w S v) ((pointsOnOpen R A ι w S v).symm d.val)).val.val.val u)
      rw [Equiv.apply_symm_apply]
      exact d.property)
lemma fromPoint_inclusion (d : VaryingWordTriplePoints318.Point R A ι w v u S) (z : H) :
    fromPoint R A ι w v u S d (algebraMap H K z)=
      VaryingNormalizedWordOverlap318.fromPoint R A ι w S v d.val z :=
  IsLocalization.Away.lift_eq _ _ z

/-- The actual iterated determinant localization represents triple frames,
with no replacement by reduced points or a different intersection algebra. -/
@[expose] def points : (K →ₐ[R] S) ≃ VaryingWordTriplePoints318.Point R A ι w v u S where
  toFun := toPoint R A ι w v u S
  invFun := fromPoint R A ι w v u S
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinate R A ι w v u))
    apply RingHom.ext
    intro z
    change fromPoint R A ι w v u S (toPoint R A ι w v u S a) (algebraMap H K z)=_
    rw [fromPoint_inclusion]
    exact congrArg (fun f : H →ₐ[R] S => f z)
      ((pointsOnOpen R A ι w S v).symm_apply_apply (a.comp (inclusion R A ι w v u)))
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R A ι w v u S d).comp (inclusion R A ι w v u)=
        VaryingNormalizedWordOverlap318.fromPoint R A ι w S v d.val := by
      ext z
      exact fromPoint_inclusion R A ι w v u S d z
    change VaryingNormalizedWordOverlap318.toPoint R A ι w S v
      ((fromPoint R A ι w v u S d).comp (inclusion R A ι w v u))=d.val
    rw [h]
    exact (pointsOnOpen R A ι w S v).apply_symm_apply d.val

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma toPoint_natural (a : K →ₐ[R] S) :
    toPoint R A ι w v u T (f.comp a)=
      VaryingWordTriplePoints318.mapPoint R A ι w v u S T f (toPoint R A ι w v u S a) := by
  apply Subtype.ext
  exact VaryingNormalizedWordOverlap318.toPoint_natural R A ι w S v T f
    (a.comp (inclusion R A ι w v u))
end VaryingWordTripleAlgebra318
