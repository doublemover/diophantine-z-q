module
public import VaryingNormalizedWordNaturality318
public section
noncomputable section
namespace VaryingNormalizedWordOverlap318
open VaryingMatrixWords318 VaryingNormalizedWordNaturality318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "B" => VaryingNormalizedWordParameter318.ring R A ι w
@[expose] def universal : VaryingNormalizedWordParameter318.Point R A ι w B :=
  VaryingNormalizedWordParameter318.toPoint R A ι w B (AlgHom.id R B)
@[expose] def delta (v : ι → List A) : B := determinant (universal R A ι w).val.val v

variable (S : Type u) [CommRing S] [Algebra R S]
lemma determinant_forward (f : B →ₐ[R] S) (v : ι → List A) :
    f (delta R A ι w v)=
      determinant (VaryingNormalizedWordParameter318.toPoint R A ι w S f).val.val v := by
  have h := toPoint_natural R A ι w B S f (AlgHom.id R B)
  simp only [AlgHom.comp_id] at h
  change f (determinant (universal R A ι w).val.val v)=_
  rw [determinant_map]
  exact congrArg (fun d : VaryingNormalizedWordParameter318.Point R A ι w S =>
    determinant d.val.val v) h.symm

variable (v : ι → List A)
abbrev ring := Localization.Away (delta R A ι w v)
local notation "H" => ring R A ι w v
instance baseAlgebra : Algebra R H :=
  ((algebraMap B H).comp (algebraMap R B)).toAlgebra
instance baseTower : IsScalarTower R B H := IsScalarTower.of_algebraMap_eq' rfl
@[expose] def inclusion : B →ₐ[R] H := IsScalarTower.toAlgHom R B H
@[expose] def determinantUnit : Hˣ where
  val := algebraMap B H (delta R A ι w v)
  inv := IsLocalization.Away.invSelf (delta R A ι w v)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]

abbrev Point := {d : VaryingNormalizedWordParameter318.Point R A ι w S //
  IsUnit (determinant d.val.val v)}
@[expose] def toPoint (a : H →ₐ[R] S) : Point R A ι w S v :=
  ⟨VaryingNormalizedWordParameter318.toPoint R A ι w S (a.comp (inclusion R A ι w v)),by
    rw [← determinant_forward]
    exact (determinantUnit R A ι w v).isUnit.map a.toMonoidHom⟩
@[expose] def fromPoint (d : Point R A ι w S v) : H →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (delta R A ι w v)
    (show IsUnit (VaryingNormalizedWordParameter318.fromPoint R A ι w S d.val
      (delta R A ι w v)) from by
      rw [determinant_forward]
      change IsUnit (determinant
        ((VaryingNormalizedWordParameter318.points R A ι w S)
          ((VaryingNormalizedWordParameter318.points R A ι w S).symm d.val)).val.val v)
      rw [Equiv.apply_symm_apply]
      exact d.property)
lemma fromPoint_inclusion (d : Point R A ι w S v) (z : B) :
    fromPoint R A ι w S v d (algebraMap B H z)=
      VaryingNormalizedWordParameter318.fromPoint R A ι w S d.val z :=
  IsLocalization.Away.lift_eq _ _ z

/-- The normalized w-chart localized at the literal v-word determinant
represents the actual w/v overlap on every coefficient ring. -/
@[expose] def pointsOnOpen : (H →ₐ[R] S) ≃ Point R A ι w S v where
  toFun := toPoint R A ι w S v
  invFun := fromPoint R A ι w S v
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (delta R A ι w v))
    apply RingHom.ext
    intro z
    change fromPoint R A ι w S v (toPoint R A ι w S v a) (algebraMap B H z)=_
    rw [fromPoint_inclusion]
    exact congrArg (fun f : B →ₐ[R] S => f z)
      ((VaryingNormalizedWordParameter318.points R A ι w S).symm_apply_apply
        (a.comp (inclusion R A ι w v)))
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R A ι w S v d).comp (inclusion R A ι w v)=
        VaryingNormalizedWordParameter318.fromPoint R A ι w S d.val := by
      ext z
      exact fromPoint_inclusion R A ι w S v d z
    change VaryingNormalizedWordParameter318.toPoint R A ι w S
      ((fromPoint R A ι w S v d).comp (inclusion R A ι w v))=d.val
    rw [h]
    exact (VaryingNormalizedWordParameter318.points R A ι w S).apply_symm_apply d.val

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def mapPoint (d : Point R A ι w S v) : Point R A ι w T v :=
  ⟨VaryingNormalizedWordNaturality318.mapPoint R A ι w S T f d.val,by
    rw [← VaryingNormalizedWordNaturality318.determinant_map]
    exact d.property.map f.toMonoidHom⟩

lemma toPoint_natural (a : H →ₐ[R] S) :
    toPoint R A ι w T v (f.comp a)=
      mapPoint R A ι w S v T f (toPoint R A ι w S v a) := by
  apply Subtype.ext
  exact VaryingNormalizedWordNaturality318.toPoint_natural R A ι w S T f
    (a.comp (inclusion R A ι w v))
end VaryingNormalizedWordOverlap318
