module
public import VaryingSourcePointNaturality318
public section
noncomputable section
namespace VaryingSourceWordOpen318
open VaryingMatrixWords318 VaryingSourcePointNaturality318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "B" => VaryingSourceActionParameter318.ring R A ι
@[expose] def universal : VaryingSourceActionParameter318.Point R A ι B :=
  VaryingSourceActionParameter318.toPoint R A ι B (AlgHom.id R B)
@[expose] def delta (w : ι → List A) : B := determinant (universal R A ι).val w

variable (S : Type u) [CommRing S] [Algebra R S]
lemma determinant_forward (f : B →ₐ[R] S) (w : ι → List A) :
    f (delta R A ι w)=
      determinant (VaryingSourceActionParameter318.toPoint R A ι S f).val w := by
  have h := toPoint_natural R A ι B S f (AlgHom.id R B)
  simp only [AlgHom.comp_id] at h
  change f (determinant (universal R A ι).val w)=_
  have hm : f (determinant (universal R A ι).val w)=
      determinant (VaryingCommutingMatrixPoints318.mapData R A ι B S f
        (universal R A ι).val) w :=
    determinant_map R (S := B) (T := S) f (universal R A ι).val w
  have hn : VaryingCommutingMatrixPoints318.mapData R A ι B S f
      (universal R A ι).val=
        (VaryingSourceActionParameter318.toPoint R A ι S f).val :=
    congrArg Subtype.val h.symm
  exact hm.trans (congrArg (fun d => determinant d w) hn)

variable (w : ι → List A)
abbrev ring := Localization.Away (delta R A ι w)
local notation "H" => ring R A ι w
instance baseAlgebra : Algebra R H :=
  inferInstanceAs (Algebra R (Localization.Away (delta R A ι w)))
instance baseTower : IsScalarTower R B H := inferInstance
@[expose] def inclusion : B →ₐ[R] H := IsScalarTower.toAlgHom R B H
@[expose] def determinantUnit : Hˣ where
  val := ((algebraMap B H) : B →+* H) (delta R A ι w)
  inv := IsLocalization.Away.invSelf (delta R A ι w)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]

abbrev Point := {d : VaryingSourceActionParameter318.Point R A ι S //
  IsUnit (determinant d.val w)}
@[expose] def toPoint (a : H →ₐ[R] S) : Point R A ι S w :=
  ⟨VaryingSourceActionParameter318.toPoint R A ι S (a.comp (inclusion R A ι w)),by
    rw [← determinant_forward]
    change IsUnit (a (((algebraMap B H) : B →+* H) (delta R A ι w)))
    exact (IsLocalization.Away.algebraMap_isUnit (S := H) (delta R A ι w)).map a.toMonoidHom⟩
@[expose] def fromPoint (d : Point R A ι S w) : H →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (S := H)
    (f := VaryingSourceActionParameter318.fromPoint R A ι S d.val) (delta R A ι w)
    (show IsUnit (VaryingSourceActionParameter318.fromPoint R A ι S d.val
      (delta R A ι w)) from by
      rw [determinant_forward]
      change IsUnit (determinant
        ((VaryingSourceActionParameter318.pointsWithRelations R A ι S)
          ((VaryingSourceActionParameter318.pointsWithRelations R A ι S).symm d.val)).val w)
      rw [Equiv.apply_symm_apply]
      exact d.property)
lemma fromPoint_inclusion (d : Point R A ι S w) (z : B) :
    fromPoint R A ι S w d (((algebraMap B H) : B →+* H) z)=
      VaryingSourceActionParameter318.fromPoint R A ι S d.val z :=
  by
    simp only [fromPoint,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
    rfl

/-- The actual source-relation parameter, restricted by the SAME full
word determinant, represents cyclic word-chart data on all test rings. -/
@[expose] def pointsOnOpen : (H →ₐ[R] S) ≃ Point R A ι S w where
  toFun := toPoint R A ι S w
  invFun := fromPoint R A ι S w
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (delta R A ι w))
    apply RingHom.ext
    intro z
    change fromPoint R A ι S w (toPoint R A ι S w a) (((algebraMap B H) : B →+* H) z)=_
    rw [fromPoint_inclusion]
    have h : VaryingSourceActionParameter318.fromPoint R A ι S
        (VaryingSourceActionParameter318.toPoint R A ι S (a.comp (inclusion R A ι w)))=
        a.comp (inclusion R A ι w) :=
      (VaryingSourceActionParameter318.pointsWithRelations R A ι S).symm_apply_apply
        (a.comp (inclusion R A ι w))
    change VaryingSourceActionParameter318.fromPoint R A ι S
      (VaryingSourceActionParameter318.toPoint R A ι S (a.comp (inclusion R A ι w))) z=
      (a.comp (inclusion R A ι w)) z
    exact congrArg (fun f : B →ₐ[R] S => f z) h
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R A ι S w d).comp (inclusion R A ι w)=
        VaryingSourceActionParameter318.fromPoint R A ι S d.val := by
      ext z
      change fromPoint R A ι S w d (((algebraMap B H) : B →+* H) z)=
        VaryingSourceActionParameter318.fromPoint R A ι S d.val z
      exact fromPoint_inclusion R A ι S w d z
    change VaryingSourceActionParameter318.toPoint R A ι S
      ((fromPoint R A ι S w d).comp (inclusion R A ι w))=d.val
    rw [h]
    exact (VaryingSourceActionParameter318.pointsWithRelations R A ι S).apply_symm_apply d.val
end VaryingSourceWordOpen318
