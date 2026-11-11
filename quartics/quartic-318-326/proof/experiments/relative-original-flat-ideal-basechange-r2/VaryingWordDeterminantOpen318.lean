module
public import VaryingMatrixWords318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace VaryingWordDeterminantOpen318
open VaryingCommutingMatrixRing318 VaryingCommutingMatrixPoints318 VaryingMatrixWords318
universe u
variable (R σ ι : Type u) [CommRing R] [Fintype ι] [DecidableEq ι]
local notation "B" => algebra R σ ι

@[expose] def universal : Data σ ι B := forward R σ ι B (AlgHom.id R B)
@[expose] def delta (w : ι → List σ) : B := determinant (universal R σ ι) w

variable (S : Type u) [CommRing S] [Algebra R S]
lemma forward_universal (f : B →ₐ[R] S) :
    forward R σ ι S f = mapData R σ ι B S f (universal R σ ι) := by
  simpa only [AlgHom.comp_id,universal] using
    forward_natural R σ ι B S f (AlgHom.id R B)

lemma determinant_forward (f : B →ₐ[R] S) (w : ι → List σ) :
    f (delta R σ ι w)=determinant (forward R σ ι S f) w := by
  change f (determinant (universal R σ ι) w)=_
  rw [determinant_map,← forward_universal]

variable (w : ι → List σ)
abbrev ring := Localization.Away (delta R σ ι w)
local notation "H" => ring R σ ι w
/-- Keep the native localization action and its actual quotient scalar
carrier; do not introduce a competing toAlgebra action on this carrier. -/
instance baseAlgebra : Algebra R H :=
  inferInstanceAs (Algebra R (Localization.Away (delta R σ ι w)))
instance baseTower : IsScalarTower R B H := inferInstance
@[expose] def inclusion : B →ₐ[R] H := IsScalarTower.toAlgHom R B H
@[expose] def determinantUnit : Hˣ where
  val := algebraMap B H (delta R σ ι w)
  inv := IsLocalization.Away.invSelf (delta R σ ι w)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]

/-- The true arbitrary-ring determinant condition. Nonvanishing at one
point is never substituted for invertibility on the entire test ring. -/
abbrev Point := {d : Data σ ι S // IsUnit (determinant d w)}

@[expose] def toPoint (a : H →ₐ[R] S) : Point σ ι S w :=
  ⟨forward R σ ι S (a.comp (inclusion R σ ι w)),by
    rw [← determinant_forward]
    change IsUnit (a (algebraMap B H (delta R σ ι w)))
    exact (IsLocalization.Away.algebraMap_isUnit (S := H) (delta R σ ι w)).map a.toMonoidHom⟩

@[expose] def fromPoint (d : Point σ ι S w) : H →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (S := H) (f := backward R σ ι S d.val) (delta R σ ι w)
    (show IsUnit (backward R σ ι S d.val (delta R σ ι w)) from by
      rw [determinant_forward]
      change IsUnit (determinant ((points R σ ι S) ((points R σ ι S).symm d.val)) w)
      rw [Equiv.apply_symm_apply]
      exact d.property)

lemma fromPoint_include (d : Point σ ι S w) (z : B) :
    fromPoint R σ ι S w d (algebraMap B H z)=backward R σ ι S d.val z :=
  by simp only [fromPoint,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]

/-- The literal principal localization represents precisely the selected
word-basis determinant open on ALL coefficient tests, including nilpotents.
No assertion that these opens cover all quotients is made here. -/
@[expose] def pointsOnOpen : (H →ₐ[R] S) ≃ Point σ ι S w where
  toFun := toPoint R σ ι S w
  invFun := fromPoint R σ ι S w
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (delta R σ ι w))
    apply RingHom.ext
    intro z
    change fromPoint R σ ι S w (toPoint R σ ι S w a) (algebraMap B H z)=_
    rw [fromPoint_include]
    have h := congrArg (fun f : B →ₐ[R] S => f z)
      ((points R σ ι S).symm_apply_apply (a.comp (inclusion R σ ι w)))
    simpa only [points,toPoint,AlgHom.comp_apply,inclusion,IsScalarTower.coe_toAlgHom,
      RingHom.coe_comp,Function.comp_apply] using h
  right_inv d := by
    apply Subtype.ext
    have h : (fromPoint R σ ι S w d).comp (inclusion R σ ι w)=
        backward R σ ι S d.val := by
      ext z
      change fromPoint R σ ι S w d (algebraMap B H z)=backward R σ ι S d.val z
      exact fromPoint_include R σ ι S w d z
    change forward R σ ι S ((fromPoint R σ ι S w d).comp (inclusion R σ ι w))=d.val
    rw [h]
    exact (points R σ ι S).apply_symm_apply d.val
end VaryingWordDeterminantOpen318
