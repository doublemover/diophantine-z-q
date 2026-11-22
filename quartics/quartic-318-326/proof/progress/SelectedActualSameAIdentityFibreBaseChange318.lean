module
public import SelectedActualSameAPlusEleven318
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.Basis

/-! The cotangent at the identity of the original marked family, before
and after scalar extension. Both specializations use the same
augmentation of an actual affine identity chart, not unrelated models. -/
public section
noncomputable section
open scoped TensorProduct Matrix
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace SelectedActualSameAIdentityFibreBaseChange318

section Affine
variable {R E S : Type*} [CommRing R] [CommRing E] [CommRing S]
  [Algebra R E] [Algebra R S]

abbrev Fibre (e : E →ₐ[R] R) := letI : Algebra E R := e.toRingHom.toAlgebra
  R ⊗[E] KaehlerDifferential R E

/-- Extension of the actual augmentation through R→S. -/
@[expose] def pushIdentity (e : E →ₐ[R] R) : E →ₐ[R] S :=
  (IsScalarTower.toAlgHom R R S).comp e

theorem pushIdentity_on (e : E →ₐ[R] R) (a : E) :
    pushIdentity (S:=S) e a=algebraMap R S (e a) := rfl

/-- The identity of the base-changed algebra; its right-hand map is the
fixed original identity, rather than a second selected point. -/
def baseIdentity (e : E →ₐ[R] R) : S ⊗[R] E →ₐ[S] S :=
  (AlgHom.liftEquiv R S E S) (pushIdentity e)

theorem baseIdentity_tmul (e : E →ₐ[R] R) (s : S) (a : E) :
    baseIdentity e (s ⊗ₜ[R] a)=s*algebraMap R S (e a) := by
  rw [baseIdentity,AlgHom.liftEquiv_tmul,pushIdentity_on,smul_eq_mul]

theorem baseIdentity_onChart (e : E →ₐ[R] R) (a : E) :
    baseIdentity e (algebraMap E (S ⊗[R] E) a)=algebraMap R S (e a) := by
  change baseIdentity e (1 ⊗ₜ[R] a)=_
  rw [baseIdentity_tmul,one_mul]

/-- Composition of the two real affine base changes: first pass across
the original identity, then along the identity of the scalar-extended
chart. Cancelling the same balanced tensor over E on both sides is what
prevents an independent S-algebra action from slipping in. -/
def atIdentity (e : E →ₐ[R] R) : S ⊗[R] Fibre e ≃ₗ[S] Fibre (baseIdentity (S:=S) e) := by
  let A := S ⊗[R] E
  let eA : Algebra E A := Algebra.TensorProduct.rightAlgebra
  letI : Algebra E A := eA
  -- Do not let the augmentation of S install the *left* E-action on A.
  letI : Module E A := @Algebra.toModule E A _ _ eA
  letI : SMul E A := eA.toSMul
  let diff := KaehlerDifferential.tensorKaehlerEquiv R S E A
  letI : Algebra E R := e.toRingHom.toAlgebra
  letI : Algebra E S := (pushIdentity (S:=S) e).toRingHom.toAlgebra
  letI : Algebra A S := (baseIdentity (S:=S) e).toRingHom.toAlgebra
  letI : IsScalarTower E R S := IsScalarTower.of_algebraMap_eq fun a => rfl
  letI : IsScalarTower E A S := IsScalarTower.of_algebraMap_eq fun a =>
    (baseIdentity_onChart (S:=S) e a).symm
  let lhs := TensorProduct.AlgebraTensorModule.cancelBaseChange E R S S (KaehlerDifferential R E)
  let rhs := TensorProduct.AlgebraTensorModule.cancelBaseChange E A S S (KaehlerDifferential R E)
  exact lhs.trans (rhs.symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) diff))

/-- Literal element 1⊗da in the corresponding marked cotangent fibre. -/
@[expose] def basedDifferential (e : E →ₐ[R] R) (a : E) : Fibre e :=
  letI : Algebra E R := e.toRingHom.toAlgebra
  (1:R) ⊗ₜ[E] KaehlerDifferential.D R E a

/-- No changes of tangent parameter or unspecified scalar occur in the
identification of the same function's differential after base change. -/
theorem atIdentity_D (e : E →ₐ[R] R) (s : S) (a : E) :
    atIdentity e (s ⊗ₜ[R] basedDifferential e a) =
      s • basedDifferential (baseIdentity e) ((1:S) ⊗ₜ[R] a) := by
  simp only [atIdentity,basedDifferential,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,one_smul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    KaehlerDifferential.tensorKaehlerEquiv_tmul_D,
    Algebra.TensorProduct.right_algebraMap_apply]
  let : Algebra (S ⊗[R] E) S := (baseIdentity (S:=S) e).toRingHom.toAlgebra
  exact TensorProduct.tmul_eq_smul_one_tmul (R := S ⊗[R] E) s _

/-- Transport an actual integral identity coframe to the literal marked
cotangent of the scalar-extended chart. -/
def carried (e : E →ₐ[R] R) {ι : Type*} (b : Module.Basis ι R (Fibre e)) :
    Module.Basis ι S (Fibre (baseIdentity (S:=S) e)) :=
  (b.baseChange S).map (atIdentity e)

theorem carried_apply (e : E →ₐ[R] R) {ι : Type*}
    (b : Module.Basis ι R (Fibre e)) (i : ι) :
    carried (S:=S) e b i=atIdentity e ((1:S) ⊗ₜ[R] b i) := by
  rw [carried,Module.Basis.map_apply,Module.Basis.baseChange_apply]

theorem carried_repr (e : E →ₐ[R] R) {ι : Type*}
    (b : Module.Basis ι R (Fibre e)) (v : Fibre e) (i : ι) :
    (carried (S:=S) e b).repr (atIdentity e ((1:S) ⊗ₜ[R] v)) i=
      algebraMap R S (b.repr v i) := by
  change (b.baseChange S).repr ((atIdentity e).symm
    (atIdentity e ((1:S) ⊗ₜ[R] v))) i = _
  rw [LinearEquiv.symm_apply_apply,Module.Basis.baseChange_repr_tmul,Algebra.smul_def,mul_one]

/-- The ordered coframe matrices are literally scalar extension of the
integral matrices; in particular the order of the two bases is fixed. -/
theorem carried_matrix (e : E →ₐ[R] R) {ι : Type*} [Fintype ι]
    (b c : Module.Basis ι R (Fibre e)) :
    (carried (S:=S) e b).toMatrix (carried (S:=S) e c) =
      (b.toMatrix c).map (algebraMap R S) := by
  ext i j
  rw [Module.Basis.toMatrix_apply,carried_apply,carried_repr,Matrix.map_apply,
    Module.Basis.toMatrix_apply]

theorem carried_det (e : E →ₐ[R] R) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Module.Basis ι R (Fibre e)) :
    ((carried (S:=S) e b).toMatrix (carried (S:=S) e c)).det =
      algebraMap R S ((b.toMatrix c).det) := by
  rw [carried_matrix,RingHom.map_det,RingHom.mapMatrix_apply]
end Affine

section Receiver
variable {L A : Type*} [Field L] [NumberField L] [CommRing A] [Algebra L A]

/-- The receiver's identity fibre is the very same balanced tensor,
restricted along the same actual augmentation. -/
def receiverFibre (e : A →ₐ[L] L) :
    Fibre e ≃ₗ[L] SelectedActualSameAPlusEleven318.Cotangent e :=
  LinearEquiv.refl L _
end Receiver
end SelectedActualSameAIdentityFibreBaseChange318
