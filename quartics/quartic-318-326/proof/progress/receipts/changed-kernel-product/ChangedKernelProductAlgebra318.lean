module
public import CanonicalChangedPrimitive318
public import Mathlib.RingTheory.TensorProduct.Pi
public section
noncomputable section
namespace ChangedKernelProductAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S] [Invertible (3:S)]
local notation "R" => OpenJModel318.Base N
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "T" => ThreeTorsionAlgebra318.Ring A B hD
local notation "T'" => ThreeTorsionCoefficientMap318.Changed (S:=S) A B hD
abbrev Ring := T' × S

/-- Scalar extension of the entire kernel product algebra is the exact
mapped-coefficient primitive algebra times the unchanged target base. -/
@[expose] def equivalence : KernelScalarExtension318.ring N S ≃ₐ[S] Ring N S :=
  (Algebra.TensorProduct.prodRight R S S T R).trans
    ((ThreeTorsionBaseChange318.equivalence (S:=S) A B hD).prodCongr (Algebra.TensorProduct.rid R S S))

theorem includeRight (t:T) (r:R) : equivalence N S
    (Algebra.TensorProduct.includeRight (t,r))=
    (ThreeTorsionCoefficientMap318.coefficientMap (S:=S) A B hD t,algebraMap R S r) := by
  change ((ThreeTorsionBaseChange318.equivalence (S:=S) A B hD)
    (1 ⊗ₜ[R] t),(Algebra.TensorProduct.rid R S S) (1 ⊗ₜ[R] r))=_
  change ((ThreeTorsionBaseChange318.forward (S:=S) A B hD)
    (Algebra.TensorProduct.includeRight t),(Algebra.TensorProduct.rid R S S) (1 ⊗ₜ[R] r))=_
  rw [ThreeTorsionBaseChange318.forward_includeRight,Algebra.TensorProduct.rid_tmul,
    Algebra.smul_def,mul_one]

lemma first_projection : (RingHom.fst T' S).comp ((equivalence N S).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : LiteralKernelCoordinateRing318.Ring N →ₐ[R]
      KernelScalarExtension318.ring N S).toRingHom)=
    (ThreeTorsionCoefficientMap318.coefficientMap (S:=S) A B hD).toRingHom.comp (RingHom.fst T R) := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.fst (includeRight N S x.1 x.2)
lemma second_projection : (RingHom.snd T' S).comp ((equivalence N S).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : LiteralKernelCoordinateRing318.Ring N →ₐ[R]
      KernelScalarExtension318.ring N S).toRingHom)=
    (algebraMap R S).comp (RingHom.snd T R) := by
  apply RingHom.ext
  intro x
  exact congrArg Prod.snd (includeRight N S x.1 x.2)
end ChangedKernelProductAlgebra318
