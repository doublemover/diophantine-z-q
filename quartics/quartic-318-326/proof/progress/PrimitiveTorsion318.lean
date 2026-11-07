module
public import EllipticTorsion318
public import Mathlib.Data.Nat.GCD.Basic
public section
noncomputable section
open ModularWeierstrass318 EllipticTorsion318
namespace PrimitiveTorsion318
variable (tau : UpperHalfPlane) (N : ℕ) [NeZero N]

/-- A residue vector is primitive exactly when its two coordinates and N have gcd one. -/
@[expose] def Primitive (x : ZMod N × ZMod N) : Prop :=
  Nat.gcd N (Nat.gcd x.1.val x.2.val)=1

lemma residue_order (x : ZMod N × ZMod N) :
    addOrderOf x=N/Nat.gcd N (Nat.gcd x.1.val x.2.val) := by
  rw [Prod.addOrderOf]
  have h1 : addOrderOf x.1=N/Nat.gcd N x.1.val := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.addOrderOf_coe x.1.val (NeZero.ne N)
  have h2 : addOrderOf x.2=N/Nat.gcd N x.2.val := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.addOrderOf_coe x.2.val (NeZero.ne N)
  rw [h1,h2,Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _),
    Nat.gcd_gcd_gcd_left]

/-- Exact order of the actual elliptic point in terms of its literal period coordinates. -/
theorem point_order (x : ZMod N × ZMod N) :
    addOrderOf (torsionMap tau N x)=N/Nat.gcd N (Nat.gcd x.1.val x.2.val) := by
  rw [addOrderOf_injective (torsionMap tau N) (torsionMap_injective tau N),residue_order]

/-- Primitive period vectors are exactly the actual points of exact order N. -/
theorem point_order_eq_iff (x : ZMod N × ZMod N) :
    addOrderOf (torsionMap tau N x)=N ↔ Primitive N x := by
  rw [point_order,Nat.div_eq_self]
  simp [Primitive,NeZero.ne N]

/-- The actual primitive-torsion parametrization is a bijection, not merely an injection. -/
@[expose] def primitiveEquiv : {x : ZMod N × ZMod N // Primitive N x} ≃
    {P : (curve tau).toAffine.Point // addOrderOf P=N} :=
  Equiv.ofBijective
    (fun x => ⟨torsionMap tau N x.val,(point_order_eq_iff tau N x.val).mpr x.property⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact torsionMap_injective tau N (congrArg Subtype.val h),by
      intro P
      have hk : N • P.val=0 := by simpa only [P.property] using addOrderOf_nsmul_eq_zero P.val
      obtain ⟨x,hx⟩ := torsionMap_surjective_kernel tau N P.val hk
      have hp : Primitive N x := (point_order_eq_iff tau N x).mp (hx ▸ P.property)
      exact ⟨⟨x,hp⟩,Subtype.ext hx⟩⟩

lemma primitiveEquiv_apply (x : {x : ZMod N × ZMod N // Primitive N x}) :
    (primitiveEquiv tau N x).val=torsionMap tau N x.val := rfl

end PrimitiveTorsion318
