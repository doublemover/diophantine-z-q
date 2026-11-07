module

public import PrimitiveTorsion318
public import InvariantRegularSplit318
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace PrimitiveDiamond318

variable (N : ℕ) [NeZero N]

/-- The existing exact primitive-torsion predicate supplies an actual Bezout pair. -/
theorem primitive_bezout (x : ZMod N × ZMod N) (hx : PrimitiveTorsion318.Primitive N x) :
    ∃ a b : ZMod N, a*x.1+b*x.2=1 := by
  have h1 := Nat.gcd_eq_gcd_ab N (Nat.gcd x.1.val x.2.val)
  rw [show Nat.gcd N (Nat.gcd x.1.val x.2.val)=1 from hx] at h1
  have h2 := Nat.gcd_eq_gcd_ab x.1.val x.2.val
  have h1' := congrArg (fun z : ℤ => (z : ZMod N)) h1
  have h2' := congrArg (fun z : ℤ => (z : ZMod N)) h2
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, zero_add] at h1'
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h2'
  refine ⟨(Nat.gcdA x.1.val x.2.val : ZMod N)*Nat.gcdB N (Nat.gcd x.1.val x.2.val),
    (Nat.gcdB x.1.val x.2.val : ZMod N)*Nat.gcdB N (Nat.gcd x.1.val x.2.val), ?_⟩
  rw [h2'] at h1'
  linear_combination -h1'

/-- Conversely an actual Bezout pair gives the same existing gcd predicate. -/
theorem primitive_of_bezout (x : ZMod N × ZMod N)
    (hx : ∃ a b : ZMod N, a*x.1+b*x.2=1) : PrimitiveTorsion318.Primitive N x := by
  obtain ⟨a,b,hab⟩ := hx
  let d := Nat.gcd N (Nat.gcd x.1.val x.2.val)
  have hdN : (d:ℤ) ∣ N := by exact_mod_cast Nat.gcd_dvd_left N (Nat.gcd x.1.val x.2.val)
  have hdm : (d:ℤ) ∣ (x.1.val:ℤ) := by
    exact_mod_cast dvd_trans (Nat.gcd_dvd_right N _) (Nat.gcd_dvd_left x.1.val x.2.val)
  have hdn : (d:ℤ) ∣ (x.2.val:ℤ) := by
    exact_mod_cast dvd_trans (Nat.gcd_dvd_right N _) (Nat.gcd_dvd_right x.1.val x.2.val)
  have hz : (((a.val:ℤ)*x.1.val+(b.val:ℤ)*x.2.val-1:ℤ):ZMod N)=0 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_one, ZMod.natCast_zmod_val] using sub_eq_zero.mpr hab
  have hN := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hz
  have hdK : (d:ℤ) ∣ (a.val:ℤ)*x.1.val+(b.val:ℤ)*x.2.val :=
    dvd_add (dvd_mul_of_dvd_right hdm _) (dvd_mul_of_dvd_right hdn _)
  have hd1 : (d:ℤ) ∣ 1 := by
    have h := dvd_sub hdK (dvd_trans hdN hN)
    convert h using 1; ring
  have hd1' : d ∣ 1 := by exact_mod_cast hd1
  exact Nat.eq_one_of_dvd_one hd1'

theorem primitive_iff_bezout (x : ZMod N × ZMod N) :
    PrimitiveTorsion318.Primitive N x ↔ ∃ a b : ZMod N, a*x.1+b*x.2=1 :=
  ⟨primitive_bezout N x, primitive_of_bezout N x⟩

abbrev Points := {x : ZMod N × ZMod N // PrimitiveTorsion318.Primitive N x}

/-- The literal scalar diamond action on the two residue coordinates. -/
def scalar (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) : ZMod N × ZMod N :=
  ((u:ZMod N)*x.1, (u:ZMod N)*x.2)

theorem primitive_scalar (u : (ZMod N)ˣ) (x : Points N) :
    PrimitiveTorsion318.Primitive N (scalar N u x.1) := by
  obtain ⟨a,b,hab⟩ := primitive_bezout N x.1 x.property
  apply primitive_of_bezout
  refine ⟨a*(↑u⁻¹:ZMod N), b*(↑u⁻¹:ZMod N), ?_⟩
  change a*(↑u⁻¹:ZMod N)*((u:ZMod N)*x.1.1)+
    b*(↑u⁻¹:ZMod N)*((u:ZMod N)*x.1.2)=1
  calc
    _ = a*((↑u⁻¹:ZMod N)*(u:ZMod N))*x.1.1+
      b*((↑u⁻¹:ZMod N)*(u:ZMod N))*x.1.2 := by ring
    _ = 1 := by rw [Units.inv_mul]; simpa using hab

instance scalarAction : MulAction (ZMod N)ˣ (Points N) where
  smul u x := ⟨scalar N u x.1, primitive_scalar N u x⟩
  one_smul x := by
    apply Subtype.ext
    change scalar N 1 x.1=x.1
    exact Prod.ext (by simp [scalar]) (by simp [scalar])
  mul_smul u v x := by
    apply Subtype.ext
    change scalar N (u*v) x.1=scalar N u (scalar N v x.1)
    exact Prod.ext (by simp [scalar, mul_assoc]) (by simp [scalar, mul_assoc])

@[simp] theorem scalarAction_val (u : (ZMod N)ˣ) (x : Points N) :
    (u • x).1 = scalar N u x.1 := rfl

/-- The scalar diamond action on actual primitive residue pairs is free. -/
instance scalarFree : IsCancelSMul (ZMod N)ˣ (Points N) where
  toIsLeftCancelSMul := inferInstance
  right_cancel' u v x h := by
    apply Units.ext
    obtain ⟨a,b,hab⟩ := primitive_bezout N x.1 x.property
    have h1 := congrArg (fun y : Points N => y.1.1) h
    have h2 := congrArg (fun y : Points N => y.1.2) h
    change (u:ZMod N)*x.1.1=(v:ZMod N)*x.1.1 at h1
    change (u:ZMod N)*x.1.2=(v:ZMod N)*x.1.2 at h2
    linear_combination a*h1+b*h2+((v:ZMod N)-(u:ZMod N))*hab

/-- Every actual diamond subgroup inherits the proved free action. -/
instance subgroupFree (H : Subgroup (ZMod N)ˣ) : IsCancelSMul H (Points N) where
  toIsLeftCancelSMul := inferInstance
  right_cancel' u v x h := Subtype.ext (IsCancelSMul.right_cancel (u:(ZMod N)ˣ) v x h)

theorem scalar_eq_nsmul (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) :
    scalar N u x = (u:ZMod N).val • x := by
  ext <;> simp [scalar, nsmul_eq_mul]

/-- The coordinate action is the actual multiplication action on the actual elliptic point. -/
theorem actual_point_scalar (tau : UpperHalfPlane) (u : (ZMod N)ˣ) (x : Points N) :
    EllipticTorsion318.torsionMap tau N (u • x).1 =
      (u:ZMod N).val • EllipticTorsion318.torsionMap tau N x.1 := by
  rw [scalarAction_val, scalar_eq_nsmul, map_nsmul]

/-- Freeness on every actual elliptic point of exact order N, not only on labels. -/
theorem actual_point_free (tau : UpperHalfPlane)
    (P : (ModularWeierstrass318.curve tau).toAffine.Point) (hP : addOrderOf P=N)
    (u v : (ZMod N)ˣ) (h : (u:ZMod N).val • P = (v:ZMod N).val • P) : u=v := by
  obtain ⟨x, hx⟩ := (PrimitiveTorsion318.primitiveEquiv tau N).surjective ⟨P,hP⟩
  have hx' : EllipticTorsion318.torsionMap tau N x.1=P := congrArg Subtype.val hx
  apply IsCancelSMul.right_cancel u v x
  apply Subtype.ext
  apply EllipticTorsion318.torsionMap_injective tau N
  simpa only [actual_point_scalar, hx'] using h

section Quotient
open TensorProduct InvariantBaseChange318
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
variable (H : Subgroup (ZMod N)ˣ)

/-- The primitive-marking torsor needs no supplied freeness premise. -/
def primitiveTorsorEquiv (ρ : H → B ≃ₐ[R] B)
    (e : S ⊗[R] B ≃ₐ[S] (Points N → S))
    (he : ∀ (g : H) (b : S ⊗[R] B) (x : Points N),
      e (baseAction S ρ g b) x = e b (g • x)) :
    B ⊗[invariants ρ] B ≃ₐ[invariants ρ] (H → B) := by
  letI := Fintype.ofFinite H
  exact InvariantRegularSplit318.invariantTorsorEquiv S ρ e he

@[simp] theorem primitiveTorsorEquiv_tmul (ρ : H → B ≃ₐ[R] B)
    (e : S ⊗[R] B ≃ₐ[S] (Points N → S))
    (he : ∀ (g : H) (b : S ⊗[R] B) (x : Points N),
      e (baseAction S ρ g b) x = e b (g • x)) (b c : B) (g : H) :
    primitiveTorsorEquiv N S H ρ e he (b ⊗ₜ[invariants ρ] c) g = b*ρ g c := rfl

end Quotient

end PrimitiveDiamond318
