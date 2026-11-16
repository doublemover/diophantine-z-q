module
public import PrimaryTateTower318
public import DyadicResidueInverseLimit318
public section
noncomputable section
namespace PrimaryTatePadicModule318
open PrimaryTateTower318

variable {G : Type*} [AddCommGroup G]

/-- On an element killed by q, natural coefficients reduce modulo q. -/
theorem nsmul_mod_of_annihilated (q a : ℕ) (x : G) (hx : q • x = 0) :
    (a % q) • x = a • x := by
  have hz : (q * (a / q)) • x = 0 := by
    rw [mul_nsmul, hx, nsmul_zero]
  conv_rhs => rw [← Nat.mod_add_div a q]
  rw [add_nsmul, hz, add_zero]

/-- Adjacent bounded representatives of a single 2-adic integer reduce
compatibly; the level-zero modulus is allowed to be one. -/
theorem scalar_residue_transition (a : ℤ_[2]) (n : ℕ) :
    (PadicInt.toZModPow (n+1) a).val % (2^n) = (PadicInt.toZModPow n a).val := by
  have h := congrArg (fun f : ℤ_[2] →+* ZMod (2^n) => (f a).val)
    (PadicInt.zmod_cast_comp_toZModPow n (n+1) (Nat.le_succ n))
  simpa only [RingHom.comp_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast] using h

/-- The canonical action on a genuine compatible tower is defined at
level n by the scalar residue modulo 2^n. No primary-torsion hypothesis on
the whole ambient group, and no chosen group equivalence, is needed. -/
def scalar (a : ℤ_[2]) (x : tower G) : tower G :=
  ⟨fun n => (PadicInt.toZModPow n a).val • x.val n, by
    constructor
    · intro n
      rw [smul_comm, x.property.1 n, nsmul_zero]
    · intro n
      change 2 • ((PadicInt.toZModPow (n+1) a).val • x.val (n+1)) =
        (PadicInt.toZModPow n a).val • x.val n
      rw [smul_comm, x.property.2 n,
        ← nsmul_mod_of_annihilated (2^n) _ (x.val n) (x.property.1 n),
        scalar_residue_transition]⟩

/-- The module laws are verified directly for the finite-residue action.
This definition retains the tower's existing additive group. -/
def naturalModule (G : Type*) [AddCommGroup G] : Module ℤ_[2] (tower G) where
  smul := scalar
  one_smul x := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n 1).val • x.val n = x.val n
    rw [map_one, ← Nat.cast_one, ZMod.val_natCast,
      nsmul_mod_of_annihilated (2^n) 1 _ (x.property.1 n), one_nsmul]
  mul_smul a b x := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n (a*b)).val • x.val n =
      (PadicInt.toZModPow n a).val • ((PadicInt.toZModPow n b).val • x.val n)
    rw [map_mul, ZMod.val_mul,
      nsmul_mod_of_annihilated (2^n) _ _ (x.property.1 n), mul_nsmul']
  smul_zero a := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n a).val • (0 : G) = 0
    exact nsmul_zero _
  smul_add a x y := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n a).val • (x.val n + y.val n) =
      (PadicInt.toZModPow n a).val • x.val n + (PadicInt.toZModPow n a).val • y.val n
    exact nsmul_add _ _ _
  add_smul a b x := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n (a+b)).val • x.val n =
      (PadicInt.toZModPow n a).val • x.val n + (PadicInt.toZModPow n b).val • x.val n
    rw [map_add, ZMod.val_add,
      nsmul_mod_of_annihilated (2^n) _ _ (x.property.1 n), add_nsmul]
  zero_smul x := by
    apply Subtype.ext
    funext n
    change (PadicInt.toZModPow n 0).val • x.val n = 0
    simp

/-- The defining coordinate formula remains available with the explicitly
chosen natural module instance. -/
theorem smul_coordinate (a : ℤ_[2]) (x : tower G) (n : ℕ) :
    letI := naturalModule G
    (a • x).val n = (PadicInt.toZModPow n a).val • x.val n := rfl

end PrimaryTatePadicModule318
