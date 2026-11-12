module
public import ActualTwoDescentPrimaryPadicScalar318
public section
noncomputable section
namespace ActualTwoDescentPrimaryPadicAction318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryPadicScalar318 ActualTwoDescentPrimaryScalarCongruence318
variable {A : Type} [AddCommGroup A]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance (k : ℕ) : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩

lemma actual_primary_padic_zero_scalar (hA : PrimaryTwo A) (x : A) :
    primaryPadicScalar hA 0 x=0 := by simp [primaryPadicScalar]

lemma actual_primary_padic_one_scalar (hA : PrimaryTwo A) (x : A) :
    primaryPadicScalar hA 1 x=x := by
  let k := primaryExponent hA x
  have hx : (2^k) • x=0 := actual_primary_exponent hA x
  rw [actual_primary_padic_scalar_at_level hA 1 k x hx,map_one]
  change ((1 : ZMod (2^k)).val) • x=x
  rw [show (1 : ZMod (2^k))=((1 : ℕ) : ZMod (2^k)) from rfl,
    ZMod.val_natCast,actual_nsmul_mod_annihilator _ _ x hx,one_nsmul]

lemma actual_primary_padic_add_scalar (hA : PrimaryTwo A) (a b : ℤ_[2]) (x : A) :
    primaryPadicScalar hA (a+b) x=primaryPadicScalar hA a x+primaryPadicScalar hA b x := by
  let k := primaryExponent hA x
  have hx : (2^k) • x=0 := actual_primary_exponent hA x
  rw [actual_primary_padic_scalar_at_level hA (a+b) k x hx,
    actual_primary_padic_scalar_at_level hA a k x hx,
    actual_primary_padic_scalar_at_level hA b k x hx,map_add]
  exact actual_zmod_residue_add_smul k _ _ x hx

lemma actual_primary_padic_mul_scalar (hA : PrimaryTwo A) (a b : ℤ_[2]) (x : A) :
    primaryPadicScalar hA (a*b) x=primaryPadicScalar hA a (primaryPadicScalar hA b x) := by
  let k := primaryExponent hA x
  have hx : (2^k) • x=0 := actual_primary_exponent hA x
  have hy : (2^k) • primaryPadicScalar hA b x=0 := by
    rw [actual_primary_padic_scalar_at_level hA b k x hx,nsmul_comm,hx,nsmul_zero]
  rw [actual_primary_padic_scalar_at_level hA (a*b) k x hx,
    actual_primary_padic_scalar_at_level hA a k _ hy,
    actual_primary_padic_scalar_at_level hA b k x hx,map_mul]
  exact actual_zmod_residue_mul_smul k _ _ x hx

/-- Native2-adic scalars act on any ACTUAL2-primary group, without a chosen
finite global exponent or an arbitrary transported module structure. -/
def primaryPadicEndHom (hA : PrimaryTwo A) : ℤ_[2] →+* AddMonoid.End A where
  toFun := primaryPadicEnd hA
  map_zero' := by ext x; exact actual_primary_padic_zero_scalar hA x
  map_one' := by ext x; exact actual_primary_padic_one_scalar hA x
  map_add' a b := by ext x; exact actual_primary_padic_add_scalar hA a b x
  map_mul' a b := by ext x; exact actual_primary_padic_mul_scalar hA a b x

end ActualTwoDescentPrimaryPadicAction318
