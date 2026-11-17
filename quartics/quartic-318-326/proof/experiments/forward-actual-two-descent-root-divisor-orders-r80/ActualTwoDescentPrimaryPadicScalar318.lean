module
public import ActualTwoDescentPrimaryScalarCongruence318
public section
noncomputable section
namespace ActualTwoDescentPrimaryPadicScalar318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryGeometricCocycles318
open ActualTwoDescentPrimaryScalarCongruence318 ActualTwoDescentHigherCohomologyDirectedMaps318
variable {A : Type} [AddCommGroup A]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Explicitly witnessed primary torsion, with no chosen finite global exponent. -/
def PrimaryTwo (A : Type) [AddCommGroup A] : Prop := ∀ x : A, ∃ k : ℕ, (2^k) • x=0

def primaryExponent (hA : PrimaryTwo A) (x : A) : ℕ := Nat.find (hA x)

lemma actual_primary_exponent (hA : PrimaryTwo A) (x : A) :
    (2^(primaryExponent hA x)) • x=0 := Nat.find_spec (hA x)

def primaryPadicScalar (hA : PrimaryTwo A) (a : ℤ_[2]) (x : A) : A :=
  (PadicInt.toZModPow (primaryExponent hA x) a).val • x

/-- The actual scalar is independent of the chosen annihilating level. -/
lemma actual_primary_padic_scalar_at_level (hA : PrimaryTwo A) (a : ℤ_[2])
    (k : ℕ) (x : A) (hx : (2^k) • x=0) :
    primaryPadicScalar hA a x=(PadicInt.toZModPow k a).val • x := by
  let j := max (primaryExponent hA x) k
  exact (actual_padic_residue_scalar_reduction a _ j (le_max_left _ _)
    x (actual_primary_exponent hA x)).symm.trans
    (actual_padic_residue_scalar_reduction a k j (le_max_right _ _) x hx)

lemma actual_primary_padic_scalar_zero (hA : PrimaryTwo A) (a : ℤ_[2]) :
    primaryPadicScalar hA a 0=0 := by simp [primaryPadicScalar]

lemma actual_primary_padic_scalar_add (hA : PrimaryTwo A) (a : ℤ_[2]) (x y : A) :
    primaryPadicScalar hA a (x+y)=primaryPadicScalar hA a x+primaryPadicScalar hA a y := by
  let k := max (primaryExponent hA x) (primaryExponent hA y)
  have hx : (2^k) • x=0 := actual_nsmul_power_mono (le_max_left _ _) (actual_primary_exponent hA x)
  have hy : (2^k) • y=0 := actual_nsmul_power_mono (le_max_right _ _) (actual_primary_exponent hA y)
  have hxy : (2^k) • (x+y)=0 := by rw [nsmul_add,hx,hy,zero_add]
  rw [actual_primary_padic_scalar_at_level hA a k _ hxy,
    actual_primary_padic_scalar_at_level hA a k _ hx,
    actual_primary_padic_scalar_at_level hA a k _ hy,nsmul_add]

def primaryPadicEnd (hA : PrimaryTwo A) (a : ℤ_[2]) : AddMonoid.End A where
  toFun := primaryPadicScalar hA a
  map_zero' := actual_primary_padic_scalar_zero hA a
  map_add' := actual_primary_padic_scalar_add hA a

end ActualTwoDescentPrimaryPadicScalar318
