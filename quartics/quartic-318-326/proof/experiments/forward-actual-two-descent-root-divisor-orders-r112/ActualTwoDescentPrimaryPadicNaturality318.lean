module
public import ActualTwoDescentPrueferPadicEndomorphisms318
public section
noncomputable section
namespace ActualTwoDescentPrimaryPadicNaturality318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryPadicScalar318
variable {A B : Type} [AddCommGroup A] [AddCommGroup B]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every actual additive map between primary groups respects the native
2-adic action; this action is not arbitrarily transported across an isomorphism. -/
lemma actual_primary_padic_natural (hA : PrimaryTwo A) (hB : PrimaryTwo B)
    (f : A →+ B) (a : ℤ_[2]) (x : A) :
    f (primaryPadicScalar hA a x)=primaryPadicScalar hB a (f x) := by
  obtain ⟨k,hk⟩ := hA x
  have hy : (2^k) • f x=0 := by rw [←map_nsmul,hk,map_zero]
  rw [actual_primary_padic_scalar_at_level hA a k x hk,
    actual_primary_padic_scalar_at_level hB a k (f x) hy,map_nsmul]

end ActualTwoDescentPrimaryPadicNaturality318
