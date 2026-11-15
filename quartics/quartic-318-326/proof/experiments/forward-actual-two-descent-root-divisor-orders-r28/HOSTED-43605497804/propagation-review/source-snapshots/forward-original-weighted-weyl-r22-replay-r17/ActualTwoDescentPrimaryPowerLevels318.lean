module
public import ActualTwoDescentFiniteHomFibers318
public section
noncomputable section
namespace ActualTwoDescentPrimaryPowerLevels318
set_option maxHeartbeats 16000000

variable (G : Type*) [CommGroup G]

def powerLevel (k : ℕ) : Subgroup G := (powMonoidHom (α:=G) (2^k)).ker

lemma actual_power_level_mono {k l : ℕ} (h : k ≤ l) : powerLevel G k ≤ powerLevel G l := by
  intro x hx
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  change x^(2^(k+d))=1
  change x^(2^k)=1 at hx
  rw [pow_add,pow_mul,hx,one_pow]

def squareLevel (k : ℕ) : powerLevel G (k+1) →* powerLevel G k where
  toFun x := ⟨x.val^2,by
    change (x.val^2)^(2^k)=1
    rw [←pow_mul,Nat.mul_comm 2 (2^k),←pow_succ]
    exact x.property⟩
  map_one' := Subtype.ext (one_pow 2)
  map_mul' x y := Subtype.ext (mul_pow x.val y.val 2)

def squareKernelInclusion (k : ℕ) : (squareLevel G k).ker →* powerLevel G 1 where
  toFun x := ⟨x.val.val,by
    have h := congrArg Subtype.val x.property
    change x.val.val^2=1 at h
    simpa only [pow_one] using h⟩
  map_one' := rfl
  map_mul' x y := rfl

lemma actual_square_kernel_injective (k : ℕ) : Function.Injective (squareKernelInclusion G k) := by
  intro x y h
  apply Subtype.ext; apply Subtype.ext
  exact congrArg Subtype.val h

end ActualTwoDescentPrimaryPowerLevels318
