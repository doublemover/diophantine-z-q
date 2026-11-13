module
public import ActualTwoDescentActualHOneConnecting318
public section
noncomputable section
namespace ActualTwoDescentSquareOneUnits318
set_option maxHeartbeats 16000000

abbrev SquareOne (K : Type*) [Field K] := (powMonoidHom (α:=Kˣ) 2).ker
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

lemma square_one_value (u : SquareOne K) : ((u : Kˣ) : K)^2=1 := by
  have h := congrArg (fun v : Kˣ => (v : K)) u.property
  simpa only [MonoidHom.mem_ker,powMonoidHom_apply,Units.val_pow_eq_pow_val,Units.val_one] using h

def negativeOne : SquareOne K := ⟨-1,by
  change (-1 : Kˣ)^2=1
  simp⟩

lemma actual_square_one_cases (u : SquareOne K) : u=1 ∨ u=negativeOne := by
  have h := square_one_value u
  have he : (((u : Kˣ) : K)-1)*(((u : Kˣ) : K)+1)=0 := by linear_combination h
  rcases mul_eq_zero.mp he with hm|hp
  · left; apply Subtype.ext; apply Units.ext
    exact sub_eq_zero.mp hm
  · right; apply Subtype.ext; apply Units.ext
    change ((u : Kˣ) : K)= -1
    linear_combination hp

lemma actual_square_one_aut_fixed {F : Type*} [Field F] [Algebra F K] (σ : K ≃ₐ[F] K) (u : SquareOne K) :
    σ ((u : Kˣ) : K)=((u : Kˣ) : K) := by
  rcases actual_square_one_cases u with rfl|rfl
  · simp only [OneMemClass.coe_one,Units.val_one,map_one]
  · change σ (-1)= -1
    rw [map_neg,map_one]

end ActualTwoDescentSquareOneUnits318
