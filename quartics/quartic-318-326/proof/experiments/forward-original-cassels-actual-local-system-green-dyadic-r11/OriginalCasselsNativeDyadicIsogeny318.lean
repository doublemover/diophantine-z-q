module
public import OriginalCasselsLiteralIsogenyAddition318
public import OriginalCasselsDyadicCokernel318
public section

noncomputable section

namespace OriginalCasselsNativeDyadicIsogeny318

open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralIsogenyAddition318
open OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open OriginalCasselsTargetClassChord318 OriginalCasselsDyadicClassUpper318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq (ℚ_[2]) := Classical.decEq _

/-- The actual fixed additive point map on Q₂. The only input is
finiteness of its literal range quotient, not the size of that quotient. -/
def dyadic (n : ℕ) (hn : 0<n)
    (hf : Finite (TargetPoint (n:ℚ_[2]) ⧸
      (literalHom (literal_addition (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))).range)) :
    LocalIsogeny (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') :=
  localIsogeny (literal_addition (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne')) hf

theorem dyadic_cokernel_card (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (hf : Finite (TargetPoint (n:ℚ_[2]) ⧸
      (literalHom (literal_addition (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))).range)) :
    (dyadic n hn hf).cokernelCard=2 :=
  actual_dyadic_cokernel_two n hn hr (dyadic n hn hf)
    (actual_target_class_product (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))
    (actual_dyadic_class_upper n hn hr)

end OriginalCasselsNativeDyadicIsogeny318

#print axioms OriginalCasselsNativeDyadicIsogeny318.dyadic_cokernel_card
