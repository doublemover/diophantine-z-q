module
public import OriginalCasselsDyadicClassUpper318
public import OriginalCasselsTargetClassChord318
public section

noncomputable section

namespace OriginalCasselsDyadicCokernel318

open OriginalSelectedCasselsParity318 OriginalCasselsDyadicClassUpper318
open OriginalCasselsTargetClassChord318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq (ℚ_[2]) := Classical.decEq _

/-- The exact dyadic row for the same actual isogeny. Independent chord
and upper-class proofs eliminate both intermediate arithmetic inputs. -/
theorem local_system_two_size (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (L : LocalSystem n hn) : L.finiteCokernelCard 2 Nat.prime_two=2 :=
  local_system_two_size_of_chord n hn hr L
    (actual_target_class_product (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne'))

end OriginalCasselsDyadicCokernel318

#print axioms OriginalCasselsDyadicCokernel318.local_system_two_size
