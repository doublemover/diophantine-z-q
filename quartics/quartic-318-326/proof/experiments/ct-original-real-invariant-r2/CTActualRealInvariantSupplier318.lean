module
public import CTRealNativeInvariant318
public import CTActualCorrectedGlobalValue318
import all CTActualCorrectedGlobalValue318
public section
noncomputable section

namespace CTActualRealInvariantSupplier318

open CTActualGlobalReciprocity318 CTActualCorrectedGlobalValue318
open CTContinuousFieldHTwo318 CTLocalInvariantDescent318 CTRealNativeInvariant318

local instance (p : PrimePlace) : Fact p.val.Prime := ⟨p.property⟩
local instance (p : PrimePlace) : DecidableEq ℚ_[p.val] := Classical.decEq _
local instance : DecidableEq ℝ := Classical.decEq _

/-- The real invariant is no longer arithmetic input. Supplying
the remaining p-adic comparison gives the actual local maps used
by the global-value adapter. It still needs canonical finite-place
normalization, and global reciprocity is separate. -/
def invariantIsomorphisms
    (finite : (p : PrimePlace) → ContH2 ℚ_[p.val] ≃+ InvValues) : ArithmeticInvariantIsomorphisms :=
  ⟨actualRealInvariantEquiv,finite⟩

end CTActualRealInvariantSupplier318
