module
public import OriginalRRC45FiniteSmithCenter318
public import ActualSelectedTraceOddEvidence318
public section
noncomputable section

namespace ActualRRC45CertificateFiniteCenter318
open OriginalRRC45FiniteSmithCenter318 OriginalRCTerminalCertificate318
open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318

local instance : DecidableEq Qbar := Classical.decEq _
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The SAME terminal certificate base scalar is zero under torsion of
the SAME actual marked conductor-one trace. The remaining arithmetic
producer must supply the original scaled survivor-row reads: the same
closed projection and central boundary after the original norm, not a
new numerical scalar or unrelated distinguished point. -/
theorem sameTraceZero_of_finite_smith {b M c L : ℕ} (cert : Certificate b M c L)
    (n : ℚ) (S : Point (algebraMap ℚ Qbar n))
    {I J : Type*} [Fintype I] [Fintype J] (s : ℕ)
    (rows : ∀ a : ℕ, 0<a → a • S = 0 →
      ∀ r : ℕ, ∃ k : ℕ, r ≤ k ∧
        Nonempty (FiniteRead (ZMod (2^k)) I J a
          (PadicInt.toZModPow k ((2:ℤ_[2])^s * cert.baseLift)))) :
    IsOfFinAddOrder S → cert.central 0 = 0 := by
  intro ht
  obtain ⟨a,ha,hS⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  have hL := lift_zero_of_cofinal_reads cert.baseLift a s ha (rows a ha hS)
  have he := cert.baseScaled
  rw [hL,PadicInt.coe_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (two_ne_zero : (2:ℚ_[2]) ≠ 0))

end ActualRRC45CertificateFiniteCenter318

#print axioms ActualRRC45CertificateFiniteCenter318.sameTraceZero_of_finite_smith
