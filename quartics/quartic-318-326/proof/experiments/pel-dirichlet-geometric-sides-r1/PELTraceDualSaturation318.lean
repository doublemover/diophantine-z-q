module
public import PELTraceDualResidues318
public section
noncomputable section
namespace PELTraceDualSaturation318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318
open PELTraceDualResidues318
set_option maxHeartbeats 1000000

/-- Coordinates obtained by inverting the exact reduced-trace Gram. -/
@[expose] def dualEmbed (a b c d : ℤ) : B :=
  ⟨(a:ℚ)/2,-(b:ℚ)/420,-(a:ℚ)/10+(c:ℚ)/5,-(b:ℚ)/420+(d:ℚ)/210⟩

theorem trace_coordinates (x : B) (a b c d : ℤ)
    (h0 : reducedTrace (x*embed (basis 0))=(a:ℚ))
    (h1 : reducedTrace (x*embed (basis 1))=(b:ℚ))
    (h2 : reducedTrace (x*embed (basis 2))=(c:ℚ))
    (h3 : reducedTrace (x*embed (basis 3))=(d:ℚ)) :
    x=dualEmbed a b c d := by
  norm_num [reducedTrace,embed,basis,Pi.single_apply] at h0 h1 h2 h3
  ext <;> simp only [dualEmbed] <;> linarith

theorem norm_dual (a b c d : ℤ) :
    210*reducedNorm (dualEmbed a b c d)=(numerator a b c d:ℚ) := by
  simp [reducedNorm,dualEmbed,numerator] <;> push_cast <;> ring

/-- Norm-integrality cuts the trace dual back down to the original order.
The constructed integer coordinates exhibit membership, including the
coupled prime-five condition and both half-integral basis vectors. -/
theorem dual_integral_norm_mem (a b c d n : ℤ)
    (hn : reducedNorm (dualEmbed a b c d)=(n:ℚ)) : dualEmbed a b c d∈order := by
  have hf : numerator a b c d=210*n := by
    have hh := norm_dual a b c d
    rw [hn] at hh
    exact_mod_cast hh.symm
  have hdiv : (210:ℤ)∣numerator a b c d := ⟨n,hf⟩
  obtain ⟨⟨B,hB⟩,⟨D,hD⟩,⟨A,hA⟩⟩ := integral_norm_congruences a b c d hdiv
  have ha : a=2*c+5*A := by omega
  refine ⟨![c+3*A,2*B-D,-A,-5*B+2*D],?_⟩
  rw [ha,hB,hD]
  ext <;> simp [embed,dualEmbed] <;> push_cast <;> ring

/-- Four actual trace tests suffice; no unspecified trace-dual lattice or
maximal-order theorem is hidden in the premise. -/
theorem mem_of_integral_trace_norm (x : B)
    (htrace : ∀ i : Fin 4,∃ z : ℤ,reducedTrace (x*embed (basis i))=(z:ℚ))
    (hnorm : ∃ n : ℤ,reducedNorm x=(n:ℚ)) : x∈order := by
  obtain ⟨a,ha⟩ := htrace 0
  obtain ⟨b,hb⟩ := htrace 1
  obtain ⟨c,hc⟩ := htrace 2
  obtain ⟨d,hd⟩ := htrace 3
  obtain ⟨n,hn⟩ := hnorm
  have hx := trace_coordinates x a b c d ha hb hc hd
  rw [hx] at hn ⊢
  exact dual_integral_norm_mem a b c d n hn
end PELTraceDualSaturation318
