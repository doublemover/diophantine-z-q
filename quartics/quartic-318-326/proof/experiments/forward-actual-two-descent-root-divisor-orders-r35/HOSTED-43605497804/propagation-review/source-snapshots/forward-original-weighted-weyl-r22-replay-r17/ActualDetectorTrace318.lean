module
public import ActualDetectorFold318
public import ConcretePadic318
public section
noncomputable section
namespace ActualDetectorTrace318
open CircuitReplay ConcreteG8Domain ConcretePadic318 ActualDetectorFold318
open NormChainCompleteness ScaledDetectorChain318
set_option maxHeartbeats 1000000

lemma place_embedding (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2) (x : K) :
    place p rho hr x=Padic.addValuation (embedding p rho hr x) := by
  obtain ⟨a,b⟩ := x
  change place p rho hr (pair a b)=Padic.addValuation (embedding p rho hr (pair a b))
  rw [embedding_pair]
  exact place_pair p rho hr a b

lemma rational_embedding (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2) (q : ℚ) :
    rationalPlace p q=Padic.addValuation (q:ℚ_[p]) := by
  rw [←place_rational p rho hr q,place_pair]
  simp

/-- Exact reciprocal-trace identity for the source quadratic field, at the
specified opposite p-adic embeddings. -/
lemma reciprocal_trace (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (a b : ℚ) (hn : a^2-2*b^2≠0) :
    (embedding p rho hr (pair a b))⁻¹+
      (embedding p (-rho) (negative_root p rho hr) (pair a b))⁻¹=
      ((2*a/(a^2-2*b^2):ℚ):ℚ_[p]) := by
  have hnorm := norm_identity p rho hr a b
  have hn' : ((a^2-2*b^2:ℚ):ℚ_[p])≠0 := Rat.cast_ne_zero.mpr hn
  have hleft : embedding p rho hr (pair a b)≠0 := by
    intro hz
    rw [hz,zero_mul] at hnorm
    exact hn' hnorm.symm
  have hright : embedding p (-rho) (negative_root p rho hr) (pair a b)≠0 := by
    intro hz
    rw [hz,mul_zero] at hnorm
    exact hn' hnorm.symm
  have hsum : embedding p rho hr (pair a b)+
      embedding p (-rho) (negative_root p rho hr) (pair a b)=((2*a:ℚ):ℚ_[p]) := by
    simp only [embedding_pair,Rat.cast_mul,Rat.cast_ofNat]
    ring
  calc
    _ = (embedding p rho hr (pair a b)+
        embedding p (-rho) (negative_root p rho hr) (pair a b))/
        (embedding p rho hr (pair a b)*
        embedding p (-rho) (negative_root p rho hr) (pair a b)) := by
          field_simp [hleft,hright] <;> ring
    _ = _ := by rw [hnorm,hsum,Rat.cast_div]

/-- Primary successful depths and opposite-place parity produce the actual
rational inverse trace as a unit. Zero leaves remain permitted. -/
theorem actual_trace_unit (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (w : Assignment)
    (hprimary : ∀ a∈leaves w, 0<place p rho hr (a.1*a.2))
    (hopposite : ∀ a∈leaves w,
      ValuationEvenNormChain.OddAt (place p (-rho) (negative_root p rho hr)) a.1 ∧
      ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2) :
    ContactChainWitness318.value187 w≠0 ∧
    padicValRat p
      (((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2)/
        (2*ContactChainWitness318.value187 w))=0 := by
  have hnear := ActualDetectorFold318.near_one (place p rho hr) w hprimary
  have hgood := ActualDetectorFold318.good
    (place p (-rho) (negative_root p rho hr)) w hopposite
  have ha := near_one_inverse (place p rho hr) (chain w) hnear
  have hb := inverse_residue (place p (-rho) (negative_root p rho hr)) (chain w) hgood
  have h2 : Padic.addValuation (2:ℚ_[p])=0 := by
    have h := rational_nat_unit p 2 (by
      intro hdiv
      have := Nat.le_of_dvd (by norm_num : 0<2) hdiv
      omega)
    rw [rational_embedding p rho hr] at h
    simpa using h
  have ha' : 0<Padic.addValuation ((embedding p rho hr (chain w))⁻¹-1) := by
    simpa only [place_embedding,map_sub,map_inv₀,map_one] using ha
  have hb' : 0<Padic.addValuation ((embedding p (-rho) (negative_root p rho hr) (chain w))⁻¹) ∨
      0<Padic.addValuation ((embedding p (-rho) (negative_root p rho hr) (chain w))⁻¹-1) := by
    simpa only [place_embedding,map_sub,map_inv₀,map_one] using hb
  have ht := trace_unit Padic.addValuation _ _ h2 ha' hb'
  have hn : (ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2≠0 := by
    have hc : chain w≠0 := good_nonzero (place p rho hr) _ (Or.inr hnear)
    simpa only [chain,AnchorNorm318.norm_pair] using AnchorNorm318.norm_ne_zero hc
  rw [chain,reciprocal_trace p rho hr _ _ hn] at ht
  have htrace : 2*ContactChainWitness318.value187 w/
      ((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2)≠0 := by
    intro hz
    rw [hz,Rat.cast_zero,Padic.addValuation.map_zero] at ht
    exact WithTop.top_ne_coe ht
  have ha0 : ContactChainWitness318.value187 w≠0 := by
    intro hz
    apply htrace
    simp [hz]
  have hval : padicValRat p
      (2*ContactChainWitness318.value187 w/
      ((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2))=0 := by
    rw [←rational_embedding p rho hr,rational_value p _ htrace] at ht
    exact_mod_cast ht
  refine ⟨ha0,?_⟩
  have he : ((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2)/
      (2*ContactChainWitness318.value187 w)=
      (2*ContactChainWitness318.value187 w/
      ((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2))⁻¹ := by
    rw [inv_div]
  rw [he,padicValRat.inv,hval,neg_zero]

/-- Same theorem for every one of the source's fixed scaled detectors. -/
theorem scaled_trace_unit (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (w : Assignment) (c t : ℚ)
    (hprimary : ∀ a∈leaves (view w c t), 0<place p rho hr (a.1*a.2))
    (hopposite : ∀ a∈leaves (view w c t),
      ValuationEvenNormChain.OddAt (place p (-rho) (negative_root p rho hr)) a.1 ∧
      ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2) :
    realChain w c t≠0 ∧ padicValRat p (traceQuotient w c t)=0 :=
  actual_trace_unit p hp rho hr (view w c t) hprimary hopposite

end ActualDetectorTrace318
