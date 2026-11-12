module
public import FormalPoleCoherentChart318
public import ValuativeOrbitMultiples318
public import ConcretePadic318
public import Mathlib.NumberTheory.Padics.ProperSpace
public section
noncomputable section
namespace ActualSplitOrbitEntry318
open ConcreteG8Domain (K D i pair)
open CoherentMultipleCharts318 (chartU chartV)
open GlobalGeneratorPoints318 (R)
open ValuativeOrbitBounds318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq ℚ_[p] := Classical.decEq ℚ_[p]

lemma nonarchimedean : IsNonarchimedean (NormedField.toAbsoluteValue ℚ_[p]) :=
  Padic.nonarchimedean

lemma root_integral (ρ : ℚ_[p]) (hρ : ρ^2=2) : ‖ρ‖≤1 := by
  have h2 := LocalDerivativeSeparation318.nat_le_one (NormedField.toAbsoluteValue ℚ_[p])
    (nonarchimedean p) 2
  have he := congrArg norm hρ
  rw [norm_pow] at he
  change ‖(2:ℚ_[p])‖≤1 at h2
  nlinarith [norm_nonneg ρ]

lemma coefficient_eq (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ConcretePadic318.embedding p ρ hρ D=(3-ρ)^2 := by
  simp only [D,map_pow,map_sub,map_ofNat,i,ConcretePadic318.embedding_pair,
    Rat.cast_zero,Rat.cast_one,zero_add,one_mul]

lemma coefficient_ne (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ConcretePadic318.embedding p ρ hρ D≠0 := by
  rw [coefficient_eq]
  apply pow_ne_zero
  intro hz
  have he : ρ=3 := (sub_eq_zero.mp hz).symm
  rw [he] at hρ
  norm_num at hρ

lemma coefficient_integral (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ‖ConcretePadic318.embedding p ρ hρ D‖≤1 := by
  rw [coefficient_eq,norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  have h3 := LocalDerivativeSeparation318.nat_le_one (NormedField.toAbsoluteValue ℚ_[p])
    (nonarchimedean p) 3
  change ‖(3:ℚ_[p])‖≤1 at h3
  simpa only [sub_eq_add_neg,norm_neg] using
    (Padic.nonarchimedean (3:ℚ_[p]) (-ρ)).trans (max_le h3 (by simpa using root_integral p ρ hρ))

lemma positive_depth (x : ℚ_[p]) (hx : ‖x‖<1) :
    (1:WithTop ℤ)≤Padic.addValuation x := by
  by_cases hz : x=0
  · simp [hz]
  · have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [Padic.norm_eq_zpow_neg_valuation hz] at hx
    have hv : -x.valuation<0 := (zpow_lt_one_iff_right₀ hp).mp hx
    rw [Padic.addValuation.apply hz]
    exact_mod_cast (show 1≤x.valuation by omega)

lemma coefficient_bound (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    Bound (ConcretePadic318.place p ρ hρ) 0 D := by
  have he := (Padic.norm_le_one_iff_val_nonneg _).mp (coefficient_integral p ρ hρ)
  change (0:WithTop ℤ)≤Padic.addValuation (ConcretePadic318.embedding p ρ hρ D)
  rw [Padic.addValuation.apply (coefficient_ne p ρ hρ)]
  exact_mod_cast he

lemma prime_bound (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    Bound (ConcretePadic318.place p ρ hρ) 1 (p:K) := by
  have he : (p:K)=pair (p:ℚ) 0 := rfl
  rw [Bound,he,ConcretePadic318.place_rational,ConcretePadic318.rational_value p _
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
    padicValRat.self (Fact.out : p.Prime).one_lt]
  exact le_rfl

/-- The entry modulus is constructed for the literal half point R and the
chosen actual p-adic embedding. It is not assumed as a reduction-order input.
Properness of Qp and the actual formal quotient supply it, even at bad reduction. -/
theorem actual_entry (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ∃ N : ℕ, 0<N ∧ Near (ConcretePadic318.place p ρ hρ) 1
      (chartU (N:ℤ)) (chartV (N:ℤ)) := by
  let φ := (ConcretePadic318.embedding p ρ hρ).toRingHom
  obtain ⟨N,hN,hformal⟩ := CompactLocalPointCoding318.orbit_entry (nonarchimedean p)
    (φ D) (coefficient_ne p ρ hρ) (coefficient_integral p ρ hρ)
    (ShortCurveBaseChange318.pointMap φ D R)
  have hmap : ShortCurveBaseChange318.pointMap φ D ((N:ℤ) • R)∈
      AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue ℚ_[p])
        (nonarchimedean p) (φ D) (coefficient_integral p ρ hρ) := by
    simpa only [map_zsmul,natCast_zsmul] using hformal
  obtain ⟨hu,hv⟩ := FormalPoleCoherentChart318.actual_chart φ
    (NormedField.toAbsoluteValue ℚ_[p]) (nonarchimedean p)
    (coefficient_integral p ρ hρ) ((N:ℤ) • R) hmap
  refine ⟨N,hN,?_⟩
  constructor
  · exact positive_depth p _ hu
  · exact positive_depth p _ hv

/-- Constructed entry followed by the proved exact oriented chart group law
supplies all precision levels at all signed multiples. No p-adic logarithm,
good-reduction assumption, or lower bound19 on the prime is used. -/
theorem actual_precision (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
      Near (ConcretePadic318.place p ρ hρ) ((e:ℤ)+1)
        (chartU ((p:ℤ)^e*N*m)) (chartV ((p:ℤ)^e*N*m)) := by
  obtain ⟨N,hN,hentry⟩ := actual_entry p ρ hρ
  exact ⟨N,hN,ValuativeOrbitMultiples318.prime_power_multiples
    (ConcretePadic318.place p ρ hρ) p (prime_bound p ρ hρ) N
    (coefficient_bound p ρ hρ) hentry⟩

/-- Both conjugate p-adic embeddings use one constructed original index.
The common entry is their product, so no coprimality or independent final
indices are inserted into later rational-coefficient recovery. -/
theorem conjugate_precision (ρ : ℚ_[p]) (hρ : ρ^2=2) :
    ∃ N : ℕ, 0<N ∧ ∀ (e : ℕ) (m : ℤ),
      Near (ConcretePadic318.place p ρ hρ) ((e:ℤ)+1)
        (chartU ((p:ℤ)^e*N*m)) (chartV ((p:ℤ)^e*N*m)) ∧
      Near (ConcretePadic318.place p (-ρ) (ConcretePadic318.negative_root p ρ hρ)) ((e:ℤ)+1)
        (chartU ((p:ℤ)^e*N*m)) (chartV ((p:ℤ)^e*N*m)) := by
  obtain ⟨N,hN,hentry⟩ := actual_entry p ρ hρ
  obtain ⟨M,hM,hentry'⟩ := actual_entry p (-ρ) (ConcretePadic318.negative_root p ρ hρ)
  have hNM := ValuativeOrbitMultiples318.near_nat (ConcretePadic318.place p ρ hρ)
    1 N (by omega) (coefficient_bound p ρ hρ) hentry M
  have hMN := ValuativeOrbitMultiples318.near_nat
    (ConcretePadic318.place p (-ρ) (ConcretePadic318.negative_root p ρ hρ))
    1 M (by omega) (coefficient_bound p (-ρ) _) hentry' N
  refine ⟨N*M,Nat.mul_pos hN hM,?_⟩
  intro e m
  constructor
  · apply ValuativeOrbitMultiples318.prime_power_multiples _ p (prime_bound p ρ hρ)
      (N*M) (coefficient_bound p ρ hρ) _ e m
    simpa only [Nat.cast_mul,mul_comm] using hNM
  · apply ValuativeOrbitMultiples318.prime_power_multiples _ p (prime_bound p (-ρ) _)
      (N*M) (coefficient_bound p (-ρ) _) _ e m
    simpa only [Nat.cast_mul] using hMN

end ActualSplitOrbitEntry318
