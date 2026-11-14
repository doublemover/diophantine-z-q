module
public import RationalScalarSupport318
public section
noncomputable section
namespace FiniteScalarCenter318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 (chartU)
open GeneratorScalarProgression318 (normCoefficient)
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Choose the genuine common index before choosing the scalar root label.
All actual norm/half-trace leaves are deep at a finite family of primes, and
64 and every earlier modulus M divide the same positive index. -/
theorem center {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (r : ℚ) (M : ℕ) (hM : 0<M) :
    ∃ h₀ : ℕ, 0<h₀ ∧ M∣h₀ ∧ 64∣h₀ ∧ ∀ i,
      padicValRat (p i) r<padicValRat (p i) (normCoefficient (chartU (h₀:ℤ))) ∧
      padicValRat (p i) r<padicValRat (p i) (2*((chartU (h₀:ℤ))^2).re) := by
  classical
  let depth := fun i => (padicValRat (p i) r).natAbs+1
  have he := fun i => GeneralScalarDepth318.scalar_leaves (p i) (depth i)
  choose L hL hdepth using he
  let J := ∏ i, L i
  let h₀ := 64*M*J
  have hJ : 0<J := Finset.prod_pos (fun i _ => hL i)
  have hh : 0<h₀ := by dsimp [h₀]; positivity
  refine ⟨h₀,hh,?_,?_,?_⟩
  · exact (dvd_mul_left M 64).trans (dvd_mul_right _ _)
  · exact (dvd_mul_right 64 M).trans (dvd_mul_right _ _)
  intro i
  have hdiv : L i∣h₀ := (Finset.dvd_prod_of_mem L (Finset.mem_univ i)).trans (dvd_mul_left J (64*M))
  obtain ⟨k,hk⟩ := hdiv
  have hk0 : k≠0 := by intro hz; rw [hz,mul_zero] at hk; omega
  have hd := hdepth i (k:ℤ) (by exact_mod_cast hk0)
  have hi : (L i:ℤ)*(k:ℤ)=(h₀:ℤ) := by rw [hk,Nat.cast_mul]
  rw [hi] at hd
  have hb : padicValRat (p i) r≤((padicValRat (p i) r).natAbs:ℤ) := by
    rw [Int.natCast_natAbs]
    exact le_abs_self _
  dsimp [depth] at hd
  push_cast at hd
  constructor <;> omega

/-- After the common index has been fixed, choose one extra scalar multiplier
that makes the translated scalar norm deep relative to the actual finite
values at that index. The free multiplier d remains available and the original
6-power, anchor3-power and label-minus-one identity are unchanged. -/
theorem label {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (r : ℚ) (h₀ A B N : ℕ) :
    ∃ J : ℕ, 0<J ∧ ∀ d : ℕ, d≠0 → ∀ i,
      2*padicValRat (p i) (normCoefficient (chartU (h₀:ℤ)))+29*padicValRat (p i) r<
      2*padicValRat (p i) (ActualScalarRoot318.inverseNorm
        (ScalarPreparedResidues318.scalarLabel A B (PreparedAnchorLabels318.multiplier N (J*d)))) := by
  classical
  let target := fun i => 2*padicValRat (p i) (normCoefficient (chartU (h₀:ℤ)))+29*padicValRat (p i) r
  let depth := fun i => (target i).natAbs+1
  have he := fun i => GeneralScalarDepth318.scalar_label (p i) A B N (depth i)
  choose L hL hdepth using he
  let J := ∏ i, L i
  have hJ : 0<J := Finset.prod_pos (fun i _ => hL i)
  refine ⟨J,hJ,?_⟩
  intro d hd i
  obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem L (Finset.mem_univ i)
  have hk0 : k≠0 := by intro hz; change J=_ at hk; rw [hz,mul_zero] at hk; omega
  have hv := hdepth i (k*d) (mul_ne_zero hk0 hd)
  have hi : L i*(k*d)=J*d := by change (∏ i, L i)=L i*k at hk; rw [hk]; ring
  rw [hi] at hv
  have hb : target i≤((target i).natAbs:ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self _
  dsimp [depth] at hv
  push_cast at hv
  change target i<_
  omega

/-- All packed scalar units are now produced at the actual center and fixed
integer/Lucas labels. The local inequalities are construction outputs, not
assumptions passed through from the final source theorem. -/
theorem center_units {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (a : ℤ) (A B N M : ℕ) (hM : 0<M) :
    ∃ h₀ J : ℕ, ∃ hJ : 0<J, 0<h₀ ∧ 64∣h₀ ∧ M∣h₀ ∧
      ∀ d : ℕ, ∀ hd : d≠0,
        let d' := PreparedAnchorLabels318.multiplier N (J*d)
        let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
          (mul_ne_zero (Nat.ne_of_gt hJ) hd)
        let labels := FixedArithmeticLabels318.labels a A B d' hd'
        ∀ i, ScalarForwardWitness318.W (DetectorGateWitness318.witness (a:ℚ) labels (h₀:ℤ)) (labels 1)≠0 ∧
          padicValRat (p i) (ScalarForwardWitness318.W
            (DetectorGateWitness318.witness (a:ℚ) labels (h₀:ℤ)) (labels 1))=0 := by
  obtain ⟨h₀,hh,hMdiv,h64,hcenter⟩ := center p (ScalarForwardWitness318.inputR (a:ℚ)) M hM
  obtain ⟨J,hJ,hlabel⟩ := label p (ScalarForwardWitness318.inputR (a:ℚ)) h₀ A B N
  refine ⟨h₀,J,hJ,hh,h64,hMdiv,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (J*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (Nat.ne_of_gt hJ) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h₀:ℤ)
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have hh0 : (h₀:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hh
  have hH : w 37≠0 := by rw [ScalarActualInputs318.detector37]; exact SeventeenScalarDepth318.norm_ne _ hh0
  have hf : w 33≠0 := by rw [ScalarActualInputs318.detector33]; exact SeventeenScalarDepth318.half_trace_ne _ hh0
  have hn := (ScalarPreparedResidues318.label_domains A B d' hd').1
  have hr : ScalarForwardWitness318.inputR (w 0)≠0 := by
    rw [hin]
    have he := ScalarForwardWitness318.integer_inputR_large a
    linarith
  intro i
  apply ScalarPackedLocalUnit318.actual_unit (p i) w (labels 1) hr hf hH
    (by change ScalarPreparedResidues318.scalarLabel A B d'≠0; omega)
    (by change ScalarPreparedResidues318.scalarLabel A B d'≠1; omega)
  · rw [hin,ScalarActualInputs318.detector37]
    exact (hcenter i).1
  · rw [hin,ScalarActualInputs318.detector33]
    exact (hcenter i).2
  · rw [hin,ScalarActualInputs318.detector37]
    exact hlabel d hd i

end FiniteScalarCenter318
