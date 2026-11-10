module
public import DetectorPreparedThresholds318
public import PreparedAllPlaceSource318
public section
noncomputable section
namespace ThreeDetectorArithmetic318
open CircuitReplay ScaledContactWeights318 ScaledDetectorChain318 DetectorPrimeProduct318
open ConcretePadic318 ActualDetectorFold318
set_option maxHeartbeats 1000000

@[expose] def scales (labels : Fin 4 → ℤ) : Fin 3 → ℚ :=
  ![1,ThreeDetectorUniformFamily318.c₁ labels,ThreeDetectorUniformFamily318.c₂ labels]

lemma scales_ne (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (j : Fin 3) : scales labels j≠0 := by
  fin_cases j
  · norm_num [scales]
  · exact FixedDetectorScales318.sum_ne labels hn
  · exact FixedDetectorScales318.normProduct_ne labels hn

lemma real_one (w : Assignment) (t : ℚ) :
    realChain w 1 t=PoleInputWitness318.realChain w t := by
  simpa [realChain,view,scaledWeight,parameter,delta,PoleInputWitness318.realChain] using
    (ContactChainLimits318.value187_view w t).symm

lemma imag_one (w : Assignment) (t : ℚ) :
    imagChain w 1 t=PoleInputWitness318.imagChain w t := by
  simpa [imagChain,view,scaledWeight,parameter,delta,PoleInputWitness318.imagChain] using
    (ContactChainLimits318.value188_view w t).symm

lemma pole_one (w : Assignment) (t : ℚ) : poleInput w 1 t=PoleInputWitness318.poleInput w t := by
  simp only [poleInput,traceQuotient,real_one,imag_one,PoleInputWitness318.poleInput,
    PoleInputWitness318.traceQuotient,parameter,delta,one_pow,one_mul]

/-- All arithmetic conclusions below refer to exactly the stored poles190,
241,292 of the same original q,labels,h and common contact parameter. -/
lemma stored_pole (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) (j : Fin 3) :
    ThreeDetectorUniformFamily318.witness q labels h t (190+51*j.val)=
      poleInput (DetectorGateWitness318.witness q labels h) (scales labels j) t := by
  fin_cases j
  · simpa [ThreeDetectorUniformFamily318.witness,ThreeDetectorPrePole318.fill190,scales] using
      (pole_one (DetectorGateWitness318.witness q labels h) t).symm
  · simp [ThreeDetectorUniformFamily318.witness,ThreeDetectorPrePole318.fill241,scales]
  · simp [ThreeDetectorUniformFamily318.witness,ThreeDetectorPrePole318.fill292,scales]

/-- Actual primary/opposite leaf hypotheses supply the support units used
by the global denominator-parity argument. No source pole constraints are inputs. -/
theorem stored_square_denominators (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h : ℤ) (u d : ℚ) (hd : d≠0) (k : Fin 3 → Fin 5 → ℤ)
    (hk : ∀ j i, linear (scales labels j) u d i=(k j i:ℚ))
    (hkn : ∀ j i, k j i≠0)
    (hdelta : ∀ j, delta (scales labels j) (u/d^2)≠0)
    (hreal : ∀ j, realChain (DetectorGateWitness318.witness q labels h) (scales labels j) (u/d^2)≠0)
    (hsupport : ∀ j, ∀ p : ℕ, ∀ hp : p.Prime,
      0<padicValInt p (product (k j)) →
      letI : Fact p.Prime := ⟨hp⟩
      3≤p ∧ padicValRat p d=0 ∧ padicValRat p (delta (scales labels j) (u/d^2))=0 ∧
      ∃ (rho : ℚ_[p]) (hr : rho^2=2),
        (∀ a∈leaves (view (DetectorGateWitness318.witness q labels h) (scales labels j) (u/d^2)),
          0<place p rho hr (a.1*a.2)) ∧
        (∀ a∈leaves (view (DetectorGateWitness318.witness q labels h) (scales labels j) (u/d^2)),
          ValuationEvenNormChain.OddAt (place p (-rho) (negative_root p rho hr)) a.1 ∧
          ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2)) :
    ∀ j : Fin 3, IsSquare (ThreeDetectorUniformFamily318.witness q labels h (u/d^2) (190+51*j.val)).den := by
  intro j
  rw [stored_pole]
  apply DetectorDenominatorPreparation318.actual_square_denominator _ _ u d (scales_ne labels hn j)
    hd (hdelta j) (DetectorSmallPrimePreparation318.traceQuotient_ne _ _ _ (hreal j))
    (k j) (hk j) (hkn j)
  intro p hp hs
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3,hdu,hdel,rho,hr,hprim,hopp⟩ := hsupport j p hp hs
  exact ⟨(ActualDetectorTrace318.scaled_trace_unit p hp3 rho hr _ _ _ hprim hopp).2,hdu,hdel⟩

/-- One threshold for the three actual fixed-scale detectors at a given
small prime. It is fixed before the common u,d and all selected values.
The same h is retained; uniformity over a later infinite CRT orbit still
requires its actual local coefficient neighborhood and is not asserted here. -/
theorem stored_local_threshold (p : ℕ) [Fact p.Prime]
    (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (h : ℤ)
    (A : ℤ) (hA : 0≤A) :
    ∃ N : ℤ, ∀ (u d : ℚ), d≠0 → N≤padicValRat p d →
      ∀ (k : Fin 3 → Fin 5 → ℤ),
      (∀ j i, linear (scales labels j) u d i=(k j i:ℚ)) →
      (∀ j i, k j i≠0) → (∀ j i, padicValRat p (k j i:ℚ)=0) →
      (∀ j i, IsSquare (k j i:ℚ_[p])) →
      ∀ j : Fin 3,
        IsSquare ((ThreeDetectorUniformFamily318.witness q labels h (u/d^2) (190+51*j.val):ℚ):ℚ_[p]) ∧
        A≤padicValRat p (ThreeDetectorUniformFamily318.witness q labels h (u/d^2) (190+51*j.val)) := by
  obtain ⟨N,hN⟩ := DetectorPreparedThresholds318.finite_uniform p
    (fun _ => DetectorGateWitness318.witness q labels h) (scales labels) (scales_ne labels hn) A hA
  refine ⟨N,?_⟩
  intro u d hd hdepth k hk hkn hku hks j
  obtain ⟨_,_,hs,hv⟩ := hN j u d hd hdepth (k j) (hk j) (hkn j) (hku j) (hks j)
  simpa only [stored_pole] using And.intro hs hv

end ThreeDetectorArithmetic318
