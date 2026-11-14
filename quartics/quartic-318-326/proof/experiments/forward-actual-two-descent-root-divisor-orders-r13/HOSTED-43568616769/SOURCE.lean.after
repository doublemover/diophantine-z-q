module
public import ScalarPoleRealDomain318
public section
noncomputable section
namespace ScalarActualInputs318
open CircuitReplay ConcreteG8Domain CoherentMultipleCharts318
open GeneratorScalarProgression318 (normCoefficient)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma detector33 (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    DetectorGateWitness318.witness q labels h 33=((chartU h)^2).re := by
  simp [DetectorGateWitness318.witness,DetectorGateWitness318.fill,ActualPadeRatios318.witness,
    PadeRatioWitness318.fill,ActualPadeRatios318.base,CoherentMultiplePrefix318.witness,
    RealGuardWitness318.fill,CompressedAnchorWitness318.fill]
lemma detector37 (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    DetectorGateWitness318.witness q labels h 37=normCoefficient (chartU h) := by
  simp [DetectorGateWitness318.witness,DetectorGateWitness318.fill,ActualPadeRatios318.witness,
    PadeRatioWitness318.fill,ActualPadeRatios318.base,CoherentMultiplePrefix318.witness,
    RealGuardWitness318.fill,CompressedAnchorWitness318.fill,normCoefficient]
lemma detector118 (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    DetectorGateWitness318.witness q labels h 118=q^2 := by
  simp [DetectorGateWitness318.witness,DetectorGateWitness318.fill,DetectorGateWitness318.value118,
    ActualPadeRatios318.witness_input,pow_two]

lemma common_bounds (h : ℤ) :
    0≤((chartU h)^2).re ∧ ((chartU h)^2).re≤1 ∧ |normCoefficient (chartU h)|≤1 := by
  have hp : |ActualQuadraticEmbeddings318.positiveEmbedding (chartU h)|≤1 := by
    simpa [RealQuarticAmbient318.orbit,RealQuarticAmbient318.embedding,
      CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.parameters,Fin.append_left] using
      RealQuarticAmbient318.coordinate_bound (RealQuarticAmbient318.orbit_mem (fun _ => 1) h) ((0 : Fin 4).castAdd 4) 0 0
  have hm : |ActualQuadraticEmbeddings318.negativeEmbedding (chartU h)|≤1 := by
    simpa [RealQuarticAmbient318.orbit,RealQuarticAmbient318.embedding,
      CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.parameters,Fin.append_left] using
      RealQuarticAmbient318.coordinate_bound (RealQuarticAmbient318.orbit_mem (fun _ => 1) h) ((0 : Fin 4).castAdd 4) 1 0
  have hp2 := (sq_le_one_iff_abs_le_one _).mpr hp
  have hm2 := (sq_le_one_iff_abs_le_one _).mpr hm
  have he : (((chartU h)^2).re:ℝ)=
      ((ActualQuadraticEmbeddings318.positiveEmbedding (chartU h))^2+
        (ActualQuadraticEmbeddings318.negativeEmbedding (chartU h))^2)/2 := by
    have hpPow := map_pow ActualQuadraticEmbeddings318.positiveEmbedding (chartU h) 2
    have hmPow := map_pow ActualQuadraticEmbeddings318.negativeEmbedding (chartU h) 2
    simpa only [RealDetectorRatios318.re,RealQuarticAmbient318.embedding,ite_true,
      show (1:Fin 2)≠0 by decide,ite_false,hpPow,hmPow] using
      (RealDetectorRatios318.re_embedding ((chartU h)^2)).symm
  have hf0 : (0:ℝ)≤(((chartU h)^2).re:ℝ) := by rw [he]; positivity
  have hf1 : (((chartU h)^2).re:ℝ)≤1 := by rw [he]; linarith
  have hnorm : |(normCoefficient (chartU h):ℝ)|≤1 := by
    rw [←GeneratorScalarProgression318.embedding_product,abs_mul]
    exact (mul_le_mul hp hm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  exact ⟨by exact_mod_cast hf0,by exact_mod_cast hf1,by exact_mod_cast hnorm⟩

/-- Filling all three contact chains and pole certificates preserves the
original scalar inputs and fixed signed root coordinates exactly. -/
lemma preserved_slots (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ)
    (C₀ : NormalizedPolePoints318.Certificate (ThreeDetectorUniformFamily318.witness q labels h t 190))
    (C₁ : NormalizedPolePoints318.Certificate (ThreeDetectorUniformFamily318.witness q labels h t 241))
    (C₂ : NormalizedPolePoints318.Certificate (ThreeDetectorUniformFamily318.witness q labels h t 292)) :
    ∀ i∈([0,33,37,82,83,118,145] : List ℕ),
      ThreePoleCertificates318.fill (ThreeDetectorUniformFamily318.witness q labels h t) C₀ C₁ C₂ i=
        DetectorGateWitness318.witness q labels h i := by
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [ThreePoleCertificates318.fill,ThreeDetectorUniformFamily318.witness,ThreeDetectorPrePole318.fill,
      ScaledDetectorChain318.fill,ScaledContactWeights318.fill,PoleInputWitness318.fill,
      ContactChainWitness318.fill,ContactWeightWitness318.fill]

lemma detector_root (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (h : ℤ)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    pair (DetectorGateWitness318.witness q labels h 82)
      (DetectorGateWitness318.witness q labels h 83)=fixedRoot (labels 1) := by
  have he := FixedDetectorScales318.source_root q labels h 1
  norm_num at he
  simpa [DetectorGateWitness318.witness,DetectorGateWitness318.fill] using
    he.trans (CoherentRootSign318.emitted_root_fixed labels h 1 (hn 1)
      (((CoherentMultiplePrefix318.guards_iff labels h).mpr hg) 1))

end ScalarActualInputs318
