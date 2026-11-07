module
public import SourceDetectorScales318
public section
noncomputable section
namespace ActualDetectorNondegenerate318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawProductHeight318 RawWeights318 RawOddAnchorPoints318 ActualQuadraticEmbeddings318
open SourceDetectorScales318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma embedding_norm (x:K) :
    (x.norm:ℝ)=positiveEmbedding x*negativeEmbedding x := by
  rcases x with ⟨u,v⟩
  change ((AnchorNorm318.norm (pair u v):ℚ):ℝ)=positiveEmbedding (pair u v)*negativeEmbedding (pair u v)
  rw [AnchorNorm318.norm_pair]
  simp only [positiveEmbedding,negativeEmbedding,realEmbedding_pair,mul_neg]
  push_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

lemma embedding_trace (x:K) :
    (x.re:ℝ)=(positiveEmbedding x+negativeEmbedding x)/2 := by
  rcases x with ⟨u,v⟩
  change (u:ℝ)=(positiveEmbedding (pair u v)+negativeEmbedding (pair u v))/2
  simp only [positiveEmbedding,negativeEmbedding,realEmbedding_pair,mul_neg]
  ring

/-- The actual squared root product is >1 at either real embedding, with
all four repeated occurrences retained. -/
lemma source_embedding_square_gt_one (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) (σ:K→+*ℝ) :
    1<(σ (Kprod w))^2 := by
  have hx := congrArg σ (source_squared_product S w source labels hlabels)
  rw [map_pow,map_prod,Fin.prod_univ_four] at hx
  have h (i:Fin 4) : 1<σ (((labels i) • P).xRep 0) :=
    RealMultiples318.multiple_P_abscissa_gt_one σ (labels i)
      (root_labels_nonzero w labels hlabels i)
  rw [hx]
  exact one_lt_mul (one_lt_mul (one_lt_mul (h 0).le (h 1)).le (h 2)).le (h 3)

lemma source_embedding_abs_gt_one (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) (σ:K→+*ℝ) :
    1 < |σ (Kprod w)| := by
  have hh := source_embedding_square_gt_one S w source labels hlabels σ
  nlinarith [sq_abs (σ (Kprod w)),abs_nonneg (σ (Kprod w))]

/-- Elementary strict norm/half-trace separation when both conjugates have
absolute value>1. It allows arbitrary signs of the conjugates. -/
lemma norm_gt_trace (a b:ℝ) (ha:1 < |a|) (hb:1 < |b|) :
    |(a+b)/2| < |a*b| := by
  rw [abs_div,abs_mul]
  norm_num
  have hab := abs_add_le a b
  have hp := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  nlinarith

lemma source_norm_gt_real_part (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) :
    |((Kprod w).re:ℝ)| < |((Kprod w).norm:ℝ)| := by
  rw [embedding_trace,embedding_norm]
  exact norm_gt_trace _ _
    (source_embedding_abs_gt_one S w source labels hlabels positiveEmbedding)
    (source_embedding_abs_gt_one S w source labels hlabels negativeEmbedding)

lemma source_norm_nonzero (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) : (Kprod w).norm≠0 := by
  intro hz
  have hh := source_norm_gt_real_part S w source labels hlabels
  rw [hz,Rat.cast_zero,abs_zero] at hh
  exact (not_lt_of_ge (abs_nonneg _)) hh

lemma source_shifted_trace_nonzero (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) : (Kprod w).re+(Kprod w).norm≠0 := by
  intro hz
  have hh := source_norm_gt_real_part S w source labels hlabels
  have he : (Kprod w).re= -(Kprod w).norm := by linear_combination hz
  rw [he,Rat.cast_neg,abs_neg] at hh
  exact (lt_irrefl _) hh

lemma source_coefficients_nonzero (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) :
    A0 S w≠0 ∧ A1 S w≠0 ∧ A2 S w≠0 := by
  refine ⟨by norm_num [A0],?_,?_⟩
  · rw [coefficient_one S w source]
    exact pow_ne_zero _ (source_shifted_trace_nonzero S w source labels hlabels)
  · rw [coefficient_two S w source]
    exact pow_ne_zero _ (source_norm_nonzero S w source labels hlabels)

/-- Fused source equality excludes every contact-polynomial root. No
positivity/square hypothesis is needed, and t=1 is allowed. -/
lemma contact_nonzero_of_fused (e A t:ℚ) (hA:A≠0)
    (he:e*contactPolynomial t=(A*(t-1))^5) : contactPolynomial t≠0 := by
  intro hf
  have hp : (A*(t-1))^5=0 := by rw [←he,hf,mul_zero]
  have hm : A*(t-1)=0 := (eq_zero_of_pow_eq_zero hp)
  have ht : t=1 := by
    have hd := (mul_eq_zero.mp hm).resolve_left hA
    linear_combination hd
  norm_num [ht,contactPolynomial] at hf

lemma source_contacts_nonzero (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (labels:Fin 4→ℤ)
    (hlabels:RootLabels w labels) :
    contactPolynomial (t0 S w)≠0 ∧ contactPolynomial (t1 S w)≠0 ∧
      contactPolynomial (t2 S w)≠0 := by
  obtain ⟨hA0,hA1,hA2⟩ := source_coefficients_nonzero S w source labels hlabels
  have h0 := eF0_source S w source
  have h1 := eF1_source S w source
  have h2 := eF2_source S w source
  rw [F0_actual S w source] at h0
  rw [F1_actual S w source] at h1
  rw [F2_actual S w source] at h2
  exact ⟨contact_nonzero_of_fused _ _ _ hA0 h0,
    contact_nonzero_of_fused _ _ _ hA1 h1,contact_nonzero_of_fused _ _ _ hA2 h2⟩

lemma five_factors_nonzero (t:ℚ) (hf:contactPolynomial t≠0) :
    t≠0 ∧ t+1/2≠0 ∧ t+1≠0 ∧ t-1/2399≠0 ∧ t+32/407≠0 := by
  simpa only [contactPolynomial,mul_ne_zero_iff,and_assoc] using hf

#print axioms embedding_norm
#print axioms embedding_trace
#print axioms source_embedding_square_gt_one
#print axioms source_embedding_abs_gt_one
#print axioms norm_gt_trace
#print axioms source_norm_gt_real_part
#print axioms source_norm_nonzero
#print axioms source_shifted_trace_nonzero
#print axioms source_coefficients_nonzero
#print axioms contact_nonzero_of_fused
#print axioms source_contacts_nonzero
#print axioms five_factors_nonzero
end ActualDetectorNondegenerate318
