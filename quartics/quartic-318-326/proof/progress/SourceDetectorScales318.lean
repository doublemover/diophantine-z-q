module
public import ActualRawProductHeight318
public import RawWeights318
public import DetectorHeightTransfer318
public section
noncomputable section
namespace SourceDetectorScales318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawProductHeight318 RawWeights318 RawOddAnchorPoints318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The literal product norm is coordinate145, not a separate chosen norm. -/
lemma norm_coordinate (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    (Kprod w).norm=w 145 := by
  have hh : r106 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=106)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r106] at hh
  change AnchorNorm318.norm (pair (w 143) (w 144))=w 145
  rw [AnchorNorm318.norm_pair]
  linear_combination -hh

/-- Row107 excludes lambda=0 directly. No positivity or square premise is used. -/
lemma lambda_nonzero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    t0 S w≠0 := by
  have hh : r107 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=107)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r107] at hh
  have hm : w 38*w 146=1 := by linear_combination hh
  simpa only [t0,div_self (by norm_num : (1:ℚ)≠0),one_mul] using left_ne_zero_of_mul_eq_one hm

/-- Current compiled coordinate194 is the shifted-trace square scale. -/
lemma scale_one (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    t1 S w=((Kprod w).re+(Kprod w).norm)^2*t0 S w := by
  have h107 : r107 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=107)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h157 : r157 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=157)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r107] at h107
  dsimp only [r157] at h157
  rw [norm_coordinate S w source]
  change (1/1:ℚ)*w 194=((pair (w 143) (w 144)).re+w 145)^2*((1/1:ℚ)*w 38)
  simp only [pair]
  linear_combination w 38*h157-w 194*h107

/-- Current compiled coordinate245 is the norm square scale. -/
lemma scale_two (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    t2 S w=(Kprod w).norm^2*t0 S w := by
  have h107 : r107 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=107)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h210 : r210 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=210)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r107] at h107
  dsimp only [r210] at h210
  rw [norm_coordinate S w source]
  dsimp only [t2,t0]
  linear_combination w 38*h210-w 245*h107

lemma coefficient_one (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    A1 S w=((Kprod w).re+(Kprod w).norm)^2 := by
  rw [norm_coordinate S w source]
  dsimp only [A1,Kprod,pair]
  ring

lemma coefficient_two (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    A2 S w=(Kprod w).norm^2 := by
  rw [norm_coordinate S w source]
  dsimp only [A2]
  ring

/-- Literal three-scale height bounds imply the actual squared-root-product
upper bound with the adopted49/(8k) exponent. The three height producers
remain explicit and no case t=1 is excluded. -/
theorem source_height_upper (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (H:ℝ) (hH:1≤H) (N:ℤ) (hN:N≠0) (k:ℕ)
    (h0:NumberField.absLogHeight₁ (t0 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h1:NumberField.absLogHeight₁ (t1 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h2:NumberField.absLogHeight₁ (t2 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k))) :
    NumberField.absLogHeight₁ ((Kprod w)^2)<7*H*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  rw [scale_one S w source] at h1
  rw [scale_two S w source] at h2
  exact DetectorHeightTransfer318.actual_norm_49_over_8_height (Kprod w) (t0 S w)
    (lambda_nonzero S w source) H hH N hN k h0 h1 h2

/-- The exact source lower and upper sides now meet. Only the three named
rational contact-height bounds are supplied to this implication. -/
theorem source_index_height_comparison (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (labels:Fin 4→ℤ) (hlabels:RootLabels w labels) (hodd:∀i,Odd (labels i))
    (H:ℝ) (hH:1≤H) (N:ℤ) (hN:N≠0) (k:ℕ)
    (h0:NumberField.absLogHeight₁ (t0 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h1:NumberField.absLogHeight₁ (t1 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)))
    (h2:NumberField.absLogHeight₁ (t2 S w)≤(H+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k))) :
    (maxIndex labels:ℝ)^2-6<7*H*|(N:ℝ)|^((49:ℝ)/(8*k)) :=
  (ActualRawProductHeight318.source_max_index_lower S w source labels hlabels hodd).trans
    (source_height_upper S w source H hH N hN k h0 h1 h2)

#print axioms norm_coordinate
#print axioms lambda_nonzero
#print axioms scale_one
#print axioms scale_two
#print axioms coefficient_one
#print axioms coefficient_two
#print axioms source_height_upper
#print axioms source_index_height_comparison
end SourceDetectorScales318
