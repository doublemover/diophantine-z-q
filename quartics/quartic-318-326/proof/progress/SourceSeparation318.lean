module
public import SourceMaxIndexHeight318
public import SoundnessHeight318
public section
noncomputable section
namespace SourceSeparation318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318
open RawOddAnchorPoints318 RawProductHeight318 HeightSeparation318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The two sign choices for the actual scalar label become exactly the two
absolute orientations consumed by the final numerical separation theorem. -/
lemma scalar_orientation (labels:Fin 4→ℤ) (c:ℤ)
    (hc:c=labels 1-1 ∨ c= -labels 1-1) :
    (c.natAbs:ℝ)=|(labels 1:ℝ)-1| ∨ (c.natAbs:ℝ)=|(labels 1:ℝ)+1| := by
  have he : (c.natAbs:ℝ)=|(c:ℝ)| := by simp
  rw [he]
  rcases hc with hc|hc
  · left
    have hc' : (c:ℝ)=(labels 1:ℝ)-1 := by exact_mod_cast hc
    rw [hc']
  · right
    have hc' : (c:ℝ)= -((labels 1:ℝ)+1) := by exact_mod_cast (show c= -(labels 1+1) by omega)
    rw [hc',abs_neg]

/-- Actual anchor divisibility and a nonzero scalar point give the original
anchor lower bound in the real normalization used by separation. -/
lemma scalar_anchor_size (c:ℤ) (hc:c≠0) (hdiv:(2*3^32767:ℤ)∣c) :
    (2:ℝ)*3^32767≤(c.natAbs:ℝ) := by
  have hn := Int.natAbs_le_of_dvd_ne_zero hdiv hc
  have hnat : 2*3^32767≤c.natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_pow,
      show Int.natAbs (2:ℤ)=2 by decide,show Int.natAbs (3:ℤ)=3 by decide] using hn
  exact_mod_cast hnat

/-- These are precisely the four still-separate analytic comparisons needed
by the checked numerical theorem. This structure is an explicit interface,
not a claim that its fields follow from the source constraints here. -/
structure RemainingComparisons (q:ℚ) (labels:Fin 4→ℤ) (c:ℤ) : Prop where
  high : lucasResidual (labels 1) (labels 2) (labels 3)≠0 →
    (maxIndex labels:ℝ)^2-6<7*heightConstant*
      |lucasResidual (labels 1) (labels 2) (labels 3)|^((49:ℝ)/104)
  lucas : lucasResidual (labels 1) (labels 2) (labels 3)=0 →
    |(labels 1:ℝ)|-3<Real.log (maxIndex labels:ℝ)
  scalar : ZInQ.rationalLogHeight (3723*(2*q+1)^2)≤
    heightConstant*(c.natAbs:ℝ)^((49:ℝ)/64)
  low : 3723*(2*q+1)^2≠(labels 0:ℚ) →
    (maxIndex labels:ℝ)^2-6<7*heightConstant*
      (((3723*(2*q+1)^2-(labels 0:ℚ)).num.natAbs:ℝ)^((49:ℝ)/32))

/-- End-to-end numerical join for the actual root/scalar labels. All oddness,
size, maximum, anchor and sign-orientation premises are explicitly proved;
only the four named comparisons are supplied. -/
theorem integer_input_of_actual_labels (q:ℚ) (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Fin 4→ℤ) (c:ℤ)
    (hlabels:RootLabels w labels) (hscalar:ScalarLabel w c)
    (horient:c=labels 1-1 ∨ c= -labels 1-1) (hdiv:(2*3^32767:ℤ)∣c)
    (hlarge:(2:ℝ)^49151<(c.natAbs:ℝ)) (h:RemainingComparisons q labels c) :
    ∃x:ℤ,(x:ℚ)=q := by
  have hodd := source_odd_labels w source labels c hlabels hscalar
  have hc0 := scalar_label_nonzero w c hscalar
  have hc4 : 4<(c.natAbs:ℝ) := by
    have hh : (4:ℝ)≤2^49151 := by
      calc
        (4:ℝ)=2^2 := by norm_num
        _≤2^49151 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact hh.trans_lt hlarge
  exact integer_input_from_height_and_group_data q (labels 0) (labels 1) (labels 2) (labels 3)
    (maxIndex labels:ℝ) (c.natAbs:ℝ) (hodd 0)
    (three_le_maxIndex_of_scalar_bound labels c horient hc4)
    (label_abs_le_maxIndex labels 0) (label_abs_le_maxIndex labels 1)
    (label_abs_le_maxIndex labels 2) (label_abs_le_maxIndex labels 3)
    (scalar_orientation labels c horient) (scalar_anchor_size c hc0 hdiv)
    h.high h.lucas h.scalar h.low

/-- The source input coordinate is w0. Actual global labels are produced from
the literal constraints; the only remaining producer obligations are the
four named comparisons for those actual labels. -/
theorem source_integer_input_of_comparisons (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (hcomparisons:∀(labels:Fin 4→ℤ)(c:ℤ), RootLabels w labels → ScalarLabel w c →
      (c=labels 1-1 ∨ c= -labels 1-1) → (2*3^32767:ℤ)∣c →
      (2:ℝ)^49151<(c.natAbs:ℝ) → RemainingComparisons (w 0) labels c) :
    ∃x:ℤ,(x:ℚ)=w 0 := by
  obtain ⟨labels,c,n,τ,hlabels,hscalar,_,horient,hdiv,hlarge,_⟩ :=
    ActualGlobalGenerator318.source_global_labels w source
  exact integer_input_of_actual_labels (w 0) w source labels c hlabels hscalar horient hdiv hlarge
    (hcomparisons labels c hlabels hscalar horient hdiv hlarge)

#print axioms scalar_orientation
#print axioms scalar_anchor_size
#print axioms integer_input_of_actual_labels
#print axioms source_integer_input_of_comparisons
end SourceSeparation318
