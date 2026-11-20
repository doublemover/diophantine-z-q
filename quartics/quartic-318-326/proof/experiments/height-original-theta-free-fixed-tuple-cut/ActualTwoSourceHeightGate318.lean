module
public import CleanSparseHeightCut318
public import LiteralSoundness318326
import all CleanSparseHeightCut318
import all Current318FinalPolynomial
public section
noncomputable section
namespace ActualTwoSourceHeightGate318
open CircuitReplay Raw318FinalReplay RawWeights318 NumberField
open ContactRadical318 ContactHeight318 DetectorContactMap318 ConsumedContactHeight318
open SourceLabelData318 SourceContactDivisibility318 SourceContactContracts318 HeightSeparation318
open RawProductHeight318 SourceHeightComparisons318
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

abbrev scale : ℚ := (3:ℚ)^65536
abbrev Source (w:Assignment) : Prop := Constraints (stage0 scale) w
def score (t:ℚ) : ℕ := max t.num.natAbs t.den
def bigger (a b:ℚ) : ℚ := if score a < score b then b else a
def winner (w:Assignment) : ℚ := bigger (bigger (t0 scale w) (t1 scale w)) (t2 scale w)

private theorem bigger_bounds (a b:ℚ) : score a≤score (bigger a b) ∧ score b≤score (bigger a b) := by
  unfold bigger
  split
  next h => exact ⟨h.le,le_rfl⟩
  next h => exact ⟨le_rfl,le_of_not_gt h⟩
private theorem bigger_property {P:ℚ→Prop} {a b:ℚ} (ha:P a) (hb:P b) : P (bigger a b) := by
  unfold bigger;split <;> assumption
private theorem win_prop {P:ℚ→Prop} (w:Assignment)
    (h0:P (t0 scale w)) (h1:P (t1 scale w)) (h2:P (t2 scale w)) : P (winner w) :=
  bigger_property (bigger_property h0 h1) h2
theorem winner_one_of (w:Assignment) : winner w=t0 scale w ∨ winner w=t1 scale w ∨ winner w=t2 scale w :=
  win_prop (P:=fun t=>t=t0 scale w ∨ t=t1 scale w ∨ t=t2 scale w) w
    (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))

private theorem rational_height (t:ℚ) : absLogHeight₁ t=Real.log (score t:ℝ) := by
  rw [SourceScalarHeight318.rational_height_eq_literal]
  simp only [ZInQ.rationalLogHeight,score,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs]
private theorem score_mono {a b:ℚ} (h:score a≤score b) : absLogHeight₁ a≤absLogHeight₁ b := by
  rw [rational_height,rational_height]
  have hp : 0<score a := lt_of_lt_of_le a.den_pos (le_max_right _ _)
  exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast h)
private theorem max_heights (w:Assignment) :
    absLogHeight₁ (t0 scale w)≤absLogHeight₁ (winner w) ∧
    absLogHeight₁ (t1 scale w)≤absLogHeight₁ (winner w) ∧
    absLogHeight₁ (t2 scale w)≤absLogHeight₁ (winner w) := by
  have a:=bigger_bounds (t0 scale w) (t1 scale w)
  have b:=bigger_bounds (bigger (t0 scale w) (t1 scale w)) (t2 scale w)
  exact ⟨score_mono (a.1.trans b.1),score_mono (a.2.trans b.1),score_mono b.2⟩

def Need (u v:ℤ) : Prop := CleanSparseHeightCut318.Extreme u v →
  pointHeight u v<CleanSparseHeightCut318.target u v
def Fail (u v:ℤ) : Prop := CleanSparseHeightCut318.Extreme u v ∧
  CleanSparseHeightCut318.target u v≤pointHeight u v
abbrev beta (w:Assignment) := ScalarSource318.beta w
abbrev detU (t:ℚ) : ℤ := 2*t.num+t.den
abbrev Gate (w:Assignment) : Prop :=
  Need (detU (winner w)) (winner w).num ∧ (beta w≠0 → Need (beta w).num (beta w).den)
abbrev Obstruction (w:Assignment) : Prop :=
  Fail (detU (winner w)) (winner w).num ∨ (beta w≠0 ∧ Fail (beta w).num (beta w).den)

private theorem absorbed {u v:ℤ} (h:Need u v) (hc:IsCoprime u v) (hn:∀j:Fin 5,forms u v j≠0) :
    pointHeight u v<heightConstant*(radical u v:ℝ)^((49:ℝ)/8) := by
  have hh : pointHeight u v<CleanSparseHeightCut318.target u v := by
    by_cases e:CleanSparseHeightCut318.Extreme u v
    · exact h e
    · exact CleanSparseHeightCut318.automatic hc hn e
  apply height_constant_absorption ((210:ℝ)^300) badProduct (radical u v) _
    (by positivity) conductor_constant_bound.le (by positivity)
    (by exact_mod_cast bad_product_bound.le) (by exact_mod_cast radical_pos u v)
  simpa only [CleanSparseHeightCut318.target,CleanSparseHeightCut318.S,Nat.cast_mul] using hh

private theorem detector_at (t:ℚ) (gate:Need (detU t) t.num) (hF:contactPolynomial t≠0)
    (N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k) (divs:ContactDivisibility t N k) :
    absLogHeight₁ t≤(heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k)) := by
  have hdiv : ∀p∈detectorPrimes t,(p:ℤ)^k∣N := by
    intro p hpm
    have hp:=member_prime (2*t.num+t.den) t.num p hpm
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨j,f,hf,hpos,hodd⟩:=member_raw_contact p t hpm
    obtain ⟨_,_,hg,_⟩:=(mem_contactPrimes _ _ p).mp hpm
    exact divs p hp hg j f hf hpos hodd
  have hr:1≤(detectorRadical t:ℝ)^((49:ℝ)/8) := Real.one_le_rpow
    (by exact_mod_cast (radical_pos (2*t.num+t.den) t.num)) (by norm_num)
  have hl:0≤Real.log (3:ℝ):=Real.log_nonneg (by norm_num)
  have hrad:=radical_weight_bound (2*t.num+t.den) t.num N hN k hk hdiv
  have hh:=absorbed gate (detector_primitive t) (forms_nonzero_of_contactPolynomial t hF)
  have hfirst:=detector_height_loss t
  have hfinal:absLogHeight₁ t≤(HeightSeparation318.heightConstant+Real.log 3)*(detectorRadical t:ℝ)^((49:ℝ)/8) := by
    have hlog:=mul_le_mul_of_nonneg_left hr hl
    dsimp only [detectorRadical] at *
    nlinarith
  exact hfinal.trans (mul_le_mul_of_nonneg_left hrad (add_nonneg (le_trans (by norm_num : (0:ℝ)≤1) HeightSeparation318.heightConstant_ge_one) hl))

/-- A single maximizer serves both k=13 and k=4.  Use ITS own divisibility
contracts in each target; transferring raw contacts between unequal tᵢ is not valid. -/
private theorem detector_three (w:Assignment) (source:Source w)
    (gate:Need (detU (winner w)) (winner w).num) (N:ℤ) (hN:N≠0) (k:ℕ) (hk:0<k)
    (d0:ContactDivisibility (t0 scale w) N k) (d1:ContactDivisibility (t1 scale w) N k)
    (d2:ContactDivisibility (t2 scale w) N k) :
    let U:=(heightConstant+Real.log 3)*|(N:ℝ)|^((49:ℝ)/(8*k))
    absLogHeight₁ (t0 scale w)≤U ∧ absLogHeight₁ (t1 scale w)≤U ∧ absLogHeight₁ (t2 scale w)≤U := by
  have hf:=win_prop (P:=fun t=>contactPolynomial t≠0) w (source_polynomial0_ne _ w source)
    (source_polynomial1_ne _ w source) (source_polynomial2_ne _ w source)
  have hd:=win_prop (P:=fun t=>ContactDivisibility t N k) w d0 d1 d2
  have h:=detector_at (winner w) gate hf N hN k hk hd
  obtain ⟨h0,h1,h2⟩:=max_heights w
  exact ⟨h0.trans h,h1.trans h,h2.trans h⟩

private theorem high_local
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source) (gate:Need (detU (winner w)) (winner w).num)
    (hne:lucasResidual (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)≠0) :
    (maxIndex (rootLabel labels):ℝ)^2-6<7*heightConstant*
      |lucasResidual (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)|^((49:ℝ)/104) := by
  have hN:highTarget labels≠0 := by
    intro hz
    apply hne
    rw [←high_target_cast w source labels,hz,Int.cast_zero]
  obtain ⟨h0,h1,h2⟩:=detector_three w source gate (highTarget labels) hN 13 (by decide)
    (source_contact0_contracts w source labels).1 (source_contact1_contracts w source labels).1 (source_contact2_contracts w source labels).1
  have hh:=SourceDetectorScales318.source_index_height_comparison _ w source
    (rootLabel labels) labels.roots labels.odd heightConstant heightConstant_ge_one
    (highTarget labels) hN 13
    h0
    h1
    h2
  simpa only [high_target_cast w source labels,Nat.cast_ofNat,show (8:ℝ)*13=104 by norm_num] using hh


private theorem low_local
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source) (gate:Need (detU (winner w)) (winner w).num)
    (hne:3723*(2*w 0+1)^2≠(rootLabel labels 0:ℚ)) :
    (maxIndex (rootLabel labels):ℝ)^2-6<7*heightConstant*
      (((3723*(2*w 0+1)^2-(rootLabel labels 0:ℚ)).num.natAbs:ℝ)^((49:ℝ)/32)) := by
  have hN:(lowTarget w labels).num≠0 := by
    intro hz
    have hh:lowTarget w labels=0 := Rat.num_eq_zero.mp hz
    apply hne
    rw [low_target_formula w source labels] at hh
    exact sub_eq_zero.mp hh
  obtain ⟨h0,h1,h2⟩:=detector_three w source gate (lowTarget w labels).num hN 4 (by decide)
    (source_contact0_contracts w source labels).2 (source_contact1_contracts w source labels).2 (source_contact2_contracts w source labels).2
  have hh:=SourceDetectorScales318.source_index_height_comparison _ w source
    (rootLabel labels) labels.roots labels.odd heightConstant heightConstant_ge_one
    (lowTarget w labels).num hN 4
    h0
    h1
    h2
  rw [low_target_formula w source labels] at hh
  simpa only [Nat.cast_natAbs,Int.cast_abs,Nat.cast_ofNat,
    show (8:ℝ)*4=32 by norm_num] using hh



private theorem scalar_local (w:Assignment) (source:Source w) (labels:Labels w source)
    (gate:beta w≠0 → Need (beta w).num (beta w).den) :
    ZInQ.rationalLogHeight (3723*(2*w 0+1)^2)≤heightConstant*(labels.c.natAbs:ℝ)^((49:ℝ)/64) := by
  have hh : absLogHeight₁ (beta w)≤heightConstant*|(labels.c:ℝ)|^((49:ℝ)/64) := by
    by_cases hb:beta w=0
    · rw [hb]
      convert ConsumedContactHeight318.rational_zero_height labels.c 8 using 1 <;> norm_num
    · have hn:=ScalarContactMap318.source_forms_nonzero _ w source hb
      have h:=absorbed (gate hb) (Rat.isCoprime_num_den (beta w)) hn
      rw [ConsumedContactHeight318.rational_point_height] at h
      have hd:=radical_weight_bound (beta w).num (beta w).den labels.c
        (RawOddAnchorPoints318.scalar_label_nonzero w labels.c labels.scalar) 8 (by decide)
        (SourceScalarHeight318.labeled_prime_divisibility w source labels hb)
      have hmul:=mul_le_mul_of_nonneg_left hd (le_trans (by norm_num : (0:ℝ)≤1) heightConstant_ge_one)
      convert h.le.trans hmul using 1 <;> norm_num
  rw [SourceScalarHeight318.rational_height_eq_literal] at hh
  simpa only [beta,ScalarSource318.beta,Nat.cast_natAbs,Int.cast_abs] using hh

theorem source_at (w:Assignment) (source:Source w) (gate:Gate w) :
    ∃x:ℤ,(x:ℚ)=w 0 := by
  obtain ⟨labels⟩:=labels_exist w source
  have hc0:=RawOddAnchorPoints318.scalar_label_nonzero w labels.c labels.scalar
  have hanchor:=SourceSeparation318.scalar_anchor_size labels.c hc0 labels.anchor_divides
  have horient:=SourceSeparation318.scalar_orientation (rootLabel labels) labels.c labels.orientation
  have hc4:4<(labels.c.natAbs:ℝ) := by
    have hh:(4:ℝ)≤2^49151 := by
      calc
        (4:ℝ)=2^2 := by norm_num
        _≤2^49151 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact hh.trans_lt labels.anchor_bound
  have hB:=three_le_maxIndex_of_scalar_bound (rootLabel labels) labels.c labels.orientation hc4
  have hz:rootLabel labels 3≠0 :=
    RawOddAnchorPoints318.root_labels_nonzero w (rootLabel labels) labels.roots 3
  exact LucasSequence318.integer_input_from_three_height_comparisons (w 0)
    (rootLabel labels 0) (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)
    (maxIndex (rootLabel labels):ℝ) (labels.c.natAbs:ℝ) (labels.odd 0) hz hB
    (label_abs_le_maxIndex (rootLabel labels) 0) (label_abs_le_maxIndex (rootLabel labels) 1)
    (label_abs_le_maxIndex (rootLabel labels) 2) (label_abs_le_maxIndex (rootLabel labels) 3)
    horient hanchor (high_local w source labels gate.1)
    (scalar_local w source labels gate.2)
    (low_local w source labels gate.1)

/-- Pointwise handoff for the geometric producer. Original projective coordinates
are unchanged; a sharp estimate is needed only if this specific bit cut fires. -/
def SharpNeed (u v:ℤ) : Prop := CleanSparseHeightCut318.Extreme u v →
  pointHeight u v<27506231*((CleanSparseHeightCut318.S u v:ℝ)^2*
    Real.log (CleanSparseHeightCut318.S u v:ℝ))

theorem not_extreme_of_sharp {u v:ℤ} (hc:IsCoprime u v)
    (h:SharpNeed u v) : ¬CleanSparseHeightCut318.Extreme u v := by
  intro e
  have hN : 0<CleanSparseHeightCut318.S u v := by
    unfold CleanSparseHeightCut318.S
    exact Nat.mul_pos (by rw [bad_product_exact];decide) (radical_pos u v)
  have hpos : (0:ℝ)<CleanSparseHeightCut318.S u v := by exact_mod_cast hN
  have hlog : Real.log (CleanSparseHeightCut318.size u v:ℝ) <
      Real.log ((CleanSparseHeightCut318.S u v:ℝ)^(27506231*(CleanSparseHeightCut318.S u v)^2 : ℕ)) := by
    rw [←CleanSparseHeightCut318.height_log hc,Real.log_pow];push_cast;linarith [h e]
  have en : CleanSparseHeightCut318.size u v <
      (CleanSparseHeightCut318.S u v)^(27506231*(CleanSparseHeightCut318.S u v)^2) := by
    by_contra! bad
    have badr : (CleanSparseHeightCut318.S u v:ℝ)^(27506231*(CleanSparseHeightCut318.S u v)^2 : ℕ)
        ≤(CleanSparseHeightCut318.size u v:ℝ) := by exact_mod_cast bad
    exact (not_lt_of_ge (Real.log_le_log (pow_pos hpos _) badr)) hlog
  have lower : (2:ℕ)^((CleanSparseHeightCut318.S u v)^6)<CleanSparseHeightCut318.size u v := e
  exact (not_lt_of_ge (CleanSparseHeightCut318.integer_ceiling u v)) (lower.trans en)

theorem need_of_sharp {u v:ℤ} (hc:IsCoprime u v) (hh:SharpNeed u v) : Need u v :=
  fun e=>((not_extreme_of_sharp hc hh) e).elim

/-- Pure clean threshold: every selected genuine pair is above ALL 35 CM
table heights. Direct contradiction with the supplemental on_table_sharp
identifies the same original off-table input without importing the table here. -/
theorem above_cm {u v:ℤ} (hc:IsCoprime u v) (h:CleanSparseHeightCut318.Extreme u v) :
    Real.log (693889:ℝ)<pointHeight u v := by
  let s:=CleanSparseHeightCut318.S u v
  have hb : badProduct≤s := by
    change badProduct≤badProduct*radical u v
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left badProduct (show 1≤radical u v from radical_pos u v)
  have h20 : 20≤s := (show 20≤badProduct by rw [bad_product_exact];decide).trans hb
  have he : 20≤s^6 := h20.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1≤s by omega) (show 1≤6 by decide))
  have hsmall : 693889 < CleanSparseHeightCut318.size u v :=
    lt_trans ((show 693889<(2:ℕ)^20 by decide).trans_le (pow_le_pow_right₀ (by decide : 1≤(2:ℕ)) he)) h
  rw [CleanSparseHeightCut318.height_log hc]
  exact Real.log_lt_log (by norm_num) (by exact_mod_cast hsmall)

theorem geometry_domains (w:Assignment) (hs:Source w) :
    (IsCoprime (detU (winner w)) (winner w).num ∧ ∀j:Fin 5,forms (detU (winner w)) (winner w).num j≠0) ∧
    (beta w≠0 → IsCoprime (beta w).num ((beta w).den:ℤ) ∧ ∀j:Fin 5,forms (beta w).num (beta w).den j≠0) := by
  have hf:=win_prop (P:=fun t=>contactPolynomial t≠0) w (source_polynomial0_ne _ w hs)
    (source_polynomial1_ne _ w hs) (source_polynomial2_ne _ w hs)
  exact ⟨⟨detector_primitive _,forms_nonzero_of_contactPolynomial _ hf⟩,
    fun hb=>⟨Rat.isCoprime_num_den _,ScalarContactMap318.source_forms_nonzero _ w hs hb⟩⟩

theorem source_of_two_sharp (w:Assignment) (hs:Source w)
    (d:SharpNeed (detU (winner w)) (winner w).num)
    (b:beta w≠0 → SharpNeed (beta w).num (beta w).den) : ∃z:ℤ,(z:ℚ)=w 0 := by
  apply source_at w hs
  obtain ⟨hd,hb⟩:=geometry_domains w hs
  exact ⟨need_of_sharp hd.1 d,fun h=>need_of_sharp (hb h).1 (b h)⟩

abbrev detPair (w:Assignment) : ℤ×ℤ := (detU (winner w),(winner w).num)
abbrev scalarPair (w:Assignment) : ℤ×ℤ := ((beta w).num,(beta w).den)
def firstExtreme (w:Assignment) : Option (ℤ×ℤ) := by
  classical
  exact if CleanSparseHeightCut318.Extreme (detPair w).1 (detPair w).2 then some (detPair w)
    else if beta w≠0 ∧ CleanSparseHeightCut318.Extreme (scalarPair w).1 (scalarPair w).2
      then some (scalarPair w) else none

/-- A concrete one-point geometric acceptance gate, chosen BEFORE evaluating
any real height, and only on an actual source lift. -/
def OneSharp (w:Assignment) : Prop := ∀p:ℤ×ℤ, firstExtreme w=some p →
  pointHeight p.1 p.2<27506231*((CleanSparseHeightCut318.S p.1 p.2:ℝ)^2*
    Real.log (CleanSparseHeightCut318.S p.1 p.2:ℝ))

theorem selection (w:Assignment) (hs:Source w) :
    (firstExtreme w=none ∧ Gate w) ∨
    ∃p:ℤ×ℤ,firstExtreme w=some p ∧ CleanSparseHeightCut318.Extreme p.1 p.2 ∧
      IsCoprime p.1 p.2 ∧ (∀j:Fin 5,forms p.1 p.2 j≠0) := by
  classical
  obtain ⟨hd,hb⟩:=geometry_domains w hs
  by_cases de:CleanSparseHeightCut318.Extreme (detPair w).1 (detPair w).2
  · right
    exact ⟨detPair w,by simp [firstExtreme,de],de,hd⟩
  · by_cases se:beta w≠0 ∧ CleanSparseHeightCut318.Extreme (scalarPair w).1 (scalarPair w).2
    · right
      exact ⟨scalarPair w,by simp [firstExtreme,de,se],se.2,hb se.1⟩
    · left
      exact ⟨by simp [firstExtreme,de,se],fun e=>(de e).elim,fun nz e=>(se ⟨nz,e⟩).elim⟩

/-- If the selector returns no point, existing arithmetic alone closes this
source witness. If it returns one, THAT point's restricted sharp theorem rules
out the entire witness. No second isogeny/flag is requested. -/
theorem source_of_one_sharp (w:Assignment) (hs:Source w) (H:OneSharp w) :
    ∃z:ℤ,(z:ℚ)=w 0 := by
  rcases selection w hs with ⟨_,hg⟩|⟨p,hp,he,hc,_⟩
  · exact source_at w hs hg
  · exact ((not_extreme_of_sharp hc (fun _=>H p hp)) he).elim

/-- Unlike the disjunction asserting failure of an OLD budget, this point is
deterministic; its SHARP estimate fails, not necessarily its old budget. -/
theorem selected_obstruction (w:Assignment) (hs:Source w) (nonint:¬∃z:ℤ,(z:ℚ)=w 0) :
    ∃p:ℤ×ℤ,firstExtreme w=some p ∧ CleanSparseHeightCut318.Extreme p.1 p.2 ∧
      IsCoprime p.1 p.2 ∧ (∀j:Fin 5,forms p.1 p.2 j≠0) ∧
      27506231*((CleanSparseHeightCut318.S p.1 p.2:ℝ)^2*Real.log (CleanSparseHeightCut318.S p.1 p.2:ℝ))
        ≤pointHeight p.1 p.2 := by
  rcases selection w hs with ⟨_,hg⟩|⟨p,hp,he,hc,hn⟩
  · exact (nonint (source_at w hs hg)).elim
  · exact ⟨p,hp,he,hc,hn,le_of_not_gt (fun lt=>(not_extreme_of_sharp hc (fun _=>lt)) he)⟩

theorem obstruction_at (w:Assignment) (source:Source w) (nonint:¬∃z:ℤ,(z:ℚ)=w 0) :
    Obstruction w := by
  classical
  by_cases d:Fail (detU (winner w)) (winner w).num
  · exact Or.inl d
  · right
    by_contra h
    apply nonint
    apply source_at w source
    constructor
    · intro e
      exact lt_of_not_ge (fun hn=>d ⟨e,hn⟩)
    · intro hb e
      exact lt_of_not_ge (fun hn=>h ⟨hb,e,hn⟩)

private theorem scaled (q:ℚ) (h:HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) q) :
    ∃w:Assignment,w 0=q ∧ Source w := by
  have he : (Current318FinalPolynomial.scale:ℚ)=scale := by
    simp only [Current318FinalPolynomial.scale,Int.cast_pow,Int.cast_ofNat] <;> rfl
  simpa only [he,HasSolution,Source] using h

/-- Preserve the quantifier on the replay witness: one genuine good lift
suffices for a fixed input. No claim that w is the supplied finite witness. -/
theorem reverse_of_one {q:ℚ} (h:∃w:Assignment,w 0=q ∧ Source w ∧ Gate w) : ∃z:ℤ,(z:ℚ)=q := by
  obtain ⟨w,hw,hs,hg⟩:=h
  obtain ⟨z,hz⟩:=source_at w hs hg
  exact ⟨z,hz.trans hw⟩

def BadLift (q:ℚ) : Prop := ∃w:Assignment,w 0=q ∧ Source w ∧ Obstruction w
private theorem badLift {q:ℚ} (hh:HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) q)
    (nonint:¬∃z:ℤ,(z:ℚ)=q) : BadLift q := by
  obtain ⟨w,hw,hs⟩:=scaled q hh
  refine ⟨w,hw,hs,obstruction_at w hs ?_⟩
  rintro ⟨z,hz⟩
  exact nonint ⟨z,hz.trans hw⟩

/-- Geometry can be instantiated only if a purported counterexample q exists:
one actual stage0 lift with one selected sharp point is sufficient. -/
def Residual (q:ℚ) : Prop := q.den≠1 →
    (∃w:Assignment,w 0=q ∧ Source w) → ∃w:Assignment,w 0=q ∧ Source w ∧ OneSharp w

private theorem reverse_selected {q:ℚ} (hs:HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) q)
    (H:Residual q) : ∃z:ℤ,(z:ℚ)=q := by
  by_contra nonint
  have hden : q.den≠1 := by
    intro hd
    apply nonint
    exact ⟨q.num,by simpa only [hd,Nat.cast_one,one_mul] using q.den_mul_eq_num.symm⟩
  obtain ⟨w,hw,src,one⟩:=H hden (scaled q hs)
  obtain ⟨z,hz⟩:=source_of_one_sharp w src one
  exact nonint ⟨z,hz.trans hw⟩

theorem from_selected318 (q:ℚ) (hw:∃w:Fin 317→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current318FinalPolynomial.P=0) (H:Residual q) : ∃z:ℤ,(z:ℚ)=q :=
  reverse_selected ((Current318FinalBridge.polynomial_zero_iff_source q).mp hw) H

theorem from_selected326 (q:ℚ) (hw:∃w:Fin 325→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current326CoefficientBinding.tablePolynomial=0) (H:Residual q) : ∃z:ℤ,(z:ℚ)=q :=
  reverse_selected ((Current326Final.table_zero_iff_source q).mp hw) H

theorem obstruction318 (q:ℚ) (hw:∃w:Fin 317→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current318FinalPolynomial.P=0) (nonint:¬∃z:ℤ,(z:ℚ)=q) : BadLift q :=
  badLift ((Current318FinalBridge.polynomial_zero_iff_source q).mp hw) nonint
theorem obstruction326 (q:ℚ) (hw:∃w:Fin 325→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current326CoefficientBinding.tablePolynomial=0) (nonint:¬∃z:ℤ,(z:ℚ)=q) : BadLift q :=
  badLift ((Current326Final.table_zero_iff_source q).mp hw) nonint

theorem reverse318 (q:ℚ) (hw:∃w:Fin 317→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current318FinalPolynomial.P=0) (rule:¬BadLift q) : ∃z:ℤ,(z:ℚ)=q := by
  by_contra hn
  exact rule (obstruction318 q hw hn)
theorem reverse326 (q:ℚ) (hw:∃w:Fin 325→ℚ,MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
    (Fin.cons q w) Current326CoefficientBinding.tablePolynomial=0) (rule:¬BadLift q) : ∃z:ℤ,(z:ℚ)=q := by
  by_contra hn
  exact rule (obstruction326 q hw hn)
end ActualTwoSourceHeightGate318
#print axioms ActualTwoSourceHeightGate318.from_selected318
#print axioms ActualTwoSourceHeightGate318.from_selected326
#print axioms ActualTwoSourceHeightGate318.selected_obstruction
#print axioms ActualTwoSourceHeightGate318.source_at
#print axioms ActualTwoSourceHeightGate318.obstruction318
#print axioms ActualTwoSourceHeightGate318.obstruction326
#print axioms ActualTwoSourceHeightGate318.reverse318
#print axioms ActualTwoSourceHeightGate318.reverse326
