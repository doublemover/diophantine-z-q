module
public import PELNormalizerOctagonMinimum318
public import PELFixedCandidateConjugators318
public section
noncomputable section
namespace PELNormalizerOctagonDomain318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionDivision318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELFixedCandidateConjugators318 PELFixedCandidateWords318
open PELNormalizerOctagonMinimum318 PELNormalizerOctagonAffine318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
set_option maxHeartbeats 3000000

@[expose] def candidateNormalizer (k : Fin 77) : positiveNormalizer :=
  conjugator k*inertiaElement (label k)*(conjugator k)⁻¹

theorem candidateNormalizer_value (k : Fin 77) :
    ((candidateNormalizer k).val:B)=embed (candidate k) := actual_conjugation k

lemma inverse_value (u : Bˣ) : ((u⁻¹:Bˣ):B)=reciprocal (u:B) := by
  calc
    ((u⁻¹:Bˣ):B)=((u⁻¹:Bˣ):B)*1 := (mul_one _).symm
    _ = ((u⁻¹:Bˣ):B)*((u:B)*reciprocal (u:B)) := by rw [mul_reciprocal _ u.ne_zero]
    _ = reciprocal (u:B) := by rw [←mul_assoc,Units.inv_val,one_mul]

/-- The eight walls come from proved members of the full original group:
four conjugates of original inertia and four actual normalizer words/inverses. -/
@[expose] def wall : Fin 8 → positiveNormalizer := ![
  candidateNormalizer 17,candidateNormalizer 14,candidateNormalizer 11,candidateNormalizer 4,
  conjugator 61,conjugator 23,(conjugator 23)⁻¹,(conjugator 61)⁻¹]

@[expose] def wallValue : Fin 8 → B := ![
  embed ![0,0,0,1],embed ![0,1,0,-1],embed ![6,1,-12,0],embed ![-6,1,12,0],
  embed ![15,2,0,-5],embed ![15,3,0,-5],
  reciprocal (embed ![15,3,0,-5]),reciprocal (embed ![15,2,0,-5])]

theorem wall_value (e : Fin 8) : ((wall e).val:B)=wallValue e := by
  have h23 : ((conjugator 23).val:B)=embed ![15,3,0,-5] := by
    rw [conjugator,positiveWord_value,coordinate_certificate]
    norm_num [wordScale,smallConjugator]
  have h61 : ((conjugator 61).val:B)=embed ![15,2,0,-5] := by
    rw [conjugator,positiveWord_value,coordinate_certificate]
    norm_num [wordScale,smallConjugator]
  fin_cases e
  · simpa [wall,wallValue,candidate] using candidateNormalizer_value 17
  · simpa [wall,wallValue,candidate] using candidateNormalizer_value 14
  · simpa [wall,wallValue,candidate] using candidateNormalizer_value 11
  · simpa [wall,wallValue,candidate] using candidateNormalizer_value 4
  · simpa only [wall,wallValue] using h61
  · simpa only [wall,wallValue] using h23
  · change (((conjugator 23).val⁻¹:Bˣ):B)=reciprocal (embed ![15,3,0,-5])
    rw [inverse_value,h23]
  · change (((conjugator 61).val⁻¹:Bˣ):B)=reciprocal (embed ![15,2,0,-5])
    rw [inverse_value,h61]

/-- Testing these actual group elements forces all eight literal original
normalizer-domain inequalities. No sufficiency of the finite list is assumed. -/
theorem wall_inequalities (A Y : ℝ)
    (h : ∀ e : Fin 8,(reducedNorm ((wall e).val:B):ℝ)≤realDen ((wall e).val:B) A Y) :
    inequalities A Y := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  rw [wall_value] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [wallValue,realDen,PELQuaternionKleinAction318.matrix,embed,reciprocal,reducedNorm] at h0 h1 h2 h3 h4 h5 h6 h7
  unfold inequalities
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith⟩

/-- The actual height-minimum condition for the ENTIRE original positive
normalizer is exactly the literal eight-sided domain. -/
theorem octagon_iff_full_minimum (τ : HalfPlane) :
    inequalities (scaledFirst τ) (scaledSecond τ) ↔
      ∀ g : positiveNormalizer,height τ≤height (baseAction g τ) := by
  constructor
  · exact original_all_normalizer_minimum τ
  · intro hm
    apply wall_inequalities
    intro e
    have h := hm (wall e)
    rw [positive_height_multiplier] at h
    have hn : 0<(reducedNorm ((wall e).val:B):ℝ) := by exact_mod_cast (wall e).property.2
    have hh := height_pos τ
    have hr : 1≤realDen ((wall e).val:B) (scaledFirst τ) (scaledSecond τ)/
        (reducedNorm ((wall e).val:B):ℝ) := by nlinarith
    simpa only [one_mul] using (le_div_iff₀ hn).mp hr

/-- Same-orbit representatives in the full-normalizer domain have the
same original height. Interior uniqueness is NOT claimed: center210
really preserves this octagon and must be divided out separately. -/
theorem octagon_orbit_height (τ : HalfPlane) (g : positiveNormalizer)
    (hτ : inequalities (scaledFirst τ) (scaledSecond τ))
    (hg : inequalities (scaledFirst (baseAction g τ)) (scaledSecond (baseAction g τ))) :
    height (baseAction g τ)=height τ := by
  apply le_antisymm
  · have h := original_all_normalizer_minimum (baseAction g τ) hg g⁻¹
    rw [←baseAction_mul,inv_mul_cancel,baseAction_one] at h
    exact h
  · exact original_all_normalizer_minimum τ hτ g
end PELNormalizerOctagonDomain318
