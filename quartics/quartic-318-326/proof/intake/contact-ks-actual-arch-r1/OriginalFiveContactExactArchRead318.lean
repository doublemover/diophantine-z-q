module
public import OriginalFiveContactExactGauge318
public import GlobalSectionNorm318

public section
noncomputable section
namespace OriginalFiveContactExactArchRead318

open NumberField SectionHeight318 PeterssonSectionNorm318
open OriginalFiveContactExactGauge318 (FiniteImage actual_sections)

universe e x
variable {E : Type e} [Field E] [NumberField E]
variable {X : Type x} [TopologicalSpace X]
variable (u v : ℤ) (C : FrameNorms E)
local notation "Tₑ" => ((32*((u:ℚ)/(v:ℚ)):ℚ):E)
local notation "J₂" => (2765952000:E)^2

/-- Read the original global Q at the analytification of the whole
retained marked point, in the chosen actual analytic chart. This
asserts coefficient/norm identities, not a smoothness, primitive
field, compactification, or numerical arch bound. The caller must
supply points from the actual same signed mark. -/
structure PlacedRead (D : GlobalSectionNorm318.Data X) (w : InfinitePlace E) (P : X) : Prop where
  second :
    SectionCoefficientBounds318.Chart.section1 (D.kind P) =
      w.embedding Tₑ * SectionCoefficientBounds318.Chart.section0 (D.kind P)
  sameNorm :
    C.arch w = quadraticNorm (D.hyperbolic P (0,0))
      (SectionCoefficientBounds318.Chart.section0 (D.kind P))

/-- The original five nonzero forms exclude poles and all four
finite branches at every actual height-field embedding. -/
theorem off_contact (w : InfinitePlace E)
    (forms : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0)
    (i : Fin 4) : w.embedding Tₑ ≠ LiteralMetricExtension318.contacts i := by
  have hv : v ≠ 0 := forms 0
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv
  have hT : w.embedding Tₑ = 32*((u:ℂ)/(v:ℂ)) := by
    calc
      _ = ((32*((u:ℚ)/(v:ℚ)):ℚ):ℂ) := map_ratCast w.embedding _
      _ = _ := by push_cast
  intro he
  rw [hT, ← mul_div_assoc, div_eq_iff hvC] at he
  fin_cases i
  · apply forms 1
    change u = 0
    change (32:ℂ)*(u:ℂ) = 0*(v:ℂ) at he
    have he' : (32:ℂ)*(u:ℂ) = 0 := by simpa only [zero_mul] using he
    have e := (mul_eq_zero.mp he').resolve_left (by norm_num : (32:ℂ) ≠ 0)
    exact_mod_cast e
  · apply forms 2
    change u-v = 0
    change (32:ℂ)*(u:ℂ) = 32*(v:ℂ) at he
    have h' : (32:ℂ)*((u:ℂ)-(v:ℂ)) = 0 := by linear_combination he
    have e := (mul_eq_zero.mp h').resolve_left (by norm_num : (32:ℂ) ≠ 0)
    exact_mod_cast e
  · apply forms 3
    change u-2401*v = 0
    change (32:ℂ)*(u:ℂ) = 76832*(v:ℂ) at he
    have h' : (32:ℂ)*((u:ℂ)-2401*(v:ℂ)) = 0 := by linear_combination he
    have e := (mul_eq_zero.mp h').resolve_left (by norm_num : (32:ℂ) ≠ 0)
    exact_mod_cast e
  · apply forms 4
    change 32*u+343*v = 0
    change (32:ℂ)*(u:ℂ) = (-343)*(v:ℂ) at he
    have e : 32*(u:ℂ)+343*(v:ℂ) = 0 := by linear_combination he
    exact_mod_cast e

/-- Once the actual marked analytic chart has coordinate σ(T), the
two original coefficients have the required ratio by definition; no
extra geometric identity of second coefficients is a premise. -/
theorem at_regular (D : GlobalSectionNorm318.Data X) (w : InfinitePlace E) (P : X)
    (forms : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0)
    (chart : D.kind P =
      SourceMetricCharts318.Chart.regular (w.embedding Tₑ) (off_contact u v w forms))
    (norm_read : C.arch w = quadraticNorm (D.hyperbolic P (0,0))
      (BicanonicalCharts318.q0 LiteralMetricExtension318.contacts (w.embedding Tₑ))) :
    PlacedRead u v C D w P where
  second := by
    simp only [chart, SectionCoefficientBounds318.Chart.section1,
      SectionCoefficientBounds318.Chart.section0, BicanonicalCharts318.q1]
  sameNorm := by
    simpa only [chart, SectionCoefficientBounds318.Chart.section0] using norm_read

variable [CompactSpace X] [Nonempty X]

/-- The already accepted curvature/archimedean theorem gives the
specific paid pair used in MetricSections, without the old produced
zoom-model closure or its K_ct-to-E metric transport. -/
theorem paid (D : GlobalSectionNorm318.Data X) (w : InfinitePlace E) (P : X)
    (R : PlacedRead u v C D w P) (j : Fin 2) :
    w (![J₂,Tₑ*J₂] j)*C.arch w ≤ ContactMetricSections318.sectionBound := by
  have h := D.integral_section_norms P
  have mapJ : w.embedding J₂ = (2765952000:ℂ)^2 := by simp only [map_pow,map_ofNat]
  fin_cases j
  · change w J₂*C.arch w ≤ _
    rw [R.sameNorm, ← InfinitePlace.norm_embedding_eq, ← quadraticNorm_mul, mapJ]
    exact h.1
  · change w (Tₑ*J₂)*C.arch w ≤ _
    rw [R.sameNorm, ← InfinitePlace.norm_embedding_eq, ← quadraticNorm_mul, map_mul, mapJ]
    rw [mul_comm (w.embedding Tₑ) ((2765952000:ℂ)^2), mul_assoc, ← R.second]
    exact h.2

/-- Direct same-E path: actual finite sections and image from the
original Yuan model, actual infinite chart and Ψ. It uses the
published numeric estimate via the real geometric chart data, not
as a hypothesis and not through the broad uncompiled experiment. -/
def sections (H : FrameNorms E) (hYuan : ℝ) (k : E) (hk : k ≠ 0)
    (degree : H.normalizedDegree = hYuan)
    (D : GlobalSectionNorm318.Data X)
    (actualAnalyticMark : InfinitePlace E → X)
    (read : ∀ w, PlacedRead u v C D w (actualAnalyticMark w))
    (finitePaid : ∀ (w : FinitePlace E) (i : Fin 2), w (![J₂,Tₑ*J₂] i)*C.finiteNorm w ≤ 1)
    (finiteImage : ∀ w : FinitePlace E, FiniteImage H C k w)
    (archIsometry : ∀ w : InfinitePlace E, w k * C.arch w = H.arch w^2) :
    RefinedContactRealization318.MetricSections E u v hYuan :=
  actual_sections u v hYuan J₂ (Tₑ*J₂) C H k hk
    (by norm_num) rfl degree finitePaid
    (fun w j => paid u v C D w (actualAnalyticMark w) (read w) j)
    finiteImage archIsometry

end OriginalFiveContactExactArchRead318
#print axioms OriginalFiveContactExactArchRead318.off_contact
#print axioms OriginalFiveContactExactArchRead318.at_regular
#print axioms OriginalFiveContactExactArchRead318.paid
#print axioms OriginalFiveContactExactArchRead318.sections
