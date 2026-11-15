module
public import OriginalArchimedeanMarkedPoint318
public import BicanonicalCharts318
public section
noncomputable section
namespace OriginalArchimedeanSectionCoefficient318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanMarkedPoint318
open ContactBicanonicalCoefficients318 ContactBranchPoint318 Polynomial
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t))

/-- Actual coefficient of the original branch coordinate differential in
the literal t coordinate, obtained by differentiating y_i²=c_i(t-a_i). -/
@[expose] def branchDerivative (i : Fin 4) : ℂ :=
  ((c i:ℚ):ℂ)/(2*markedRoot c t w i)
include hn in
lemma branchDerivative_ne (i : Fin 4) : branchDerivative c t w i≠0 :=
  div_ne_zero (Rat.cast_ne_zero.mpr (Units.ne_zero _))
    (mul_ne_zero (by norm_num) (markedRoot_ne c t hn w i))
include hn in
lemma branchDerivative_square (i : Fin 4) : branchDerivative c t w i^2=
    ((c i:ℚ):ℂ)/(4*((t:ℂ)-LiteralMetricExtension318.contacts i)) := by
  have hc : ((c i:ℚ):ℂ)≠0 := Rat.cast_ne_zero.mpr (Units.ne_zero _)
  have ht := sub_ne_zero.mpr (coordinate_ne c t hn i)
  rw [branchDerivative,div_pow,mul_pow,markedRoot_square]
  field_simp
  <;> ring

/-- The true branch coefficient of the global section, before any analytic
frame change, retains its actual localized denominator. -/
lemma branch_coefficient_cleared (i : Fin 4) :
    w.embedding (branchPoint c t hn i (branchQ0 c i))*
      (aeval (t:ℂ) (SourceDenominatorCover318.twisted c i))=
        ((branchScale c i:ℚ):ℂ) := by
  let D := SourceDenominatorCover318.denominator c i
  have h := congrArg (fun a => w.embedding (branchPoint c t hn i a))
    (IsLocalization.Away.mul_invSelf (S:=BranchRing c i) D)
  have hd : w.embedding (branchPoint c t hn i
      (algebraMap (ContactKummerOrder318.SourceOrder c) (BranchRing c i) D))=
      aeval (t:ℂ) (SourceDenominatorCover318.twisted c i) := by
    rw [branchPoint_algebraMap]
    change w.embedding (RationalContactPoint318.sourcePoint c t
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c)
        (SourceDenominatorCover318.twisted c i)))=_
    rw [(RationalContactPoint318.sourcePoint c t).commutes]
    simp only [map_ratCast]
    simp [SourceDenominatorCover318.twisted,ContactKummerOrder318.coefficient,
      RationalContactPoint318.parameters,Fin.prod_univ_succ]
  simp only [map_mul,map_one] at h
  rw [hd] at h
  simp only [branchQ0,map_mul,map_ratCast]
  calc
    _ = ((branchScale c i:ℚ):ℂ)*
        (aeval (t:ℂ) (SourceDenominatorCover318.twisted c i)*
          w.embedding (branchPoint c t hn i (IsLocalization.Away.invSelf D))) := by ring
    _ = _ := by rw [h,mul_one]

/-- Pure explicit polynomial identity for the SAME pivot permutation and
all four original contacts. No untwisted replacement of the point field. -/
lemma denominator_identity (i : Fin 4) :
    aeval (t:ℂ) (SourceDenominatorCover318.twisted c i)*
      (4*((t:ℂ)-LiteralMetricExtension318.contacts i))=
    ((branchScale c i:ℚ):ℂ)*((c i:ℚ):ℂ)*
      BicanonicalCharts318.contactPolynomial LiteralMetricExtension318.contacts (t:ℂ) := by
  have hc : ∀ j : Fin 4,((c j:ℚ):ℂ)≠0 := fun j => Rat.cast_ne_zero.mpr (Units.ne_zero _)
  fin_cases i <;>
    simp [SourceDenominatorCover318.twisted,ContactKummerOrder318.coefficient,
      branchScale,fourUnit,SourceDenominatorCover318.twistUnit,FourRootPivot318.indices,
      LinearContactSquareclass318.contacts,LiteralMetricExtension318.contacts,
      BicanonicalCharts318.contactPolynomial,Fin.prod_univ_succ] <;>
    field_simp [hc] <;> ring

lemma unscaled_coordinate (i : Fin 4) :
    w.embedding (branchPoint c t hn i (branchQ0 c i))*branchDerivative c t w i^2=
      BicanonicalCharts318.q0 LiteralMetricExtension318.contacts (t:ℂ) := by
  have hp : BicanonicalCharts318.contactPolynomial LiteralMetricExtension318.contacts (t:ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (coordinate_ne c t hn j))
  have hs : ((branchScale c i:ℚ):ℂ)≠0 := Rat.cast_ne_zero.mpr (Units.ne_zero _)
  have hc : ((c i:ℚ):ℂ)≠0 := Rat.cast_ne_zero.mpr (Units.ne_zero _)
  have ht := sub_ne_zero.mpr (coordinate_ne c t hn i)
  have hq := branch_coefficient_cleared c t hn w i
  have hd := denominator_identity c t i
  rw [branchDerivative_square c t hn w i,BicanonicalCharts318.q0]
  apply (eq_div_iff hp).mpr
  rw [mul_assoc,div_mul_eq_mul_div,←mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero (by norm_num) ht)).mpr
  have he := congrArg (fun z : ℂ => z*(4*((t:ℂ)-LiteralMetricExtension318.contacts i))) hq
  rw [mul_assoc,hd] at he
  apply mul_left_cancel₀ hs
  linear_combination he

/-- Actual J²-scaled original global sections in the genuine original
branch frame become the literal analytic pair under this differential. -/
lemma scaled_coordinates (i : Fin 4) :
    w.embedding (ContactBicanonicalPointHeight318.a0 c t hn i)*branchDerivative c t w i^2=
      (2765952000:ℂ)^2*BicanonicalCharts318.q0 LiteralMetricExtension318.contacts (t:ℂ) ∧
    w.embedding (ContactBicanonicalPointHeight318.a1 c t hn i)*branchDerivative c t w i^2=
      (2765952000:ℂ)^2*BicanonicalCharts318.q1 LiteralMetricExtension318.contacts (t:ℂ) := by
  have h0 : w.embedding (ContactBicanonicalPointHeight318.a0 c t hn i)=
      (2765952000:ℂ)^2*w.embedding (branchPoint c t hn i (branchQ0 c i)) := by
    simp only [ContactBicanonicalPointHeight318.a0,ContactScaledBicanonicalPoint318.scaledQ0,
      ContactScaledBicanonicalPoint318.value_nsmul,ContactBicanonicalPointValue318.value_q0,
      nsmul_eq_mul,map_mul,map_natCast,ContactScaledBicanonicalPoint318.J,Nat.cast_pow]
  have hh : w.embedding (ContactBicanonicalPointHeight318.a0 c t hn i)*branchDerivative c t w i^2=
      (2765952000:ℂ)^2*BicanonicalCharts318.q0 LiteralMetricExtension318.contacts (t:ℂ) := by
    rw [h0,mul_assoc,unscaled_coordinate c t hn w i]
  refine ⟨hh,?_⟩
  rw [ContactBicanonicalPointHeight318.ratio,map_mul,map_ratCast,mul_assoc,hh,
    BicanonicalCharts318.q1]
  ring
end OriginalArchimedeanSectionCoefficient318
