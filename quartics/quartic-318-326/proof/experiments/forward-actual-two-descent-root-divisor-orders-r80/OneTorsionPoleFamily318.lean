module
public import NormalizedPolePoints318
public import PadeDenominatorNonvanishing
public section
namespace OneTorsionPoleFamily318
open NormalizedPolePoints318

/-- One ordinate vanishes, but the other is explicitly constructed.
This condition is different from requiring the complement to be a square. -/
def certificate (b k : ℚ) (h : 51*b+k^2=1156) : Certificate b where
  e := 17
  s := 17
  p := 0
  q := b*k
  first := by ring
  second := by nlinarith [congrArg (fun x : ℚ => 17*b^2*x) h]

/-- A nonempty real interval gives positive poles strictly below 17. -/
lemma pole_bounds (k : ℚ) (hlo : 17^2<k^2) (hhi : k^2<34^2) :
    0<(1156-k^2)/51 ∧ (1156-k^2)/51<17 := by
  constructor <;> nlinarith

/-- The first curve contributes a torsion point; the second ordinate is nonzero. -/
lemma second_ordinate_ne (b k : ℚ) (hb : 0<b) (hk : 17^2<k^2)
    (h : 51*b+k^2=1156) : (certificate b k h).q≠0 := by
  change b*k≠0
  apply mul_ne_zero (ne_of_gt hb)
  intro he
  subst k
  norm_num at hk

/-- A concrete certificate beyond the previously constructed square-complement family. -/
def exampleCertificate : Certificate (832/51 : ℚ) :=
  certificate (832/51) 18 (by norm_num)

lemma example_bounds : (0:ℚ)<832/51 ∧ (832/51:ℚ)<17 := by norm_num
lemma example_complement : (1:ℚ)-(832/51)/17=35/867 := by norm_num

/-- Thus the new family really escapes the both-ordinates-zero construction. -/
lemma example_no_square_complement :
    ¬ ∃ r : ℚ, 1-(832/51:ℚ)/17=r^2 := by
  rintro ⟨r,hr⟩
  have hgap := PadeDenominatorNonvanishing.rational_square_gap
    (51*r) 105 10 (by norm_num) (by norm_num) (by norm_num)
  apply hgap
  norm_num at hr ⊢
  nlinarith

end OneTorsionPoleFamily318
