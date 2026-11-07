module
public import PadeNumeratorNonvanishing
public import PadeDenominatorNonvanishing
public section
namespace PadeAccuracy
variable {K : Type*} [Field K] [CharZero K]

@[expose] def G5 (x : K) : K :=
  1-(2/5)*x-(2/15)*x^2-(14/195)*x^3-(154/3315)*x^4-(22/663)*x^5
@[expose] def J5 (x : K) : K :=
  1-x/5+x^2/15-x^3/39+(7/663)*x^4-x^5/221

theorem G_error (x : K) :
    PadeNumeratorNonvanishing.G x-PadeDenominatorNonvanishing.QG x*G5 x =
      x^6*((-29282/1183455)+(242/33813)*x) := by
  unfold PadeNumeratorNonvanishing.G PadeDenominatorNonvanishing.QG G5
  norm_num
  ring

theorem J_error (x : K) :
    PadeNumeratorNonvanishing.J x-PadeDenominatorNonvanishing.QJ x*J5 x =
      x^6*((67/33813)+(5/11271)*x) := by
  unfold PadeNumeratorNonvanishing.J PadeDenominatorNonvanishing.QJ J5
  norm_num
  ring

theorem G_denominator_at_zero : PadeDenominatorNonvanishing.QG (0:K)=1 := by
  simp [PadeDenominatorNonvanishing.QG]
theorem J_denominator_at_zero : PadeDenominatorNonvanishing.QJ (0:K)=1 := by
  simp [PadeDenominatorNonvanishing.QJ]

theorem G_quotient_nonzero (x : ConcreteG8Domain.K) :
    PadeNumeratorNonvanishing.G x/PadeDenominatorNonvanishing.QG x ≠ 0 :=
  div_ne_zero (PadeNumeratorNonvanishing.G_nonzero x)
    (PadeDenominatorNonvanishing.QG_nonzero x)

theorem J_quotient_nonzero (x : ConcreteG8Domain.K) :
    PadeNumeratorNonvanishing.J x/PadeDenominatorNonvanishing.QJ x ≠ 0 :=
  div_ne_zero (PadeNumeratorNonvanishing.J_nonzero x)
    (PadeDenominatorNonvanishing.QJ_nonzero x)

theorem J_log_zero_iff (u x : ConcreteG8Domain.K) :
    -u*(PadeNumeratorNonvanishing.J x/PadeDenominatorNonvanishing.QJ x)=0 ↔ u=0 := by
  simp only [mul_eq_zero,neg_eq_zero,J_quotient_nonzero x,or_false]
end PadeAccuracy
