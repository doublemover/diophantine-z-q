module
public import Mathlib.Tactic
public section
namespace NormalizedPolePoints318

/-- The two literal factored equations consumed by each source pole block.
This is proof data, not a claim of existence from real inequalities alone. -/
structure Certificate (b : ℚ) where
  e : ℚ
  s : ℚ
  p : ℚ
  q : ℚ
  first : 17*p^2=b*((17-e)*(17+3*e))
  second : 17*q^2=b*((s^2-e*(17-b))*(s^2+3*(e*(17-b))))

/-- Exact output of the simultaneous-twist point realization after scaling
its two actual abscissas to B and B*s^2, where B=17*b. -/
structure PointPair (b : ℚ) where
  parameter : ℚ
  s : ℚ
  y₁ : ℚ
  y₂ : ℚ
  s_ne : s≠0
  first : y₁^2=(17*b)*((17*b)-parameter)*((17*b)+3*parameter)
  second : y₂^2=((17*b)*s^2)*
    (((17*b)*s^2)-parameter*((17*b)^2*(1-b/17)))*
    (((17*b)*s^2)+3*parameter*((17*b)^2*(1-b/17)))

/-- The conversion retains both original point equations and their common
parameter. In particular, the second twist is the actual V=B^2(1-b/17),
not an independently selected twist or pole witness. -/
noncomputable def PointPair.certificate {b : ℚ} (hb : b≠0) (P : PointPair b) :
    Certificate b where
  e := P.parameter/b
  s := P.s/b
  p := P.y₁/(17*b)
  q := 17*P.y₂/((17*b)^3*P.s)
  first := by
    apply sub_eq_zero.mp
    calc
      17*(P.y₁/(17*b))^2-b*((17-P.parameter/b)*(17+3*(P.parameter/b))) =
          (P.y₁^2-(17*b)*((17*b)-P.parameter)*((17*b)+3*P.parameter))/(17*b^2) := by
        field_simp [hb]
        <;> ring
      _ = 0 := by rw [P.first]; simp
  second := by
    apply sub_eq_zero.mp
    calc
      17*(17*P.y₂/((17*b)^3*P.s))^2-
          b*(((P.s/b)^2-(P.parameter/b)*(17-b))*
            ((P.s/b)^2+3*((P.parameter/b)*(17-b)))) =
          (P.y₂^2-((17*b)*P.s^2)*
            (((17*b)*P.s^2)-P.parameter*((17*b)^2*(1-b/17)))*
            (((17*b)*P.s^2)+3*P.parameter*((17*b)^2*(1-b/17))))/
            (4913*b^6*P.s^2) := by
        field_simp [hb,P.s_ne]
        <;> ring
      _ = 0 := by rw [P.second]; simp

end NormalizedPolePoints318
