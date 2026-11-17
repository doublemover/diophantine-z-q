module
public import Mathlib.Tactic
public section
namespace LegendreNormDescentStep318

/-- Literal witness ascent for the classical norm descent. A solution for
the smaller coefficient c is transformed to one for b when t²-a=b*c. -/
theorem witness_ascent {F : Type*} [CommRing F]
    (a b c t u v w : F) (hstep : t^2-a=b*c)
    (hsol : u^2-a*v^2=c*w^2) :
    (t*u+a*v)^2-a*(u+t*v)^2=b*(c*w)^2 := by
  calc
    (t*u+a*v)^2-a*(u+t*v)^2 = (t^2-a)*(u^2-a*v^2) := by ring
    _ = (b*c)*(c*w^2) := by rw [hstep,hsol]
    _ = b*(c*w)^2 := by ring

/-- The affine norm witness also transfers over every completion. This is
the algebraic local-solvability preservation step, not a local-global axiom. -/
theorem affine_transfer {F : Type*} [Field F]
    (a b c t u v : F) (hb : b≠0) (hstep : t^2-a=b*c)
    (hsol : u^2-a*v^2=b) :
    ∃ x y : F, x^2-a*y^2=c := by
  have he : (t*u+a*v)^2-a*(u+t*v)^2=c*b^2 := by
    calc
      (t*u+a*v)^2-a*(u+t*v)^2 = (t^2-a)*(u^2-a*v^2) := by ring
      _ = c*b^2 := by rw [hstep,hsol]; ring
  refine ⟨(t*u+a*v)/b,(u+t*v)/b,?_⟩
  calc
    ((t*u+a*v)/b)^2-a*((u+t*v)/b)^2
        = ((t*u+a*v)^2-a*(u+t*v)^2)/b^2 := by ring
    _ = c := by simp [he,hb]

/-- The arithmetic measure really decreases after choosing a centered
square root of a modulo b. Existence of that modular root and preservation
of local solvability are separate obligations, not premises hidden here. -/
theorem coefficient_strictly_smaller (a b c t : ℤ)
    (hsize : |a|≤|b|) (hb : 2≤|b|) (ht : 2*|t|≤|b|)
    (hstep : t^2-a=b*c) : |c|<|b| := by
  have hprod : |b|*|c|≤t^2+|a| := by
    rw [←abs_mul,←hstep]
    calc
      |t^2-a| ≤ |t^2|+|a| := abs_sub _ _
      _ = t^2+|a| := by rw [abs_of_nonneg (sq_nonneg t)]
  have ht2 : 4*t^2≤|b|^2 := by
    have he := mul_nonneg (sub_nonneg.mpr ht)
      (show 0≤|b|+2*|t| by positivity)
    nlinarith [sq_abs t]
  by_contra hn
  have hc : |b|≤|c| := le_of_not_gt hn
  have he := mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hc)
  nlinarith [sq_nonneg (|b|-2)]

end LegendreNormDescentStep318
