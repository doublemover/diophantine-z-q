module
public import ActualGaussianWeberPowerSeriesArc318
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section
noncomputable section

namespace ActualGaussianWeberSameRatioJetCross318

open IsLocalRing Polynomial ActualGaussianWeberPowerSeriesArc318

variable {k : Type*} [Field k]

private theorem map_eval₂_lift {R S : Type*} [CommRing R] [CommRing S]
    (a : k →+* R) (b : R →+* S) (P : k[X]) (x : R) :
    b (P.eval₂ a x) = P.eval₂ (b.comp a) (b x) := hom_eval₂ _ _ _ _

private theorem value_constant (P : k[X]) (x : FormalValuation k) :
    constantTerm k (P.eval₂ (constVal k) x) = P.eval (constantTerm k x) := by
  have h : (constantTerm k).comp (constVal k) = RingHom.id k :=
    RingHom.ext (constantTerm_const k)
  rw [map_eval₂_lift,h,eval₂_id]

private theorem parameter_const : constantTerm k (parameter k) = 0 := by
  change PowerSeries.constantCoeff ((seriesEquiv k).symm ((seriesEquiv k) PowerSeries.X)) = 0
  rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_X]

theorem linear_arc_constant (x e : k) (c : FormalValuation k) :
    constantTerm k (constVal k x + parameter k * constVal k e + (parameter k)^2*c) = x := by
  simp only [map_add,map_mul,map_pow,constantTerm_const,parameter_const,
    zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,add_zero]

private def jetIdeal (k : Type*) [Field k] : Ideal (FormalValuation k) :=
  Ideal.span {(parameter k)^2}

private theorem parameter_times_const_cancel (a : k)
    (h : parameter k * constVal k a ∈ jetIdeal k) : a = 0 := by
  change parameter k * constVal k a ∈ Ideal.span {(parameter k)^2} at h
  obtain ⟨g,hg⟩ := Ideal.mem_span_singleton.mp h
  have hcancel : parameter k * constVal k a = parameter k * (parameter k*g) := by
    rw [hg,pow_two,mul_assoc]
  have h1 : constVal k a = parameter k*g :=
    mul_left_cancel₀ (parameter_ne k) hcancel
  simpa only [constantTerm_const,map_mul,parameter_const,zero_mul]
    using congrArg (constantTerm k) h1

/-- Cross multiplication is performed in the integral ring before
passing to the genuine quotient modulo t². Cancellation of t in the
integral ring, not division by its residue, makes the linear
coefficient faithful. -/
theorem cross_from_same_germ (A B : k[X]) (x e z : k) (he : e ≠ 0) (hB : B.eval x ≠ 0)
    (X Y c d : FormalValuation k)
    (hX : X = constVal k x + parameter k * constVal k e + (parameter k)^2*c)
    (hY : Y = constVal k z + (parameter k)^2*d)
    (hRat : (FormalValuation k).subtype Y =
      A.eval₂ (constField k) ((FormalValuation k).subtype X) /
      B.eval₂ (constField k) ((FormalValuation k).subtype X)) :
    (A.derivative*B-A*B.derivative).eval x = 0 := by
  let V := FormalValuation k
  let t := parameter k
  let C := constVal k
  let Cfield := constField k
  have hX0 : constantTerm k X = x := (congrArg (constantTerm k) hX).trans (linear_arc_constant x e c)
  have hY0 : constantTerm k Y = z := by
    rw [hY]
    simp only [map_add,map_mul,map_pow,constantTerm_const,parameter_const,
      zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,add_zero]
  have hmap (P : k[X]) : V.subtype (P.eval₂ C X) = P.eval₂ Cfield (V.subtype X) :=
    map_eval₂_lift C V.subtype P X
  have hDen : B.eval₂ Cfield (V.subtype X) ≠ 0 := by
    intro eB
    have hZ : B.eval₂ C X = 0 :=
      V.subtype_injective ((hmap B).trans (eB.trans (map_zero V.subtype).symm))
    apply hB
    have h0 := congrArg (constantTerm k) hZ
    rw [value_constant,hX0,map_zero] at h0
    exact h0
  have hIntegral : Y * B.eval₂ C X = A.eval₂ C X := by
    apply V.subtype_injective
    rw [map_mul,hmap B,hmap A]
    exact (eq_div_iff hDen).mp hRat
  have hConstant : z*B.eval x = A.eval x := by
    have h := congrArg (constantTerm k) hIntegral
    rw [map_mul,value_constant,value_constant,hX0,hY0] at h
    exact h
  let S := V ⧸ jetIdeal k
  let q : V →+* S := Ideal.Quotient.mk _
  let j := q.comp C
  let ε := q t
  have hε : ε^2 = 0 := by
    change (q (parameter k))^2 = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [jetIdeal]))
  have hT : q ((parameter k)^2) = 0 := (map_pow q t 2).trans hε
  have hCancel (u : k) (h : ε*j u = 0) : u = 0 := by
    have e : q (t*C u)=0 := by
      rw [map_mul]
      exact h
    exact parameter_times_const_cancel u (Ideal.Quotient.eq_zero_iff_mem.mp e)
  have hJX : q X = j x + ε * j e := by
    rw [hX]
    simp only [map_add,map_mul,hT,zero_mul,add_zero,j,RingHom.comp_apply,ε,C,t]
  have hJY : q Y = j z := by
    rw [hY]
    simp only [map_add,map_mul,hT,zero_mul,add_zero,j,RingHom.comp_apply,C,t]
  have hj := congrArg q hIntegral
  rw [map_mul,map_eval₂_lift,map_eval₂_lift,hJX,hJY] at hj
  letI : Algebra k S := j.toAlgebra
  let U := algebraMap k S x + ε * algebraMap k S e
  have hj' : algebraMap k S z * B.aeval U = A.aeval U := hj
  have hCross : A.aeval U * algebraMap k S (B.eval x) =
      algebraMap k S (A.eval x) * B.aeval U := by
    rw [←hj',←hConstant,map_mul]
    ring
  have hnil : (ε * algebraMap k S e)^2 = 0 := by rw [mul_pow,hε,zero_mul]
  change A.aeval (algebraMap k S x + ε * algebraMap k S e) * algebraMap k S (B.eval x) =
    algebraMap k S (A.eval x) * B.aeval (algebraMap k S x + ε * algebraMap k S e) at hCross
  rw [Polynomial.aeval_add_of_sq_eq_zero A _ _ hnil,
      Polynomial.aeval_add_of_sq_eq_zero B _ _ hnil] at hCross
  simp only [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hCross
  have hFinal : e*((A.derivative*B-A*B.derivative).eval x)=0 := by
    apply hCancel
    change ε * algebraMap k S (e*((A.derivative*B-A*B.derivative).eval x)) = 0
    simp only [eval_mul,eval_sub,map_mul,map_sub]
    linear_combination hCross
  exact (mul_eq_zero.mp hFinal).resolve_left he

end ActualGaussianWeberSameRatioJetCross318
