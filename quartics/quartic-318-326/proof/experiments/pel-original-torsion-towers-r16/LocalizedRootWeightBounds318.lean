module
public import PrincipalOpenWeight318
public import WeightedMonicRootBound318
public section
noncomputable section
namespace LocalizedRootWeightBounds318
open Polynomial PolynomialWeightBounds318
variable {ι X : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (b : X → ι → ℂ)
variable (hb : ∀ x, MvPolynomial.eval (b x) d ≠ 0)

/-- Every root of the actual monic family is bounded in one common
weight, with no selected branch or simple-root hypothesis. -/
theorem root (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (r : X → ℂ)
    (hr : ∀ x, (Q.map (ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x))).IsRoot (r x)) :
    Bounded (fun x => PrincipalOpenWeight318.weight d (b x)) (fun x => ‖r x‖) := by
  let W := fun x => PrincipalOpenWeight318.weight d (b x)
  have hW (x : X) : 1 ≤ W x := PrincipalOpenWeight318.one_le d (b x)
  obtain ⟨C,hC,N,hcoeff⟩ := uniform hW (Finset.range Q.natDegree)
    (fun n x => ‖ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x) (Q.coeff n)‖)
    (fun n => PrincipalOpenWeight318.localized d (Q.coeff n) b hb)
  have hbound : Bounded W (fun x => C*W x^N+1) :=
    add hW ⟨C,hC,N,fun _ => le_rfl⟩ (const 1)
  apply mono hbound
  intro x
  let e := ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x)
  have hc : ∀ n < (Q.map e).natDegree, 1*‖(Q.map e).coeff n‖ ≤ C*W x^N := by
    intro n hn
    rw [hm.natDegree_map e] at hn
    simpa only [one_mul,Polynomial.coeff_map] using hcoeff n (Finset.mem_range.mpr hn) x
  simpa only [one_mul] using WeightedMonicRootBound318.root_bound (Q.map e) (hm.map e)
    1 (C*W x^N) zero_lt_one (mul_nonneg hC (pow_nonneg (zero_le_one.trans (hW x)) _))
    hc (r x) (hr x)

/-- Evaluation of EVERY fixed polynomial over the whole localization
at a bounded root has the same kind of uniform bound. -/
theorem polynomial (P : Polynomial (Localization.Away d)) (r : X → ℂ)
    (hr : Bounded (fun x => PrincipalOpenWeight318.weight d (b x)) (fun x => ‖r x‖)) :
    Bounded (fun x => PrincipalOpenWeight318.weight d (b x))
      (fun x => ‖P.eval₂ (ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x)) (r x)‖) := by
  classical
  let W := fun x => PrincipalOpenWeight318.weight d (b x)
  have hW (x : X) : 1 ≤ W x := PrincipalOpenWeight318.one_le d (b x)
  have ht (n : ℕ) : Bounded W (fun x =>
      ‖ComplexPolynomialOpenPoints318.evaluation d (b x) (hb x) (P.coeff n)‖ * ‖r x‖^n) :=
    mul (fun x => zero_le_one.trans (hW x))
      (PrincipalOpenWeight318.localized d (P.coeff n) b hb)
      (pow (fun x => zero_le_one.trans (hW x)) hr (fun x => norm_nonneg _) n)
      (fun x => pow_nonneg (norm_nonneg _) _)
  apply mono (sum hW P.support _ (fun n _ => ht n))
  intro x
  rw [Polynomial.eval₂_eq_sum,Polynomial.sum]
  exact (norm_sum_le _ _).trans (le_of_eq (by
    apply Finset.sum_congr rfl
    intro n hn
    rw [norm_mul,norm_pow]))
end LocalizedRootWeightBounds318
