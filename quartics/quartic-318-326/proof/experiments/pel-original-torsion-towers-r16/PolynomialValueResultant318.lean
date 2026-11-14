module
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public section
noncomputable section
namespace PolynomialValueResultant318
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Y is the outer variable, T the coefficient-ring variable. This is
the literal relation T-H(Y), retaining the original coefficients. -/
@[expose] def relation (H : Polynomial R) : Polynomial (Polynomial R) :=
  C X-H.map C

/-- The literal norm equation Res_Y(Q(Y),T-H(Y)). Fixed degree bounds
are explicit so specialization never changes the Sylvester matrix. -/
@[expose] def equation (Q H : Polynomial R) (m n : ℕ) : Polynomial R :=
  (Q.map C).resultant (relation H) m n

lemma relation_degree (H : Polynomial R) :
    (relation H).natDegree ≤ H.natDegree+1 := by
  apply (natDegree_sub_le _ _).trans
  exact max_le (natDegree_C_le.trans (Nat.zero_le _))
    (natDegree_map_le.trans (Nat.le_succ _))

lemma relation_map (H : Polynomial R) (φ : R →+* S) :
    (relation H).map (Polynomial.mapRingHom φ) = relation (H.map φ) := by
  simp only [relation,Polynomial.map_sub,Polynomial.map_C,Polynomial.coe_mapRingHom,
    Polynomial.map_X,Polynomial.map_map,Polynomial.mapRingHom_comp_C]

/-- Specialization uses the SAME fixed matrix sizes even when H loses
its leading coefficient. No generic-degree specialization is assumed. -/
lemma equation_map (Q H : Polynomial R) (m n : ℕ) (φ : R →+* S) :
    (equation Q H m n).map φ = equation (Q.map φ) (H.map φ) m n := by
  change (Polynomial.mapRingHom φ) ((Q.map C).resultant (relation H) m n) = _
  rw [←Polynomial.resultant_map_map,relation_map]
  simp only [equation,Polynomial.map_map,Polynomial.mapRingHom_comp_C]

lemma relation_eval (H : Polynomial R) (r : R) :
    (relation H).eval (C r) = X-C (H.eval r) := by
  simp only [relation,Polynomial.eval_sub,Polynomial.eval_C,Polynomial.eval_map_apply]

/-- The actual resultant vanishes at H(beta) whenever Q(beta)=0.
This follows from the FULL resultant Bezout identity over R[T], not
from a selected set of complex points. -/
theorem annihilates (Q H : Polynomial R) (φ : R →+* S) (β : S)
    (hβ : Q.eval₂ φ β=0) :
    (equation Q H Q.natDegree (H.natDegree+1)).eval₂ φ (H.eval₂ φ β)=0 := by
  obtain ⟨p,q,hp,hq,he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (Q.map C) (relation H) (natDegree_map_le) (relation_degree H)
    (Or.inr (Nat.succ_ne_zero _))
  let e : Polynomial R →+* S := Polynomial.eval₂RingHom φ (H.eval₂ φ β)
  let f : Polynomial (Polynomial R) →+* S := Polynomial.eval₂RingHom e β
  have hQ : f (Q.map C)=0 := by
    change (Q.map C).eval₂ e β=0
    rw [Polynomial.eval₂_map,Polynomial.eval₂RingHom_comp_C]
    exact hβ
  have hH : f (relation H)=0 := by
    change (C X-H.map C).eval₂ e β=0
    rw [Polynomial.eval₂_sub,Polynomial.eval₂_C,Polynomial.eval₂_map,
      Polynomial.eval₂RingHom_comp_C]
    change H.eval₂ φ β-H.eval₂ φ β=0
    exact sub_self _
  have h := congrArg f he
  rw [map_add,map_mul,map_mul,hQ,hH,zero_mul,zero_add,zero_mul] at h
  exact h.symm

/-- The full specialized norm equation is the product of all values
H(r_i), including repetitions among those values. No injectivity of H
or selected branch is used. -/
theorem equation_product [Nontrivial R] (Q H : Polynomial R) (m n : ℕ)
    (r : Fin m → R) (hQ : Q=∏ i : Fin m, (X-C (r i)))
    (hn : (relation H).natDegree ≤ n) :
    equation Q H m n = ∏ i : Fin m, (X-C (H.eval (r i))) := by
  classical
  have hmap : Q.map C=∏ i : Fin m, (X-C (C (r i))) := by
    rw [hQ]
    simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  have hdeg : (∏ i : Fin m, (X-C (C (r i)) : Polynomial (Polynomial R))).natDegree=m := by
    rw [Polynomial.natDegree_prod_of_monic (fun _ _ => Polynomial.monic_X_sub_C _)]
    simp
  have hlead : ∏ i : Fin m, (X-C (C (r i)) : Polynomial (Polynomial R)).leadingCoeff ≠ 0 := by
    simp only [Polynomial.leadingCoeff_X_sub_C,Finset.prod_const_one,ne_eq,one_ne_zero,not_false_eq_true]
  have hr := Polynomial.resultant_prod_left Finset.univ
    (fun i : Fin m => (X-C (C (r i)) : Polynomial (Polynomial R))) (relation H) n hlead hn
  rw [hdeg] at hr
  unfold equation
  rw [hmap,hr]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left (relation H) n (C (r i)) hn,relation_eval]
end PolynomialValueResultant318
