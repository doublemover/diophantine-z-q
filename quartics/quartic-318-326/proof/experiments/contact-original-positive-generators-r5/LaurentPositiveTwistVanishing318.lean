module
public import LaurentCechFinite318
public section
noncomputable section
namespace LaurentPositiveTwistVanishing318
open LaurentVectorFiltration318 LaurentTransitionBounds318
set_option maxHeartbeats 600000
universe u
variable {k : Type u} [Field k] {r : ℕ}

/-- Multiplication by the ACTUAL Laurent monomial, with its actual inverse. -/
def shift (d : ℤ) : V k r ≃ₗ[LaurentPolynomial k] V k r where
  toFun v := (LaurentPolynomial.T d : LaurentPolynomial k) • v
  invFun v := (LaurentPolynomial.T (-d) : LaurentPolynomial k) • v
  left_inv v := by
    rw [smul_smul,← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero,one_smul]
  right_inv v := by
    rw [smul_smul,← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,one_smul]
  map_add' := smul_add _
  map_smul' a v := smul_comm _ _ _

/-- The displayed old transition multiplied by the original positive
Laurent monomial. Identification with a geometric tensor twist is separate. -/
def transition (e : V k r ≃ₗ[LaurentPolynomial k] V k r) (d : ℤ) := e.trans (shift d)

lemma inverse_apply (e : V k r ≃ₗ[LaurentPolynomial k] V k r) (d : ℤ) (v : V k r) :
    (transition e d).symm v = (LaurentPolynomial.T (-d) : LaurentPolynomial k) • e.symm v :=
  e.symm.map_smul _ _

/-- The existing bound on the OLD inverse columns shifts by exactly -d;
no new bound on a modified, unknown transition is postulated. -/
lemma inverse_column_bound (e : V k r ≃ₗ[LaurentPolynomial k] V k r)
    (b : ℤ) (hb : ∀ i : Fin r, e.symm (monomial i 0) ∈ upper b) (d : ℤ) :
    ∀ i : Fin r, (transition e d).symm (monomial i 0) ∈ upper (-d+b) := by
  intro i
  rw [inverse_apply]
  exact shift_upper (-d) b (hb i)

/-- The actual two-chart restriction image is the whole Laurent module
after every shift at least the proved original inverse-column bound. -/
lemma boundary_eq_top (e : V k r ≃ₗ[LaurentPolynomial k] V k r)
    (b : ℤ) (hb : ∀ i : Fin r, e.symm (monomial i 0) ∈ upper b)
    (d : ℤ) (hd : b ≤ d) : LaurentCechFinite318.boundary (transition e d) = ⊤ := by
  apply top_unique
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ (supported_univ v)
  · rintro w ⟨i,a,ha,rfl⟩
    by_cases hpos : 0 ≤ a
    · exact (le_sup_left : positive ≤ LaurentCechFinite318.boundary (transition e d))
        (monomial_mem i a hpos)
    · exact (le_sup_right : negative.map (underlying (transition e d)) ≤
        LaurentCechFinite318.boundary (transition e d))
        (negative_tail (transition e d) (-d+b) (inverse_column_bound e b hb d) i a (by omega))
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

lemma quotient_zero (e : V k r ≃ₗ[LaurentPolynomial k] V k r)
    (b : ℤ) (hb : ∀ i : Fin r, e.symm (monomial i 0) ∈ upper b)
    (d : ℤ) (hd : b ≤ d) (x : LaurentCechFinite318.H1 (transition e d)) : x = 0 := by
  obtain ⟨v,rfl⟩ := (LaurentCechFinite318.boundary (transition e d)).mkQ_surjective x
  rw [Submodule.mkQ_apply]
  apply Submodule.Quotient.mk_eq_zero.mpr
  rw [boundary_eq_top e b hb d hd]
  trivial

/-- A uniform eventual-vanishing threshold is CONSTRUCTED for all positive
integer shifts of this same transition, rather than chosen separately for
each shift. The geometric twist identification remains an explicit next join. -/
theorem exists_vanishing_bound (e : V k r ≃ₗ[LaurentPolynomial k] V k r) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : LaurentCechFinite318.H1 (transition e (n : ℤ)), x = 0 := by
  obtain ⟨b,hb⟩ := exists_column_bound e.symm
  refine ⟨b.toNat,fun n hn x => quotient_zero e b hb n ?_ x⟩
  omega
end LaurentPositiveTwistVanishing318
