module
public import ComplexFiniteHolePolynomial318
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Analytic.Polynomial
public section
noncomputable section
namespace BivariateFiniteGridPolynomial318
open Set Filter Polynomial
open scoped Topology BigOperators

@[expose] def coordinatePolynomial (i : Fin 2) (p : Polynomial ℂ) : MvPolynomial (Fin 2) ℂ :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i)

lemma eval_coordinatePolynomial (v : Fin 2 → ℂ) (i : Fin 2) (p : Polynomial ℂ) :
    MvPolynomial.eval v (coordinatePolynomial i p) = p.eval (v i) := by
  simp only [coordinatePolynomial,Polynomial.hom_eval₂,MvPolynomial.eval_X]
  have h : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    simp only [RingHom.comp_apply,MvPolynomial.eval_C,RingHom.id_apply]
  rw [h,Polynomial.eval₂_id]

/-- Finite-grid reconstruction on every nonexceptional horizontal slice.
The right-hand object is an actual two-variable polynomial, with vertical
polynomial coefficients and fixed original interpolation nodes. -/
theorem exists_polynomial_on_slices (N : ℕ) (v : Fin (N+1) → ℂ)
    (hv : Function.Injective v) (q : Fin (N+1) → Polynomial ℂ)
    (f : ℂ → ℂ → ℂ) (U : Set (ℂ × ℂ)) (Y : Set ℂ)
    (hrow : ∀ y ∈ Y, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧
      (∀ i, p.eval (v i) = (q i).eval y) ∧ ∀ x, (x,y) ∈ U → p.eval x = f x y) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      ∀ y ∈ Y, ∀ x, (x,y) ∈ U → MvPolynomial.eval ![x,y] P = f x y := by
  classical
  let P : MvPolynomial (Fin 2) ℂ := ∑ i : Fin (N+1),
    coordinatePolynomial 0 (Lagrange.basis Finset.univ v i) * coordinatePolynomial 1 (q i)
  refine ⟨P,?_⟩
  intro y hy x hx
  obtain ⟨p,hp,hnode,hval⟩ := hrow y hy
  have hdeg : p.degree < (Finset.univ : Finset (Fin (N+1))).card := by
    have hle := Polynomial.degree_le_of_natDegree_le hp
    simpa only [Finset.card_univ,Fintype.card_fin] using
      hle.trans_lt (by exact_mod_cast Nat.lt_succ_self N)
  have he : p = Lagrange.interpolate Finset.univ v (fun i => (q i).eval y) :=
    Lagrange.eq_interpolate_of_eval_eq _ hv.injOn hdeg (fun i _ => hnode i)
  rw [←hval x hx,he]
  simp only [P,map_sum,map_mul,eval_coordinatePolynomial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Lagrange.interpolate_apply,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _
/-- The excluded horizontal parameters form a finite set. Continuity
on the actual open domain forces the SAME polynomial identity on all
remaining slices too; no value outside the domain is used. -/
theorem extend_from_cofinite_slices (P : MvPolynomial (Fin 2) ℂ)
    (U : Set (ℂ × ℂ)) (hU : IsOpen U) (f : ℂ × ℂ → ℂ)
    (hf : ∀ z ∈ U, ContinuousAt f z) (S : Set ℂ) (hS : S.Finite)
    (he : ∀ y ∉ S, ∀ x, (x,y) ∈ U → MvPolynomial.eval ![x,y] P = f (x,y)) :
    ∀ z ∈ U, MvPolynomial.eval ![z.1,z.2] P = f z := by
  intro z hz
  have hc : Continuous (fun y : ℂ => (z.1,y)) := continuous_const.prodMk continuous_id
  have hfc : ContinuousAt (fun y : ℂ => f (z.1,y)) z.2 := (hf z hz).comp z.2 hc.continuousAt
  have hpv : Continuous (fun v : Fin 2 → ℂ => MvPolynomial.eval v P) :=
    continuous_iff_continuousAt.mpr (fun v =>
      ((AnalyticOnNhd.eval_mvPolynomial P) v (mem_univ v)).continuousAt)
  have hpc : Continuous (fun y : ℂ => MvPolynomial.eval ![z.1,y] P) := hpv.comp (by fun_prop)
  have hnear : ∀ᶠ y in 𝓝 z.2, (z.1,y) ∈ U := hc.continuousAt.eventually (hU.mem_nhds hz)
  have havoid : (S \ {z.2})ᶜ ∈ 𝓝 z.2 :=
    (hS.diff {z.2}).isClosed.isOpen_compl.mem_nhds (by simp)
  have heq : (fun y : ℂ => MvPolynomial.eval ![z.1,y] P) =ᶠ[𝓝[≠] z.2]
      (fun y => f (z.1,y)) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear,
      eventually_nhdsWithin_of_eventually_nhds havoid,self_mem_nhdsWithin] with y hy ha hne
    exact he y (fun hs => ha ⟨hs,hne⟩) z.1 hy
  exact tendsto_nhds_unique
    (hpc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hfc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
end BivariateFiniteGridPolynomial318
