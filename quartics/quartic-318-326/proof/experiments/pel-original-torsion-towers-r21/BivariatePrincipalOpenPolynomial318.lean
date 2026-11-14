module
public import BivariateFiniteGridPolynomial318
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Basic
public section
noncomputable section
namespace BivariatePrincipalOpenPolynomial318
open Set Filter Polynomial
open scoped Topology BigOperators

@[expose] def horizontal (d : MvPolynomial (Fin 2) ℂ) (y : ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C ![Polynomial.X,Polynomial.C y] d
@[expose] def vertical (d : MvPolynomial (Fin 2) ℂ) (x : ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C ![Polynomial.C x,Polynomial.X] d

lemma horizontal_eval (d : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    (horizontal d y).eval x = MvPolynomial.eval ![x,y] d := by
  change (Polynomial.evalRingHom x) (MvPolynomial.eval₂ Polynomial.C
    ![Polynomial.X,Polynomial.C y] d) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℂ := by ext c; simp
  change MvPolynomial.eval₂ ((Polynomial.evalRingHom x).comp Polynomial.C)
    (fun i => Polynomial.eval x (![Polynomial.X,Polynomial.C y] i)) d = _
  rw [hc]
  have hv : (fun i => Polynomial.eval x (![Polynomial.X,Polynomial.C y] i)) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  rw [hv,MvPolynomial.eval₂_id]
lemma vertical_eval (d : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    (vertical d x).eval y = MvPolynomial.eval ![x,y] d := by
  change (Polynomial.evalRingHom y) (MvPolynomial.eval₂ Polynomial.C
    ![Polynomial.C x,Polynomial.X] d) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : (Polynomial.evalRingHom y).comp Polynomial.C = RingHom.id ℂ := by ext c; simp
  rw [hc]
  have hv : (fun i => (Polynomial.evalRingHom y) (![Polynomial.C x,Polynomial.X] i)) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  rw [hv,MvPolynomial.eval₂_id]

lemma exists_nonzero_pair (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0) :
    ∃ x y : ℂ, MvPolynomial.eval ![x,y] d ≠ 0 := by
  by_contra! h
  apply hd
  apply MvPolynomial.funext
  intro v
  have he : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  simpa only [he,map_zero] using h (v 0) (v 1)

/-- A nonzero bivariate polynomial admits arbitrarily long distinct
horizontal interpolation grids, every chosen vertical polynomial nonzero. -/
theorem exists_grid (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0) (N : ℕ) :
    ∃ v : Fin (N+1) → ℂ, Function.Injective v ∧ ∀ i, vertical d (v i) ≠ 0 := by
  classical
  obtain ⟨x,y,hxy⟩ := exists_nonzero_pair d hd
  have hp : horizontal d y ≠ 0 := by
    intro hz
    apply hxy
    rw [←horizontal_eval,hz,Polynomial.eval_zero]
  let S : Set ℂ := {x | (horizontal d y).IsRoot x}
  have hS : S.Finite := Polynomial.finite_setOfPred_isRoot hp
  let e : ℕ ↪ Sᶜ := hS.infinite_compl.natEmbedding _
  let v : Fin (N+1) → ℂ := fun i => (e i.val).val
  refine ⟨v,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    exact e.injective (Subtype.ext hij)
  · intro i hz
    have hn := (e i.val).property
    apply hn
    change (horizontal d y).eval (v i) = 0
    rw [horizontal_eval,←vertical_eval,hz,Polynomial.eval_zero]

/-- Uniform polynomial growth on a true principal open forces an
actual bivariate polynomial numerator. Finite-hole one-variable filling
and finite interpolation replace any unproved several-variable extension
or analytic-to-rational assumption. -/
theorem exists_polynomial (d : MvPolynomial (Fin 2) ℂ) (hd : d ≠ 0)
    (f : ℂ × ℂ → ℂ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x y, MvPolynomial.eval ![x,y] d ≠ 0 → DifferentiableAt ℂ f (x,y))
    (hb : ∀ x y, MvPolynomial.eval ![x,y] d ≠ 0 →
      ‖f (x,y)‖ ≤ C * (1+‖x‖)^N * (1+‖y‖)^N) :
    ∃ P : MvPolynomial (Fin 2) ℂ,
      ∀ x y, MvPolynomial.eval ![x,y] d ≠ 0 → MvPolynomial.eval ![x,y] P = f (x,y) := by
  classical
  obtain ⟨v,hv,hvpol⟩ := exists_grid d hd N
  have hcol (i : Fin (N+1)) : ∃ q : Polynomial ℂ, q.natDegree ≤ N ∧
      ∀ y, MvPolynomial.eval ![v i,y] d ≠ 0 → q.eval y = f (v i,y) := by
    obtain ⟨q,hq,he⟩ := ComplexFiniteHolePolynomial318.exists_polynomial
      {y | (vertical d (v i)).IsRoot y} (Polynomial.finite_setOfPred_isRoot (hvpol i))
      (fun y => f (v i,y)) N (C*(1+‖v i‖)^N) (by positivity)
      (fun y hy => (hf (v i) y (by simpa only [Polynomial.IsRoot.def,vertical_eval] using hy)).comp y
        (differentiableAt_const.prodMk differentiableAt_id))
      (fun y hy => hb (v i) y (by simpa only [Polynomial.IsRoot.def,vertical_eval] using hy))
    exact ⟨q,hq,fun y hy => he y (by simpa only [Polynomial.IsRoot.def,vertical_eval] using hy)⟩
  choose q hq hqe using hcol
  let S : Set ℂ := ⋃ i : Fin (N+1), {y | (vertical d (v i)).IsRoot y}
  have hS : S.Finite := Set.finite_iUnion (fun i => Polynomial.finite_setOfPred_isRoot (hvpol i))
  have hnode (y : ℂ) (hy : y ∉ S) (i : Fin (N+1)) : MvPolynomial.eval ![v i,y] d ≠ 0 := by
    intro hz
    apply hy
    exact Set.mem_iUnion.mpr ⟨i,by simpa only [Polynomial.IsRoot.def,vertical_eval] using hz⟩
  let U : Set (ℂ × ℂ) := {z | MvPolynomial.eval ![z.1,z.2] d ≠ 0}
  have hrow (y : ℂ) (hy : y ∈ Sᶜ) : ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧
      (∀ i, p.eval (v i) = (q i).eval y) ∧ ∀ x, (x,y) ∈ U → p.eval x = f (x,y) := by
    have hp : horizontal d y ≠ 0 := by
      intro hz
      apply hnode y hy ⟨0,by omega⟩
      rw [←horizontal_eval,hz,Polynomial.eval_zero]
    obtain ⟨p,hpdeg,he⟩ := ComplexFiniteHolePolynomial318.exists_polynomial
      {x | (horizontal d y).IsRoot x} (Polynomial.finite_setOfPred_isRoot hp)
      (fun x => f (x,y)) N (C*(1+‖y‖)^N) (by positivity)
      (fun x hx => (hf x y (by simpa only [Polynomial.IsRoot.def,horizontal_eval] using hx)).comp x
        (differentiableAt_id.prodMk differentiableAt_const))
      (fun x hx => by
        have h := hb x y (by simpa only [Polynomial.IsRoot.def,horizontal_eval] using hx)
        nlinarith)
    refine ⟨p,hpdeg,?_,?_⟩
    · intro i
      exact (he (v i) (by simpa only [Polynomial.IsRoot.def,horizontal_eval] using hnode y hy i)).trans
        (hqe i y (hnode y hy i)).symm
    · intro x hx
      exact he x (by simpa only [Polynomial.IsRoot.def,horizontal_eval] using hx)
  obtain ⟨P,hP⟩ := BivariateFiniteGridPolynomial318.exists_polynomial_on_slices N v hv q
    (fun x y => f (x,y)) U Sᶜ hrow
  have hcont : Continuous (fun z : ℂ × ℂ => MvPolynomial.eval ![z.1,z.2] d) := by
    have hc : Continuous (fun v : Fin 2 → ℂ => MvPolynomial.eval v d) :=
      continuous_iff_continuousAt.mpr (fun v =>
        ((AnalyticOnNhd.eval_mvPolynomial d) v (mem_univ v)).continuousAt)
    exact hc.comp (by fun_prop)
  have hU : IsOpen U := isOpen_ne hcont continuous_const
  have hwhole := BivariateFiniteGridPolynomial318.extend_from_cofinite_slices P U hU f
    (fun z hz => (hf z.1 z.2 hz).continuousAt) S hS hP
  exact ⟨P,fun x y hxy => hwhole (x,y) hxy⟩
end BivariatePrincipalOpenPolynomial318
