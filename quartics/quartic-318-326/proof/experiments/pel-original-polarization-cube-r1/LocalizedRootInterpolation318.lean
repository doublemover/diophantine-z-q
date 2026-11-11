module
public import LocalizedPrimitiveSelectedPolynomial318
public import LocalizedSelectedComplementProduct318
public import AnalyticFiniteInterpolation318
public import LagrangeBezoutWeights318
public section
noncomputable section
namespace LocalizedRootInterpolation318
open Polynomial Set Filter
open scoped Topology
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
open LocalizedPrimitiveSelectedGraphs318 LocalizedPrimitiveSelectedPolynomial318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- Canonical interpolation uses EVERY actual independent root once.
The function F is supplied on the whole root locus, not on a chosen sheet. -/
@[expose] def fiber (hm : Q.Monic) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) : Polynomial ℂ := by
  classical
  exact Lagrange.interpolate (allRoots d Q hm v hv) Subtype.val
    (fun r => F (point d Q v hv r))

@[expose] def polynomial (hm : Q.Monic) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) : Polynomial ℂ := by
  classical
  exact if hv : MvPolynomial.eval v d ≠ 0 then fiber d Q hm F v hv else 0

lemma on_open (hm : Q.Monic) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    polynomial d Q hm F v = fiber d Q hm F v hv := by
  simp only [polynomial,dif_pos hv]

lemma allRoots_card (hm : Q.Monic) (hs : Q.Separable)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (allRoots d Q hm v hv).card = Q.natDegree := by
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  letI : Fintype (Roots Q V) := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
    (rootsEquivRootSet Q V hm).symm
  change Fintype.card (Roots Q V) = Q.natDegree
  rw [Fintype.card_congr (rootsEquivRootSet Q V hm),
    Polynomial.card_rootSet_eq_natDegree hs.map (IsAlgClosed.splits _)]
  exact hm.natDegree_map V

lemma degree_lt (hm : Q.Monic) (hs : Q.Separable) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (polynomial d Q hm F v).degree < Q.natDegree := by
  classical
  rw [on_open]
  simpa only [fiber,allRoots_card d Q hm hs v hv] using
    Lagrange.degree_interpolate_lt (fun r => F (point d Q v hv r))
      (Subtype.val_injective.injOn : Set.InjOn
        (Subtype.val : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv) → ℂ)
        (allRoots d Q hm v hv))

/-- The canonical interpolant recovers the exact supplied value at each
whole-root point, with no ordering or primitive-root-choice ambiguity. -/
theorem evaluation (hm : Q.Monic) (F : OpenRoots d Q → ℂ) (q : OpenRoots d Q) :
    (polynomial d Q hm F q.val.val.1).eval q.val.val.2 = F q := by
  classical
  let r : Roots Q (ComplexPolynomialOpenPoints318.evaluation d q.val.val.1 q.property) :=
    ⟨q.val.val.2,(LocalizedPrimitiveRootChart318.equation_on_open d Q _ q.property _).symm.trans
      q.val.property⟩
  have hp : point d Q q.val.val.1 q.property r = q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [on_open]
  exact (Lagrange.eval_interpolate_at_node (fun r => F (point d Q _ q.property r))
    Subtype.val_injective.injOn (mem_allRoots d Q hm _ q.property r)).trans (congrArg F hp)

/-- Any full-degree distinct analytic root list gives the SAME canonical
polynomial once the values are the actual values on those roots. This is
proved by degree and evaluation uniqueness, not by assuming a labeling
of roots extends globally. -/
theorem enumeration_eq {I : Type*} [DecidableEq I]
    (hm : Q.Monic) (hs : Q.Separable) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
    (T : Finset I) (g a : I → ℂ) (hcard : T.card = Q.natDegree)
    (hi : Set.InjOn g T)
    (hr : ∀ i ∈ T, LocalizedPrimitiveRootChart318.equation d Q (v,g i) = 0)
    (ha : ∀ (i : I) (hit : i ∈ T), F ⟨⟨(v,g i),hr i hit⟩,hv⟩ = a i) :
    polynomial d Q hm F v = Lagrange.interpolate T g a := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq T hi
  · rw [hcard]
    exact degree_lt d Q hm hs F v hv
  · exact Lagrange.degree_interpolate_lt a hi
  · intro i hit
    exact (evaluation d Q hm F ⟨⟨(v,g i),hr i hit⟩,hv⟩).trans
      ((ha i hit).trans (Lagrange.eval_interpolate_at_node a hi hit).symm)
/-- Ring separability produces ONE actual pair of localized Bezout
polynomials. Their every specialization supplies the interpolation weights. -/
theorem exists_bezout_formula (hm : Q.Monic) (hs : Q.Separable) :
    ∃ A B : Polynomial (Localization.Away d), A*Q+B*Q.derivative=1 ∧
      ∀ F : OpenRoots d Q → ℂ, ∀ v : ι → ℂ,
      ∀ hv : MvPolynomial.eval v d ≠ 0,
      polynomial d Q hm F v =
        ∑ r ∈ allRoots d Q hm v hv,
          C (F (point d Q v hv r) *
            (B.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval r.val) *
          (∏ t ∈ (allRoots d Q hm v hv).erase r, (X-C t.val)) := by
  classical
  obtain ⟨A,B,hAB⟩ := (Polynomial.separable_def' Q).mp hs
  refine ⟨A,B,hAB,?_⟩
  intro F v hv
  let e := ComplexPolynomialOpenPoints318.evaluation d v hv
  have hab : A.map e * Q.map e + B.map e * (Q.map e).derivative = 1 := by
    simpa only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one,
      Polynomial.derivative_map] using congrArg (Polynomial.map e) hAB
  have hn : Lagrange.nodal (allRoots d Q hm v hv) Subtype.val = Q.map e :=
    LocalizedSelectedComplementProduct318.all_root_product d Q hm hs v hv
  rw [on_open]
  exact LagrangeBezoutWeights318.interpolate_eq _ _ _ _ _ _ hn hab
/-- A genuine local exhaustive graph description with analytic values
implies analyticity of the globally canonical coefficient. All equalities
are on the SAME principal open; no global root enumeration is chosen. -/
theorem coefficient_analytic_of_enumeration {I : Type*} [DecidableEq I]
    (hm : Q.Monic) (hs : Q.Separable) (F : OpenRoots d Q → ℂ)
    (v : ι → ℂ) (U : Set (ι → ℂ)) (hU : IsOpen U) (hvU : v ∈ U)
    (T : Finset I) (g a : I → (ι → ℂ) → ℂ) (hcard : T.card = Q.natDegree)
    (hd : ∀ w ∈ U, MvPolynomial.eval w d ≠ 0)
    (hi : ∀ w ∈ U, Set.InjOn (fun i => g i w) T)
    (hr : ∀ w ∈ U, ∀ i ∈ T, LocalizedPrimitiveRootChart318.equation d Q (w,g i w)=0)
    (ha : ∀ (w : ι → ℂ) (hw : w ∈ U) (i : I) (hit : i ∈ T),
      F ⟨⟨(w,g i w),hr w hw i hit⟩,hd w hw⟩ = a i w)
    (hgA : ∀ i ∈ T, AnalyticAt ℂ (g i) v)
    (haA : ∀ i ∈ T, AnalyticAt ℂ (a i) v) (n : ℕ) :
    AnalyticAt ℂ (fun w => (polynomial d Q hm F w).coeff n) v := by
  have h := AnalyticFiniteInterpolation318.coefficient_analytic T g a v hgA haA (hi v hvU) n
  apply h.congr
  filter_upwards [hU.mem_nhds hvU] with w hw
  exact congrArg (fun P : Polynomial ℂ => P.coeff n)
    (enumeration_eq d Q hm hs F w (hd w hw) T (fun i => g i w) (fun i => a i w)
      hcard (hi w hw) (hr w hw) (ha w hw)).symm
end LocalizedRootInterpolation318
