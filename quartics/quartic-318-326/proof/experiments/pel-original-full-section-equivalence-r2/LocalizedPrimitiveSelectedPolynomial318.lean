module
public import LocalizedPrimitiveSelectedGraphs318
public import AnalyticFiniteRootProduct318
public section
noncomputable section
namespace LocalizedPrimitiveSelectedPolynomial318
open Set Filter Polynomial
open scoped Topology
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
open LocalizedPrimitiveSelectedGraphs318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

@[expose] def point (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
    (r : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)) : OpenRoots d Q :=
  ⟨⟨(v,r.val),(LocalizedPrimitiveRootChart318.equation_on_open d Q v hv r.val).trans r.property⟩,hv⟩

@[expose] def allRoots (hm : Q.Monic) (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    Finset (Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)) := by
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  letI : Fintype (Roots Q V) := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
    (rootsEquivRootSet Q V hm).symm
  exact Finset.univ

lemma mem_allRoots (hm : Q.Monic) (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
    (r : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)) :
    r ∈ allRoots d Q hm v hv := by
  simp [allRoots]

@[expose] def selectedRoots (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    Finset (Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)) := by
  classical
  exact (allRoots d Q hm v hv).filter (fun r => point d Q v hv r ∈ S)

lemma mem_selectedRoots (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
    (r : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)) :
    r ∈ selectedRoots d Q hm S v hv ↔ point d Q v hv r ∈ S := by
  classical
  simp only [selectedRoots,Finset.mem_filter,mem_allRoots,true_and]

/-- Canonical fiber product: each actual selected simple root occurs
once. It does not depend on any ordering or analytic graph choices. -/
@[expose] def fiberPolynomial (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) : Polynomial ℂ :=
  ∏ r ∈ selectedRoots d Q hm S v hv, (Polynomial.X - Polynomial.C r.val)

/-- A single globally defined coefficient source. Its arbitrary value
outside D(d) is never used for an analytic or algebraic conclusion. -/
@[expose] def selectedPolynomial (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) : Polynomial ℂ := by
  classical
  exact if hv : MvPolynomial.eval v d ≠ 0 then fiberPolynomial d Q hm S v hv else 1

lemma selectedPolynomial_on_open (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    selectedPolynomial d Q hm S v = fiberPolynomial d Q hm S v hv := by
  classical
  simp only [selectedPolynomial,dif_pos hv]


/-- Literal root membership for the canonical fiber product, with each
independent root identified as the same point of the whole root locus. -/
theorem selected_root_iff (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (q : OpenRoots d Q) :
    (selectedPolynomial d Q hm S q.val.val.1).eval q.val.val.2 = 0 ↔ q ∈ S := by
  classical
  rw [selectedPolynomial_on_open d Q hm S _ q.property]
  simp only [fiberPolynomial,Polynomial.eval_prod,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_C,Finset.prod_eq_zero_iff,sub_eq_zero]
  constructor
  · rintro ⟨r,hr,hval⟩
    have he : point d Q q.val.val.1 q.property r = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl hval.symm
    rw [←he]
    exact (mem_selectedRoots d Q hm S _ q.property r).mp hr
  · intro hq
    let r : Roots Q (ComplexPolynomialOpenPoints318.evaluation d q.val.val.1 q.property) :=
      ⟨q.val.val.2,(LocalizedPrimitiveRootChart318.equation_on_open d Q _ q.property _).symm.trans
        q.val.property⟩
    have he : point d Q q.val.val.1 q.property r = q := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    refine ⟨r,(mem_selectedRoots d Q hm S _ q.property r).mpr ?_,rfl⟩
    rw [he]
    exact hq

lemma selected_monic (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    (selectedPolynomial d Q hm S v).Monic := by
  rw [selectedPolynomial_on_open d Q hm S v hv]
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

/-- Any locally exhaustive selected graph list gives the SAME canonical
fiber product. The proof is a finite bijection of actual root subtypes,
not a claim that roots determine polynomials without multiplicities. -/
lemma product_eq_fiber {I : Type*} (hm : Q.Monic) (S : Set (OpenRoots d Q))
    (w : ι → ℂ) (hw : MvPolynomial.eval w d ≠ 0)
    (T : Finset I) (g : I → ℂ)
    (hr : ∀ i, LocalizedPrimitiveRootChart318.equation d Q (w,g i) = 0)
    (hi : Function.Injective g)
    (hS : ∀ q : OpenRoots d Q, q.val.val.1 = w →
      (q ∈ S ↔ ∃ i ∈ T, g i = q.val.val.2)) :
    (∏ i ∈ T, (Polynomial.X - Polynomial.C (g i))) = fiberPolynomial d Q hm S w hw := by
  classical
  let k (i : I) : Roots Q (ComplexPolynomialOpenPoints318.evaluation d w hw) :=
    ⟨g i,(LocalizedPrimitiveRootChart318.equation_on_open d Q w hw (g i)).symm.trans (hr i)⟩
  unfold fiberPolynomial
  apply Finset.prod_bij (fun i _ => k i)
  · intro i hit
    apply (mem_selectedRoots d Q hm S w hw (k i)).mpr
    exact (hS (point d Q w hw (k i)) rfl).mpr ⟨i,hit,rfl⟩
  · intro i hit j hjt hij
    exact hi (congrArg Subtype.val hij)
  · intro r hrt
    obtain ⟨i,hit,hir⟩ := (hS (point d Q w hw r) rfl).mp
      ((mem_selectedRoots d Q hm S w hw r).mp hrt)
    exact ⟨i,hit,Subtype.ext hir⟩
  · intro i hit
    rfl

/-- The canonical selected polynomial agrees on a genuine neighborhood
with one finite product of analytic simple-root graphs. This supplies
actual global coefficient gluing without a rationality assumption. -/
theorem exists_local_product (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (ho : IsOpen S) (hc : IsClosed S)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ v ∈ U ∧
    ∃ g : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv) → (ι → ℂ) → ℂ,
    ∃ T : Finset (Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)),
      ∀ w ∈ U, MvPolynomial.eval w d ≠ 0 ∧
        (∀ i ∈ T, AnalyticAt ℂ (g i) w) ∧
        selectedPolynomial d Q hm S w = AnalyticFiniteRootProduct318.factor T g w := by
  obtain ⟨U,hU,hUv,g,T,hcenter,hg⟩ := exists_selected_graphs d Q hm hs S ho hc v hv
  refine ⟨U,hU,hUv,g,T,?_⟩
  intro w hw
  have h := hg w hw
  refine ⟨h.1,fun i _ => (h.2.1 i).1,?_⟩
  rw [selectedPolynomial_on_open d Q hm S w h.1]
  exact (product_eq_fiber d Q hm S w h.1 T (fun i => g i w)
    (fun i => (h.2.1 i).2) h.2.2.1 h.2.2.2.2).symm

/-- Every coefficient is one global function analytic on the genuine
principal open. No meromorphic extension, growth estimate or polynomial
numerator is smuggled into this assertion. -/
theorem selected_coeff_analytic (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (ho : IsOpen S) (hc : IsClosed S)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) (n : ℕ) :
    AnalyticAt ℂ (fun w => (selectedPolynomial d Q hm S w).coeff n) v := by
  obtain ⟨U,hU,hUv,g,T,hg⟩ := exists_local_product d Q hm hs S ho hc v hv
  have ha := AnalyticFiniteRootProduct318.factor_coeff_analytic T g v (hg v hUv).2.1 n
  apply ha.congr
  filter_upwards [hU.mem_nhds hUv] with w hw
  exact congrArg (fun P : Polynomial ℂ => P.coeff n) (hg w hw).2.2.symm
end LocalizedPrimitiveSelectedPolynomial318
