module
public import LocalizedPrimitiveExhaustiveGraphs318
public import FiniteClopenSelection318
public section
noncomputable section
namespace LocalizedPrimitiveSelectedGraphs318
open Set Filter Polynomial
open scoped Topology
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- The whole independently topologized root locus on the true base open. -/
abbrev OpenRoots := {q : AnalyticParameterizedRootChart318.ZeroLocus
  (LocalizedPrimitiveRootChart318.equation d Q) // MvPolynomial.eval q.val.1 d ≠ 0}

/-- A clopen subset selects a FIXED finite set of the exhaustive simple
root graphs on a genuine common base neighborhood. The subset and the
ambient roots are supplied independently; no exhaustion of the selected
subset by all candidate roots is assumed. -/
theorem exists_selected_graphs (hm : Q.Monic) (hs : Q.Separable)
    (S : Set (OpenRoots d Q)) (ho : IsOpen S) (hc : IsClosed S)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ v ∈ U ∧
    ∃ g : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv) → (ι → ℂ) → ℂ,
    ∃ T : Finset (Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)),
      (∀ i, g i v = i.val) ∧
      ∀ w ∈ U,
        MvPolynomial.eval w d ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (g i) w ∧
          LocalizedPrimitiveRootChart318.equation d Q (w,g i w) = 0) ∧
        Function.Injective (fun i => g i w) ∧
        (∀ z : ℂ, LocalizedPrimitiveRootChart318.equation d Q (w,z) = 0 ↔
          ∃ i, g i w = z) ∧
        ∀ q : OpenRoots d Q, q.val.val.1 = w →
          (q ∈ S ↔ ∃ i ∈ T, g i w = q.val.val.2) := by
  classical
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  let I := Roots Q V
  letI : Fintype I := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
    (rootsEquivRootSet Q V hm).symm
  obtain ⟨U,hU,hUv,g,hcenter,hg⟩ :=
    LocalizedPrimitiveExhaustiveGraphs318.exists_exhaustive_graphs d Q hm hs v hv
  let f : I → U → OpenRoots d Q := fun i w =>
    ⟨⟨(w.val,g i w.val),((hg w.val w.property).2.1 i).2⟩,(hg w.val w.property).1⟩
  have hf (i : I) : Continuous (f i) := by
    have hgi : Continuous (fun w : U => g i w.val) := by
      apply continuous_iff_continuousAt.mpr
      intro w
      exact (((hg w.val w.property).2.1 i).1.continuousAt).comp
        continuous_subtype_val.continuousAt
    exact (continuous_subtype_val.prodMk hgi).subtype_mk _ |>.subtype_mk _
  obtain ⟨W,hW,hWv,hselect⟩ :=
    FiniteClopenSelection318.exists_selection_neighborhood f hf S ho hc ⟨v,hUv⟩
  let T : Finset I := Finset.univ.filter (fun i => f i ⟨v,hUv⟩ ∈ S)
  refine ⟨Subtype.val '' W,hU.isOpenMap_subtype_val W hW,
    ⟨⟨v,hUv⟩,hWv,rfl⟩,g,T,hcenter,?_⟩
  rintro w ⟨u,hu,rfl⟩
  refine ⟨(hg u.val u.property).1,(hg u.val u.property).2.1,
    (hg u.val u.property).2.2.1,(hg u.val u.property).2.2.2,?_⟩
  intro q hq
  have hsame (i : I) (hi : g i u.val = q.val.val.2) : q = f i u := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hq hi.symm
  constructor
  · intro hqS
    have heq : LocalizedPrimitiveRootChart318.equation d Q (u.val,q.val.val.2) = 0 := by
      rw [←hq]
      exact q.val.property
    obtain ⟨i,hi⟩ := ((hg u.val u.property).2.2.2 _).mp heq
    refine ⟨i,?_,hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(hselect u hu i).mp ?_⟩
    rw [←hsame i hi]
    exact hqS
  · rintro ⟨i,hi,hroot⟩
    rw [hsame i hroot]
    exact (hselect u hu i).mpr (Finset.mem_filter.mp hi).2
end LocalizedPrimitiveSelectedGraphs318
