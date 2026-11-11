module
public import LocalizedPrimitiveRootChart318
public import Mathlib.Data.Fintype.EquivFin
public section
noncomputable section
namespace LocalizedPrimitiveExhaustiveGraphs318
open Set Filter Polynomial
open scoped Topology
open AdjoinRootSpecializedPoints318 AdjoinRootSeparablePointCount318
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- All simple roots over one base point extend simultaneously to
pairwise distinct analytic graphs on ONE genuine base neighborhood.
These graphs exhaust EVERY root over EVERY point of that neighborhood,
by the exact monic degree count. No selected analytic-image sheet is
used to define the root family or to exclude additional roots. -/
theorem exists_exhaustive_graphs (hm : Q.Monic) (hs : Q.Separable)
    (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ U : Set (ι → ℂ), IsOpen U ∧ v ∈ U ∧
    ∃ g : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv) → (ι → ℂ) → ℂ,
      (∀ i, g i v = i.val) ∧
      ∀ w ∈ U,
        MvPolynomial.eval w d ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (g i) w ∧
          LocalizedPrimitiveRootChart318.equation d Q (w,g i w) = 0) ∧
        Function.Injective (fun i => g i w) ∧
        ∀ z : ℂ, LocalizedPrimitiveRootChart318.equation d Q (w,z) = 0 ↔
          ∃ i, g i w = z := by
  classical
  let V := ComplexPolynomialOpenPoints318.evaluation d v hv
  let I := Roots Q V
  letI : Fintype I := Fintype.ofEquiv ((Q.map V).rootSet ℂ)
    (rootsEquivRootSet Q V hm).symm
  choose g hg hcenter heq hunique using fun i : I =>
    LocalizedPrimitiveRootChart318.exists_root_graph d Q hs v hv i.val i.property
  have hroots : ∀ᶠ w in 𝓝 v, ∀ i : I,
      AnalyticAt ℂ (g i) w ∧ LocalizedPrimitiveRootChart318.equation d Q (w,g i w) = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hg i).eventually_analyticAt.and (heq i)
  have hdistinct : ∀ᶠ w in 𝓝 v, ∀ i j : I, i ≠ j → g i w ≠ g j w := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · have h0 : g i v - g j v ≠ 0 := by
        rw [hcenter i,hcenter j]
        exact sub_ne_zero.mpr (fun h => hij (Subtype.ext h))
      filter_upwards [((hg i).continuousAt.sub (hg j).continuousAt).eventually_ne h0] with w hw _
      exact sub_ne_zero.mp hw
  have hd : ∀ᶠ w in 𝓝 v, MvPolynomial.eval w d ≠ 0 :=
    (((AnalyticOnNhd.eval_mvPolynomial d) v (mem_univ v)).continuousAt).eventually_ne hv
  obtain ⟨U,hU,hUopen,hUv⟩ := eventually_nhds_iff.mp (hd.and (hroots.and hdistinct))
  refine ⟨U,hUopen,hUv,g,hcenter,?_⟩
  intro w hw
  have hwD := (hU w hw).1
  have hwr := (hU w hw).2.1
  have hwi : Function.Injective (fun i : I => g i w) := by
    intro i j hij
    by_contra h
    exact (hU w hw).2.2 i j h hij
  let W := ComplexPolynomialOpenPoints318.evaluation d w hwD
  let J := Roots Q W
  letI : Fintype J := Fintype.ofEquiv ((Q.map W).rootSet ℂ)
    (rootsEquivRootSet Q W hm).symm
  have hj (i : I) : (Q.map W).eval (g i w) = 0 := by
    rw [←LocalizedPrimitiveRootChart318.equation_on_open d Q w hwD]
    exact (hwr i).2
  let k : I → J := fun i => ⟨g i w,hj i⟩
  have hk : Function.Injective k := by
    intro i j h
    exact hwi (congrArg Subtype.val h)
  have hcard (T : Localization.Away d →+* ℂ)
      [Fintype (Roots Q T)] : Fintype.card (Roots Q T) = Q.natDegree := by
    rw [Fintype.card_congr (rootsEquivRootSet Q T hm),
      Polynomial.card_rootSet_eq_natDegree hs.map (IsAlgClosed.splits _)]
    exact hm.natDegree_map T
  have hsurj : Function.Surjective k :=
    ((Fintype.bijective_iff_injective_and_card k).mpr
      ⟨hk,(hcard V).trans (hcard W).symm⟩).2
  refine ⟨hwD,hwr,hwi,?_⟩
  intro z
  constructor
  · intro hz
    have hz' : (Q.map W).eval z = 0 := by
      rw [←LocalizedPrimitiveRootChart318.equation_on_open d Q w hwD]
      exact hz
    obtain ⟨i,hi⟩ := hsurj ⟨z,hz'⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  · rintro ⟨i,rfl⟩
    exact (hwr i).2
end LocalizedPrimitiveExhaustiveGraphs318
