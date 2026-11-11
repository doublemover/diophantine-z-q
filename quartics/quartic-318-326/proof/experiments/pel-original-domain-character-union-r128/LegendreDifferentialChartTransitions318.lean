module
public import LegendreDifferentialReparametrization318
public section
noncomputable section
namespace LegendreDifferentialChartTransitions318
open Set Filter
open scoped Topology
open LegendreInvariantAnalytic318 LegendreInvariantChartUnits318
open LegendreDifferentialReparametrization318
open LegendreCompletedComplexAtlas318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

abbrev Transition (i j : Finite l ⊕ Infinite l) :=
  (localChart l i).symm.trans (localChart l j)

lemma finite_inverse_identity (p q : Finite l) (z : ℂ)
    (hz : z∈(Transition l (.inl p) (.inl q)).source) :
    (LegendreFiniteComplexAtlas318.chart l q).symm
        (Transition l (.inl p) (.inl q) z)=
      (LegendreFiniteComplexAtlas318.chart l p).symm z := by
  apply (LegendrePlaneOverlap318.finite_open l).injective
  change (finiteChart l q).symm (finiteChart l q ((finiteChart l p).symm z))=
    (finiteChart l p).symm z
  exact (finiteChart l q).left_inv hz.2
lemma infinity_inverse_identity (p q : Infinite l) (z : ℂ)
    (hz : z∈(Transition l (.inr p) (.inr q)).source) :
    (LegendreInfinityComplexAtlas318.chart l q).symm
        (Transition l (.inr p) (.inr q) z)=
      (LegendreInfinityComplexAtlas318.chart l p).symm z := by
  apply (LegendrePlaneOverlap318.infinity_open l).injective
  change (infinityChart l q).symm (infinityChart l q ((infinityChart l p).symm z))=
    (infinityChart l p).symm z
  exact (infinityChart l q).left_inv hz.2

/-- On the full actual mixed overlap, inverse target coordinates are
exactly the reciprocal original source coordinates, not a chosen bijection. -/
lemma mixed_inverse_coordinates (p : Infinite l) (q : Finite l) (z : ℂ)
    (hz : z∈(Transition l (.inr p) (.inl q)).source) :
    finiteX l q (Transition l (.inr p) (.inl q) z)=infiniteU l p z/infiniteV l p z ∧
    finiteY l q (Transition l (.inr p) (.inl q) z)=1/infiniteV l p z := by
  let a := (LegendreFiniteComplexAtlas318.chart l q).symm
    (Transition l (.inr p) (.inl q) z)
  let b := (LegendreInfinityComplexAtlas318.chart l p).symm z
  have he : LegendrePlaneOverlap318.finiteChart l a=
      LegendrePlaneOverlap318.infinityChart l b := (finiteChart l q).left_inv hz.2
  obtain ⟨ha,hab⟩ := (LegendrePlaneOverlap318.chart_identification l a b).mp he
  have hab' : a=LegendrePlaneOverlap318.toFinite l b := by
    rw [←hab,LegendrePlaneOverlap318.left_inverse l a ha]
  have hb := infinity_to_finite_denominator l p q z hz
  have hcoords := congrArg Subtype.val hab'
  rw [LegendrePlaneOverlap318.toFinite_value l b hb] at hcoords
  exact ⟨congrArg Prod.fst hcoords,congrArg Prod.snd hcoords⟩

lemma finite_finite (p q : Finite l) (z : ℂ)
    (hz : z∈(Transition l (.inl p) (.inl q)).source) :
    finiteForm l p z=finiteForm l q (Transition l (.inl p) (.inl q) z)*
      deriv (Transition l (.inl p) (.inl q)) z := by
  let t := Transition l (.inl p) (.inl q)
  have htarget := (finiteChart l q).map_source hz.2
  have he : ∀ᶠ w in 𝓝 z,
      (LegendreFiniteComplexAtlas318.chart l p).symm w=
        (LegendreFiniteComplexAtlas318.chart l q).symm (t w) := by
    filter_upwards [t.open_source.mem_nhds hz] with w hw
    exact (finite_inverse_identity l p q w hw).symm
  apply finite_reparam l (finiteX l p) (finiteY l p) (finiteX l q) (finiteY l q) t z
    ((finite_coordinates l q).1 (t z) htarget).differentiableAt
    ((finite_coordinates l q).2 (t z) htarget).differentiableAt
    ((analytic_transition l (.inl p) (.inl q)) z hz).differentiableAt
  · filter_upwards [he] with w hw
    exact congrArg (fun a=>a.val.1) hw
  · filter_upwards [he] with w hw
    exact congrArg (fun a=>a.val.2) hw
lemma infinity_infinity (p q : Infinite l) (z : ℂ)
    (hz : z∈(Transition l (.inr p) (.inr q)).source) :
    infinityForm l p z=infinityForm l q (Transition l (.inr p) (.inr q) z)*
      deriv (Transition l (.inr p) (.inr q)) z := by
  let t := Transition l (.inr p) (.inr q)
  have htarget := (infinityChart l q).map_source hz.2
  have he : ∀ᶠ w in 𝓝 z,
      (LegendreInfinityComplexAtlas318.chart l p).symm w=
        (LegendreInfinityComplexAtlas318.chart l q).symm (t w) := by
    filter_upwards [t.open_source.mem_nhds hz] with w hw
    exact (infinity_inverse_identity l p q w hw).symm
  apply infinity_reparam l (infiniteU l p) (infiniteV l p) (infiniteU l q) (infiniteV l q) t z
    ((infinite_coordinates l q).1 (t z) htarget).differentiableAt
    ((infinite_coordinates l q).2 (t z) htarget).differentiableAt
    ((analytic_transition l (.inr p) (.inr q)) z hz).differentiableAt
  · filter_upwards [he] with w hw
    exact congrArg (fun a=>a.val.1) hw
  · filter_upwards [he] with w hw
    exact congrArg (fun a=>a.val.2) hw

lemma infinity_finite (p : Infinite l) (q : Finite l) (z : ℂ)
    (hz : z∈(Transition l (.inr p) (.inl q)).source) :
    infinityForm l p z=finiteForm l q (Transition l (.inr p) (.inl q) z)*
      deriv (Transition l (.inr p) (.inl q)) z := by
  let t := Transition l (.inr p) (.inl q)
  have htarget := (finiteChart l q).map_source hz.2
  have he : ∀ᶠ w in 𝓝 z,
      finiteX l q (t w)=infiniteU l p w/infiniteV l p w ∧
      finiteY l q (t w)=1/infiniteV l p w := by
    filter_upwards [t.open_source.mem_nhds hz] with w hw
    exact mixed_inverse_coordinates l p q w hw
  have hr := reciprocal_path l (infiniteU l p) (infiniteV l p) z
    ((infinite_coordinates l p).1 z hz.1).differentiableAt
    ((infinite_coordinates l p).2 z hz.1).differentiableAt
    (infinity_to_finite_denominator l p q z hz)
    (Filter.Eventually.of_forall (fun w=>((LegendreInfinityComplexAtlas318.chart l p).symm w).property))
  change infinityCoefficient l (infiniteU l p) (infiniteV l p) z=_
  rw [←hr]
  apply finite_reparam l _ _ (finiteX l q) (finiteY l q) t z
    ((finite_coordinates l q).1 (t z) htarget).differentiableAt
    ((finite_coordinates l q).2 (t z) htarget).differentiableAt
    ((analytic_transition l (.inr p) (.inl q)) z hz).differentiableAt
  · filter_upwards [he] with w hw
    exact hw.1.symm
  · filter_upwards [he] with w hw
    exact hw.2.symm

lemma inverse_transition_derivative (i j : Finite l ⊕ Infinite l) (z : ℂ)
    (hz : z∈(Transition l i j).source) :
    deriv (Transition l j i) (Transition l i j z)*deriv (Transition l i j) z=1 := by
  have htarget : Transition l i j z∈(Transition l j i).source :=
    (Transition l i j).map_source hz
  have h1:=((analytic_transition l i j) z hz).differentiableAt.hasDerivAt
  have h2:=((analytic_transition l j i) (Transition l i j z) htarget).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun w : ℂ=>w)
      (deriv (Transition l j i) (Transition l i j z)*deriv (Transition l i j) z) z := by
    apply (h2.comp z h1).congr_of_eventuallyEq
    filter_upwards [(Transition l i j).open_source.mem_nhds hz] with w hw
    exact ((Transition l i j).left_inv hw).symm
  exact hd.unique (hasDerivAt_id z)

lemma finite_infinity (p : Finite l) (q : Infinite l) (z : ℂ)
    (hz : z∈(Transition l (.inl p) (.inr q)).source) :
    finiteForm l p z=infinityForm l q (Transition l (.inl p) (.inr q) z)*
      deriv (Transition l (.inl p) (.inr q)) z := by
  have hback := infinity_finite l q p (Transition l (.inl p) (.inr q) z)
    ((Transition l (.inl p) (.inr q)).map_source hz)
  rw [hback,(Transition l (.inl p) (.inr q)).left_inv hz,mul_assoc,
    inverse_transition_derivative l (.inl p) (.inr q) z hz,mul_one]
end LegendreDifferentialChartTransitions318
