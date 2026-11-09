module
public import CyclicPrefixWitness318
public section
noncomputable section

/-! An explicit scalar-good neighborhood in the genuine orbit closure. Its
centre is P, not the identity component; arbitrary CRT access remains open. -/
namespace GeneratorScalarProgression318
open Set Filter TopologicalSpace
open scoped Topology
open ConcreteG8Domain (K pair)
open ActualCyclicClosure318 ActualCyclicGuards318
open ActualCyclicProgressions318 (guard_value progression_point)
open CoherentMultipleCharts318 (chartU)
set_option maxHeartbeats 2000000

/-- Exact coherent chart of P, obtained by doubling the original half point. -/
lemma chartU_one : chartU 1=pair (8/41) (14/41) := by
  simp only [chartU,one_zsmul]
  change 2*GlobalGeneratorPoints318.yR/
      (GlobalGeneratorPoints318.xR^2+ConcreteG8Domain.D)=pair (8/41) (14/41)
  apply (div_eq_iff (CoherentMultipleCharts318.denominator_ne _)).mpr
  ext <;> norm_num [GlobalGeneratorPoints318.xR,GlobalGeneratorPoints318.yR,
    ConcreteG8Domain.D,ConcreteG8Domain.i,pair,pow_succ]

/-- The rational quadratic norm coefficient used by the literal source. -/
@[expose] def normCoefficient (U : K) : ℚ := U.re^2-2*U.im^2

lemma normCoefficient_one : normCoefficient (chartU 1)= -(8/41) := by
  rw [chartU_one]
  norm_num [normCoefficient,pair]

lemma embedding_product (U : K) :
    ActualQuadraticEmbeddings318.positiveEmbedding U *
      ActualQuadraticEmbeddings318.negativeEmbedding U=(normCoefficient U:ℝ) := by
  rcases U with ⟨a,b⟩
  change ActualQuadraticEmbeddings318.positiveEmbedding (pair a b) *
    ActualQuadraticEmbeddings318.negativeEmbedding (pair a b)=((a^2-2*b^2:ℚ):ℝ)
  simp only [ActualQuadraticEmbeddings318.positiveEmbedding,
    ActualQuadraticEmbeddings318.negativeEmbedding,
    ActualQuadraticEmbeddings318.realEmbedding_pair]
  push_cast
  linear_combination -(b:ℝ)^2 * (Real.sq_sqrt (by norm_num : (0:ℝ)≤2))

/-- Product of the two original real chart coordinates, with no choice of
independent square roots or altered chart signs. -/
@[expose] def scalarNorm (X : Pair) : ℝ := (X 0).val.1*(X 1).val.1

lemma scalarNorm_continuous : Continuous scalarNorm := by
  unfold scalarNorm
  fun_prop

lemma scalarNorm_orbit (h : ℤ) :
    scalarNorm (pairOrbit h)=(normCoefficient (chartU h):ℝ) := by
  change RealQuarticAmbient318.embedding 0 (chartU h) *
    RealQuarticAmbient318.embedding 1 (chartU h)=_
  simpa only [RealQuarticAmbient318.embedding,ite_true,ite_false,
    show (1:Fin 2)≠0 by decide] using embedding_product (chartU h)

lemma scalarNorm_generator : scalarNorm generator= -(8/41:ℝ) := by
  rw [generator,scalarNorm_orbit,normCoefficient_one]
  norm_num

lemma guard_generator_negative (labels : Fin 4 → ℤ) (j : Fin 4) (hn : labels j≠0) :
    guard labels j generator<0 := by
  rw [generator,guard_value]
  simpa only [one_zsmul] using
    (show (RealGuardTrace318.guardValue (labels j) LocalGenerator318.P:ℝ)<0 by
      exact_mod_cast CoherentMultiplePrefix318.guard_at_generator_negative (labels j) hn)

/-- Margins are fixed by the original labelled roots, before any progression. -/
@[expose] def margin (labels : Fin 4 → ℤ) (j : Fin 4) : ℝ :=
  -guard labels j generator/2

lemma margin_positive (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (j : Fin 4) :
    0<margin labels j := by
  exact half_pos (neg_pos.mpr (guard_generator_negative labels j (hn j)))

/-- The scalar lower bound 1/100 is stronger than the manuscript's
1/(100 sqrt(7)). This set also has all four guards bounded away from zero. -/
@[expose] def region (labels : Fin 4 → ℤ) : Set Pair :=
  {X | (1/100:ℝ)<|scalarNorm X| ∧ ∀ j : Fin 4, guard labels j X< -margin labels j}

lemma region_open (labels : Fin 4 → ℤ) : IsOpen (region labels) := by
  have he : region labels={X : Pair | (1/100:ℝ)<|scalarNorm X|} ∩
      ⋂ j : Fin 4, {X : Pair | guard labels j X< -margin labels j} := by
    ext X
    simp [region]
  rw [he]
  exact (isOpen_lt continuous_const scalarNorm_continuous.abs).inter
    (isOpen_iInter_of_finite fun j => isOpen_lt (guard_continuous labels j) continuous_const)

lemma generator_mem_region (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    generator∈region labels := by
  constructor
  · rw [scalarNorm_generator]
    norm_num
  · intro j
    have hp := guard_generator_negative labels j (hn j)
    dsimp [margin]
    linarith

/-- Access to this explicit region is guaranteed whenever the progression's
closed coset contains P. Nothing here places P in the cyclic identity component. -/
@[expose] def Compatible (r k : ℕ) : Prop :=
  generator-pairOrbit (r:ℤ) ∈
    (AddSubgroup.zmultiples ((k:ℤ) • generator)).topologicalClosure

lemma compatible_one (k : ℕ) : Compatible 1 k := by
  change generator-generator ∈ _
  rw [sub_self]
  exact AddSubgroup.zero_mem _

/-- Arbitrarily late hits of the very same scalar-good, guard-good region. -/
theorem tail_in_region (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (r k : ℕ) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<t ∧ pairOrbit ((r+k*t:ℕ):ℤ)∈region labels := by
  have hrec := mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr hc
  have hnb : (fun X : Pair => pairOrbit (r:ℤ)+X) ⁻¹' region labels ∈
      𝓝 (generator-pairOrbit (r:ℤ)) :=
    ((region_open labels).preimage (continuous_const.add continuous_id)).mem_nhds
      (by simpa [add_comm] using generator_mem_region labels hn)
  obtain ⟨t,ht,hgood⟩ := frequently_atTop'.mp (hrec.frequently hnb) B
  refine ⟨t,ht,?_⟩
  rwa [←progression_point r k t]

/-- The original assignment and fixed roots now coexist with an explicit
quantitative scalar bound, for every compatible progression. Only the first
51 source rows are concluded, not the later scalar/Lucas/local equations. -/
theorem scalar_prefix_in_progression (S q : ℚ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (r k : ℕ) (hk : 0<k) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<r+k*t ∧
      let h : ℤ := ((r+k*t:ℕ):ℤ)
      (1/100:ℝ)<|(normCoefficient (chartU h):ℝ)| ∧
      (∀ j : Fin 4, (RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P):ℝ)
        < -margin labels j) ∧
      CoherentMultiplePrefix318.witness q labels h 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (CoherentMultiplePrefix318.witness q labels h) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels h)
        (CoherentMultiplePrefix318.v labels h) j=CoherentMultipleCharts318.fixedRoot (labels j)) := by
  obtain ⟨t,ht,hscalar,hguards⟩ := tail_in_region labels hn r k hc B
  have hkt : t≤k*t := by nlinarith
  have hbig : B<r+k*t := by omega
  have hh : ((r+k*t:ℕ):ℤ)≠0 := by
    exact_mod_cast (show r+k*t≠0 by omega)
  rw [scalarNorm_orbit] at hscalar
  have hbounds : ∀ j : Fin 4,
      (RealGuardTrace318.guardValue (labels j) (((r+k*t:ℕ):ℤ) • LocalGenerator318.P):ℝ)
        < -margin labels j := by
    intro j
    simpa only [guard_value] using hguards j
  have hg : ∀ j : Fin 4,
      RealGuardTrace318.guardValue (labels j) (((r+k*t:ℕ):ℤ) • LocalGenerator318.P)≠0 := by
    intro j
    have hp := lt_trans (hbounds j) (neg_neg_of_pos (margin_positive labels hn j))
    exact ne_of_lt (by exact_mod_cast hp)
  refine ⟨t,hbig,hscalar,hbounds,CoherentMultiplePrefix318.witness_input q labels _,
    CoherentMultiplePrefix318.witness_rows S q labels _ hh hg,?_⟩
  intro j
  exact CoherentRootSign318.emitted_root_fixed labels _ j (hn j)
    (((CoherentMultiplePrefix318.guards_iff labels _).mpr hg) j)

/-- Every positive step admits arbitrarily late h=1+k*t witnesses satisfying
both the scalar norm bound and all four guard bounds. Mixed CRT residues are
not covered unless their separate compatibility condition has been supplied. -/
theorem scalar_prefix_one_mod (S q : ℚ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (k : ℕ) (hk : 0<k) (B : ℕ) :
    ∃ t : ℕ, B<1+k*t ∧
      let h : ℤ := ((1+k*t:ℕ):ℤ)
      (1/100:ℝ)<|(normCoefficient (chartU h):ℝ)| ∧
      (∀ j : Fin 4, (RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P):ℝ)
        < -margin labels j) ∧
      CoherentMultiplePrefix318.witness q labels h 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (CoherentMultiplePrefix318.witness q labels h) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels h)
        (CoherentMultiplePrefix318.v labels h) j=CoherentMultipleCharts318.fixedRoot (labels j)) :=
  scalar_prefix_in_progression S q labels hn 1 k hk (compatible_one k) B

end GeneratorScalarProgression318
