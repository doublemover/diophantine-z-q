module
public import ActualThreeExceptionalParameter318
public import ActualJAllLevels318
public import Mathlib.Topology.Algebra.Module.Cardinality
public section
noncomputable section
namespace ActualThreeParameterProper318
open ActualThreeExceptionalParameter318 ThreeCompactParameter318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
set_option maxHeartbeats 0

/-- Natural punctured complex line with its inherited, independent topology. -/
abbrev NonzeroParameter := {t : ℂ // t ≠ 0}

@[expose] def fullParameter : Base (image 3) → NonzeroParameter :=
  fun q => ⟨quotientParameter q,quotientParameter_ne_zero q⟩

@[expose] def parameterJ : NonzeroParameter → ℂ := fun t => J t.val

lemma fullParameter_continuous : Continuous fullParameter :=
  quotientParameter_continuous.subtype_mk _

lemma parameterJ_continuous : Continuous parameterJ := by
  unfold parameterJ J
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact pow_ne_zero 3 t.property

lemma parameterJ_fullParameter : parameterJ ∘ fullParameter=QuotientJ318.jMap 3 := by
  funext q
  exact quotientParameter_j q

/-- The actual full quotient coordinate is proper. This uses genuine j
properness at level three, including elliptic stabilizers, not a replacement
source topology or any asserted compactification. -/
theorem fullParameter_proper : IsProperMap fullParameter := by
  apply isProperMap_of_comp_of_t2 fullParameter_continuous parameterJ_continuous
  rw [parameterJ_fullParameter]
  exact ActualJAllLevels318.proper 3

@[expose] def excludedPolynomial : Polynomial ℂ :=
  Polynomial.X*(Polynomial.X+27)*(Polynomial.X+243)*
    (Polynomial.X^2-486*Polynomial.X-19683)

lemma excludedPolynomial_ne_zero : excludedPolynomial ≠ 0 := by
  intro h
  have hh := congrArg (fun p : Polynomial ℂ => p.eval 1) h
  norm_num [excludedPolynomial] at hh

lemma excludedPolynomial_eval (t : ℂ) :
    excludedPolynomial.eval t=t*(t+27)*(t+243)*D t := by
  simp [excludedPolynomial,D]

/-- The old admissible parameter domain is dense in the independently
topologized punctured line. No exceptional points are omitted in the target. -/
lemma admissible_dense : Dense {t : NonzeroParameter |
    t.val+27 ≠ 0 ∧ t.val+243 ≠ 0 ∧ D t.val ≠ 0} := by
  have hd := (Polynomial.finite_setOfPred_isRoot excludedPolynomial_ne_zero).countable.dense_compl ℂ
  have ho : IsOpen {t : ℂ | t ≠ 0} := isClosed_singleton.isOpen_compl
  have hh : Dense ((fun t : NonzeroParameter => t.val) ⁻¹'
      {t : ℂ | excludedPolynomial.IsRoot t}ᶜ) := hd.preimage ho.isOpenMap_subtype_val
  apply hh.mono
  intro t ht
  change ¬excludedPolynomial.IsRoot t.val at ht
  simpa only [Polynomial.IsRoot,excludedPolynomial_eval,mul_eq_zero,not_or,
    t.property,not_false_eq_true,true_and,and_assoc,Set.mem_setOf_eq] using ht

lemma admissible_mem_range (t : NonzeroParameter)
    (ht : t.val+27 ≠ 0 ∧ t.val+243 ≠ 0 ∧ D t.val ≠ 0) : t ∈ Set.range fullParameter := by
  let p : ParameterOpen := ⟨t.val,t.property,ht⟩
  let q := (LiteralThreeCompactParameter318.sourceParameter 1).symm p
  refine ⟨q.val,Subtype.ext ?_⟩
  change quotientParameter q.val=t.val
  rw [quotientParameter_restrict 1]
  exact congrArg Subtype.val ((LiteralThreeCompactParameter318.sourceParameter 1).apply_symm_apply p)

/-- Every nonzero complex parameter is realized by an orbit in the original
Gamma1(3) quotient. Injectivity at exceptional fibers is a separate obligation. -/
theorem fullParameter_surjective : Function.Surjective fullParameter := by
  intro t
  have hd : Dense (Set.range fullParameter) := admissible_dense.mono (fun x hx =>
    admissible_mem_range x hx)
  have ht := hd t
  rw [fullParameter_proper.isClosed_range.closure_eq] at ht
  exact ht

/-- Point-level realization retains the exact original period coordinate. -/
theorem periodParameter_surjective (t : ℂ) (ht : t ≠ 0) :
    ∃ tau : UpperHalfPlane,periodParameter tau=t := by
  obtain ⟨q,hq⟩ := fullParameter_surjective ⟨t,ht⟩
  obtain ⟨tau,rfl⟩ := quotient_surjective 3 q
  exact ⟨tau,congrArg Subtype.val hq⟩

end ActualThreeParameterProper318
