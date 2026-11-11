module
public import PELGlobalUnitReductionSurjective318
public section
noncomputable section
namespace PELGlobalNormOneLevelLifts318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELOrderReductionThree318
open PELGlobalIntegralUnitLifts318 PELGlobalUnitReductionSurjective318
set_option maxHeartbeats 1400000

theorem norm_pow (x : B) (n : ℕ) : reducedNorm (x^n)=reducedNorm x^n := by
  induction n with
  | zero => norm_num [reducedNorm]
  | succ n ih => rw [pow_succ,PELQuaternionNormParity318.norm_mul,ih,pow_succ]

/-- The only sign in an actual global word comes from the specified
norm-minus-one generator, not from an arbitrary choice of finite lift. -/
theorem word_norm (k : Fin 8) (a b : Fin 3) :
    reducedNorm ((globalWord k a b:order):B)=(-1:ℚ)^k.val := by
  change reducedNorm ((((generator 0:order):B)^k.val * ((generator 1:order):B)^a.val) *
    ((generator 2:order):B)^b.val)=_
  rw [PELQuaternionNormParity318.norm_mul,PELQuaternionNormParity318.norm_mul,
    norm_pow,norm_pow,norm_pow]
  simp [generator_norm]

/-- Literal finite-word computation in the original reduction ring. -/
theorem finite_word_norm (k : Fin 8) (a b : Fin 3) :
    QuadraticAlgebra.norm (PELReductionResidueField318.residue (finiteWord k a b))=
      (-1:F3)^k.val := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [finiteWord,finiteGenerator,PELReductionResidueField318.residue,
      QuadraticAlgebra.norm_def,pow_succ,pow_two]

/-- EVERY norm-one unit of the literal order quotient has an actual
norm-one GLOBAL original-order lift. The larger72-element unit group is
not identified with this norm-one subgroup. -/
theorem original_norm_one_lift (u : QuotientOrderˣ)
    (hu : PELLevelThreeSimilitudes318.norm (u:QuotientOrder)=1) :
    ∃ v : orderˣ, originalUnitReduction v=u ∧ reducedNorm ((v:order):B)=1 := by
  have hres : PELReductionResidueField318.residue (quotientEquiv (u:QuotientOrder))≠0 :=
    ((u.isUnit.map quotientEquiv.toRingHom).map PELReductionResidueField318.residue).ne_zero
  obtain ⟨k,a,b,hword⟩ := finite_cover (quotientEquiv (u:QuotientOrder)) hres
  have hn : (-1:F3)^k.val=1 := by
    rw [←finite_word_norm k a b,hword]
    exact hu
  have hk : (-1:ℚ)^k.val=1 := by
    fin_cases k <;> norm_num at hn ⊢
  refine ⟨globalWord k a b,?_,?_⟩
  · apply Units.ext
    apply quotientEquiv.injective
    change reduction (globalWord k a b:order)=quotientEquiv (u:QuotientOrder)
    rw [word_reduction]
    exact hword
  · exact (word_norm k a b).trans hk
end PELGlobalNormOneLevelLifts318
