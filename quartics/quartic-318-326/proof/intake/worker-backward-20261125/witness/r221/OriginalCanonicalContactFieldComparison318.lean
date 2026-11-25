module
public import FourRootAutomorphisms318
public import FourRootSignBaseChange318
public import SourceTwistArithmetic318
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
noncomputable section

namespace OriginalCanonicalContactFieldComparison318
open scoped TensorProduct
open QuadraticPresentation318

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev K := RatFunc ℚ
abbrev parameter := SourceKummerField318.parameter SourceTwistArithmetic318.units
abbrev L := KummerTensorField318.Raw parameter

variable {M : Type} [Field M] [Algebra K M]

/-- One function on the genuine rational canonical curve satisfies the
exact equation of one listed character, including its rational twist. -/
private def rootMap (i : Fin 4) (y : M)
    (eq : y ^ 2 = algebraMap K M (parameter i)) : RootRing (parameter i) →ₐ[K] M :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId K M) y (by
    change Polynomial.aeval y (polynomial (parameter i)) = 0
    simp only [polynomial, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq, sub_self])

private theorem rootMap_read (i : Fin 4) (y : M)
    (eq : y ^ 2 = algebraMap K M (parameter i)) :
    rootMap i y eq (AdjoinRoot.root (polynomial (parameter i))) = y :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

variable (y : Fin 4 → M) (hy : ∀ i, y i ^ 2 = algebraMap K M (parameter i))

/-- Evaluate the four actual monic quadratic quotients, and their
tensor, on the four rational functions on the canonical curve. -/
def comparisonHom : L →ₐ[K] M :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (rootMap 0 (y 0) (hy 0)) (rootMap 1 (y 1) (hy 1))
      (fun _ _ => Commute.all _ _))
    (Algebra.TensorProduct.lift (rootMap 2 (y 2) (hy 2)) (rootMap 3 (y 3) (hy 3))
      (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

theorem comparisonHom_read (i : Fin 4) :
    comparisonHom y hy (FourRootAutomorphisms318.generator parameter i) = y i := by
  fin_cases i <;> simp [comparisonHom, FourRootAutomorphisms318.generator,
    Algebra.TensorProduct.lift_tmul, rootMap_read]

theorem comparisonHom_injective : Function.Injective (comparisonHom y hy) := by
  letI : Field L := (KummerTensorField318.source_raw_field SourceTwistArithmetic318.units).toField
  exact (comparisonHom y hy).toRingHom.injective

/-- The canonical map is an isomorphism once the degree of the genuine
Atkin-Lehner quotient is sixteen. There is no assumption that the four
functions generate the field or an input isomorphism. -/
def comparison [Module.Finite K M] (d : Module.finrank K M = 16) : L ≃ₐ[K] M := by
  letI : Module.Finite K L := (FourRootOrder318.finite_free parameter).1
  refine AlgEquiv.ofBijective (comparisonHom y hy) ⟨comparisonHom_injective y hy, ?_⟩
  have hdim : Module.finrank K L = Module.finrank K M :=
    (KummerTensorField318.source_raw_degree SourceTwistArithmetic318.units).trans d.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (comparisonHom y hy).toLinearMap)).mp (comparisonHom_injective y hy)

theorem comparison_read [Module.Finite K M] (d : Module.finrank K M = 16) (i : Fin 4) :
    comparison y hy d (FourRootAutomorphisms318.generator parameter i) = y i :=
  comparisonHom_read y hy i

/-- This comparison respects the actual labelled deck action, not
merely the extension degree. The target automorphism is read on the
same four functions, and then on the entire algebra. -/
theorem comparison_intertwines [Module.Finite K M] (d : Module.finrank K M = 16)
    (s : Fin 4 → Bool) (w : M ≃ₐ[K] M) (hw : ∀ i, w (y i) = if s i then -y i else y i) :
    (FourRootAutomorphisms318.signEquiv parameter s).trans (comparison y hy d) =
      (comparison y hy d).trans w := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply FourRootSignBaseChange318.hom_ext parameter
  intro i
  change comparison y hy d
      (FourRootAutomorphisms318.signEquiv parameter s (FourRootAutomorphisms318.generator parameter i)) =
    w (comparison y hy d (FourRootAutomorphisms318.generator parameter i))
  rw [FourRootAutomorphisms318.signEquiv_generator, comparison_read, hw]
  cases h : s i <;> simp [h, comparison_read]

end OriginalCanonicalContactFieldComparison318

#print axioms OriginalCanonicalContactFieldComparison318.comparisonHom_read
#print axioms OriginalCanonicalContactFieldComparison318.comparisonHom_injective
#print axioms OriginalCanonicalContactFieldComparison318.comparison
#print axioms OriginalCanonicalContactFieldComparison318.comparison_read
#print axioms OriginalCanonicalContactFieldComparison318.comparison_intertwines
