module
public import PELOriginalCompletedChartEvaluation318
public import PELOriginalCoordinateRangeDeck318
public import PELOriginalRegularEvaluationInjective318
public section
noncomputable section
namespace PELOriginalFiniteFunctionRange318
open PELOriginalRegularCoordinateAlgebra318 PELOriginalCompletedChartEvaluation318
open PELOriginalCoordinateRangeDeck318 PELOriginalCommonContactBase318
open PELOriginalMaximalQuotient318

/-- Functions on the FULL original finite-chart graph, including its actual
branch centers. The first component remains an original analytic point. -/
abbrev FiniteFunctions := FiniteSource → ℂ
@[expose] def finiteEvaluation : CoordinateRing →ₐ[ℂ] FiniteFunctions where
  toFun a x := finiteAt x a
  map_zero' := funext (fun x => map_zero (finiteAt x))
  map_one' := funext (fun x => map_one (finiteAt x))
  map_add' a b := funext (fun x => map_add (finiteAt x) a b)
  map_mul' a b := funext (fun x => map_mul (finiteAt x) a b)
  commutes' c := funext (fun x => (finiteAt x).commutes c)

lemma regular_evaluation (a : CoordinateRing) (x : OriginalRegular) :
    finiteEvaluation a (regularPoint x) = evaluation a x :=
  AlgHom.congr_fun (regular_agreement x) a

/-- Injectivity on the full finite chart follows from the ACTUAL original
regular restriction and the root-monomial separation proof, not from size,
dimension, or the false assertion that all functions form a domain. -/
theorem finiteEvaluation_injective : Function.Injective finiteEvaluation := by
  intro a b h
  apply PELOriginalRegularEvaluationInjective318.evaluation_injective
  funext x
  exact (regular_evaluation a x).symm.trans
    ((congrFun h (regularPoint x)).trans (regular_evaluation b x))

abbrev FiniteAlgebra := finiteEvaluation.range
@[expose] def coefficientMap : CoordinateRing →ₐ[ℂ] FiniteAlgebra where
  toFun a := ⟨finiteEvaluation a,⟨a,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero finiteEvaluation)
  map_one' := Subtype.ext (map_one finiteEvaluation)
  map_add' a b := Subtype.ext (map_add finiteEvaluation a b)
  map_mul' a b := Subtype.ext (map_mul finiteEvaluation a b)
  commutes' c := Subtype.ext (finiteEvaluation.commutes c)
lemma coefficientMap_surjective : Function.Surjective coefficientMap := by
  rintro ⟨f,⟨a,ha⟩⟩
  exact ⟨a,Subtype.ext ha⟩

/-- Literal restriction of original finite-chart functions to the genuine
original regular source. Its range proof keeps the SAME polynomial a. -/
@[expose] def restriction : FiniteAlgebra →ₐ[ℂ] OriginalAlgebra where
  toFun f := ⟨fun x => f.val (regularPoint x),by
    obtain ⟨a,ha⟩ := f.property
    refine ⟨a,?_⟩
    funext x
    exact (regular_evaluation a x).symm.trans (congrFun ha (regularPoint x))⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl
lemma restriction_value (f : FiniteAlgebra) (x : OriginalRegular) :
    (restriction f).val x = f.val (regularPoint x) := rfl

lemma restriction_injective : Function.Injective restriction := by
  intro f g h
  obtain ⟨a,rfl⟩ := coefficientMap_surjective f
  obtain ⟨b,rfl⟩ := coefficientMap_surjective g
  apply congrArg coefficientMap
  apply PELOriginalRegularEvaluationInjective318.evaluation_injective
  funext x
  have hx := congrArg (fun q : OriginalAlgebra => q.val x) h
  change finiteEvaluation a (regularPoint x) = finiteEvaluation b (regularPoint x) at hx
  exact (regular_evaluation a x).symm.trans (hx.trans (regular_evaluation b x))
lemma restriction_surjective : Function.Surjective restriction := by
  rintro ⟨f,⟨a,ha⟩⟩
  refine ⟨coefficientMap a,Subtype.ext ?_⟩
  funext x
  exact (regular_evaluation a x).trans (congrFun ha x)
@[expose] def restrictionEquiv : FiniteAlgebra ≃ₐ[ℂ] OriginalAlgebra :=
  AlgEquiv.ofBijective restriction ⟨restriction_injective,restriction_surjective⟩
lemma restrictionEquiv_value (f : FiniteAlgebra) (x : OriginalRegular) :
    (restrictionEquiv f).val x = f.val (regularPoint x) := rfl

/-- The evaluator on ALL original finite-chart points retains the actual
original deck label and its native finite coordinate-ring action. -/
theorem finiteEvaluation_deck (w : Labels) (a : CoordinateRing) (x : FiniteSource) :
    finiteEvaluation (FourRootCoordinateRingSigns318.finiteEnd branches
      (OriginalContactInertiaBasis318.basis w) a) x =
      finiteEvaluation a (finiteAction w x) :=
  (AlgHom.congr_fun (finite_deck w x) a).symm

/-- This is an algebra of original finite-chart functions, not the full
analytic stalk, a sheaf gluing theorem, or a rational canonical model. -/
theorem range_elements_extend (f : OriginalAlgebra) :
    ∃ g : FiniteAlgebra, ∀ x : OriginalRegular, g.val (regularPoint x) = f.val x := by
  obtain ⟨g,hg⟩ := restriction_surjective f
  exact ⟨g,fun x => congrArg (fun q : OriginalAlgebra => q.val x) hg⟩
end PELOriginalFiniteFunctionRange318
