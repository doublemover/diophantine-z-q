module
public import VaryingSourceTensorAction318
public import CyclicQuotientFiniteFlat318
public section
noncomputable section
namespace VaryingSourceWordQuotient318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingMatrixWords318 CyclicQuotientEvaluation318
open AlgebraicGeometry
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Action R A ι S)
@[expose] def standardBasis : Basis ι S (ι → S) :=
  Basis.ofEquivFun (LinearEquiv.refl S (ι → S))

/-- The selected determinant condition now applies to a CONSTRUCTED
original base-changed source action, with no source relations left assumed. -/
lemma cyclic (w : ι → List A)
    (h : IsUnit (determinant (point R A ι S a).val w)) :
    Function.Surjective (evaluation (linearAction R A ι S a) a.marked) := by
  apply LinearEvaluationDeterminant318.surjective
    (evaluation (linearAction R A ι S a) a.marked) (standardBasis ι S)
    (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
  have hc : LinearEvaluationDeterminant318.columns
      (evaluation (linearAction R A ι S a) a.marked) (standardBasis ι S)
      (fun j => (1 : S) ⊗ₜ[R] (w j).prod) = columns (point R A ι S a).val w := by
    ext i j
    change (standardBasis ι S).equivFun
      (evaluation (linearAction R A ι S a) a.marked ((1 : S) ⊗ₜ[R] (w j).prod)) i=_
    simp only [standardBasis,Basis.equivFun_ofEquivFun,LinearEquiv.refl_apply]
    exact congrFun (word_evaluation R A ι S a (w j)) i
  rw [hc]
  exact h

/-- The whole scheme-theoretic annihilator in the literal S tensor A. -/
abbrev quotientRing := (S ⊗[R] A) ⧸ ideal (linearAction R A ι S a) a.marked

@[expose] def quotientBasis (w : ι → List A)
    (h : IsUnit (determinant (point R A ι S a).val w)) :
    Basis ι S (quotientRing R A ι S a) :=
  CyclicQuotientKernel318.quotientBasis (linearAction R A ι S a) a.marked
    (standardBasis ι S) (cyclic R A ι S a w h)

lemma finite (w : ι → List A)
    (h : IsUnit (determinant (point R A ι S a).val w)) :
    IsFinite (CyclicQuotientFiniteFlat318.projection (linearAction R A ι S a) a.marked) :=
  CyclicQuotientFiniteFlat318.finite (linearAction R A ι S a) a.marked
    (standardBasis ι S) (cyclic R A ι S a w h)
lemma flat (w : ι → List A)
    (h : IsUnit (determinant (point R A ι S a).val w)) :
    Flat (CyclicQuotientFiniteFlat318.projection (linearAction R A ι S a) a.marked) :=
  CyclicQuotientFiniteFlat318.flat (linearAction R A ι S a) a.marked
    (standardBasis ι S) (cyclic R A ι S a w h)
end VaryingSourceWordQuotient318
