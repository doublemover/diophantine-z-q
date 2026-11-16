module
public import VaryingNormalizedIdealGenerators318
public import Mathlib.RingTheory.Ideal.Maps
public section
noncomputable section
namespace VaryingNormalizedIdealBaseChange318
open VaryingNormalizedIdealGenerators318 VaryingNormalizedWordFrame318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S T : Type u) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
variable (f : S →ₐ[R] T) (d : VaryingNormalizedWordParameter318.Point R A ι w S)
local notation "dT" => VaryingNormalizedWordNaturality318.mapPoint R A ι w S T f d
local notation "F" => framed R A ι w S d
local notation "FT" => framed R A ι w T dT
@[expose] def sourceMap : S ⊗[R] A →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map f (AlgHom.id R A)
lemma evaluation_natural (z : S ⊗[R] A) :
    evaluate R A ι w T dT (sourceMap R A S T f z)=
      fun i => f (evaluate R A ι w S d z i) :=
  VaryingSourceSurjectiveCoefficient318.evaluation_map R A ι S T f (sourceAction R A ι w S d) z

lemma section_natural (x : ι → S) :
    sourceMap R A S T f (sectionMap R A ι w S x)=
      sectionMap R A ι w T (fun i => f (x i)) := by
  rw [section_formula,section_formula,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Algebra.TensorProduct.map_tmul f (AlgHom.id R A) (x j) ((w j).prod)

lemma relation_natural (a : A) :
    sourceMap R A S T f (relation R A ι w S d a)=relation R A ι w T dT a := by
  change sourceMap R A S T f
    ((1 : S) ⊗ₜ[R] a-sectionMap R A ι w S (evaluate R A ι w S d ((1 : S) ⊗ₜ[R] a)))=
    (1 : T) ⊗ₜ[R] a-sectionMap R A ι w T (evaluate R A ι w T dT ((1 : T) ⊗ₜ[R] a))
  rw [map_sub,section_natural,← evaluation_natural]
  simp only [sourceMap,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]

/-- Exact extension of the original full quotient ideal under EVERY
coefficient map. No flatness, injectivity, surjectivity or reducedness is
imposed on the map; the explicit normalized source relations prove it. -/
lemma ideal_map : Ideal.map (sourceMap R A S T f).toRingHom (ideal F.action F.marked)=
    ideal FT.action FT.marked := by
  rw [ideal_eq_relations,ideal_eq_relations]
  change Ideal.map (sourceMap R A S T f).toRingHom
    (Ideal.span (Set.range (relation R A ι w S d)))=
      Ideal.span (Set.range (relation R A ι w T dT))
  rw [Ideal.map_span,Set.image_range]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact relation_natural R A ι w S T f d a
end VaryingNormalizedIdealBaseChange318
