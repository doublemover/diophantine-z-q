module
public import VaryingCyclicCoefficientSections318
public section
noncomputable section
namespace VaryingCyclicIdealBaseChange318
open VaryingSourceFreeQuotientClassifier318 VaryingSourceTensorAction318
open VaryingSourceSurjectiveCoefficient318 VaryingCyclicCoefficientSections318
open VaryingSplitIdealGenerators318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S) (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "ρ" => linearAction R A ι S a.data
local notation "v" => a.data.marked
local notation "s" => sectionMap R A ι S a
local notation "aT" => mapAction R A ι S T f a.data
local notation "ρT" => linearAction R A ι T aT
local notation "vT" => aT.marked
local notation "sT" => mappedSection R A ι S a T f
local notation "source" => VaryingNormalizedIdealBaseChange318.sourceMap R A S T f
lemma relation_natural (b : A) : source (relation R A S ρ v s b)=relation R A T ρT vT sT b := by
  change source ((1 : S) ⊗ₜ[R] b-s (evaluation ρ v ((1 : S) ⊗ₜ[R] b)))=
    (1 : T) ⊗ₜ[R] b-sT (evaluation ρT vT ((1 : T) ⊗ₜ[R] b))
  rw [map_sub,section_natural,← evaluation_map]
  simp only [VaryingNormalizedIdealBaseChange318.sourceMap,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]

/-- Exact ideal extension for EVERY cyclic original-source action, without
a global word basis and without flatness/surjectivity of coefficients. -/
lemma ideal_map : Ideal.map source.toRingHom (ideal ρ v)=ideal ρT vT := by
  rw [ideal_eq_relations R A S ρ v s (evaluation_section R A ι S a),
    ideal_eq_relations R A T ρT vT sT (evaluation_mappedSection R A ι S a T f)]
  change Ideal.map source.toRingHom (Ideal.span (Set.range (relation R A S ρ v s)))=
    Ideal.span (Set.range (relation R A T ρT vT sT))
  rw [Ideal.map_span,Set.image_range]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext b
  exact relation_natural R A ι S a T f b
end VaryingCyclicIdealBaseChange318
