module
public import SelectedJOneExactMinorLoss318
import all SelectedJOneExactMinorLoss318
public import JLineAtlas318
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.ValuationSubring
public section
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open SelectedJOneExactMinorLoss318 IsDedekindDomain

namespace SelectedJOneValuativeSections318
universe u
variable {L : Type u} [Field L] [NumberField L] (v : FinitePlace L)

/-- The actual localization of the ring of integers at the finite
prime of the evaluation field, as a valuation subring of L. -/
abbrev trait : ValuationSubring L :=
  HeightOneSpectrum.valuationSubringAtPrime L v.maximalIdeal

/-- Match the literal embedded localization to the EXACT norm≤1
subring used by the determinant rows, before any model comparison. -/
theorem trait_subring : (trait v).toSubring = integralAt v := by
  ext x
  change x ∈ trait v ↔ v x ≤ 1
  rw [trait,HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff,← FinitePlace.norm_embedding_eq v x,
    FinitePlace.norm_embedding']
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (m:=v.maximalIdeal.valuation L x)
    (HeightOneSpectrum.one_lt_absNorm_nnreal v.maximalIdeal)).symm

local notation "O" => ↥(trait v)
local notation "S" => Spec (CommRingCat.of O)
local notation "G" => Spec (CommRingCat.of L)

@[expose] def genericInclusion : G ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap O L))

/-- The valuative square is over this exact finite-place base. -/
@[expose] def sectionSquare {X : Scheme.{u}} (f : X ⟶ S)
    (P : G ⟶ X) (hP : P ≫ f = genericInclusion v) : ValuativeCommSq f where
  R := O
  K := L
  i₁ := P
  i₂ := 𝟙 S
  commSq := ⟨by rw [Category.comp_id]; exact hP⟩

/-- Extend the selected generic point on the actual proper model;
no new field, no arbitrary extension of a rational function map. -/
theorem extends_uniquely {X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (P : G ⟶ X) (hP : P ≫ f = genericInclusion v) :
    ∃! s : S ⟶ X, genericInclusion v ≫ s = P ∧ s ≫ f = 𝟙 S := by
  have hf : @IsProper _ _ f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hf
  have hC : ValuativeCriterion f := hf.1.1.1
  let Q := sectionSquare v f P hP
  obtain ⟨U⟩ := hC Q
  refine ⟨U.default.l,⟨U.default.fac_left,U.default.fac_right⟩,?_⟩
  intro t ht
  let T : Q.commSq.LiftStruct := ⟨t,ht.1,ht.2⟩
  exact congrArg CommSq.LiftStruct.l (U.uniq T)

/-- The literal j=1 section of the already constructed projective
j-line, with the fixed polynomial chart orientation. -/
@[expose] def onePoint : S ⟶ ProjectiveJLine318.scheme O :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (1:O)).toRingHom) ≫ JLineAtlas318.chart O 1

theorem onePoint_base : onePoint v ≫ ProjectiveJLine318.structureMap O = 𝟙 S := by
  rw [onePoint,Category.assoc,JLineAtlas318.chart_over_base,← Spec.map_comp,← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
    ((Polynomial.aeval (1:O)).commutes r)

/-- Separatedness on the actual projective j-line fixes the whole
integral image, not merely its generic or special fiber value. -/
theorem sections_one {X : Scheme.{u}}
    (j : X ⟶ ProjectiveJLine318.scheme O)
    (s : S ⟶ X) (P : G ⟶ X)
    (hs : genericInclusion v ≫ s = P)
    (hbase : s ≫ (j ≫ ProjectiveJLine318.structureMap O) = 𝟙 S)
    (hj : P ≫ j = genericInclusion v ≫ onePoint v) :
    s ≫ j = onePoint v := by
  let f := ProjectiveJLine318.structureMap O
  let Pj := genericInclusion v ≫ onePoint v
  have hPj : Pj ≫ f = genericInclusion v := by
    change (genericInclusion v ≫ onePoint v) ≫ ProjectiveJLine318.structureMap O = _
    rw [Category.assoc,onePoint_base,Category.comp_id]
  let Q := sectionSquare v f Pj hPj
  have H : ValuativeCriterion.Uniqueness f :=
    IsSeparated.valuativeCriterion f
  letI : Subsingleton Q.commSq.LiftStruct := H Q
  let sj : Q.commSq.LiftStruct :=
    ⟨s ≫ j,by change genericInclusion v ≫ (s ≫ j) = Pj
              rw [← Category.assoc,hs]; exact hj,
      by change (s ≫ j) ≫ f = 𝟙 S
         rw [Category.assoc]; exact hbase⟩
  let oj : Q.commSq.LiftStruct := ⟨onePoint v,rfl,onePoint_base v⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim sj oj)

/-- Extend the very same ordered evaluation points to the very same
proper model over v. The projection is literally 1 as a morphism
from the trait, so the sections factor through that j-fiber. -/
theorem ordered_sections {ι : Type*} {X : Scheme.{u}}
    (j : X ⟶ ProjectiveJLine318.scheme O)
    [IsProper (j ≫ ProjectiveJLine318.structureMap O)]
    (P : ι → G ⟶ X)
    (hP : ∀ i, P i ≫ (j ≫ ProjectiveJLine318.structureMap O) = genericInclusion v)
    (hJ : ∀ i, P i ≫ j = genericInclusion v ≫ onePoint v) :
    ∃ s : ι → S ⟶ X, (∀ i, genericInclusion v ≫ s i = P i) ∧
      (∀ i, s i ≫ (j ≫ ProjectiveJLine318.structureMap O) = 𝟙 S) ∧
      (∀ i, s i ≫ j = onePoint v) ∧
      (Function.Injective P → Function.Injective s) := by
  have h (i : ι) :=
    (extends_uniquely v (j ≫ ProjectiveJLine318.structureMap O) (P i) (hP i)).exists
  choose s hs using h
  refine ⟨s,fun i => (hs i).1,fun i => (hs i).2,?_,?_⟩
  · intro i
    exact sections_one v j (s i) (P i) (hs i).1 (hs i).2 (hJ i)
  · intro inj i i' he
    apply inj
    rw [← (hs i).1,← (hs i').1,he]

end SelectedJOneValuativeSections318

#print axioms SelectedJOneValuativeSections318.trait_subring
#print axioms SelectedJOneValuativeSections318.extends_uniquely
#print axioms SelectedJOneValuativeSections318.ordered_sections
