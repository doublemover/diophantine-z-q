module
public import VaryingSplitIdealGenerators318
public section
noncomputable section
namespace VaryingCyclicCoefficientSections318
open VaryingSourceFreeQuotientClassifier318 VaryingSourceTensorAction318
open VaryingSourceSurjectiveCoefficient318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "e" => evaluation (linearAction R A ι S a.data) a.data.marked
local notation "std" T => VaryingSourceWordQuotient318.standardBasis ι T
@[expose] def preimage (j : ι) : S ⊗[R] A := Classical.choose (a.cyclic (std S j))
lemma evaluation_preimage (j : ι) : e (preimage R A ι S a j)=std S j :=
  Classical.choose_spec (a.cyclic (std S j))
@[expose] def sectionMap : (ι → S) →ₗ[S] (S ⊗[R] A) :=
  (std S).constr S (preimage R A ι S a)
lemma section_formula (x : ι → S) : sectionMap R A ι S a x=∑ j,x j • preimage R A ι S a j := by
  simp only [sectionMap,Basis.constr_apply_fintype,VaryingSourceWordQuotient318.standardBasis,
    Basis.equivFun_ofEquivFun,LinearEquiv.refl_apply]
lemma evaluation_section : e.comp (sectionMap R A ι S a)=LinearMap.id := by
  apply (std S).ext
  intro j
  rw [LinearMap.comp_apply,show sectionMap R A ι S a (std S j)=preimage R A ι S a j from
    Basis.constr_basis _ S _ j]
  exact evaluation_preimage R A ι S a j

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "source" => VaryingNormalizedIdealBaseChange318.sourceMap R A S T f
local notation "aT" => mapAction R A ι S T f a.data
local notation "eT" => evaluation (linearAction R A ι T aT) aT.marked
@[expose] def mappedSection : (ι → T) →ₗ[T] (T ⊗[R] A) :=
  (std T).constr T (fun j => source (preimage R A ι S a j))
lemma mapped_formula (x : ι → T) :
    mappedSection R A ι S a T f x=∑ j,x j • source (preimage R A ι S a j) := by
  simp only [mappedSection,Basis.constr_apply_fintype,VaryingSourceWordQuotient318.standardBasis,
    Basis.equivFun_ofEquivFun,LinearEquiv.refl_apply]
private lemma basis_image (j : ι) : (fun i => f (std S j i))=std T j := by
  rw [show std S j=Pi.single j 1 from
    congrFun (Basis.coe_ofEquivFun (LinearEquiv.refl S (ι → S))) j,
    show std T j=Pi.single j 1 from
    congrFun (Basis.coe_ofEquivFun (LinearEquiv.refl T (ι → T))) j]
  ext i
  simp only [Pi.single_apply]
  split_ifs <;> simp only [map_one,map_zero]
lemma evaluation_mappedSection : eT.comp (mappedSection R A ι S a T f)=LinearMap.id := by
  apply (std T).ext
  intro j
  rw [LinearMap.comp_apply,show mappedSection R A ι S a T f (std T j)=
      source (preimage R A ι S a j) from Basis.constr_basis _ T _ j]
  have h := evaluation_map R A ι S T f a.data (preimage R A ι S a j)
  rw [evaluation_preimage] at h
  exact h.trans (basis_image R ι S T f j)

/-- Cyclicity survives EVERY coefficient homomorphism. The proof maps
chosen source preimages of the standard basis, not arbitrary vectors. -/
lemma cyclic : Function.Surjective eT := by
  intro y
  refine ⟨mappedSection R A ι S a T f y,?_⟩
  exact congrArg (fun g : (ι → T) →ₗ[T] (ι → T) => g y)
    (evaluation_mappedSection R A ι S a T f)
@[expose] def mapCyclic : Cyclic R A ι T := ⟨aT,cyclic R A ι S a T f⟩

lemma source_smul (c : S) (z : S ⊗[R] A) : source (c • z)=f c • source z := by
  rw [Algebra.smul_def,Algebra.smul_def,map_mul]
  congr 1
  exact Algebra.TensorProduct.map_tmul f (AlgHom.id R A) c (1 : A)
lemma section_natural (x : ι → S) :
    source (sectionMap R A ι S a x)=mappedSection R A ι S a T f (fun i => f (x i)) := by
  rw [section_formula,mapped_formula,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact source_smul R A S T f (x j) (preimage R A ι S a j)
end VaryingCyclicCoefficientSections318
