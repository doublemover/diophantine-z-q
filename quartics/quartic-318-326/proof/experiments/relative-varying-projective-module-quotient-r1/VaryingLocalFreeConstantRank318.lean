module
public import VaryingWholeQuotientRank318
public import VaryingLocalFreeModuleDegree318
public import Mathlib.LinearAlgebra.Dimension.Finrank
public section
noncomputable section
namespace VaryingLocalFreeConstantRank318
open AlgebraicGeometry CategoryTheory
open VaryingLocalFreeQuotientEquiv318 VaryingLocalFreeModuleProjective318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : LocalIdeal R A ι S)
/-- The geometric local-free input has the intended constant numerical
rank on EVERY coefficient prime, not merely on chosen free charts. -/
lemma degree_eq (x : PrimeSpectrum S) :
    VaryingLocalFreeModuleDegree318.degree R A ι S I x=Fintype.card ι := by
  let C := Classical.choice I.property
  obtain ⟨i,y,hy⟩ := C.coefficients.covers x
  let T := C.coefficients.ring i
  let f : S →ₐ[R] T := C.coefficients.coefficient i
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Nontrivial T := ⟨⟨1,0,by
    intro h
    apply y.isPrime.one_notMem
    rw [h]
    exact y.asIdeal.zero_mem⟩⟩
  let J : Ideal (T ⊗[R] A) := VaryingWholeQuotientTensor318.ideal R A S T I.val
  let b : Module.Basis ι T ((T ⊗[R] A) ⧸ J) := Classical.choice (C.free i)
  letI : Module.Free T ((T ⊗[R] A) ⧸ J) := Module.Free.of_basis b
  have hbase := VaryingWholeQuotientRank318.degree_baseChange R A S T I.val y
  change y.comap (algebraMap S T)=x at hy
  rw [hy] at hbase
  change Module.rankAtStalk ((S ⊗[R] A) ⧸ I.val) x=_
  rw [← hbase,Module.rankAtStalk_eq_finrank_of_free]
  simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_nat_card_basis b
/-- A concrete finite-projective module certificate for the original
quotient, with the intended rank verified rather than assumed. -/
theorem finite_projective_rank : Module.Finite S (quotient R A ι S I) ∧
    Module.Projective S (quotient R A ι S I) ∧
    ∀ x : PrimeSpectrum S, Module.rankAtStalk (quotient R A ι S I) x=Fintype.card ι :=
  ⟨inferInstance,inferInstance,degree_eq R A ι S I⟩
end VaryingLocalFreeConstantRank318
