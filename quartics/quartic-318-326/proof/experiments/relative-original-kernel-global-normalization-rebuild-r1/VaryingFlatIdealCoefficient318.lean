module
public import IdealAlgebraEquiv318
public section
noncomputable section
namespace VaryingFlatIdealCoefficient318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (I : Ideal (S ⊗[R] A)) [Module.Flat S ((S ⊗[R] A) ⧸ I)]
local notation "e" => VaryingSourceTensorCollapse318.equivalence R A S T
local notation "J" => FlatQuotientIdealTensor318.extended S (S ⊗[R] A) T I
/-- The full ideal module of the actual original coefficient source is
exactly coefficient tensor of the original ideal. No flatness of T/S. -/
@[expose] def equivalence : T ⊗[S] I ≃ₗ[T] VaryingWholeQuotientTensor318.ideal R A S T I :=
  FlatQuotientIdealTensor318.equivalence S (S ⊗[R] A) T I ≪≫ₗ
    IdealAlgebraEquiv318.equivalence T (T ⊗[S] (S ⊗[R] A)) (T ⊗[R] A) e J ≪≫ₗ
      LinearEquiv.ofEq _ _ (congrArg (fun K : Ideal (T ⊗[R] A) => K.restrictScalars T)
        (VaryingSourceTensorCollapse318.ideal R A S T I))
lemma value (z : T ⊗[S] I) : (equivalence R A S T I z).val=
    e (FlatQuotientIdealTensor318.map S (S ⊗[R] A) T I z) := rfl
lemma unit_tmul (i : I) : (equivalence R A S T I ((1 : T) ⊗ₜ[S] i)).val=
    VaryingWholeQuotientTensor318.source R A S T i.val :=
  VaryingSourceTensorCollapse318.source R A S T i.val
lemma tmul (t : T) (i : I) : (equivalence R A S T I (t ⊗ₜ[S] i)).val=
    t • VaryingWholeQuotientTensor318.source R A S T i.val := by
  have h := (equivalence R A S T I).map_smul t ((1 : T) ⊗ₜ[S] i)
  have h' := congrArg Subtype.val h
  simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one,Submodule.coe_smul,unit_tmul] using h'
end VaryingFlatIdealCoefficient318
