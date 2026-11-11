module
public import VaryingParameterPointIdeal318
public section
noncomputable section
namespace VaryingClassifiedIdealRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (I : VaryingFreeIdealClassifyingMap318.IdealData R A ι S)
local notation "x" => VaryingParameterPoint318.ofIdeal R A ι S I
local notation "e" => VaryingFreeIdealFamilyRecovery318.comparison R A ι S I
lemma comparison_source : e.hom ≫ VaryingParameterPointFamily318.intoSource R A ι S x=
    VaryingFreeIdealFamilyRecovery318.into R A ι S I := by
  apply (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).hom_ext
  · rw [Category.assoc,VaryingParameterPointFamily318.into_projection]
    have he := (VaryingFreeIdealFamilyRecovery318.cartesian R A ι S I).isoPullback_hom_snd
    rw [he]
    change Spec.map (CommRingCat.ofHom (algebraMap S ((S ⊗[R] A) ⧸ I.val)))=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.val)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A)))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact IsScalarTower.algebraMap_eq S (S ⊗[R] A) ((S ⊗[R] A) ⧸ I.val)
  · rw [Category.assoc,VaryingParameterPointFamily318.into_original,← Category.assoc,
      (VaryingFreeIdealFamilyRecovery318.cartesian R A ι S I).isoPullback_hom_fst,
      VaryingFreeIdealFamilyRecovery318.map_original]
/-- Extracting the actual universal-family ideal after classification
returns the original ideal exactly, including all nilpotent structure. -/
lemma ideal_ofIdeal : VaryingParameterPointIdeal318.ideal R A ι S x=I.val := by
  apply VaryingParameterPointIdeal318.unique R A ι S x I.val e.symm
  rw [← comparison_source,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
end VaryingClassifiedIdealRecovery318
