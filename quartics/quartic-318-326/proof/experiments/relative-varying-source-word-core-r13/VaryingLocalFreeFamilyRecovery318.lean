module
public import VaryingLocalFreeQuotientNaturality318
public section
noncomputable section
namespace VaryingLocalFreeFamilyRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingLocalFreeQuotientEquiv318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : LocalIdeal R A ι S)
local notation "x" => classify R A ι S I
local notation "J" => VaryingParameterPointIdeal318.ideal R A ι S x
local notation "Q" => VaryingWholeIdealFamily318.family R A S I.val
local notation "q" => VaryingWholeIdealFamily318.into R A S I.val
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
lemma ideal_eq : J=I.val := congrArg Subtype.val (recover_classify R A ι S I)
/-- The literal original quotient of ANY locally free full ideal is the
actual universal-family pullback, not a framed replacement model. -/
@[expose] def comparison : Q ≅ VaryingParameterPointFamily318.family R A ι S x :=
  (VaryingParameterPointIdeal318.comparison R A ι S x ≪≫
    AffineIdealEqualityIso318.iso (S ⊗[R] A) J I.val (ideal_eq R A ι S I)).symm
@[reassoc] lemma comparison_inv_into : (comparison R A ι S I).inv ≫ q=
    VaryingParameterPointFamily318.intoSource R A ι S x := by
  change ((VaryingParameterPointIdeal318.comparison R A ι S x).hom ≫
    (AffineIdealEqualityIso318.iso (S ⊗[R] A) J I.val (ideal_eq R A ι S I)).hom) ≫ q=_
  rw [Category.assoc,AffineIdealEqualityIso318.hom_into,VaryingParameterPointIdeal318.comparison_into]
@[reassoc] lemma comparison_into : (comparison R A ι S I).hom ≫
    VaryingParameterPointFamily318.intoSource R A ι S x=q := by
  rw [← comparison_inv_into,← Category.assoc,Iso.hom_inv_id,Category.id_comp]
@[reassoc] lemma comparison_projection : (comparison R A ι S I).hom ≫
    VaryingParameterPointFamily318.projection R A ι S x=
    VaryingWholeIdealFamily318.projection R A S I.val := by
  rw [← VaryingParameterPointFamily318.into_projection,← Category.assoc,comparison_into]
  rfl
@[expose] def map : Q ⟶ VaryingWordFamilyGluing318.scheme R A ι :=
  (comparison R A ι S I).hom ≫ VaryingParameterPointFamily318.intoFamily R A ι S x
lemma cartesian : IsPullback (map R A ι S I) (VaryingWholeIdealFamily318.projection R A S I.val) π x.val := by
  apply IsPullback.of_iso_pullback (i := comparison R A ι S I)
  · constructor
    rw [map,Category.assoc,pullback.condition,← Category.assoc,comparison_projection]
  · rfl
  · exact comparison_projection R A ι S I
instance finite : IsFinite (VaryingWholeIdealFamily318.projection R A S I.val) := by
  rw [← comparison_projection]
  infer_instance
instance flat : Flat (VaryingWholeIdealFamily318.projection R A S I.val) := by
  rw [← comparison_projection]
  infer_instance
end VaryingLocalFreeFamilyRecovery318
