module
public import ActualTwoDescentOriginalRootNativeSquareCharts318
public import TildeComparison318
public section
noncomputable section
namespace ActualTwoDescentIdealLocalizationAdjoint318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
open ActualTwoDescentLocalizedIdealTensorEquivalence318
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

/-- The LITERAL element map into the actual extended ideal,with its
precise restricted scalar action. -/
def idealModuleMap : ModuleCat.of R I ⟶
    (ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S (I.map (algebraMap R S))) :=
  ModuleCat.ofHom (Y:=(ModuleCat.restrictScalars (algebraMap R S)).obj
    (ModuleCat.of S (I.map (algebraMap R S)))) {
    toFun := fun x => ⟨algebraMap R S (x:R),Ideal.mem_map_of_mem _ x.property⟩
    map_add' x y := Subtype.ext (map_add (algebraMap R S) (x:R) (y:R))
    map_smul' r x := by
      apply Subtype.ext
      change algebraMap R S (r*(x:R))=algebraMap R S r*algebraMap R S (x:R)
      exact map_mul (algebraMap R S) r (x:R) }

def idealExtensionEquiv :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R I) ≃ₗ[S]
      I.map (algebraMap R S) :=
  (ScalarExtensionTensor318.tensorEquiv (T:=S) (ModuleCat.of R I)).trans
    (localizedIdealTensorEquiv S M I)

/-- The exact native extension equivalence has the original ideal
localization map as its adjoint. This fixes normalization,not just rank. -/
lemma module_adjoint :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _
      (idealExtensionEquiv S M I).toModuleIso.hom=idealModuleMap S I := by
  ext x
  apply Subtype.ext
  change (idealExtensionEquiv S M I ((1:S) ⊗ₜ[R,algebraMap R S] x) : S)=algebraMap R S (x:R)
  change (localizedIdealTensorEquiv S M I ((1:S) ⊗ₜ[R] x) : S)=_
  rw [actual_localized_ideal_tensor_value,one_mul]
end ActualTwoDescentIdealLocalizationAdjoint318
