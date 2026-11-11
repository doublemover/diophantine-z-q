module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public section
noncomputable section
namespace OpenCartesianSectionSquare318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
variable {W U V X : Scheme} (right : W ⟶ V) (left : W ⟶ U)
  (k : V ⟶ X) (j : U ⟶ X) [IsOpenImmersion left] [IsOpenImmersion k]
  (H : IsPullback right left k j)

/-- Exact opens equality in a genuine Cartesian open-immersion square. -/
lemma opens_square (O : V.Opens) : left ''ᵁ right ⁻¹ᵁ O=j ⁻¹ᵁ k ''ᵁ O :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H O

lemma transport_appIso (O : W.Opens) (A : U.Opens) (h : left ''ᵁ O=A) :
    U.presheaf.map (eqToHom h).op≫(left.appIso O).hom=
      left.app A≫W.presheaf.map
        (eqToHom (by rw [←h,left.preimage_image_eq] : O=left ⁻¹ᵁ A)).op := by
  subst A
  simp only [eqToHom_refl,op_id,Functor.map_id,Category.id_comp,Scheme.Hom.appIso_hom]

/-- The scalar maps on the two actual module-section constructions
agree after the exact opens transport. This retains the original ring
sheaf maps, rather than identifying only the underlying abelian groups. -/
theorem scalar_square (O : V.Opens) :
    (k.appIso O).inv≫j.app (k ''ᵁ O)≫
      U.presheaf.map (eqToHom (opens_square right left k j H O)).op=
    right.app O≫(left.appIso (right ⁻¹ᵁ O)).inv := by
  apply (cancel_mono (left.appIso (right ⁻¹ᵁ O)).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [transport_appIso left (right ⁻¹ᵁ O) _ (opens_square right left k j H O)]
  rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq right k (left≫j) H.w.symm O,
    Scheme.Hom.comp_app]
  simpa only [Category.assoc]
end OpenCartesianSectionSquare318
