module
public import ContactHilbertFixedRankEquiv318
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public section
noncomputable section
namespace IdealSheafCoefficientCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
@[expose] def map : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
/-- The full ideal comap has its ACTUAL canonical closed-family
Cartesian square, including the entire nonreduced scheme structure. -/
lemma cartesian : IsPullback (map I f) (I.comap f).subschemeι I.subschemeι f := by
  have H := (IsPullback.of_hasPullback f I.subschemeι).flip
  apply H.of_iso (I.comapIso f).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [map,Iso.symm_hom,Iso.refl_hom,Category.comp_id,Iso.inv_hom_id_assoc]
  · simpa only [Iso.symm_hom,Iso.refl_hom,Category.comp_id] using I.comapIso_inv_subschemeι f
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
end IdealSheafCoefficientCartesian318
