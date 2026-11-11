module
public import AffineQuotientFactorRigidity318
public section
noncomputable section
namespace AffineIdealEqualityIso318
open AlgebraicGeometry CategoryTheory
universe u
variable (B : Type u) [CommRing B] (I J : Ideal B) (h : I=J)
@[expose] def iso : Spec (CommRingCat.of (B ⧸ I)) ≅ Spec (CommRingCat.of (B ⧸ J)) := by
  subst J
  exact Iso.refl _
@[reassoc] lemma hom_into : (iso B I J h).hom ≫ AffineQuotientFactorRigidity318.into B J=
    AffineQuotientFactorRigidity318.into B I := by
  subst J
  simp only [iso,Iso.refl_hom,Category.id_comp]
@[reassoc] lemma inv_into : (iso B I J h).inv ≫ AffineQuotientFactorRigidity318.into B I=
    AffineQuotientFactorRigidity318.into B J := by
  subst J
  simp only [iso,Iso.refl_inv,Category.id_comp]
variable (S : Type u) [CommRing S] [Algebra S B]
@[reassoc] lemma hom_projection : (iso B I J h).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap S (B ⧸ J)))=
    Spec.map (CommRingCat.ofHom (algebraMap S (B ⧸ I))) := by
  subst J
  simp only [iso,Iso.refl_hom,Category.id_comp]
end AffineIdealEqualityIso318
