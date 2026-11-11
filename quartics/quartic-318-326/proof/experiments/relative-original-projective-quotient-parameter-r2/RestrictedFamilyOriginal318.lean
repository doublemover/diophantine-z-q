module
public import TwoRestrictedFamilyPullback318
public section
noncomputable section
namespace RestrictedFamilyOriginal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {E A W T : Scheme.{u}} (π : E ⟶ A) (w : W ⟶ A) (j : T ⟶ W)
  (g : T ⟶ A) (h : j ≫ w=g)

@[reassoc] lemma one : (RestrictedFamilyPullback318.iso π w j g h).hom ≫ pullback.fst π g=
    pullback.fst (pullback.snd π w) j ≫ pullback.fst π w :=
  (RestrictedFamilyPullback318.square π w j g h).isoPullback_hom_fst
@[reassoc] lemma one_inv : (RestrictedFamilyPullback318.iso π w j g h).inv ≫
    pullback.fst (pullback.snd π w) j ≫ pullback.fst π w=pullback.fst π g := by
  rw [← one π w j g h,Iso.inv_hom_id_assoc]

variable {B U : Scheme.{u}} (k : B ⟶ W) (l : U ⟶ B) (q : U ⟶ A) (hq : l ≫ k ≫ w=q)
/-- Both original Cartesian restrictions retain their actual map into
the ORIGINAL total family, not merely the coefficient projection. -/
@[reassoc] lemma two : (TwoRestrictedFamilyPullback318.iso π w k l q hq).hom ≫
    pullback.fst π q=
    pullback.fst (pullback.snd (pullback.snd π w) k) l ≫
      pullback.fst (pullback.snd π w) k ≫ pullback.fst π w := by
  rw [TwoRestrictedFamilyPullback318.iso,Iso.trans_hom,Category.assoc,one,
    ← Category.assoc,one,Category.assoc]
@[reassoc] lemma two_inv : (TwoRestrictedFamilyPullback318.iso π w k l q hq).inv ≫
    pullback.fst (pullback.snd (pullback.snd π w) k) l ≫
      pullback.fst (pullback.snd π w) k ≫ pullback.fst π w=pullback.fst π q := by
  rw [← two π w k l q hq,Iso.inv_hom_id_assoc]
end RestrictedFamilyOriginal318
