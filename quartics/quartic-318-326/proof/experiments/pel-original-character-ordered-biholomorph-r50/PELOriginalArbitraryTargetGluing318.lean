module
public import PELOriginalArbitraryTargetDomainCover318
public section
noncomputable section
namespace PELOriginalArbitraryTargetGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalLocalTargetSchemeMaps318 PELOriginalLocalSchemeFactorization318
open PELOriginalArbitraryTargetDomainCover318
variable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
  (hg:∀a:Kernel i,schemeDeck a.val≫g=g)
local instance mapFlat:Flat (morphism i):=PELOriginalWholeCharacterFlat318.flat i
local instance mapSurjective:Surjective (morphism i):=PELOriginalWholeCharacterProper318.surjective i

@[expose] def chartMap (V:Z.affineOpens):(cover i g hg).X V⟶Z:=
  localMapToTarget i g hg V.val V.property

lemma compatible (V W:Z.affineOpens):
    pullback.fst ((cover i g hg).f V) ((cover i g hg).f W)≫chartMap i g hg V=
      pullback.snd _ _≫chartMap i g hg W:=
  FlatSurjectiveLocalFactorAgreement318.pullback_compatibility (morphism i) g
    (domain i g hg V) (domain i g hg W) _ _
      (restricted_factor_to_target i g hg V.val V.property)
      (restricted_factor_to_target i g hg W.val W.property)

/-- The ACTUAL glued morphism into the ORIGINAL arbitrary target,
constructed from produced local maps and proved overlap compatibility. -/
@[expose] def quotientLift:Curve i⟶Z:=
  (cover i g hg).glueMorphisms (chartMap i g hg) (compatible i g hg)

lemma on_domain (V:Z.affineOpens):
    (domain i g hg V).ι≫quotientLift i g hg=chartMap i g hg V:=
  (cover i g hg).ι_glueMorphisms _ _ V

/-- Exact scheme factor equality is checked on a produced source cover;
no pointwise/dense-locus uniqueness or quotient hypothesis is substituted. -/
theorem quotientLift_factor:morphism i≫quotientLift i g hg=g:=by
  apply (sourceCover i g hg).hom_ext
  intro V
  change (morphism i⁻¹ᵁdomain i g hg V).ι≫(morphism i≫quotientLift i g hg)=
    (morphism i⁻¹ᵁdomain i g hg V).ι≫g
  calc
    _=(morphism i ∣_ domain i g hg V)≫((domain i g hg V).ι≫quotientLift i g hg):=by
      rw [←Category.assoc,morphismRestrict_ι,Category.assoc]
    _=(morphism i ∣_ domain i g hg V)≫chartMap i g hg V:=by rw [on_domain]
    _=_:=restricted_factor_to_target i g hg V.val V.property
end PELOriginalArbitraryTargetGluing318
