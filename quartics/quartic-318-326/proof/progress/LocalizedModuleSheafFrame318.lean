module
public import AffineModuleBasisFrame318
public import Mathlib.RingTheory.Localization.Module
public section
noncomputable section
namespace LocalizedModuleSheafFrame318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:CommRingCat.{u}} (M:(Spec R).Modules) [M.IsQuasicoherent] (a:R)
abbrev ring:=CommRingCat.of (Localization.Away a)
abbrev ringMap:R⟶ring a:=CommRingCat.ofHom (algebraMap R (Localization.Away a))
abbrev schemeMap:=Spec.map (ringMap a)
abbrev restricted:=M.restrict (schemeMap a)
abbrev globals:=moduleSpecΓFunctor.obj (restricted M a)
local instance:Module R (globals M a):=Module.compHom _ (ringMap a).hom
local instance:IsScalarTower R (ring a) (globals M a):=IsScalarTower.of_compHom ..
lemma image_top:schemeMap a ''ᵁ ⊤=PrimeSpectrum.basicOpen a:=by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact Opens.ext (PrimeSpectrum.localization_away_comap_range (Localization.Away a) a)
/-- Exact additive section comparison on the literal localization open. -/
@[expose] def openIso:Γ(restricted M a,⊤)≅Γ(M,PrimeSpectrum.basicOpen a):=
  M.restrictAppIso (schemeMap a) ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (image_top a).symm).op
/-- The original localization-open section comparison, retaining the R action. -/
@[expose] def openEquiv:globals M a≃ₗ[R]Γ(M,PrimeSpectrum.basicOpen a) where
  toFun:=(openIso M a).hom
  invFun:=(openIso M a).inv
  left_inv s:=(openIso M a).hom_inv_id_apply s
  right_inv s:=(openIso M a).inv_hom_id_apply s
  map_add' s t:=(openIso M a).hom.hom.map_add s t
  map_smul' r s:=by
    change (openIso M a).hom ((ringMap a) r • s)=r • (openIso M a).hom s
    dsimp only [openIso,Iso.trans_hom]
    rw [ConcreteCategory.comp_apply,Scheme.Modules.restrictAppIso_smul_Spec]
    exact Scheme.Modules.map_smul_Spec _ _ _
/-- The map is precisely restriction of the original global section, transported
through the actual open immersion's section comparison. -/
@[expose] def restriction:moduleSpecΓFunctor.obj M→ₗ[R]globals M a:=
  (openEquiv M a).symm.toLinearMap.comp
    (((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom)
lemma restriction_localizes:IsLocalizedModule (Submonoid.powers a) (restriction M a):=by
  letI:=Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  change IsLocalizedModule (Submonoid.powers a)
    ((openEquiv M a).symm.toLinearMap.comp
      (((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom))
  rw [IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers a)
    (openEquiv M a).symm.toLinearMap (openEquiv M a).symm.bijective]
  exact ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) a
/-- Actual two-sided linear equivalence with the canonical localized original
module; the extended scalar action is the genuine localization-ring action. -/
@[expose] def equiv:LocalizedModule.Away a (moduleSpecΓFunctor.obj M)≃ₗ[ring a]globals M a:=by
  letI:=restriction_localizes M a
  exact (IsLocalizedModule.iso (Submonoid.powers a) (restriction M a)).extendScalarsOfIsLocalization
    (Submonoid.powers a) (ring a)
lemma equiv_mk_one (s:moduleSpecΓFunctor.obj M):
    equiv M a (LocalizedModule.mk s 1)=restriction M a s:=by
  letI:=restriction_localizes M a
  exact IsLocalizedModule.iso_mk_one (Submonoid.powers a) (restriction M a) s
lemma equiv_left_inverse (s:LocalizedModule.Away a (moduleSpecΓFunctor.obj M)):
    (equiv M a).symm (equiv M a s)=s:=(equiv M a).symm_apply_apply s
lemma equiv_right_inverse (s:globals M a):
    equiv M a ((equiv M a).symm s)=s:=(equiv M a).apply_symm_apply s
/-- A localized basis yields an actual free frame of the original sheaf
restricted along the literal principal localization immersion. -/
@[expose] def frame {ι:Type u}
    (b:Module.Basis ι (ring a) (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    SheafOfModules.free (R:=(Spec (ring a)).ringCatSheaf) ι≅restricted M a:=
  AffineModuleBasisFrame318.frame (restricted M a) (b.map (equiv M a))
lemma frame_hom_inv {ι:Type u}
    (b:Module.Basis ι (ring a) (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    (frame M a b).hom≫(frame M a b).inv=𝟙 _ :=(frame M a b).hom_inv_id
lemma frame_inv_hom {ι:Type u}
    (b:Module.Basis ι (ring a) (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    (frame M a b).inv≫(frame M a b).hom=𝟙 _ :=(frame M a b).inv_hom_id
end LocalizedModuleSheafFrame318
