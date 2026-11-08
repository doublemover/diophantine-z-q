module
public import FifthQuarticFiniteCoordinates318
public import FifthBranchAgreement318
public section
noncomputable section
namespace FifthQuarticCompatibility318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FifthQuarticCover318 FifthCharacterShortPolynomial318
set_option maxHeartbeats 700000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
abbrev LocalRing (b:Bool):=Localization.Away (chartElement b)
@[expose] def input (b:Bool):Quartic→ₐ[ℚ]LocalRing b:=IsScalarTower.toAlgHom ℚ Quartic _
@[expose] def localMap (b:Bool):Spec (CommRingCat.of (LocalRing b))⟶FifthCharacterShortScheme318.completed:=
  match b with
  | false=>FifthQuarticFinite318.map
  | true=>FifthBranchScheme318.intoCompleted

section Agreement
variable {S:Type} [CommRing S] [Algebra ℚ S]
theorem mixed (φ:LocalRing false→ₐ[ℚ]S) (ψ:LocalRing true→ₐ[ℚ]S)
    (hp:∀r:Quartic,φ (input false r)=ψ (input true r)):
    Spec.map (CommRingCat.ofHom φ.toRingHom)≫localMap false=
      Spec.map (CommRingCat.ofHom ψ.toRingHom)≫localMap true:=by
  change FifthQuarticFinite318.Local→ₐ[ℚ]S at φ
  change FifthBranchLocal318.Local→ₐ[ℚ]S at ψ
  have hb:algebraMap Quartic FifthBranchLocal318.Local parameter=FifthBranchLocal318.t:=
    (IsScalarTower.algebraMap_apply ℚ[X] Quartic FifthBranchLocal318.Local X).symm
  have ht:φ FifthQuarticFiniteCoordinates318.t=ψ FifthBranchLocal318.t:=by
    have h:=hp parameter
    change φ FifthQuarticFiniteCoordinates318.t=ψ (algebraMap Quartic FifthBranchLocal318.Local parameter) at h
    rw [hb] at h
    exact h
  have hw:φ FifthQuarticFiniteCoordinates318.w=ψ FifthBranchLocal318.w:=hp _
  have hx:=congrArg φ FifthQuarticFiniteCoordinates318.x_relation
  have hy:=congrArg φ FifthQuarticFiniteCoordinates318.y_relation
  change φ (FifthQuarticFinite318.shortMap (ShortAffineJacobian318.x A B) *
    FifthQuarticFiniteCoordinates318.t) = φ (algebraMap ℚ FifthQuarticFinite318.Local (xScale:ℚ) +
    algebraMap ℚ FifthQuarticFinite318.Local shift * FifthQuarticFiniteCoordinates318.t) at hx
  change φ (FifthQuarticFinite318.shortMap (ShortAffineJacobian318.y A B) *
    FifthQuarticFiniteCoordinates318.t^2) = φ (algebraMap ℚ FifthQuarticFinite318.Local (yScale:ℚ) *
    FifthQuarticFiniteCoordinates318.w) at hy
  simp only [map_mul,map_add,map_pow,AlgHom.commutes,ht,hw] at hx hy
  change Spec.map (CommRingCat.ofHom φ.toRingHom)≫
      (Spec.map (CommRingCat.ofHom FifthQuarticFinite318.shortMap.toRingHom)≫
        WeierstrassGluing318.finiteChart A B)=_
  rw [←Category.assoc,←Spec.map_comp]
  exact FifthBranchAgreement318.agreement ψ (φ.comp FifthQuarticFinite318.shortMap)
    (ht ▸ FifthQuarticFiniteCoordinates318.t_unit.map φ) hx hy

theorem same_chart (b:Bool) (φ ψ:LocalRing b→ₐ[ℚ]S)
    (hp:∀r:Quartic,φ (input b r)=ψ (input b r)):
    Spec.map (CommRingCat.ofHom φ.toRingHom)≫localMap b=
      Spec.map (CommRingCat.ofHom ψ.toRingHom)≫localMap b:=by
  have he:φ=ψ:=by
    apply IsLocalization.algHom_ext (Submonoid.powers (chartElement b))
    apply AlgHom.ext
    exact hp
  rw [he]

theorem agreement (b d:Bool) (φ:LocalRing b→ₐ[ℚ]S) (ψ:LocalRing d→ₐ[ℚ]S)
    (hp:∀r:Quartic,φ (input b r)=ψ (input d r)):
    Spec.map (CommRingCat.ofHom φ.toRingHom)≫localMap b=
      Spec.map (CommRingCat.ofHom ψ.toRingHom)≫localMap d:=by
  cases b <;> cases d
  · exact same_chart false φ ψ hp
  · exact mixed φ ψ hp
  · exact (mixed ψ φ (fun r=>(hp r).symm)).symm
  · exact same_chart true φ ψ hp
end Agreement

abbrev Common (b d:Bool):=LocalRing b⊗[Quartic]LocalRing d
@[expose] def left (b d:Bool):LocalRing b→ₐ[ℚ]Common b d:=
  (Algebra.TensorProduct.includeLeft:LocalRing b→ₐ[Quartic]Common b d).restrictScalars ℚ
@[expose] def right (b d:Bool):LocalRing d→ₐ[ℚ]Common b d:=
  (Algebra.TensorProduct.includeRight:LocalRing d→ₐ[Quartic]Common b d).restrictScalars ℚ
lemma same_input (b d:Bool) (r:Quartic):left b d (input b r)=right b d (input d r):=
  ((Algebra.TensorProduct.includeLeft:LocalRing b→ₐ[Quartic]Common b d).commutes r).trans
    ((Algebra.TensorProduct.includeRight:LocalRing d→ₐ[Quartic]Common b d).commutes r).symm

/-- Compatibility on the actual categorical overlap, retaining the full tensor algebra. -/
theorem compatible (b d:Bool):
    pullback.fst (cover.f b) (cover.f d)≫localMap b=
      pullback.snd (cover.f b) (cover.f d)≫localMap d:=by
  change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Quartic (LocalRing b))))
      (Spec.map (CommRingCat.ofHom (algebraMap Quartic (LocalRing d))))≫localMap b=
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap Quartic (LocalRing b))))
      (Spec.map (CommRingCat.ofHom (algebraMap Quartic (LocalRing d))))≫localMap d
  apply (cancel_epi (pullbackSpecIso Quartic (LocalRing b) (LocalRing d)).inv).mp
  rw [←Category.assoc,pullbackSpecIso_inv_fst,←Category.assoc,pullbackSpecIso_inv_snd]
  exact agreement b d (left b d) (right b d) (same_input b d)
end FifthQuarticCompatibility318
