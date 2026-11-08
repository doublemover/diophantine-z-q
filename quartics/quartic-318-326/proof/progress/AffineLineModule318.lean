module
public import OpenLineSectionBasis318
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public section
noncomputable section
namespace AffineLineModule318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 650000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R:CommRingCat.{u}) (M:(Spec R).Modules) [M.IsQuasicoherent]
abbrev globals:=moduleSpecΓFunctor.obj M
@[expose] def basic (r:R):(Spec R).Opens:=PrimeSpectrum.basicOpen r
@[expose] def restriction (r:R):globals R M→ₗ[R]Γ(M,PrimeSpectrum.basicOpen r):=
  ((modulesSpecToSheaf.obj M).obj.map (show op (⊤:(Spec R).Opens) ⟶ op (basic R r) from (homOfLE le_top).op)).hom
instance restriction_localized (r:R):IsLocalizedModule.Away r (restriction R M r):=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
@[expose] def frameSet:Set R:={r|Nonempty
  (SheafOfModules.unit ((basic R r):Scheme).ringCatSheaf≅
    M.restrict (basic R r).ι)}
variable (cover:∀p:PrimeSpectrum R,∃r:R,r∉p.asIdeal ∧ r∈frameSet R M)
include cover in
lemma span_top:Ideal.span (frameSet R M)=⊤:=by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply top_unique
  intro p _
  obtain ⟨r,hr,hf⟩:=cover p
  exact Opens.mem_iSup.mpr ⟨r,Opens.mem_iSup.mpr ⟨hf,hr⟩⟩
@[expose] def localBasis (r:frameSet R M):
    Module.Basis (Fin 1) Γ(Spec R,PrimeSpectrum.basicOpen r.val)
      Γ(M,PrimeSpectrum.basicOpen r.val):=
  OpenLineSectionBasis318.basis M (PrimeSpectrum.basicOpen r.val) r.property.some
local instance localFree (r:frameSet R M):
    Module.Free Γ(Spec R,PrimeSpectrum.basicOpen r.val) Γ(M,PrimeSpectrum.basicOpen r.val):=
  Module.Free.of_basis (localBasis R M r)
local instance localFinite (r:frameSet R M):
    Module.Finite Γ(Spec R,PrimeSpectrum.basicOpen r.val) Γ(M,PrimeSpectrum.basicOpen r.val):=
  Module.Finite.of_basis (localBasis R M r)
include cover in
/-- Finite presentation of the original affine global section module, from
actual line frames on a principal cover and literal QC restriction maps. -/
lemma finitePresentation:Module.FinitePresentation R (globals R M):=
  Module.FinitePresentation.of_localizationSpan' (frameSet R M) (span_top R M cover)
    (Rₚ:=fun r=>Γ(Spec R,PrimeSpectrum.basicOpen r.val))
    (fun r=>restriction R M r.val)
      (fun r=>Module.finitePresentation_of_projective _ _)
include cover in
/-- Flatness of the same original module, using exact localizations. -/
lemma flat:Module.Flat R (globals R M):=by
  apply Module.flat_of_isLocalized_span R (globals R M) (frameSet R M) (span_top R M cover)
    (fun r=>Γ(M,PrimeSpectrum.basicOpen r.val)) (fun r=>restriction R M r.val)
  intro r
  letI:Module.Flat R Γ(Spec R,PrimeSpectrum.basicOpen r.val):=
    IsLocalization.flat _ (Submonoid.powers r.val)
  exact Module.Flat.trans R Γ(Spec R,PrimeSpectrum.basicOpen r.val) Γ(M,PrimeSpectrum.basicOpen r.val)
include cover in
/-- Every actual prime has module stalk rank one; this is not just a
generic-fiber rank or a claim on a chosen component. -/
lemma rank_one (p:PrimeSpectrum R):Module.rankAtStalk (globals R M) p=1:=by
  letI:=finitePresentation R M cover
  letI:=flat R M cover
  obtain ⟨r,hr,hf⟩:=cover p
  let t:frameSet R M:=⟨r,hf⟩
  have hp:p∈Set.range (PrimeSpectrum.comap
      (algebraMap R Γ(Spec R,PrimeSpectrum.basicOpen r))):=by
    rw [PrimeSpectrum.localization_away_comap_range _ r]
    exact hr
  obtain ⟨q,hq⟩:=hp
  have h:=Module.rankAtStalk_isBaseChange
    (IsLocalizedModule.isBaseChange (Submonoid.powers r)
      Γ(Spec R,PrimeSpectrum.basicOpen r) (restriction R M r)) q
  rw [hq] at h
  letI:Module.Free Γ(Spec R,PrimeSpectrum.basicOpen r) Γ(M,PrimeSpectrum.basicOpen r):=
    localFree R M t
  haveI:Nontrivial Γ(Spec R,PrimeSpectrum.basicOpen r):=q.nontrivial
  rw [←h,Module.rankAtStalk_eq_finrank_of_free]
  simpa using Module.finrank_eq_card_basis (localBasis R M t)
end AffineLineModule318
