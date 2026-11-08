module
public import FiniteLocalRankOne318
public section
noncomputable section
namespace RankOneTargetNeighborhood318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable (A:Type u) (B:Type v) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]
variable (L:Type w) [AddCommGroup L] [Module B L]
  [Module.FinitePresentation B L] [Module.Flat B L]
  (rk:∀q:PrimeSpectrum B,Module.rankAtStalk L q=1)
include rk in
/-- A genuine rank-one trivialization on an entire inverse-image principal
open of the base. The finitely presented flat rank-one source module is
retained exactly, without invoking a missing line-sheaf comparison. -/
lemma exists_basis (p:PrimeSpectrum A):
    ∃a:A,a∉p.asIdeal ∧ Nonempty
      (Module.Basis (Fin 1) (Localization.Away (algebraMap A B a))
        (LocalizedModule.Away (algebraMap A B a) L)):=by
  let S:Submonoid B:=Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl
  let Bₚ:=Localization S
  let Lₚ:=LocalizedModule S L
  have hr:∀q:PrimeSpectrum Bₚ,Module.rankAtStalk Lₚ q=1:=by
    intro q
    have h:=Module.rankAtStalk_isBaseChange
      (IsLocalizedModule.isBaseChange S Bₚ (LocalizedModule.mkLinearMap S L)) q
    exact h.trans (rk _)
  obtain ⟨bs⟩:=FiniteLocalRankOne318.exists_basis (Localization.AtPrime p.asIdeal) Bₚ Lₚ hr
  obtain ⟨b,hb,bs',_⟩:=Module.FinitePresentation.exists_basis_localizedModule_powers
    S (LocalizedModule.mkLinearMap S L) Bₚ bs
  obtain ⟨a,ha,hab⟩:=hb
  subst b
  exact ⟨a,ha,⟨bs'⟩⟩
end RankOneTargetNeighborhood318
