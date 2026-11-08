module
public import FiniteLocalInvertible318
public section
noncomputable section
namespace InvertibleTargetNeighborhood318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable (A:Type u) (B:Type v) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]
variable (L:Type w) [AddCommGroup L] [Module B L] [Module.Invertible B L]
/-- A rank-one trivialization on an entire inverse-image principal open of
the base, not just on a chosen source neighborhood. This is an algebraic
invertible-module theorem; no Scheme line-bundle comparison is assumed. -/
lemma exists_basis (p:PrimeSpectrum A):
    ∃a:A,a∉p.asIdeal ∧ Nonempty
      (Module.Basis Unit (Localization.Away (algebraMap A B a))
        (LocalizedModule.Away (algebraMap A B a) L)):=by
  let S:Submonoid B:=Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl
  let Bₚ:=Localization S
  let Lₚ:=LocalizedModule S L
  obtain ⟨e⟩:=FiniteLocalInvertible318.exists_equiv (Localization.AtPrime p.asIdeal) Bₚ Lₚ
  let bs:Module.Basis Unit Bₚ Lₚ:=(Module.Basis.singleton Unit Bₚ).map e.symm
  obtain ⟨b,hb,bs',_⟩:=Module.FinitePresentation.exists_basis_localizedModule_powers
    S (LocalizedModule.mkLinearMap S L) Bₚ bs
  obtain ⟨a,ha,hab⟩:=hb
  subst b
  exact ⟨a,ha,⟨bs'⟩⟩
end InvertibleTargetNeighborhood318
