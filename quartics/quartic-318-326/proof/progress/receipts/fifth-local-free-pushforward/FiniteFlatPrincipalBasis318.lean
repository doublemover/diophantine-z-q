module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Localization.Free
public section
noncomputable section
namespace FiniteFlatPrincipalBasis318
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (R:Type u) [CommRing R] (M:Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]
/-- A true principal neighborhood basis of the finite-flat module. Its
length is the actual stalk rank, and the open contains the specified prime.
No global basis or trivial determinant class is assumed. -/
lemma exists_basis (p:PrimeSpectrum R):
    ∃r:R,r∉p.asIdeal ∧ Nonempty
      (Module.Basis (Fin (Module.rankAtStalk M p)) (Localization.Away r) (LocalizedModule.Away r M)):=by
  let Rₚ:=Localization.AtPrime p.asIdeal
  let Mₚ:=LocalizedModule.AtPrime p.asIdeal M
  let f:M→ₗ[R]Mₚ:=LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  letI:Module.Free Rₚ Mₚ:=Module.free_of_flat_of_isLocalRing
  let b:Module.Basis (Fin (Module.rankAtStalk M p)) Rₚ Mₚ:=Module.finBasis Rₚ Mₚ
  obtain ⟨r,hr,b',_⟩:=Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl f Rₚ b
  exact ⟨r,hr,⟨b'⟩⟩
lemma exists_basis_of_rank (p:PrimeSpectrum R) (n:ℕ) (h:Module.rankAtStalk M p=n):
    ∃r:R,r∉p.asIdeal ∧ Nonempty
      (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r M)):=by
  simpa only [h] using exists_basis R M p
end FiniteFlatPrincipalBasis318
