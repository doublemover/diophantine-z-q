module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
namespace ProperRegularPrincipalOpen318

/-- An affine principal-open form of the proper shrinking step. This
uses closedness of the *map of total spaces* and openness of the good
locus on the total space. It does not replace either by fibre regularity. -/
theorem exists_principal_good {A Y : Type*} [CommRing A] [TopologicalSpace Y]
    (f : Y → PrimeSpectrum A) (hf : IsClosedMap f)
    (G : Set Y) (hG : IsOpen G) (p : PrimeSpectrum A)
    (hp : ∀ y, f y = p → y ∈ G) :
    ∃ s : A, s ∉ p.asIdeal ∧ ∀ y, f y ∈ PrimeSpectrum.basicOpen s → y ∈ G := by
  classical
  obtain ⟨Z, hZ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp (hf _ hG.isClosed_compl)
  have hnot : p ∉ f '' Gᶜ := by
    rintro ⟨y, hy, hy'⟩
    exact hy (hp y hy')
  rw [hZ, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hnot
  obtain ⟨s, hs, hsp⟩ := hnot
  refine ⟨s, hsp, ?_⟩
  intro y hy
  by_contra hbad
  have hmem : f y ∈ f '' Gᶜ := ⟨y, hbad, rfl⟩
  rw [hZ, PrimeSpectrum.mem_zeroLocus] at hmem
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hy (hmem hs)

end ProperRegularPrincipalOpen318
