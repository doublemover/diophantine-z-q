module
public import FiniteFlatAffineProjective318
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace FiniteFlatRankBounds318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (p : Z ⟶ Spec R)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
/-- Degree of the WHOLE finite-flat family at a coefficient prime, not
length of a chosen original affine-chart restriction. -/
@[expose] def degree : PrimeSpectrum R → ℕ := Module.rankAtStalk (FiniteAffineAlgebra318.ring R p)
lemma locallyConstant : IsLocallyConstant (degree R p) :=
  Module.isLocallyConstant_rankAtStalk
lemma degree_component (n : ℕ) : IsClopen {x | degree R p x=n} :=
  (locallyConstant R p).isClopen_fiber n
lemma finite_values : (Set.range (degree R p)).Finite := (locallyConstant R p).range_finite
/-- A uniform bound over the entire original coefficient spectrum,
including all disconnected components and the empty spectrum case. -/
lemma exists_bound : ∃ N : ℕ, ∀ x : PrimeSpectrum R, degree R p x≤N := by
  classical
  let h := finite_values R p
  refine ⟨h.toFinset.sup id,fun x => ?_⟩
  exact Finset.le_sup (f := id) (h.mem_toFinset.mpr ⟨x,rfl⟩)
/-- Actual principal neighborhoods carrying free modules of functions of
the entire family. No global free basis is asserted or substituted. -/
lemma free_neighborhood (x : PrimeSpectrum R) :
    ∃ f : R, f∉x.asIdeal ∧ Module.Free (Localization.Away f)
      (LocalizedModule.Away f (FiniteAffineAlgebra318.ring R p)) := by
  let M := FiniteAffineAlgebra318.ring R p
  letI : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨f,hf,hfree,-⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨f,hf,hfree⟩
end FiniteFlatRankBounds318
