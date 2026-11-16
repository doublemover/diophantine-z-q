module
public import VaryingLocalFreeModuleProjective318
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public section
noncomputable section
namespace VaryingLocalFreeModuleDegree318
open VaryingLocalFreeQuotientEquiv318 VaryingLocalFreeModuleProjective318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : LocalIdeal R A ι S)
/-- Actual stalk rank of the LITERAL original quotient module. -/
@[expose] def degree : PrimeSpectrum S → ℕ := Module.rankAtStalk (quotient R A ι S I)
lemma locallyConstant : IsLocallyConstant (degree R A ι S I) :=
  Module.isLocallyConstant_rankAtStalk
lemma degree_component (n : ℕ) : IsClopen {x | degree R A ι S I x=n} :=
  (locallyConstant R A ι S I).isClopen_fiber n
lemma finite_values : (Set.range (degree R A ι S I)).Finite :=
  (locallyConstant R A ι S I).range_finite
lemma exists_bound : ∃ N : ℕ, ∀ x, degree R A ι S I x≤N := by
  classical
  let h := finite_values R A ι S I
  refine ⟨h.toFinset.sup id,fun x => ?_⟩
  exact Finset.le_sup (f:=id) (h.mem_toFinset.mpr ⟨x,rfl⟩)
/-- Local bases for the actual original quotient module, without a
choice of parameter word frame or a global freeness assumption. -/
lemma free_neighborhood (x : PrimeSpectrum S) :
    ∃ f : S, f∉x.asIdeal ∧ Module.Free (Localization.Away f)
      (LocalizedModule.Away f (quotient R A ι S I)) := by
  let M := quotient R A ι S I
  letI : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule x.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨f,hf,hfree,-⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨f,hf,hfree⟩
end VaryingLocalFreeModuleDegree318
