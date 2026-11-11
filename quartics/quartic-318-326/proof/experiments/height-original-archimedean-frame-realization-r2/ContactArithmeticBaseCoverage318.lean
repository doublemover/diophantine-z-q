module
public import ContactArithmeticTwists318
public section
noncomputable section
namespace ContactArithmeticBaseCoverage318
open AlgebraicGeometry CategoryTheory
open ContactArithmeticDenominator318 ContactArithmeticBase318
set_option maxHeartbeats 700000
variable (c : Fin 4 → ℚˣ)

@[expose] def baseMap : Spec (CommRingCat.of (Base c)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (Base c)))
instance : IsOpenImmersion (baseMap c) := by
  unfold baseMap Base
  infer_instance

/-- The arithmetic base covers exactly the full principal open determined
by its displayed integer, on all prime ideals of Z. -/
theorem range_exact : (baseMap c).opensRange=PrimeSpectrum.basicOpen (denominator c) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Base c) (denominator c)

/-- No arithmetic prime outside the explicit denominator is silently lost. -/
theorem prime_covered_iff (p : PrimeSpectrum ℤ) :
    (∃ q : PrimeSpectrum (Base c), baseMap c q=p) ↔ denominator c∉p.asIdeal := by
  change p∈(baseMap c).opensRange ↔ _
  rw [range_exact]
  rfl
end ContactArithmeticBaseCoverage318
