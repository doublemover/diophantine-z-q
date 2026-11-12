module
public import PELOriginalLevelPowerSections318
public section
noncomputable section
namespace PELOriginalLevelThetaNegation318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318
open PELOriginalThetaQuasiperiods318 PELOriginalSiegelMatrix318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalThetaGaugeMatrix318 PELOriginalThetaHermitianGauge318
open PELOriginalGaugedTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N]

lemma residue_neg (k : Index) : residue N (-k) = -residue N k := by
  apply Prod.ext <;> simp [residue]

/-- Negation changes the actual characteristic, rather than making every
level-three coordinate even as happens in the level-two Kummer map. -/
lemma theta_neg (r : Label N) (z : ComplexVectors) :
    levelTheta τ N r (-z) = levelTheta τ N (-r) z := by
  have he : ∀ k : Index, levelTerm τ N r k (-z) = levelTerm τ N (-r) (-k) z := by
    intro k
    simp only [levelTerm,PELOriginalScaledThetaHolomorphy318.selectedTerm,
      accepts,residue_neg,neg_inj]
    split_ifs
    · simp only [PELOriginalScaledThetaConvergence318.term]
      congr 1
      simp only [quadratic,linear,Pi.neg_apply,Prod.fst_neg,Prod.snd_neg,Int.cast_neg]
      ring
    · rfl
  change (∑' k : Index, levelTerm τ N r k (-z)) = _
  simp_rw [he]
  exact (Equiv.neg Index).tsum_eq (fun k : Index => levelTerm τ N (-r) k z)

/-- The exact original even gauge and linear normalization are retained. -/
lemma value_neg (r : Label N) (z : ComplexVectors) :
    value τ hτ N r (-z) = value τ hτ N (-r) z := by
  simp only [value,normalizedValue,map_neg,theta_neg,gauge,LinearMap.neg_apply,neg_neg]
end PELOriginalLevelThetaNegation318
