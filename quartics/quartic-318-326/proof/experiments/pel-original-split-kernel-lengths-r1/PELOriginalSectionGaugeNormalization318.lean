module
public import PELOriginalPowerSectionDescent318
public import PELOriginalAutomorphicSpanning318
public section
noncomputable section
namespace PELOriginalSectionGaugeNormalization318
open QuaternionicRealPeriod318 PELOriginalPowerSectionDescent318
open PELOriginalThetaHermitianGauge318 PELOriginalThetaGaugeMatrix318
open PELOriginalSiegelNormalization318 PELOriginalGaugedTheta318
open PELOriginalThetaQuasiperiods318 PELOriginalThetaConvergence318
open PELOriginalAutomorphicFourierRecurrence318 PELOriginalSymplecticCoordinates318
variable (τ:ℂ)(hτ:0<τ.im)(N:ℕ)

/-- Remove the exact produced entire nonzero quadratic gauge, and only
then use the actual original complex-linear period normalization. -/
@[expose] def normalize(f:OriginalAutomorphic τ hτ N)(z:ComplexVectors):ℂ:=
  f.value ((normalization τ hτ).symm z)/gauge (bilinearMap τ) z^N
lemma entire(f:OriginalAutomorphic τ hτ N):Differentiable ℂ (normalize τ hτ N f):=
  (f.entire.comp (normalization τ hτ).symm.toContinuousLinearEquiv.differentiable).div
    (((gauge_smooth τ).differentiable (by simp)).pow N)
    (fun z=>pow_ne_zero N (gauge_nonzero _ z))
lemma full_period(f:OriginalAutomorphic τ hτ N)(p:Pair)(z:ComplexVectors):
    normalize τ hτ N f (z+standardPeriod τ p)=
      multiplier τ (p.2 0,p.2 1) z^N*normalize τ hτ N f z:=by
  have hf:=f.lattice_rule (latticeEquiv τ hτ (fromPair p)) ((normalization τ hτ).symm z)
  have hg:=congrArg (fun x:ℂ=>x^N)
    (exact_multiplier τ hτ (bilinearMap τ) (symmetric τ) (period_difference τ hτ) p z)
  simp only [mul_pow] at hg
  simp only [normalize,map_add,denormalized_period,hf]
  change normalizedFactor τ hτ p z^N*f.value ((normalization τ hτ).symm z)/
    gauge (bilinearMap τ) (z+standardPeriod τ p)^N=_
  apply (div_eq_iff (pow_ne_zero N (gauge_nonzero _ _))).mpr
  rw [div_eq_mul_inv]
  calc
    _=(normalizedFactor τ hτ p z^N*gauge (bilinearMap τ) z^N)*
      ((gauge (bilinearMap τ) z^N)⁻¹*f.value ((normalization τ hτ).symm z)):=by
        field_simp [pow_ne_zero N (gauge_nonzero _ z)]
    _=multiplier τ (p.2 0,p.2 1) z^N*
      (f.value ((normalization τ hτ).symm z)*(gauge (bilinearMap τ) z^N)⁻¹)*
      gauge (bilinearMap τ) (z+standardPeriod τ p)^N:=by rw [←hg];ring

/-- Every original section produces an element of the FULL normalized
automorphic space whose spanning theorem was proved independently. -/
theorem automorphic(f:OriginalAutomorphic τ hτ N):Automorphic τ N (normalize τ hτ N f) where
  entire:=entire τ hτ N f
  integer m z:=by
    let p:Pair:=(![m.1,m.2],0)
    have hp:standardPeriod τ p=integerVector m:=by
      ext i;fin_cases i <;> simp [p,standardPeriod,integerVector]
    simpa [hp,p,multiplier,quadratic,linear] using full_period τ hτ N f p z
  period b z:=by
    let p:Pair:=(0,![b.1,b.2])
    have hp:standardPeriod τ p=periodVector τ b:=by
      ext i;fin_cases i <;> simp [p,standardPeriod,periodVector]
    simpa only [hp,p,Matrix.cons_val_zero,Matrix.cons_val_one] using full_period τ hτ N f p z

lemma recover(f:OriginalAutomorphic τ hτ N)(z:ComplexVectors):
    gauge (bilinearMap τ) (normalization τ hτ z)^N*
      normalize τ hτ N f (normalization τ hτ z)=f.value z:=by
  simp only [normalize,LinearEquiv.symm_apply_apply]
  field_simp [pow_ne_zero N (gauge_nonzero (bilinearMap τ) (normalization τ hτ z))]
end PELOriginalSectionGaugeNormalization318
