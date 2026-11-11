module
public import PELOriginalThetaGaugeMatrix318
public import PELOriginalAutomorphyQuotientTopology318
public section
noncomputable section
namespace PELOriginalGaugedTheta318
open QuaternionicRealPeriod318 PELOriginalThetaGaugeMatrix318
open PELOriginalThetaHermitianGauge318 PELOriginalSiegelNormalization318
open PELOriginalSymplecticCoordinates318 PELOriginalThetaConvergence318
open PELOriginalPolarizationAutomorphy318 PELPeriodRiemannForm318
variable (τ:ℂ) (hτ:0<τ.im)

@[expose] def continuousBilinear:ComplexVectors→L[ℂ]ComplexVectors→L[ℂ]ℂ:=
  (show ComplexVectors→ₗ[ℂ]ComplexVectors→L[ℂ]ℂ from
    { toFun:=fun z=>(bilinearMap τ z).toContinuousLinearMap
      map_add':=by intro z w;ext v;exact congrArg (fun f:ComplexVectors→ₗ[ℂ]ℂ=>f v) ((bilinearMap τ).map_add z w)
      map_smul':=by intro a z;ext v;exact congrArg (fun f:ComplexVectors→ₗ[ℂ]ℂ=>f v) ((bilinearMap τ).map_smul a z) }).toContinuousLinearMap
lemma gauge_smooth:ContDiff ℂ ⊤ (gauge (bilinearMap τ)):=by
  have hb:ContDiff ℂ ⊤ (fun z:ComplexVectors=>bilinearMap τ z z):=
    ((continuousBilinear τ).analyticOnNhd_bilinear Set.univ).contDiff.comp
      (contDiff_id.prodMk contDiff_id)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hb)
lemma gauged_differentiable:Differentiable ℂ (gaugedTheta τ (bilinearMap τ)):=
  ((gauge_smooth τ).differentiable (by simp)).mul (PELOriginalThetaHolomorphy318.holomorphic τ hτ)

/-- Entire scalar representative on the ACTUAL original universal
period carrier. It is obtained from the genuine convergent theta series
and explicit gauge, not an assumed section of an unrelated theta line. -/
@[expose] def value (z:ComplexVectors):ℂ:=
  gaugedTheta τ (bilinearMap τ) (normalization τ hτ z)
lemma holomorphic:Differentiable ℂ (value τ hτ):=
  (gauged_differentiable τ hτ).comp (normalization τ hτ).toContinuousLinearEquiv.differentiable

@[expose] def label (l:L τ hτ):Pair:=coordinates ((latticeEquiv τ hτ).symm l)
lemma label_exact (l:L τ hτ):latticeEquiv τ hτ (fromPair (label τ hτ l))=l:=by
  rw [label,show fromPair (coordinates ((latticeEquiv τ hτ).symm l))=
    (latticeEquiv τ hτ).symm l from from_to _,LinearEquiv.apply_symm_apply]
lemma period_exact (l:L τ hτ):normalization τ hτ l.val=standardPeriod τ (label τ hτ l):=by
  have h:=congrArg (fun k:L τ hτ=>normalization τ hτ k.val) (label_exact τ hτ l)
  rw [←h]
  exact original_period τ hτ (label τ hτ l)

/-- Exact automorphy on every original lattice element with the SAME
Appell-Humbert factor. No finite-index sublattice or character twist. -/
theorem original_automorphy (l:L τ hτ) (z:ComplexVectors):
    value τ hτ (z+l.val)=factor τ hτ l z*value τ hτ z:=by
  simp only [value,map_add,period_exact]
  rw [original_factor τ hτ (bilinearMap τ) (symmetric τ) (period_difference τ hτ)]
  simp only [normalizedFactor,LinearEquiv.symm_apply_apply,label_exact]
end PELOriginalGaugedTheta318
