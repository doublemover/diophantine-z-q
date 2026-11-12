module
public import FourRootCanonicalInfinityEquationOrder318
public section
noncomputable section
namespace FourRootCanonicalFiniteEquationOrder318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootCanonicalFiniteSectionPropagation318 FourRootActualCanonicalLine318
open FourRootCanonicalRationalEquations318 FourRootActualSchemeDvr318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance affineDedekind:IsDedekindDomain (FourRootAffineCoordinateRing318.Ring b):=
  FourRootActualDedekind318.finite_dedekind b hb
local instance pointPrime(p:FinitePoints b):(finitePrime b p).IsPrime:=finite_prime b p
local instance actualFiniteDvr(p:FinitePoints b):
    IsDiscreteValuationRing ((scheme b).presheaf.stalk (finiteImage b p)):=
  finiteActualDvr b hb p
local instance finiteNonempty:Nonempty (finiteOpen b):=by
  obtain ⟨p⟩:Nonempty (finiteScheme b):=inferInstance
  exact ⟨⟨finiteChart b p,⟨p,trivial,rfl⟩⟩⟩
@[expose] def coefficientSection(i:Fin 4):Γ(scheme b,finiteOpen b):=
  ActualOpenAffineCoefficientGerm318.chartSection (finiteChart b)
    (2*FourRootAffineCoordinateRing318.coordinate b (some i))
lemma coefficient_on_chart(i:Fin 4):
    (scheme b).presheaf.map (homOfLE (chart_le b i)).op (coefficientSection b i)=
      ((finiteEmbedding b i).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
          (2*FourRootActualBranchKaehler318.sourceCoordinate b i)):=by
  have h:=OpenChartSections318.affine_restriction (CommRingCat.ofHom
    (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))) (finiteChart b)
    (2*FourRootAffineCoordinateRing318.coordinate b (some i))
  simpa only [map_mul,map_ofNat,FourRootActualBranchKaehler318.source_coordinate_original] using h
lemma point_mem(p:FinitePoints b)(i:Fin 4)
    (hi:FourRootActualFiniteBranchChart318.denominator b i∉finitePrime b p):
    finiteImage b p∈opens b hb (some i):=by
  have hr:finiteSpectrum b p∈Set.range (PrimeSpectrum.comap
      (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))):=by
    rw [PrimeSpectrum.localization_away_comap_range (FiniteRing b i)
      (FourRootActualFiniteBranchChart318.denominator b i)]
    exact hi
  obtain ⟨q,hq⟩:=hr
  exact ⟨q,congrArg (finiteChart b) hq⟩
/-- In every actual finite canonical chart, the new intrinsic rational
equation has the valuation of the SAME original literal coefficient 2z_i.
The comparison uses actual regular unit frame coefficients and actual
whole-Scheme germs, not an assumed equality of transported frames. -/
lemma equation_value(p:FinitePoints b)(i:Fin 4)
    (hi:FourRootActualFiniteBranchChart318.denominator b i∉finitePrime b p):
    ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk (finiteImage b p))
      (scheme b).functionField (localEquation b hb (some i))=
    ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk (finiteImage b p))
      (scheme b).functionField ((scheme b).germToFunctionField (finiteOpen b) (coefficientSection b i)):=by
  let V:=opens b hb (some i)
  let e:=OpenLineFrameCoordinates318.frame (omega b) V (frame b hb (some i)) V le_rfl
  have hV:V≤finiteEmbedding b i ''ᵁ ⊤:=(finiteEmbedding b i).image_top_eq_opensRange.symm.le
  have h:=FourRootActualIntrinsicFrameComparison318.finite_dt_value b V e (finiteImage b p)
    (point_mem b hb p i hi) i hV
  have he:=equation_on_finite b hb (some i) V le_rfl (ambient_le b hb i)
  rw [←ActualRationalSectionPropagation318.restrict_chain (omega b) hV (chart_le b i),
    wholeDt_on_chart] at he
  rw [he] at h
  rw [←coefficient_on_chart] at h
  have hc:(scheme b).presheaf.map (homOfLE hV).op
      ((scheme b).presheaf.map (homOfLE (chart_le b i)).op (coefficientSection b i))=
      (scheme b).presheaf.map (homOfLE (ambient_le b hb i)).op (coefficientSection b i):=
    (Functor.map_comp_apply (scheme b).presheaf (homOfLE (chart_le b i)).op
      (homOfLE hV).op (coefficientSection b i)).symm
  rw [hc,AffineDominantNormRestriction318.germ_restrict] at h
  exact h
/-- At the genuine original chosen finite frame, actual intrinsic local
orders equal the earlier independently computed original dt coefficients.
The field comparison is fixed on EVERY original affine coefficient. -/
theorem same_finite_value(p:FinitePoints b):
    ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk (finiteImage b p))
      (scheme b).functionField (localEquation b hb (some (FourRootActualFiniteDifferentialOrders318.chartIndex b p)))=
      FourRootActualFiniteDifferentialOrders318.value b hb p:=by
  letI:IsDiscreteValuationRing (Localization.AtPrime (finitePrime b p)):=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (FourRootAffineCoordinateRing318.Ring b)
      (FourRootLocalDifferentMultiplicity318.all_finite_prime_nonzero b hb p)
      (Localization.AtPrime (finitePrime b p))
  rw [equation_value b hb p _ (FourRootActualFiniteDifferentialOrders318.chartIndex_neighborhood b hb p),
    ←ActualOpenAffineStalkFraction318.value_preserved (finiteChart b) (finiteSpectrum b p),
    ActualOpenAffineCoefficientGerm318.fraction_coefficient]
  rw [FourRootActualFiniteDifferentialOrders318.value,
    FourRootActualFiniteDifferentialOrders318.coefficient,
    FourRootActualMeromorphicFinite318.dt_coefficient]
  congr 1
  simp only [map_mul,map_ofNat,FourRootActualMeromorphicFinite318.z]
end FourRootCanonicalFiniteEquationOrder318
