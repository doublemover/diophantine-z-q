module
public import FourRootCanonicalInfinitySection318
public section
noncomputable section
namespace FourRootCanonicalInfinityEquationOrder318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootIntrinsicOverlapDifferential318 FourRootCanonicalInfinitySection318
open FourRootActualSchemeDvr318 FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance infinityDedekind:IsDedekindDomain (FourRootInfinityCoordinateRing318.Ring b):=
  FourRootActualDedekind318.infinity_dedekind b hb
local instance pointPrime(p:InfinityPoints b):(infinityPrime b p).IsPrime:=infinity_prime b p
local instance overlapDomain:IsDomain (FourRootCoordinateOverlap318.InfinityOverlap b):=
  FourRootInfinityDomain318.infinity_overlap_domain b hb
local instance overlapNonempty:Nonempty (domain b):=by
  obtain ⟨p⟩:Nonempty (overlapScheme b):=inferInstance
  exact ⟨⟨embedding b p,⟨p,trivial,rfl⟩⟩⟩
local instance infinityNonempty:Nonempty (infinityChart b ''ᵁ ⊤):=by
  obtain ⟨x⟩:Nonempty (domain b):=inferInstance
  exact ⟨⟨x.val,domain_le_infinity b x.property⟩⟩
@[expose] def uSection:Γ(scheme b,infinityChart b ''ᵁ ⊤):=
  ActualOpenAffineCoefficientGerm318.chartSection (infinityChart b)
    (FourRootInfinityCoordinateRing318.coordinate b none)
@[expose] def originalU:(scheme b).functionField:=
  (scheme b).germToFunctionField (infinityChart b ''ᵁ ⊤) (uSection b)
lemma u_restriction:
    (scheme b).presheaf.map (homOfLE (domain_le_infinity b)).op (uSection b)=
      scalar b (FourRootCoordinateOverlap318.u b):=
  OpenChartSections318.affine_restriction (CommRingCat.ofHom
    (algebraMap (FourRootInfinityCoordinateRing318.Ring b)
      (FourRootCoordinateOverlap318.InfinityOverlap b))) (infinityChart b)
    (FourRootInfinityCoordinateRing318.coordinate b none)
lemma u_on_overlap:originalU b hb=(scheme b).germToFunctionField (domain b)
    (scalar b (FourRootCoordinateOverlap318.u b)):=by
  rw [←u_restriction,AffineDominantNormRestriction318.germ_restrict]
  rfl
lemma originalU_inverse:inverseU b hb=(originalU b hb)⁻¹:=by
  have hu:originalU b hb*inverseU b hb=1:=by
    rw [u_on_overlap,inverseU,←map_mul,←map_mul,FourRootCoordinateOverlap318.u_ui,map_one,map_one]
  exact eq_inv_of_mul_eq_one_right hu
lemma center_mem(p:InfinityPoints b)(hp:p.val.1=0):infinityImage b p∈U b hb:=by
  have hden:=FourRootActualKaehlerNeighborhoods318.infinity_neighborhood b hb p hp
  have hr:infinitySpectrum b p∈Set.range (PrimeSpectrum.comap
      (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))):=by
    rw [PrimeSpectrum.localization_away_comap_range (InfinityRing b hb)
      (FourRootActualInfinityKaehler318.denominator b hb)]
    exact hden
  obtain ⟨q,hq⟩:=hr
  exact ⟨q,congrArg (infinityChart b) hq⟩
/-- The original generic u is pinned under the actual open-immersion
stalk fraction comparison at every infinity center, with no change of
field coordinate or valuation normalization. -/
lemma originalU_compared(p:InfinityPoints b)(hp:p.val.1=0):
    letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
    ActualOpenAffineStalkFraction318.comparison (infinityChart b) (infinitySpectrum b p)
      (originalU b hb)=FourRootActualMeromorphicInfinity318.u b:=by
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  exact ActualOpenAffineCoefficientGerm318.fraction_coefficient (infinityChart b)
    (infinitySpectrum b p) (FourRootInfinityCoordinateRing318.coordinate b none)
/-- The ACTUAL intrinsic rational equation has order minus three at
EACH of the eight genuine whole-Scheme infinity DVRs. This is now a
comparison with the new canonical-line equation, not merely with a
separately computed coefficient in an abstract isomorphic field. -/
theorem infinity_equation_value(p:InfinityPoints b)(hp:p.val.1=0):
    letI:=infinityActualDvr b hb p hp
    ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk (infinityImage b p))
      (scheme b).functionField (FourRootCanonicalRationalEquations318.localEquation b hb none)=(-3:ℤ):=by
  letI:=FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
  letI:=infinityActualDvr b hb p hp
  let ν:=ActualDvrMeromorphicOrder318.value ((scheme b).presheaf.stalk (infinityImage b p))
    (scheme b).functionField
  have hu:ν (originalU b hb)=1:=by
    rw [←ActualOpenAffineStalkFraction318.value_preserved (infinityChart b) (infinitySpectrum b p),
      originalU_compared b hb p hp]
    exact ActualPrimeMeromorphicOrder318.value_source_uniformizer
      (FourRootInfinityCoordinateRing318.Ring b) (infinityPrime b p)
      (FourRootInfinityCoordinateRing318.coordinate b none)
      (FourRootActualInfinityTraceTransport318.actual_infinity_uniformizer b hb p hp)
  have h2:ν (2:(scheme b).functionField)=0:=by
    rw [←ActualOpenAffineStalkFraction318.value_preserved (infinityChart b) (infinitySpectrum b p),map_ofNat]
    exact ActualPrimeMeromorphicOrder318.value_two
      (FourRootInfinityCoordinateRing318.Ring b) (infinityPrime b p)
  have hg:ν ((scheme b).germToFunctionField (U b hb) (unitCoefficient b hb))=0:=by
    have hh: IsUnit ((scheme b).presheaf.germ (U b hb) (infinityImage b p)
        (center_mem b hb p hp) (unitCoefficient b hb)):=
      (unitCoefficient_unit b hb).map ((scheme b).presheaf.germ (U b hb)
        (infinityImage b p) (center_mem b hb p hp)).hom
    have he:=ActualDvrMeromorphicOrder318.value_unit
      ((scheme b).presheaf.stalk (infinityImage b p)) (scheme b).functionField _ hh
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at he
    exact he
  change ν _=(-3:ℤ)
  rw [infinity_equation,originalU_inverse,ν.map_mul,ν.map_mul,ν.map_neg,ν.map_pow,ν.map_inv,hu,h2,hg]
  norm_num
end FourRootCanonicalInfinityEquationOrder318
