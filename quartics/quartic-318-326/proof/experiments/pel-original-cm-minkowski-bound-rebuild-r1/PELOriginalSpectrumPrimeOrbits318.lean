module
public import PELOriginalSectionPrimeOrbits318
public section
noncomputable section
namespace PELOriginalSpectrumPrimeOrbits318
open AlgebraicGeometry CategoryTheory
open scoped Pointwise
open PELOriginalWholeCharacterMorphisms318 PELOriginalKernelStableOpens318
open PELOriginalSectionKernelAction318

/-- Prime-ideal transitivity in the CORRECT contravariant Spec direction.
The inverse kernel element converts pointwise ideal image to comap. -/
theorem spectrum_fiber_orbit (i:Fin 4) (U:(Curve i).Opens)
    (P Q:Spec (CommRingCat.of (SourceSections i U)))
    (hPQ:Spec.map ((morphism i).app U) P=Spec.map ((morphism i).app U) Q):
    ∃a:Kernel i,Spec.map (CommRingCat.ofHom (sectionAction i U a.val a.property)) P=Q:=by
  letI:=sectionActionInstance i U
  letI:=sectionAlgebra i U
  letI:=P.isPrime
  letI:=Q.isPrime
  obtain ⟨a,ha⟩:=PELOriginalSectionPrimeOrbits318.original_prime_transitive i U
    P.asIdeal Q.asIdeal (congrArg PrimeSpectrum.asIdeal hPQ)
  refine ⟨a⁻¹,?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (sectionAction i U (a⁻¹).val (a⁻¹).property) P.asIdeal=Q.asIdeal
  rw [ha,Ideal.pointwise_smul_eq_comap]
end PELOriginalSpectrumPrimeOrbits318
