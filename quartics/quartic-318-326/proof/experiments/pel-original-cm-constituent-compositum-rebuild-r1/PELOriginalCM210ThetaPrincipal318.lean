module
public import PELOriginalCM210PrimeIdealTransport318
public section
noncomputable section
namespace PELOriginalCM210ThetaPrincipal318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318 PELOriginalCM210NativePrimeResidue318
open PELOriginalCM210PrimeIdealTransport318
lemma theta_principal : kernel 210 (by norm_num)=Ideal.span ({thetaR}:Set R) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a,ha⟩ := (mem_kernel 210 (by norm_num) z).mp hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨z.im,-a⟩,?_⟩
    ext
    · simpa [thetaR,QuadraticAlgebra.omega,QuadraticAlgebra.re_mul] using ha
    · simp [thetaR,QuadraticAlgebra.omega,QuadraticAlgebra.im_mul]
  · apply Ideal.span_le.mpr
    intro z hz
    have hz' : z=thetaR := Set.mem_singleton_iff.mp hz
    subst z
    exact theta_mem _ _
lemma native_theta_principal : nativeIdeal 210 (by norm_num)=
    Ideal.span ({integerEquiv thetaR}:Set O) := by
  have h := congrArg (Ideal.map integerEquiv.toRingHom) theta_principal
  simpa only [map_kernel,Ideal.map_span,Set.image_singleton,RingEquiv.coe_toRingHom] using h
end PELOriginalCM210ThetaPrincipal318
