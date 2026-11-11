module
public import FourRootDerivativeContraction318
public import FourRootActualIntrinsicFrameComparison318
public section
noncomputable section
namespace FourRootDerivativeGeneratorUnits318
open AlgebraicGeometry CategoryTheory Polynomial
open FourRootProjectiveDifferential318
/-- The original polynomial generator dt is a genuine generator of the
actual base cotangent module on its ENTIRE affine chart. Its coefficient
in an arbitrary actual frame is a regular unit, not a fraction scalar. -/
theorem finite_base_unit(V:Base.Opens)(hV:V≤finiteBaseChart ''ᵁ ⊤)
    (e:Γ(Base,V)≃ₗ[Γ(Base,V)]Γ(baseOmega,V)):
    IsUnit (e.symm (baseOmega.presheaf.map (homOfLE hV).op finiteBaseGenerator)):=by
  apply ActualIntrinsicFrameUnitComparison318.original_generator_unit
    finiteBaseChart baseStructure finite_base_structure
    (KaehlerDifferential.polynomialEquiv ℂ)
    (KaehlerDifferential.D ℂ (Polynomial ℂ) X) _ V hV e
  rw [KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X]
/-- The translated projective infinity coordinate is the original
v=1/(t-b0), whose differential generator dv has the same genuine unit
property. This does not replace dv by the meromorphic dt. -/
theorem infinity_base_unit(b:Fin 4→ℂ)(V:Base.Opens)(hV:V≤infinityBaseChart b ''ᵁ ⊤)
    (e:Γ(Base,V)≃ₗ[Γ(Base,V)]Γ(baseOmega,V)):
    IsUnit (e.symm (baseOmega.presheaf.map (homOfLE hV).op (infinityBaseGenerator b))):=by
  apply ActualIntrinsicFrameUnitComparison318.original_generator_unit
    (infinityBaseChart b) baseStructure (infinity_base_structure b)
    (KaehlerDifferential.polynomialEquiv ℂ)
    (KaehlerDifferential.D ℂ (Polynomial ℂ) X) _ V hV e
  rw [KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X]
end FourRootDerivativeGeneratorUnits318
