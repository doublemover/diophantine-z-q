module
public import InvariantNormalizedFrames318
public import DifferentialFunctor318
public section
noncomputable section
namespace InvariantCoefficient318
open KaehlerDifferential
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

theorem inverse_coefficient (e : KaehlerDifferential R S ≃ₗ[S] S)
    (ω : KaehlerDifferential R S) (hω : e ω=1) (c : S) : e.symm c=c • ω := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply,map_smul,hω,smul_eq_mul,mul_one]

theorem transport_coefficient (f : S →ₐ[R] T)
    (e : KaehlerDifferential R S ≃ₗ[S] S) (ω : KaehlerDifferential R S)
    (hω : e ω=1) (c : S) :
    AlgHomDifferential318.map f (e.symm c)=f c • AlgHomDifferential318.map f ω := by
  rw [inverse_coefficient e ω hω,AlgHomDifferential318.map_smul]

/-- Generator agreement gives exact agreement for every pair of corresponding
coefficients, rather than only equality of distinguished forms. -/
theorem compatible_coefficients (f : S →ₐ[R] U) (g : T →ₐ[R] U)
    (eS : KaehlerDifferential R S ≃ₗ[S] S) (eT : KaehlerDifferential R T ≃ₗ[T] T)
    (ωS : KaehlerDifferential R S) (ωT : KaehlerDifferential R T)
    (hS : eS ωS=1) (hT : eT ωT=1)
    (hω : AlgHomDifferential318.map f ωS=AlgHomDifferential318.map g ωT)
    (c : S) (d : T) (hcd : f c=g d) :
    AlgHomDifferential318.map f (eS.symm c)=AlgHomDifferential318.map g (eT.symm d) := by
  rw [transport_coefficient f eS ωS hS,transport_coefficient g eT ωT hT,hω,hcd]
end InvariantCoefficient318
