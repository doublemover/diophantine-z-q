module
public import FourRootDualityUnitScale318
public import FiniteDualTransport318
public section
noncomputable section
namespace FourRootDualOverlapTensor318
open FourRootIntegralDuality318 FourRootDualityUnitScale318 FiniteDualModuleAction318
open FiniteDualTransport318
set_option maxHeartbeats 2000000
variable {R : Type*} [CommRing R] (a b : Fin 4 → R) (s : Rˣ)
  (h : ∀ i,b i=a i*(s:R)^2)
local notation "A" => FourRootOrder318.Order b
local notation "B" => FourRootOrder318.Order a
local notation "E" => FourRootUnitScale318.four a b s h

/-- Actual whole-dual transport, with its correct order-module action,
identifies the finite-chart generator with s^-4 times the infinity one. -/
theorem transported_generator :
    transport E (FiniteDualModuleAction318.frame R A (FourRootIntegralDuality318.frame b) 1)=
      algebraMap R B ((↑s⁻¹:R)^4) • FiniteDualModuleAction318.frame R B (FourRootIntegralDuality318.frame a) 1 := by
  apply LinearMap.ext
  intro x
  change coefficient b (1*E.symm x)=
    coefficient a (1*(algebraMap R B ((↑s⁻¹:R)^4)*x))
  rw [one_mul,one_mul,←Algebra.smul_def,map_smul,smul_eq_mul,
    coefficient_inverse a b s h,AlgEquiv.apply_symm_apply]

/-- Tensor transport is an actual balanced semilinear map, and the
square transition is s^-8 on the true finite-dual tensor square. -/
theorem tensor_generator (x : A) :
    squareTransport E (squareFrame (FourRootIntegralDuality318.frame b) x)=
      squareFrame (FourRootIntegralDuality318.frame a) (E x*algebraMap R B ((↑s⁻¹:R)^8)) := by
  rw [squareTransport_frame E (FourRootIntegralDuality318.frame b) (FourRootIntegralDuality318.frame a) _ (transported_generator a b s h)]
  congr 1
  rw [←map_pow]
  congr 2
  ring
end FourRootDualOverlapTensor318
