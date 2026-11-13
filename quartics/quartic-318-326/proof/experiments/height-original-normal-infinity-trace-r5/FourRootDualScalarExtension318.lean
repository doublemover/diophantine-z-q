module
public import FourRootDualityBaseChange318
public import FiniteDualTransport318
public section
noncomputable section
namespace FourRootDualScalarExtension318
open FiniteDualModuleAction318 FiniteDualTransport318 FourRootSignBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 2000000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : Fin 4 → R)
local notation "A" => FourRootOrder318.Order a
local notation "B" => FourRootOrder318.Order (fun i => algebraMap R S (a i))
local notation "F" => FourRootIntegralDuality318.frame a
local notation "G" => FourRootIntegralDuality318.frame (fun i => algebraMap R S (a i))

/-- Actual scalar-extension map on the entire dual, constructed from the
proved integral frames and literal marked-order coefficient map. The
following evaluation theorem identifies its meaning on all old elements. -/
@[expose] def map : Dual R A →ₛₗ[(coefficientMap a S).toRingHom] Dual S B where
  toFun f := frame S B G (coefficientMap a S ((frame R A F).symm f))
  map_add' f g := by simp only [map_add]
  map_smul' x f := by
    rw [map_smul]
    change frame S B G (coefficientMap a S (x*((frame R A F).symm f)))=_
    rw [map_mul]
    exact (frame S B G).map_smul (coefficientMap a S x) _

theorem map_frame (x : A) : map a (frame R A F x)=frame S B G (coefficientMap a S x) := by
  change frame S B G (coefficientMap a S ((frame R A F).symm (frame R A F x)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem map_evaluate (f : Dual R A) (x : A) :
    evaluate S B (map a f) (coefficientMap a S x)=algebraMap R S (evaluate R A f x) := by
  let y := (frame R A F).symm f
  change FourRootIntegralDuality318.coefficient _ (coefficientMap a S y*coefficientMap a S x)=_
  rw [←map_mul,FourRootDualityBaseChange318.coefficientMap_coefficient]
  congr 1
  have hy := congrArg (fun g : Dual R A => evaluate R A g x) ((frame R A F).apply_symm_apply f)
  exact hy

/-- Balanced scalar-extension map on the genuine full dual tensor square. -/
@[expose] def squareMap : Square (R:=R) (A:=A) →ₛₗ[(coefficientMap a S).toRingHom]
    Square (R:=S) (A:=B) := TensorProduct.map (map a) (map a)

theorem squareMap_frame (x : A) : squareMap a (squareFrame F x)=
    squareFrame G (coefficientMap a S x) := by
  rw [squareFrame_scalar,map_smul,squareFrame_one]
  change coefficientMap a S x • (map a (frame R A F 1) ⊗ₜ[B] map a (frame R A F 1))=_
  rw [map_frame,map_one,←squareFrame_one,squareFrame_scalar]
end FourRootDualScalarExtension318
