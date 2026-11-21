module
public import CTLiteralDualDisplacement318
public import CTActualQuadraticRootSigns318
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTLiteralDualActualPhase318

open CTLiteralDualDisplacement318 CTLiteralDualFiberCoordinates318
open CTLiteralDualFiberTargetPoints318 CTLiteralDualTargetAction318
open CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "ι" => (algebraMap K A)
local instance : DecidableEq A := Classical.decEq _

theorem original_equation_to_closure (n x y : K) (he : y^2=x*(x-n)*(x+3*n)) :
    (ι y)^2=ι x*(ι x-ι n)*(ι x+3*ι n) := by
  have h := congrArg ι he
  simpa only [map_pow,map_mul,map_add,map_sub,map_ofNat] using h

/-- The literal reverse-isogeny connecting displacement of the chosen
affine point is exactly the already existing continuous root phase on [x]. -/
theorem affine_actual_phase (n x y : K) (hn : n≠0) (hx : x≠0)
    (he : y^2=x*(x-n)*(x+3*n)) (r : Aˣ) (hr : (r:A)^2=ι x) (g : Gal K) :
    let hnA := ((map_ne_zero ι).mpr hn)
    let P := fiberPoint hnA
      (affineFiber (ι n) (ι x) (ι y) (r:A) hnA (((map_ne_zero ι).mpr hx)) hr
        (original_equation_to_closure K n x y he))
    targetAction n (act K g) P - P =
      if phase K r g then targetKernel (ι n) hnA else 0 := by
  have hp := act_on_square_root K r (Units.mk0 x hx) (by simpa only [Units.val_mk0] using hr) g
  exact affine_of_root_sign n (act K g) (((map_ne_zero ι).mpr hn)) (ι x) (ι y) (r:A)
    (((map_ne_zero ι).mpr hx)) hr (original_equation_to_closure K n x y he)
    ((act K g).commutes x) ((act K g).commutes y) (phase K r g) hp

/-- The exceptional source point (0,0) uses the actual class [-3n²]. -/
theorem kernel_actual_phase (n : K) (hn : n≠0) (r : Aˣ)
    (hr : (r:A)^2= -3*(ι n)^2) (g : Gal K) :
    let hnA := ((map_ne_zero ι).mpr hn)
    let P := fiberPoint hnA (kernelFiber (ι n) (r:A) hnA hr)
    targetAction n (act K g) P - P =
      if phase K r g then targetKernel (ι n) hnA else 0 := by
  let a : Kˣ := Units.mk0 (-3*n^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hn))
  have hA : (r:A)^2=ι (a:K) := by simpa only [a,Units.val_mk0,map_mul,map_ofNat,map_neg,map_pow] using hr
  exact kernel_of_root_sign n (act K g) (((map_ne_zero ι).mpr hn)) (r:A) hr (phase K r g)
    (act_on_square_root K r a hA g)

end CTLiteralDualActualPhase318

#print axioms CTLiteralDualActualPhase318.affine_actual_phase
#print axioms CTLiteralDualActualPhase318.kernel_actual_phase
