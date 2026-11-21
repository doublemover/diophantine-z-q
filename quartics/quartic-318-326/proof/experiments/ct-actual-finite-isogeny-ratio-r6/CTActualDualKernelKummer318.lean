module
public import CTActualQuadraticHOne318
public import CTLiteralDualActualPhase318
import all CTLiteralDualFiberTargetPoints318
import all ActualTwoDescentEllipticModel318
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTActualDualKernelKummer318

open CTActualQuadraticHOne318 CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318
open CTLiteralDualActualPhase318 CTLiteralDualFiberTargetPoints318
open CTLiteralDualFiberCoordinates318 CTLiteralDualTargetAction318
open OriginalSelectedCasselsParity318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentEllipticModel318

section Field
variable {K : Type} [Field K] [CharZero K] [DecidableEq K]

theorem targetKernel_ne_zero (n : K) (hn : n≠0) : targetKernel n hn≠0 := by
  unfold targetKernel targetPoint
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem targetKernel_add_self (n : K) (hn : n≠0) :
    targetKernel n hn+targetKernel n hn=0 := by
  unfold targetKernel targetPoint
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY,targetModel]

/-- The genuine point-group embedding of the two rational reverse
kernel points. Its image is exactly the fiber over O. -/
def encode (n : K) (hn : n≠0) : Bit →+ TargetPoint n where
  toFun b := if b=0 then 0 else targetKernel n hn
  map_zero' := if_pos rfl
  map_add' := by
    intro b c
    have hOne : (1:Bit)≠0 := by decide
    have hTwo : (1:Bit)+1=0 := by decide
    have hb : b=0 ∨ b=1 := by fin_cases b <;> decide
    have hc : c=0 ∨ c=1 := by fin_cases c <;> decide
    rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;>
      simp [hOne,hTwo,targetKernel_add_self n hn]

@[simp] theorem encode_zero (n : K) (hn : n≠0) : encode n hn 0=0 := map_zero _
@[simp] theorem encode_one (n : K) (hn : n≠0) : encode n hn 1=targetKernel n hn := by
  have h : (1:Bit)≠0 := by decide
  exact if_neg h

theorem encode_bit (n : K) (hn : n≠0) (b : Bool) :
    encode n hn (bit b)=if b then targetKernel n hn else 0 := by
  cases b
  · exact encode_zero n hn
  · exact encode_one n hn

theorem encode_injective (n : K) (hn : n≠0) : Function.Injective (encode n hn) := by
  intro b c h
  have hb : b=0 ∨ b=1 := by fin_cases b <;> decide
  have hc : c=0 ∨ c=1 := by fin_cases c <;> decide
  rcases hb with rfl|rfl <;> rcases hc with rfl|rfl
  · rfl
  · exact False.elim (targetKernel_ne_zero n hn (by simpa only [encode_zero,encode_one] using h.symm))
  · exact False.elim (targetKernel_ne_zero n hn (by simpa only [encode_zero,encode_one] using h))
  · rfl

private theorem point_eq_target_of_zero_x (n : K) (hn : n≠0) (t : K)
    (h : (targetModel n).toAffine.Nonsingular 0 t) :
    WeierstrassCurve.Affine.Point.some 0 t h=targetKernel n hn := by
  have ht : t=0 := by
    have he := h.left
    rw [WeierstrassCurve.Affine.equation_iff] at he
    have hz : t^2=0 := by simpa [targetModel] using he
    exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hz
  subst t
  rfl

theorem dual_kernel_iff (n : K) (hn : n≠0) (Q : TargetPoint n) :
    dualPoint n hn Q=0 ↔ Q=0 ∨ Q=targetKernel n hn := by
  constructor
  · intro h
    cases Q with
    | zero => exact Or.inl rfl
    | some s t he =>
      by_cases hs : s=0
      · subst s
        exact Or.inr (point_eq_target_of_zero_x n hn t he)
      · simp only [dualPoint,dif_neg hs] at h
        exact False.elim (point_ne_zero _ _ _ _ _ h)
  · rintro (rfl|rfl)
    · exact dual_zero n hn
    · exact dual_target_kernel n hn

end Field

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "ι" => (algebraMap K A)
local instance : DecidableEq A := Classical.decEq _

theorem action_on_encoded (n : K) (hn : n≠0) (b : Bit) (g : Gal K) :
    targetAction n (act K g) (encode (ι n) (map_ne_zero ι hn) b) =
      encode (ι n) (map_ne_zero ι hn) b := by
  have h : b=0 ∨ b=1 := by fin_cases b <;> decide
  rcases h with rfl|rfl
  · rw [encode_zero,map_zero]
  · rw [encode_one,targetAction_fixes_kernel]

/-- In ordinary affine fibers the actual connecting cocycle is the
canonical scalar Kummer class of the literal original x-coordinate. -/
theorem affine_displacement_scalar (n x y : K) (hn : n≠0) (hx : x≠0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    ∃ Q : TargetPoint (ι n),
      dualPoint (ι n) (map_ne_zero ι hn) Q =
        point (ι n) (ι x) (ι y) (map_ne_zero ι hn) (original_equation_to_closure K n x y he) ∧
      ∀ g : Gal K, targetAction n (act K g) Q-Q =
        encode (ι n) (map_ne_zero ι hn) ((scalarKummer K (classOf x hx)).toAdd.val g) := by
  let a : Kˣ := Units.mk0 x hx
  obtain ⟨r,hr⟩ := exists_unit_root K a
  have hxA : (r:A)^2=ι x := hr
  let Q := fiberPoint (map_ne_zero ι hn)
    (affineFiber (ι n) (ι x) (ι y) (r:A) (map_ne_zero ι hn) (map_ne_zero ι hx) hxA
      (original_equation_to_closure K n x y he))
  refine ⟨Q,dual_fiber_point _ _ _,?_⟩
  intro g
  have h := scalarKummer_on_root K a r hr
  change (scalarKummer K (classOf x hx)).toAdd=rootCycle K a r hr at h
  rw [h,rootCycle_apply,encode_bit]
  exact affine_actual_phase K n x y hn hx he r hxA g

/-- The exceptional original (0,0) uses [−3n²], exactly as in the
local squareclass calculation; no arbitrary scalar may be substituted. -/
theorem torsion_displacement_scalar (n : K) (hn : n≠0)
    (h3 : -3*n^2≠0) :
    ∃ Q : TargetPoint (ι n),
      dualPoint (ι n) (map_ne_zero ι hn) Q = point (ι n) 0 0 (map_ne_zero ι hn) (by simp) ∧
      ∀ g : Gal K, targetAction n (act K g) Q-Q =
        encode (ι n) (map_ne_zero ι hn) ((scalarKummer K (classOf (-3*n^2) h3)).toAdd.val g) := by
  let a : Kˣ := Units.mk0 (-3*n^2) h3
  obtain ⟨r,hr⟩ := exists_unit_root K a
  have hA : (r:A)^2= -3*(ι n)^2 := by
    simpa only [a,Units.val_mk0,map_neg,map_mul,map_ofNat,map_pow] using hr
  let Q := fiberPoint (map_ne_zero ι hn) (kernelFiber (ι n) (r:A) (map_ne_zero ι hn) hA)
  refine ⟨Q,dual_fiber_point _ _ _,?_⟩
  intro g
  have h := scalarKummer_on_root K a r hr
  change (scalarKummer K (classOf (-3*n^2) h3)).toAdd=rootCycle K a r hr at h
  rw [h,rootCycle_apply,encode_bit]
  exact kernel_actual_phase K n hn r hA g

theorem origin_displacement_scalar (n : K) (hn : n≠0) :
    dualPoint (ι n) (map_ne_zero ι hn) 0=0 ∧
      ∀ g : Gal K, targetAction n (act K g) 0-0 =
        encode (ι n) (map_ne_zero ι hn) ((scalarKummer K 1).toAdd.val g) := by
  refine ⟨dual_zero _ _,?_⟩
  intro g
  rw [map_zero,sub_zero,map_one] <;> exact (encode_zero _ _).symm

end CTActualDualKernelKummer318

#print axioms CTActualDualKernelKummer318.dual_kernel_iff
#print axioms CTActualDualKernelKummer318.affine_displacement_scalar
#print axioms CTActualDualKernelKummer318.torsion_displacement_scalar
#print axioms CTActualDualKernelKummer318.origin_displacement_scalar
