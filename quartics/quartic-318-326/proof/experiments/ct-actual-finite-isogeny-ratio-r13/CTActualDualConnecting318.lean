module
public import CTActualDualKernelKummer318
public import CTLiteralDualArithmeticHom318
import all CTLiteralDualFiberTargetPoints318
import all CTLiteralDualArithmeticHom318
import all ActualTwoDescentEllipticModel318
import all OriginalSelectedCasselsParity318
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTActualDualConnecting318

open CTActualQuadraticHOne318 CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318
open CTLiteralDualActualPhase318 CTLiteralDualDisplacement318 CTLiteralDualFiberTargetPoints318
open CTLiteralDualTargetAction318 CTActualDualKernelKummer318
open CTLiteralDualArithmeticHom318 CTLiteralisogenyScalarPoints318
open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open OriginalSelectedCasselsParity318

variable (K : Type) [Field K] [CharZero K] [DecidableEq K]
local notation "Kbar" => AlgebraicClosure K
local notation "ι" => (algebraMap K Kbar)
local instance : DecidableEq Kbar := Classical.decEq _
local notation "ρ" => (act K)

theorem exceptional_scalar_ne (n : K) (hn : n≠0) : -3*n^2≠0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero 2 hn)

def reverseValue (n : K) (hn : n≠0) : Point n → SquareClass K
  | .zero => 1
  | .some x _ _ => if hx : x=0 then classOf (-3*n^2) (exceptional_scalar_ne K n hn)
     else classOf x hx

def connectingValue (n : K) (hn : n≠0) (P : Point n) : QuadraticHOne K :=
  (scalarKummer K (reverseValue K n hn P)).toAdd

/-- Arbitrary chosen reverse lifts of one actual point give exactly
the same displacement, because their difference lies in the fixed
literal kernel. This is at cochain level, before any quotient. -/
theorem same_displacement (n : K) (hn : n≠0) (P Q : TargetPoint (ι n))
    (he : dualPoint (ι n) ((map_ne_zero ι).mpr hn) P=dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q) (g : Gal K) :
    targetAction (F:=K) (A:=Kbar) n (ρ g) P-P=targetAction (F:=K) (A:=Kbar) n (ρ g) Q-Q := by
  have hz : arithmeticDualHom (F:=Kbar) (ι n) ((map_ne_zero ι).mpr hn) (P-Q)=0 := by
    rw [map_sub]
    change dualPoint (ι n) ((map_ne_zero ι).mpr hn) P-dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q=0
    rw [he,sub_self]
  change dualPoint (ι n) ((map_ne_zero ι).mpr hn) (P-Q)=0 at hz
  have h := (dual_kernel_iff (ι n) ((map_ne_zero ι).mpr hn) (P-Q)).mp hz
  have hf : targetAction (F:=K) (A:=Kbar) n (ρ g) (P-Q)=P-Q := by
    rcases h with h|h
    · rw [h,map_zero]
    · rw [h,targetAction_fixes_kernel]
  rw [map_sub] at hf
  calc
    targetAction (F:=K) (A:=Kbar) n (ρ g) P-P = (targetAction (F:=K) (A:=Kbar) n (ρ g) P-targetAction (F:=K) (A:=Kbar) n (ρ g) Q)-(P-Q)+(targetAction (F:=K) (A:=Kbar) n (ρ g) Q-Q) := by abel
    _ = targetAction (F:=K) (A:=Kbar) n (ρ g) Q-Q := by rw [hf,sub_self,zero_add]

theorem exists_lift_with_displacement (n : K) (hn : n≠0) (P : Point n) :
    ∃ Q : TargetPoint (ι n), dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q=sourceBase (A:=Kbar) n P ∧
      ∀ g : Gal K, targetAction (F:=K) (A:=Kbar) n (ρ g) Q-Q=encode (ι n) ((map_ne_zero ι).mpr hn) ((connectingValue K n hn P).val g) := by
  cases P with
  | zero =>
    refine ⟨0,?_,?_⟩
    · change dualPoint (ι n) ((map_ne_zero ι).mpr hn) (0 : TargetPoint (ι n)) =
        sourceBase (A:=Kbar) n (0 : Point n)
      rw [dual_zero,map_zero]
    · exact (origin_displacement_scalar K n hn).2
  | some x y h =>
    have he := (curve_equation n x y).mp h.left
    by_cases hx : x=0
    · subst x
      have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using he)
      subst y
      obtain ⟨Q,hQ,hD⟩ := torsion_displacement_scalar K n hn (exceptional_scalar_ne K n hn)
      refine ⟨Q,?_,?_⟩
      · change dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q=sourceBase (A:=Kbar) n (point n 0 0 hn he)
        rw [sourceBase_point]
        unfold point at hQ ⊢
        simpa only [map_zero] using hQ
      · simpa only [connectingValue,reverseValue,dif_pos rfl] using hD
    obtain ⟨Q,hQ,hD⟩ := affine_displacement_scalar K n x y hn hx he
    refine ⟨Q,?_,?_⟩
    · change dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q=sourceBase (A:=Kbar) n (point n x y hn he)
      rw [sourceBase_point]
      exact hQ
    · simpa only [connectingValue,reverseValue,dif_neg hx] using hD

theorem displacement_of_lift (n : K) (hn : n≠0) (P : Point n) (Q : TargetPoint (ι n))
    (hQ : dualPoint (ι n) ((map_ne_zero ι).mpr hn) Q=sourceBase (A:=Kbar) n P) (g : Gal K) :
    targetAction (F:=K) (A:=Kbar) n (ρ g) Q-Q=encode (ι n) ((map_ne_zero ι).mpr hn) ((connectingValue K n hn P).val g) := by
  obtain ⟨R,hR,hD⟩ := exists_lift_with_displacement K n hn P
  exact (same_displacement K n hn Q R (hQ.trans hR.symm) g).trans (hD g)

/-- Actual continuous connecting homomorphism of the reverse
isogeny on the rational points. Its image is a native local subgroup. -/
def connecting (n : K) (hn : n≠0) : Point n →+ QuadraticHOne K where
  toFun := connectingValue K n hn
  map_zero' := by
    change (scalarKummer K 1).toAdd=0
    rw [map_one] <;> rfl
  map_add' := by
    intro P R
    obtain ⟨Q,hQ,_⟩ := exists_lift_with_displacement K n hn P
    obtain ⟨S,hS,_⟩ := exists_lift_with_displacement K n hn R
    have hAdd : dualPoint (ι n) ((map_ne_zero ι).mpr hn) (Q+S)=sourceBase (A:=Kbar) n (P+R) := by
      rw [dual_add,hQ,hS,map_add]
    apply Subtype.ext
    funext g
    change (connectingValue K n hn (P+R)).val g=
      (connectingValue K n hn P).val g+(connectingValue K n hn R).val g
    apply encode_injective (ι n) ((map_ne_zero ι).mpr hn)
    rw [map_add,← displacement_of_lift K n hn (P+R) (Q+S) hAdd g,
      ← displacement_of_lift K n hn P Q hQ g,← displacement_of_lift K n hn R S hS g,map_add]
    abel

private theorem target_fixed_on_base (n : K) (hn : n≠0) (Q : TargetPoint n) (g : Gal K) :
    targetAction (F:=K) (A:=Kbar) n (ρ g) (targetBase n Q)=targetBase n Q := by
  cases Q with
  | zero =>
      change targetAction (F:=K) (A:=Kbar) n (ρ g) (targetBase n (0 : TargetPoint n))=
        targetBase n (0 : TargetPoint n)
      simp only [map_zero]
  | some x y w =>
    have he := w.left
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [targetModel,zero_mul,add_zero,zero_add] at he
    have hEq : y^2=x*(x^2-4*n*x+16*n^2) := by linear_combination he
    change targetAction (F:=K) (A:=Kbar) n (ρ g) (targetBase n (targetPoint n x y hn hEq))=
      targetBase n (targetPoint n x y hn hEq)
    rw [targetBase_point,targetAction_on_point]
    unfold targetPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨(ρ g).commutes x,(ρ g).commutes y⟩

/-- Galois fixed points of the literal quotient descend to actual
base-field points, by descent of their two affine coordinates. -/
theorem target_fixed_descends (n : K) (hn : n≠0) (Q : TargetPoint (ι n))
    (hFix : ∀ g : Gal K, targetAction (F:=K) (A:=Kbar) n (ρ g) Q=Q) :
    ∃ R : TargetPoint n, targetBase n R=Q := by
  cases Q with
  | zero => exact ⟨0,map_zero _⟩
  | some s t w =>
    have he := w.left
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [targetModel,zero_mul,add_zero,zero_add] at he
    have hEq : t^2=s*(s^2-4*ι n*s+16*(ι n)^2) := by linear_combination he
    have hSt (g : Gal K) : ρ g s=s ∧ ρ g t=t := by
      have hg := hFix g
      change targetAction (F:=K) (A:=Kbar) n (ρ g) (targetPoint (ι n) s t ((map_ne_zero ι).mpr hn) hEq)=
        targetPoint (ι n) s t ((map_ne_zero ι).mpr hn) hEq at hg
      rw [targetAction_on_point] at hg
      unfold targetPoint at hg
      exact WeierstrassCurve.Affine.Point.some.inj hg
    have hS (g : Kbar ≃ₐ[K] Kbar) : g s=s := (hSt (show Gal K from g)).1
    have hT (g : Kbar ≃ₐ[K] Kbar) : g t=t := (hSt (show Gal K from g)).2
    obtain ⟨x,hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K) s).mpr hS
    obtain ⟨y,hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k:=K) t).mpr hT
    have hE : y^2=x*(x^2-4*n*x+16*n^2) := by
      apply (algebraMap K Kbar).injective
      simpa only [map_pow,map_mul,map_add,map_sub,map_ofNat,hx,hy] using hEq
    refine ⟨targetPoint n x y hn hE,?_⟩
    rw [targetBase_point]
    unfold targetPoint
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,hy⟩

/-- Exact Kummer row on the literal arithmetic point groups. This is
the actual reverse cokernel, not a proxy test on raw x-coordinates. -/
theorem connecting_ker_eq_range (n : K) (hn : n≠0) :
    (connecting K n hn).ker=(arithmeticDualHom n hn).range := by
  ext P
  constructor
  · intro hz
    change connecting K n hn P=0 at hz
    obtain ⟨Q,hQ,hD⟩ := exists_lift_with_displacement K n hn P
    have hFix (g : Gal K) : targetAction (F:=K) (A:=Kbar) n (ρ g) Q=Q := by
      apply sub_eq_zero.mp
      have hv := congrArg (fun z : QuadraticHOne K => z.val g) hz
      change (connectingValue K n hn P).val g=0 at hv
      rw [hD g,hv,encode_zero]
    obtain ⟨R,hR⟩ := target_fixed_descends K n hn Q hFix
    refine ⟨R,?_⟩
    change dualPoint n hn R=P
    apply (sourceBase_injective (A:=Kbar) n)
    rw [dual_base,hR,hQ]
  · rintro ⟨Q,rfl⟩
    change connecting K n hn (arithmeticDualHom n hn Q)=0
    have hQ : dualPoint (ι n) ((map_ne_zero ι).mpr hn) (targetBase n Q)=sourceBase (A:=Kbar) n (arithmeticDualHom n hn Q) :=
      (dual_base (A:=Kbar) n hn Q).symm
    apply Subtype.ext
    funext g
    change (connectingValue K n hn (arithmeticDualHom n hn Q)).val g=0
    apply encode_injective (ι n) ((map_ne_zero ι).mpr hn)
    rw [←displacement_of_lift K n hn _ _ hQ g,target_fixed_on_base K n hn Q g,sub_self,encode_zero]

/-- First isomorphism on the actual native local quotient. -/
def literalReverseQuotientEquiv (n : K) (hn : n≠0) :
    Point n ⧸ (arithmeticDualHom n hn).range ≃+ (connecting K n hn).range := by
  have h := connecting_ker_eq_range K n hn
  let e : Point n ⧸ (arithmeticDualHom n hn).range ≃+
      Point n ⧸ (connecting K n hn).ker :=
    QuotientAddGroup.quotientAddEquivOfEq h.symm
  exact e.trans (QuotientAddGroup.quotientKerEquivRange (connecting K n hn))

end CTActualDualConnecting318

#print axioms CTActualDualConnecting318.same_displacement
#print axioms CTActualDualConnecting318.displacement_of_lift
#print axioms CTActualDualConnecting318.connecting

#print axioms CTActualDualConnecting318.connecting_ker_eq_range

#print axioms CTActualDualConnecting318.literalReverseQuotientEquiv
