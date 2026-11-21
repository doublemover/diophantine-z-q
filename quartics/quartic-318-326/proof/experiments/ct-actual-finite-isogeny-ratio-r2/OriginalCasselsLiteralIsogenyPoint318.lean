module
public import OriginalSelectedCasselsParity318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
public section

noncomputable section

namespace OriginalCasselsLiteralIsogenyPoint318

open OriginalSelectedCasselsParity318 ActualTwoDescentEllipticModel318

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

def kernelPoint (n : F) (hn : n ≠ 0) : Point n := point n 0 0 hn (by simp)

/-- The actual total point function. It does not call the expression with
denominator x on either exceptional point, which map to infinity. -/
@[expose] def literalMap (n : F) (hn : n ≠ 0) : Point n → TargetPoint n
  | .zero => 0
  | .some x y h =>
    if hx : x=0 then 0
    else imagePoint n x y hn hx ((curve_equation n x y).mp h.left)

theorem literal_zero (n : F) (hn : n ≠ 0) : literalMap n hn 0=0 := rfl

theorem literal_kernel_point (n : F) (hn : n ≠ 0) :
    literalMap n hn (kernelPoint n hn)=0 := by
  simp [literalMap,kernelPoint,point]

theorem literal_affine (n : F) (hn : n ≠ 0) (x y : F) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    literalMap n hn (point n x y hn he)=imagePoint n x y hn hx he := by
  simp [literalMap,point,hx]

private theorem literal_image_ne_zero {n x y : F} (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) : imagePoint n x y hn hx he ≠ 0 := by
  rw [imagePoint,targetPoint]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The exact kernel as actual points, even before proving additivity. -/
theorem literal_zero_iff {n : F} (hn : n ≠ 0) (P : Point n) :
    literalMap n hn P=0 ↔ P=0 ∨ P=kernelPoint n hn := by
  constructor
  · intro h
    cases P with
    | zero => exact Or.inl rfl
    | some x y hxy =>
      have he := (curve_equation n x y).mp hxy.left
      by_cases hx : x=0
      · subst x
        have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp (by simpa using he)
        subst y
        exact Or.inr rfl
      · change literalMap n hn (point n x y hn he)=0 at h
        rw [literal_affine n hn x y hx he] at h
        exact (literal_image_ne_zero hn hx he h).elim
  · rintro (rfl|rfl)
    · exact literal_zero n hn
    · exact literal_kernel_point n hn

/-- The remaining native issue is only additivity of this fixed total
point map. No choices of maps, kernels, or signs are implicit here. -/
@[expose] def LiteralAddition (n : F) (hn : n ≠ 0) : Prop :=
  ∀ P Q : Point n, literalMap n hn (P+Q)=literalMap n hn P+literalMap n hn Q

def literalHom {n : F} {hn : n ≠ 0} (ha : LiteralAddition n hn) : Point n →+ TargetPoint n where
  toFun := literalMap n hn
  map_zero' := literal_zero n hn
  map_add' := ha

def literalKernelEquiv {n : F} {hn : n ≠ 0} (ha : LiteralAddition n hn) :
    Bool ≃ (literalHom ha).ker := by
  let O : (literalHom ha).ker := ⟨0,literal_zero n hn⟩
  let T : (literalHom ha).ker := ⟨kernelPoint n hn,literal_kernel_point n hn⟩
  let f : Bool → (literalHom ha).ker := fun b => if b then T else O
  have hT : f true ≠ f false := by
    intro he
    have h := congrArg Subtype.val he
    change kernelPoint n hn=0 at h
    exact point_ne_zero n 0 0 hn (by simp) h
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b h
    cases a <;> cases b
    · rfl
    · exact (hT h.symm).elim
    · exact (hT h).elim
    · rfl
  · intro P
    have hp := (literal_zero_iff hn P.val).mp P.prop
    rcases hp with h|h
    · exact ⟨false,Subtype.ext h.symm⟩
    · exact ⟨true,Subtype.ext h.symm⟩

/-- The actual local point ABI is obtained from the single remaining
addition law and finiteness of the same literal range quotient. -/
def localIsogeny {n : F} {hn : n ≠ 0} (ha : LiteralAddition n hn)
    (hf : Finite (TargetPoint n ⧸ (literalHom ha).range)) : LocalIsogeny n hn where
  hom := literalHom ha
  on_affine := literal_affine n hn
  at_kernel := literal_kernel_point n hn
  finiteKernel := Finite.of_equiv Bool (literalKernelEquiv ha)
  finiteCokernel := hf
  kernelCard := by
    rw [Nat.card_congr (literalKernelEquiv ha).symm,Nat.card_eq_fintype_card] <;> decide

/-- A supplied arithmetic isogeny cannot choose a different point map. -/
theorem supplied_map_eq_literal {n : F} {hn : n ≠ 0}
    (L : LocalIsogeny n hn) (P : Point n) : L.hom P=literalMap n hn P := by
  cases P with
  | zero => exact map_zero L.hom
  | some x y hxy =>
    have he := (curve_equation n x y).mp hxy.left
    by_cases hx : x=0
    · subst x
      have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp (by simpa using he)
      subst y
      change L.hom (kernelPoint n hn)=literalMap n hn (kernelPoint n hn)
      rw [literal_kernel_point]
      exact L.at_kernel
    · change L.hom (point n x y hn he)=literalMap n hn (point n x y hn he)
      rw [L.on_affine x y hx he,literal_affine n hn x y hx he]

end OriginalCasselsLiteralIsogenyPoint318

#print axioms OriginalCasselsLiteralIsogenyPoint318.literal_zero_iff
#print axioms OriginalCasselsLiteralIsogenyPoint318.localIsogeny
#print axioms OriginalCasselsLiteralIsogenyPoint318.supplied_map_eq_literal
