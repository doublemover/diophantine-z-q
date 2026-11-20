module
public import OriginalSelectedCasselsParity318
public import ActualTwoDescentSquareClassQuotient318
public import ActualTwoDescentTwoAdicUnits318
public import ActualTwoDescentTwoAdicSquare318
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Linarith
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
public section

noncomputable section

namespace OriginalCasselsDyadicXClass318

open OriginalSelectedCasselsParity318 ActualTwoDescentEllipticModel318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentTwoAdicSquare318 ActualTwoDescentLocalValuationTools318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq (ℚ_[2]) := Classical.decEq _

section Field

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- The actual abscissa class on the literal target. At its zero root,
the root derivative is 16n²=(4n)², so its nonzero class is one. -/
@[expose] def targetClass {n : F} (P : TargetPoint n) : SquareClass F := by
  classical
  exact match P with
  | .zero => 1
  | .some x _ _ => if h : x = 0 then 1 else classOf x h

theorem target_class_at_affine {n : F} {x y : F} (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x^2-4*n*x+16*n^2)) :
    targetClass (targetPoint n x y hn he) = classOf x hx := by
  simp [targetClass,targetPoint,hx]

private theorem eq_points {n : F} {hn : n ≠ 0} {x y X Y : F}
    {h : y^2=x*(x^2-4*n*x+16*n^2)} {H : Y^2=X*(X^2-4*n*X+16*n^2)}
    (hx : x = X) (hy : y = Y) :
    targetPoint n x y hn h = targetPoint n X Y hn H := by
  subst X
  subst Y
  rfl

private theorem target_equation_at_coordinates (n x y : F) :
    (targetModel n).toAffine.Equation x y ↔ y^2=x*(x^2-4*n*x+16*n^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [targetModel,zero_mul,add_zero,zero_add]
  constructor <;> intro h <;> linear_combination h

private theorem source_ord_zero {n x y : F} (hx : x = 0)
    (he : y^2=x*(x-n)*(x+3*n)) : y = 0 := by
  rw [hx] at he
  simp only [zero_mul] at he
  exact (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp he

private theorem image_x_square {n x y : F} (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    x+2*n-3*n^2/x = (y/x)^2 := by
  rw [div_pow,he]
  field_simp [hx] <;> ring

/-- Exact quadratic inverse chart, with the ordinate sign fixed by Y/u. -/
private theorem lift_square_affine {n X Y u : F} (hn : n ≠ 0) (hX : X ≠ 0)
    (hu : u ≠ 0) (huX : u^2=X) (hY : Y^2=X*(X^2-4*n*X+16*n^2)) :
    ∃ x y : F, ∃ hx : x ≠ 0, ∃ he : y^2=x*(x-n)*(x+3*n),
      imagePoint n x y hn hx he = targetPoint n X Y hn hY := by
  let v := Y/u
  have hv : v^2=X^2-4*n*X+16*n^2 := by
    dsimp [v]
    rw [div_pow,hY,huX]
    field_simp [hX] <;> ring
  let x := (X-2*n+v)/2
  have hr : x^2+(2*n-X)*x-3*n^2=0 := by
    have h4 : (4:F)*(x^2+(2*n-X)*x-3*n^2)=0 := by
      dsimp [x]
      linear_combination hv
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  have hx : x ≠ 0 := by
    intro hz
    rw [hz] at hr
    have h3 : (3:F) ≠ 0 := by norm_num
    exact (mul_ne_zero h3 (pow_ne_zero 2 hn)) (by linear_combination -hr)
  have he : (u*x)^2=x*(x-n)*(x+3*n) := by
    calc
      _ = u^2*x^2 := by ring
      _ = _ := by rw [huX]; linear_combination -x * hr
  refine ⟨x,u*x,hx,he,?_⟩
  have hdiv : 3*n^2/x=x+2*n-X := by
    apply (div_eq_iff hx).mpr
    linear_combination -hr
  have hcoord : x+2*n-3*n^2/x=X := by rw [hdiv]; ring
  have hvcoord : x+(x+2*n-X)=v := by dsimp [x]; ring
  have hYcoord : u*x+3*n^2*(u*x)/x^2=Y := by
    calc
      _ = u*(x+3*n^2/x) := by field_simp [hx] <;> ring
      _ = u*v := by rw [hdiv,hvcoord]
      _ = Y := by dsimp [v]; field_simp [hu] <;> ring
  exact eq_points hcoord hYcoord

theorem target_class_one_iff_range {n : F} {hn : n ≠ 0}
    (L : LocalIsogeny n hn) (P : TargetPoint n) :
    targetClass P = 1 ↔ P ∈ L.hom.range := by
  classical
  constructor
  · intro hclass
    cases P with
    | zero => exact ⟨0,map_zero L.hom⟩
    | some X Y h =>
      have hY := (target_equation_at_coordinates n X Y).mp h.left
      by_cases hX : X = 0
      · subst X
        have hY0 : Y=0 := by
          apply (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp
          simpa using hY
        subst Y
        have he : (0 : F)^2=n*(n-n)*(n+3*n) := by simp
        refine ⟨point n n 0 hn he,?_⟩
        change L.hom (point n n 0 hn he)=targetPoint n 0 0 hn (by simp)
        rw [L.on_affine n 0 hn he]
        apply eq_points
        · field_simp [hn] <;> ring
        · simp
      · change targetClass (targetPoint n X Y hn hY) = 1 at hclass
        rw [target_class_at_affine hn hX hY,←class_of_one] at hclass
        obtain ⟨u,hu,huX⟩ := (class_of_eq_iff X 1 hX one_ne_zero).mp hclass
        have heq : u^2=X := by simpa only [one_mul] using huX.symm
        obtain ⟨x,y,hx,he,him⟩ := lift_square_affine hn hX hu heq hY
        refine ⟨point n x y hn he,?_⟩
        rw [L.on_affine x y hx he]
        exact him
  · rintro ⟨Q,rfl⟩
    cases Q with
    | zero => simp [targetClass,map_zero]
    | some x y h =>
      have he := (curve_equation n x y).mp h.left
      by_cases hx : x = 0
      · have hy := source_ord_zero hx he
        subst x
        subst y
        change targetClass (L.hom (point n 0 0 hn (by simp)))=1
        rw [L.at_kernel]
        simp [targetClass]
      · change targetClass (L.hom (point n x y hn he))=1
        rw [L.on_affine x y hx he]
        by_cases hz : x+2*n-3*n^2/x=0
        · simp [imagePoint,targetPoint,targetClass,hz]
        · rw [imagePoint,target_class_at_affine hn hz]
          have hsq := image_x_square hx he
          have hs : y/x ≠ 0 := by
            intro hh
            rw [hh,zero_pow (by decide : (2:ℕ) ≠ 0)] at hsq
            exact hz hsq
          rw [←class_of_one]
          exact (class_of_eq_iff _ 1 hz one_ne_zero).mpr ⟨y/x,hs,by simpa using hsq⟩

/-- Explicit pending target chord law. The exact kernel comparison above
was proved without it and with the same literal isogeny. -/
@[expose] def XClassProduct (n : F) : Prop :=
  ∀ P Q : TargetPoint n, targetClass (P+Q)=targetClass P*targetClass Q

def xClassHom {n : F} (hm : XClassProduct n) : TargetPoint n →+ Additive (SquareClass F) where
  toFun P := Additive.ofMul (targetClass P)
  map_zero' := rfl
  map_add' P Q := hm P Q

def actual_cokernel_equiv_xClass {n : F} {hn : n ≠ 0}
    (L : LocalIsogeny n hn) (hm : XClassProduct n) :
    TargetPoint n ⧸ L.hom.range ≃+ (xClassHom hm).range := by
  have hker : (xClassHom hm).ker = L.hom.range := by
    ext P
    change targetClass P = 1 ↔ P ∈ L.hom.range
    exact target_class_one_iff_range L P
  have he := QuotientAddGroup.quotientKerEquivRange (xClassHom hm)
  rw [hker] at he
  exact he

end Field

section Dyadic

private def radicand5 (n : ℕ) : ℕ := 80*n^2+125-100*n

private theorem radicand5_sub (n : ℕ) : 100*n ≤ 80*n^2+125 := by
  have hh : (100:ℤ)*(n:ℤ) ≤ 80*(n:ℤ)^2+125 := by
    nlinarith [sq_nonneg (8*(n:ℤ)-5)]
  exact_mod_cast hh

private theorem radicand5_reduction (n : ℕ) (hr : (n:ZMod 12)=11) :
    (radicand5 n : ZMod 8)=1 := by
  have h12 : n%12=11 := by
    have h := congrArg ZMod.val hr
    norm_num only [ZMod.val_natCast] at h
    exact h
  have h24 : n%24=11 ∨ n%24=23 := by
    have hm := (Nat.mod_mod_of_dvd n (by decide : 12 ∣ 24)).trans h12
    have hl := Nat.mod_lt n (by decide : 0<24)
    omega
  have h8 : (n:ZMod 8) = ((n%24 : ℕ):ZMod 8) :=
    (ZMod.natCast_eq_natCast_iff' n (n%24) 8).mpr
      (Nat.mod_mod_of_dvd n (by decide : 8 ∣ 24)).symm
  rw [radicand5,Nat.cast_sub (radicand5_sub n)]
  push_cast
  rw [h8]
  rcases h24 with h | h <;> rw [h] <;> decide

theorem actual_class_five_witness (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    ∃ P : TargetPoint (n:ℚ_[2]), targetClass P=classOf (5:ℚ_[2]) (by norm_num) := by
  obtain ⟨y,hy⟩ := actual_two_adic_square (radicand5 n) (radicand5_reduction n hr)
  have hrad : (radicand5 n : ℚ_[2])=(5 : ℚ_[2])*(5^2-4*n*5+16*n^2) := by
    rw [radicand5,Nat.cast_sub (radicand5_sub n)]
    push_cast
    ring
  let hp := hy.trans hrad
  let P := targetPoint (n:ℚ_[2]) 5 y (Nat.cast_ne_zero.mpr hn.ne') hp
  exact ⟨P,target_class_at_affine _ (by norm_num) hp⟩

theorem actual_class_five_ne_one : classOf (5:ℚ_[2]) (by norm_num) ≠ 1 := by
  intro h
  rw [←class_of_one] at h
  obtain ⟨u,hu,hh⟩ := (class_of_eq_iff (5:ℚ_[2]) 1 (by norm_num) one_ne_zero).mp h
  have hsq : u^2=(5:ℚ_[2]) := by simpa only [one_mul] using hh.symm
  have hval : (5:ℚ_[2]).valuation=0 :=
    actual_prime_unit_valuation (p:=2) 5 (by decide)
  have hvalU := congrArg Padic.valuation hsq
  rw [Padic.valuation_pow,hval] at hvalU
  have huV : u.valuation=0 := by omega
  obtain ⟨U,hU,hUnit⟩ := actual_two_unit_lift u hu huV
  have hU5 : U^2=(5:ℤ_[2]) := by
    apply PadicInt.ext
    change ((U^2 : ℤ_[2]) : ℚ_[2]) = (5:ℚ_[2])
    rw [PadicInt.coe_pow,hU,hsq]
  let f : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3
  have hres : (f U)^2=5 := by
    have h' := congrArg f hU5
    simpa only [map_pow,map_ofNat] using h'
  have h1 := actual_unit_square_mod8 (f U) (hUnit.map f)
  rw [h1] at hres
  exact (by decide : (1:ZMod 8) ≠ 5) hres

/-- An actual nontrivial coker representative, even without the
target class multiplication law or the upper restriction on classes. -/
theorem actual_dyadic_has_nonimage (n : ℕ) (hp : 0<n) (hr : (n:ZMod 12)=11)
    (L : LocalIsogeny (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hp.ne')) :
    ∃ P : TargetPoint (n:ℚ_[2]), P ∉ L.hom.range := by
  obtain ⟨P,hP⟩ := actual_class_five_witness n hp hr
  refine ⟨P,?_⟩
  intro h
  exact actual_class_five_ne_one (hP.symm.trans ((target_class_one_iff_range L P).mpr h))

/-- The remaining dyadic inputs are exclusion of further actual classes
and the exact target chord law. The class-five witness is native above. -/
theorem actual_dyadic_cokernel_two (n : ℕ) (hp : 0<n) (hr : (n:ZMod 12)=11)
    (L : LocalIsogeny (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hp.ne'))
    (hm : XClassProduct (n:ℚ_[2]))
    (hAll : ∀ P : TargetPoint (n:ℚ_[2]), targetClass P=1 ∨
      targetClass P=classOf (5:ℚ_[2]) (by norm_num)) : L.cokernelCard=2 := by
  obtain ⟨P5,hP5⟩ := actual_class_five_witness n hp hr
  let xhom := xClassHom hm
  let img (P : TargetPoint (n:ℚ_[2])) : xhom.range := ⟨xhom P,⟨P,rfl⟩⟩
  let f : Bool → xhom.range := fun b => if b then img P5 else img 0
  have hne : f true ≠ f false := by
    intro h
    have he := congrArg Subtype.val h
    change targetClass P5 = (1 : SquareClass ℚ_[2]) at he
    exact actual_class_five_ne_one (hP5.symm.trans he)
  have hInjective : Function.Injective f := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact (hne h.symm).elim
    · exact (hne h).elim
    · rfl
  have hSurjective : Function.Surjective f := by
    rintro ⟨a,P,rfl⟩
    rcases hAll P with h | h
    · refine ⟨false,Subtype.ext ?_⟩
      change (1 : SquareClass ℚ_[2])=targetClass P
      exact h.symm
    · refine ⟨true,Subtype.ext ?_⟩
      change targetClass P5=targetClass P
      exact hP5.trans h.symm
  change Nat.card (TargetPoint (n:ℚ_[2]) ⧸ L.hom.range) = 2
  rw [Nat.card_congr (actual_cokernel_equiv_xClass L hm).toEquiv,
    Nat.card_congr (Equiv.ofBijective f ⟨hInjective,hSurjective⟩).symm,
    Nat.card_eq_fintype_card] <;> decide

/-- Exact adapter for the two_size field of ExactLocalCokernels. -/
theorem local_system_two_size (n : ℕ) (hp : 0<n) (hr : (n:ZMod 12)=11)
    (L : LocalSystem n hp) (hm : XClassProduct (n:ℚ_[2]))
    (hAll : ∀ P : TargetPoint (n:ℚ_[2]), targetClass P=1 ∨
      targetClass P=classOf (5:ℚ_[2]) (by norm_num)) :
    L.finiteCokernelCard 2 Nat.prime_two=2 := by
  change (L.padic 2 Nat.prime_two).cokernelCard=2
  exact actual_dyadic_cokernel_two n hp hr (L.padic 2 Nat.prime_two) hm hAll

end Dyadic

end OriginalCasselsDyadicXClass318

#print axioms OriginalCasselsDyadicXClass318.target_class_one_iff_range
#print axioms OriginalCasselsDyadicXClass318.actual_class_five_witness
#print axioms OriginalCasselsDyadicXClass318.actual_dyadic_cokernel_two
