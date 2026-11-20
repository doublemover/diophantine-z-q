module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators

public section

namespace OriginalRCNonzeroAddressBounds318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Actual central factor read in its normalized lattice. The unit is
integral, not a unit of the fraction field or the Laurent coefficient ring. -/
@[expose] def PowUnit (x : ℚ_[2]) (w : ℤ) : Prop :=
  ∃ u : ℤ_[2]ˣ, x = (2 : ℚ_[2])^w * ((u : ℤ_[2]) : ℚ_[2])

theorem integral_unit_val (u : ℤ_[2]ˣ) : ((u : ℤ_[2]) : ℚ_[2]).valuation = 0 := by
  have h : ((u : ℤ_[2]) * (↑u⁻¹ : ℤ_[2])).valuation = 0 := by
    rw [Units.mul_inv, PadicInt.valuation_one]
  rw [PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero (u⁻¹))] at h
  rw [PadicInt.valuation_coe]
  omega

theorem PowUnit.read {x : ℚ_[2]} {w : ℤ} (h : PowUnit x w) :
    x ≠ 0 ∧ x.valuation = w := by
  obtain ⟨u, rfl⟩ := h
  have hu : ((u : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr (Units.ne_zero u)
  have h₂ : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hp : ((2 : ℚ_[2])^w) ≠ 0 := zpow_ne_zero w h₂
  refine ⟨mul_ne_zero hp hu, ?_⟩
  have hv : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  rw [Padic.valuation_mul hp hu, Padic.valuation_zpow, hv, integral_unit_val, mul_one, add_zero]

theorem PowUnit.mul {x y : ℚ_[2]} {a b : ℤ} (hx : PowUnit x a) (hy : PowUnit y b) :
    PowUnit (x*y) (a+b) := by
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  refine ⟨u*v, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℚ_[2]) ≠ 0), Units.val_mul, PadicInt.coe_mul]
  ring

/-- The active loss is exactly four per actual active split prime,
as the two actual normalized local degree-two lengths are two each.
The summation is over the actual active set, not all graph vertices. -/
theorem active_blocks_read {A : Type*} (s : Finset A)
    (above₁ above₂ : A → ℚ_[2])
    (h : ∀ q ∈ s, PowUnit (above₁ q) 2 ∧ PowUnit (above₂ q) 2) :
    PowUnit (∏ q ∈ s, above₁ q * above₂ q) (4*(s.card:ℤ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert q s hq ih =>
      have hp := h q (Finset.mem_insert_self _ _)
      have hfour : PowUnit (above₁ q * above₂ q) 4 := by
        simpa only [show (2:ℤ)+2 = 4 by decide] using hp.1.mul hp.2
      have hs := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
      have hC : 4+4*(s.card:ℤ) = 4*((insert q s).card:ℤ) := by
        rw [Finset.card_insert_of_notMem hq, Nat.cast_add, Nat.cast_one]
        ring
      rw [Finset.prod_insert hq, ← hC]
      exact hfour.mul hs

/-- The actual scalar survivor differential kills its marked column.
If that column specializes nontrivially, no additional rank
assumption on this two-line Schur survivor is needed. -/
theorem survivor_differential_zero {A K : Type*} [CommRing A] [IsDomain A] [CommRing K]
    (res : A →+* K) (δ alpha : A)
    (hmarked : res alpha ≠ 0) (hcycle : δ * alpha = 0) :
    δ = 0 := by
  refine (mul_eq_zero.mp hcycle).resolve_right ?_
  intro he
  exact hmarked (by rw [he, map_zero])

/-- One actual final same-supported central read, **before** translating
the ordinary compact Kummer degree-two length by the isogeny formula.
Even/odd disks are ordinary integral Kummer disks; local quotient
factors are retained separately, not fictitious cohomology summands. -/
structure MarkedCentralRow (central : ℚ_[2]) where
  omega : ℕ
  jRC : ℕ
  Lval : ℕ
  movingScalarVal : ℕ
  g : ℕ
  shaLength : ℕ
  movingLength : ℕ
  basisShift : ℤ
  basis : ℚ_[2]
  alpha : ℚ_[2]
  beta : ℚ_[2]
  evenDisks : ℚ_[2]
  oddDisk : ℚ_[2]
  activeQuotient : ℚ_[2]
  movingQuotient : ℚ_[2]
  basisRead : PowUnit basis basisShift
  alphaRead : PowUnit alpha ((jRC:ℤ)+Lval+movingScalarVal)
  betaRead : PowUnit beta ((jRC:ℤ)+Lval+movingScalarVal)
  evenRead : PowUnit evenDisks (2*(g:ℤ))
  oddRead : PowUnit oddDisk (shaLength:ℤ)
  activeRead : PowUnit activeQuotient (4*(omega:ℤ))
  movingRead : PowUnit movingQuotient (movingLength:ℤ)
  exactProduct : central =
    basis * ((alpha*beta*evenDisks)/(oddDisk*activeQuotient*movingQuotient))

/-- Nonvanishing is a conclusion, not a sign or positivity premise
on the selected address. This is the literal determinant product
of the two marked coordinates and the exact local disk factors. -/
theorem MarkedCentralRow.read {x : ℚ_[2]} (C : MarkedCentralRow x) :
    x ≠ 0 ∧ x.valuation = C.basisShift+2*(C.jRC:ℤ)+2*C.Lval+2*C.movingScalarVal+
      2*C.g-C.shaLength-4*C.omega-C.movingLength := by
  obtain ⟨hb,hbv⟩ := C.basisRead.read
  obtain ⟨ha,hav⟩ := C.alphaRead.read
  obtain ⟨hβ,hβv⟩ := C.betaRead.read
  obtain ⟨he,hev⟩ := C.evenRead.read
  obtain ⟨ho,hov⟩ := C.oddRead.read
  obtain ⟨hA,hAv⟩ := C.activeRead.read
  obtain ⟨hM,hMv⟩ := C.movingRead.read
  have hN := mul_ne_zero (mul_ne_zero ha hβ) he
  have hD := mul_ne_zero (mul_ne_zero ho hA) hM
  refine ⟨?_, ?_⟩
  · rw [C.exactProduct]
    exact mul_ne_zero hb (div_ne_zero hN hD)
  · rw [C.exactProduct, Padic.valuation_mul hb (div_ne_zero hN hD),
      div_eq_mul_inv, Padic.valuation_mul hN (inv_ne_zero hD), Padic.valuation_inv,
      Padic.valuation_mul (mul_ne_zero ha hβ) he, Padic.valuation_mul ha hβ,
      Padic.valuation_mul (mul_ne_zero ho hA) hM, Padic.valuation_mul ho hA,
      hbv, hav, hβv, hev, hov, hAv, hMv]
    omega

/-- One fixed bound, chosen before the graph dimension. Allowing an
old fixed basis shift is harmless; a literal integral comparison
has shift zero. No moving-length equality or companion component
formula is required for this one direction. -/
@[expose] def budget (CJ old : ℤ) (ell cE gMax : ℕ) : ℕ :=
  (CJ+old+2*(ell:ℤ)+2*(cE:ℤ)+2*(gMax:ℤ)).toNat

theorem MarkedCentralRow.upper {x : ℚ_[2]} (C : MarkedCentralRow x)
    (CJ old : ℤ) (ell cE gMax : ℕ)
    (hJ : 2*(C.jRC:ℤ) ≤ 4*(C.omega:ℤ)+CJ)
    (hOld : C.basisShift ≤ old) (hL : C.Lval ≤ ell)
    (hM : C.movingScalarVal ≤ cE) (hG : C.g ≤ gMax) :
    x ≠ 0 ∧ x.valuation ≤ (budget CJ old ell cE gMax:ℤ) := by
  obtain ⟨hne, hv⟩ := C.read
  refine ⟨hne, ?_⟩
  rw [hv]
  unfold budget
  omega

/-- Reapply the same (3.4) observed ratio to the actual fixed-k pair
of (3.9), rather than multiplying those separate address sets. -/
theorem index_bound_of_same_39 (jGen jRC omega : ℕ)
    (lEven vStar err Co Ce Cphase : ℤ)
    (hgen : (jGen:ℤ) ≤ (omega:ℤ)+Co)
    (heven : lEven ≤ 2*(omega:ℤ)+Ce)
    (hindex : 2*(jRC:ℤ)-2*(jGen:ℤ) = lEven-vStar+err)
    (herr : err ≤ Cphase) :
    2*(jRC:ℤ) ≤ 4*(omega:ℤ)+(2*Co+Ce-vStar+Cphase) := by omega

/-- The exact budget hypothesis of the terminal certificate for every
actual nonzero address; the original L+2 selector is untouched.
Its cohomological and analytic factors are not constructed here. -/
theorem original_upper_after_same_39 {X : Type*} [Zero X] (center : X → ℚ_[2])
    (rows : (x : X) → x ≠ 0 → MarkedCentralRow (center x))
    (Co Ce vStar Cphase old : ℤ) (ell cE gMax : ℕ)
    (same39 : ∀ x (hx : x ≠ 0), ∃ (jGen : ℕ) (lEven err : ℤ),
      (jGen:ℤ) ≤ ((rows x hx).omega:ℤ)+Co ∧
      lEven ≤ 2*((rows x hx).omega:ℤ)+Ce ∧
      2*((rows x hx).jRC:ℤ)-2*(jGen:ℤ) = lEven-vStar+err ∧ err ≤ Cphase)
    (controls : ∀ x (hx : x ≠ 0), (rows x hx).basisShift ≤ old ∧
      (rows x hx).Lval ≤ ell ∧ (rows x hx).movingScalarVal ≤ cE ∧ (rows x hx).g ≤ gMax) :
    ∀ x, x ≠ 0 → center x ≠ 0 ∧
      (center x).valuation ≤ (budget (2*Co+Ce-vStar+Cphase) old ell cE gMax:ℤ) := by
  intro x hx
  obtain ⟨jGen,lEven,err,hgen,heven,hindex,herr⟩ := same39 x hx
  obtain ⟨hold,hL,hM,hG⟩ := controls x hx
  exact (rows x hx).upper _ old ell cE gMax
    (index_bound_of_same_39 jGen _ _ lEven vStar err Co Ce Cphase hgen heven hindex herr)
    hold hL hM hG

end OriginalRCNonzeroAddressBounds318

#print axioms OriginalRCNonzeroAddressBounds318.original_upper_after_same_39
