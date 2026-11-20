module
public import ActualTwoDescentGaloisFixedRational318
public import OriginalRCTerminalCertificate318
public import Mathlib.GroupTheory.OrderOfElement
import all ActualTwoDescentGaloisFixedRational318
public section
noncomputable section

namespace ActualSelectedTraceOddEvidence318
open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
open OriginalRCTerminalCertificate318

local instance : DecidableEq Qbar := Classical.decEq _
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- This constructs the actual rational multiple after the even comparison,
before knowing whether it has finite order. -/
theorem descends (n : ℚ) (hn : n ≠ 0) (S : Point (algebraMap ℚ Qbar n)) (L : ℕ)
    (heven : ∀ σ : GalQ, L • (galoisPointHom σ n hn S - S) = 0) :
    ∃ R : Point n, rationalPointMap n hn R = L • S := by
  apply actual_fixed_point_rational n hn
  intro σ
  rw [map_nsmul]
  exact sub_eq_zero.mp (by simpa only [nsmul_sub] using heven σ)

theorem rationalMap_injective (n : ℚ) (hn : n ≠ 0) :
    Function.Injective (rationalPointMap n hn) :=
  ActualTwoDescentActualEllipticFieldMap318.actual_elliptic_field_map_injective
    (algebraMap ℚ Qbar) n hn

/-- The empty odd branch consumes the literal observed coefficient (O.7)
after the original L. Its finite detector is the composite of the actual
good-reduction and finite Kummer detector, if that arithmetic donor is
supplied; it is not obtained from the level-two Selmer coordinate. -/
structure EmptyOdd (n : ℚ) (hn : n ≠ 0) (S : Point (algebraMap ℚ Qbar n)) (L : ℕ) where
  M : ℕ
  C : Type
  [ringC : CommRing C]
  residue : ZMod (2^M) →+* C
  detector : Point n →+ ZMod (2^M)
  aOne : C
  c₀ : ℕ
  omegaN : ℕ
  phase : Cˣ
  compared : ∀ R : Point n, rationalPointMap n hn R = L • S →
    aOne = (c₀:C) * (2:C)^omegaN * (phase:C) * residue (detector R)
  visible : aOne ≠ 0
  killsTorsion : IsOfFinAddOrder S → L • S = 0

theorem empty_nontorsion (n : ℚ) (hn : n ≠ 0)
    (S : Point (algebraMap ℚ Qbar n)) (L : ℕ) (D : EmptyOdd n hn S L)
    (R : Point n) (hR : rationalPointMap n hn R = L • S) :
    ¬ IsOfFinAddOrder S := by
  letI : CommRing D.C := D.ringC
  intro h
  have hz : rationalPointMap n hn R = rationalPointMap n hn (0 : Point n) := by
    rw [hR,D.killsTorsion h,map_zero]
  have hR0 : R = 0 := rationalMap_injective n hn hz
  apply D.visible
  simp only [D.compared R hR,hR0,map_zero,mul_zero]

/-- Nonempty odd branch, tied to the *same* conductor-one trace. The
arithmetic source must construct the original finite certificate and show
that torsion of this exact trace zeros its corrected central coordinate.
The Boolean/constant-term contradiction is not an imported non-torsion
or rank promise. -/
structure NonemptyOdd (n : ℚ) (S : Point (algebraMap ℚ Qbar n)) where
  a : ℕ
  hK : ℕ
  cE : ℕ
  tK : ℕ
  dK : ℕ
  b : ℕ
  M : ℕ
  c : ℕ
  B : ℕ
  cert : Certificate b M c (poleCutoff dK M)
  hc : c ≤ detBudget a hK cE tK
  hM : max (detBudget a hK cE tK) (max (B+2*detBudget a hK cE tK) 0) < M
  hb : (poleCutoff dK M+2)*(2^M-1) < b
  upper : ∀ x, x ≠ 0 → cert.central x ≠ 0 ∧ (cert.central x).valuation ≤ (B:ℤ)
  sameTraceZero : IsOfFinAddOrder S → cert.central 0 = 0

theorem nonempty_nontorsion (n : ℚ)
    (S : Point (algebraMap ℚ Qbar n)) (D : NonemptyOdd n S) :
    ¬ IsOfFinAddOrder S := by
  intro h
  exact central_base_ne_zero_of_original_bounds D.a D.hK D.cE D.tK D.dK
    D.b D.M D.c D.B D.cert D.hc D.hM D.hb D.upper (D.sameTraceZero h)

inductive OddEvidence (n : ℚ) (hn : n ≠ 0) (S : Point (algebraMap ℚ Qbar n))
    (L : ℕ) : Prop
  | empty : EmptyOdd n hn S L → OddEvidence n hn S L
  | nonempty : NonemptyOdd n S → OddEvidence n hn S L

theorem nontorsion_of_odd_evidence (n : ℚ) (hn : n ≠ 0)
    (S : Point (algebraMap ℚ Qbar n)) (L : ℕ)
    (heven : ∀ σ : GalQ, L • (galoisPointHom σ n hn S - S) = 0)
    (odd : OddEvidence n hn S L) : ¬ IsOfFinAddOrder S := by
  cases odd with
  | empty D =>
    obtain ⟨R,hR⟩ := descends n hn S L heven
    exact empty_nontorsion n hn S L D R hR
  | nonempty D => exact nonempty_nontorsion n S D

end ActualSelectedTraceOddEvidence318

#print axioms ActualSelectedTraceOddEvidence318.empty_nontorsion
#print axioms ActualSelectedTraceOddEvidence318.nonempty_nontorsion
