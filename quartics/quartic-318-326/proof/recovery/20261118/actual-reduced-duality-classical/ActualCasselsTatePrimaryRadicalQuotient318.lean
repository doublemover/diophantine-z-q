module
public import ActualTwoDescentActualShaReducedDuality318
public section
noncomputable section
namespace ActualCasselsTatePrimaryRadicalQuotient318
variable {P T : Type*} [CommGroup P] [CommGroup T]
variable (D : Subgroup P) (B : P →* (P →* T))
variable (hr : ∀ x : P, D ≤ (B x).ker)
private def right : P →* ((P ⧸ D) →* T) where
  toFun x := QuotientGroup.lift D (B x) (hr x)
  map_one' := by
    apply MonoidHom.ext
    intro r
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective r
    exact congrArg (fun f : P →* T => f y) B.map_one
  map_mul' x x' := by
    apply MonoidHom.ext
    intro r
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective r
    exact congrArg (fun f : P →* T => f y) (B.map_mul x x')

variable (hl : ∀ x : P, (∀ y : P, B x y = 1) ↔ x ∈ D)

private theorem left_kernel : D ≤ (right D B hr).ker := by
  intro x hx
  apply MonoidHom.ext
  intro r
  obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective r
  exact (hl x).mpr hx y

/-- Descend both variables through the actual quotient subgroup, retaining
the original values on every pair of representatives. -/
def descended : (P ⧸ D) →* ((P ⧸ D) →* T) :=
  QuotientGroup.lift D (right D B hr) (left_kernel D B hr hl)

lemma descended_mk (x y : P) :
    descended D B hr hl (QuotientGroup.mk x) (QuotientGroup.mk y) = B x y := rfl

theorem descended_properties (ha : ∀ x : P, B x x = 1) :
    (∀ x : P ⧸ D, descended D B hr hl x x = 1) ∧
    (∀ x : P ⧸ D, (∀ y, descended D B hr hl x y = 1) → x = 1) := by
  constructor
  · intro r
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective r
    exact ha x
  · intro r
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective r
    intro hx
    exact (QuotientGroup.eq_one_iff x).mpr ((hl x).mp (fun y => hx (QuotientGroup.mk y)))

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedPrimary318
open ActualTwoDescentActualShaReducedDuality318
/-- Precise classical input: the full 2-primary pairing, zero against the
right divisible core and with exactly the left core as radical. No finiteness
of all of Sha or decision of the Prüfer alternative is assumed. -/
theorem reducedDuality_of_primary_pairing (n : ℚ) (hn : n ≠ 0)
    (B : actualShaPrimary n hn →*
      (actualShaPrimary n hn →* Multiplicative (AddCircle (1 : ℚ))))
    (hr : ∀ x, actualShaDivisibleCore n hn ≤ (B x).ker)
    (hl : ∀ x, (∀ y, B x y = 1) ↔ x ∈ actualShaDivisibleCore n hn)
    (ha : ∀ x, B x x = 1) : ActualReducedDuality n hn :=
  ⟨descended _ B hr hl,descended_properties _ B hr hl ha⟩
end ActualCasselsTatePrimaryRadicalQuotient318
