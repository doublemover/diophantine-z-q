module
public import ActualTwoDescentKummerFullKernel318
public section
noncomputable section
namespace ActualTwoDescentEllipticDoubleQuotient318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentKummerHom318 ActualTwoDescentKummerFullKernel318
variable [DecidableEq K]

lemma actual_kummer_ker_range (n : K) (hn : n ≠ 0) :
    (kummerHom n hn).ker=(powMonoidHom (α:=Multiplicative (Point n)) 2).range := by
  ext P
  change kummerClass n hn P.toAdd=1 ↔ ∃ Q : Multiplicative (Point n), Q^2=P
  rw [actual_kummer_kernel]
  constructor
  · rintro ⟨Q,hQ⟩
    refine ⟨Multiplicative.ofAdd Q,?_⟩
    rw [pow_two]
    exact congrArg Multiplicative.ofAdd hQ
  · rintro ⟨Q,hQ⟩
    refine ⟨Q.toAdd,?_⟩
    rw [pow_two] at hQ
    exact congrArg Multiplicative.toAdd hQ

abbrev DoubleQuotient (n : K) :=
  Multiplicative (Point n) ⧸ (powMonoidHom (α:=Multiplicative (Point n)) 2).range

/-- The actual elliptic quotient by doubles injects in the literal squareclass pair. -/
def ellipticKummerInjection (n : K) (hn : n ≠ 0) : DoubleQuotient n →* (SquareClass K × SquareClass K) :=
  (QuotientGroup.kerLift (kummerHom n hn)).comp
    (QuotientGroup.quotientMulEquivOfEq (actual_kummer_ker_range n hn).symm).toMonoidHom

lemma actual_elliptic_kummer_injective (n : K) (hn : n ≠ 0) :
    Function.Injective (ellipticKummerInjection n hn) :=
  (QuotientGroup.kerLift_injective (kummerHom n hn)).comp
    (QuotientGroup.quotientMulEquivOfEq (actual_kummer_ker_range n hn).symm).injective

lemma actual_elliptic_kummer_mk (n : K) (hn : n ≠ 0) (P : Point n) :
    ellipticKummerInjection n hn (QuotientGroup.mk (Multiplicative.ofAdd P))=kummerClass n hn P := rfl

end ActualTwoDescentEllipticDoubleQuotient318
