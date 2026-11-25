module

public import OriginalAllFiniteTrueAffineData318
public import OriginalCommonHodgeScalar318

@[expose] public section
noncomputable section

namespace OriginalYuanAllFinitePlaces318

open AlgebraicGeometry CategoryTheory
open NumberField SectionHeight318
open OriginalAllFiniteTrueAffineData318 OriginalFineArithmeticPlaceSwitch318
open OriginalThreeElevenNamedProperCentres318 OriginalCommonHodgeScalar318
open OriginalYuanNamedTraitFiniteRealization318 OriginalYuanMarkedSectionEvaluation318
open OriginalYuanActualFiniteSectionPayment318 OriginalExactLocalKSUnit318
open OriginalRetainedComplexZeroByPasting318 (specOf)
open OriginalMarkedTraitAffineSectionPull318 (chartRing)

universe u
variable {E : Type u} [Field E] [NumberField E]
variable (B : OriginalFineBases.{u}) (m : CommonMark (E:=E) B)
variable (HN CN : FrameNorms E) (t : E)
variable {H₀ C₀ : Type u}
  [AddCommGroup H₀] [AddCommGroup C₀] [Module E H₀] [Module E C₀]
variable {H C : Lane→Type u}
  [∀ n,AddCommGroup (H n)] [∀ n,AddCommGroup (C n)]
  [∀ n,Module E (H n)] [∀ n,Module E (C n)]
variable (h₀ : H₀≃ₗ[E]E) (c₀ : C₀≃ₗ[E]E)
variable (hT : ∀ n,H n≃ₗ[E]H₀) (cT : ∀ n,C n≃ₗ[E]C₀)
variable (Ψ : H₀→ₗ[E]C₀)
variable (noncontact : P t≠0)

abbrev coefficientH (n : Lane) (v : H n) : E := h₀ (hT n v)
abbrev coefficientC (n : Lane) (v : C n) : E := c₀ (cT n v)

/-- The two generic maps are transports of the one raw map. The actual
affine KS is compared to this transport by `At.raw_generic`, not by
another globally supplied same-scalar equation. -/
def lowerRaw (n : Lane) : H n→ₗ[E]C n :=
  (cT n).symm.toLinearMap.comp (Ψ.comp (hT n).toLinearMap)

theorem lowerRaw_reads (n : Lane) (z : H n) :
    cT n (lowerRaw hT cT Ψ n z)=Ψ (hT n z) := by
  change cT n ((cT n).symm (Ψ (hT n z)))=_
  exact (cT n).apply_symm_apply _

abbrev charts (w : FinitePlace E) :=
  At B m HN CN t H C (coefficientH h₀ hT) (coefficientC c₀ cT) (lowerRaw hT cT Ψ) w

abbrev k : E := heldScalar h₀ c₀ Ψ

variable (w : FinitePlace E) (d : charts B m HN CN t h₀ c₀ hT cT Ψ w)

/-- The literal chosen affine evaluation carries the same raw
scalar k for every tensor over this actual trait. The statement
does not receive a separately checked scalar formula at w. -/
theorem local_raw_read :
    letI : AddCommGroup d.M := d.addM
    letI : AddCommGroup d.N := d.addN
    letI : Module (chartRing d.U) d.M := d.moduleM
    letI : Module (chartRing d.U) d.N := d.moduleN
    ∀ z : ActualTensor w d.U d.affine (centreAt B m w) d.closed d.M,
    (d.canonicalCoeff (actualBaseChange w d.U d.affine (centreAt B m w) d.closed d.raw z):E)=
      (d.hodgeCoeff z:E)*k h₀ c₀ Ψ := by
  intro z
  rw [d.canonical_generic_read,d.raw_generic,d.hodge_generic_read]
  exact both_actual_lines_read_one_scalar h₀ c₀ hT cT Ψ (lowerRaw hT cT Ψ)
    (lowerRaw_reads hT cT Ψ) (lane w) (d.genericH z)

include noncontact in
/-- Both actual finite outputs are supplied on the uniquely extended
chosen fine mark before any archimedean input. -/
theorem on_actual_named_trait :
    Nonempty (OriginalFiveContactExactGauge318.FiniteImage HN CN (k h₀ c₀ Ψ) w) ∧
    (specOf (g w d.U d.affine (centreAt B m w) d.closed) ≫ d.affine.fromSpec =
      m.P33≫B.forget (lane w)) ∧
    (∀ i : Fin 2, w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*CN.finiteNorm w≤1) := by
  letI := d.fieldK
  letI := d.chartDomain
  letI := d.toStructuralField
  letI := d.fractionK
  letI := d.addM
  letI := d.addN
  letI := d.moduleM
  letI := d.moduleN
  have markRead : specOf (toHeldField w)≫centreAt B m w=m.P33≫B.forget (lane w) :=
    named_centre_retains B m (prime w)
  exact exact_v11_slots
    (w:=w) (U:=d.U) (hU:=d.affine) (centre:=centreAt B m w) (closed:=d.closed)
    (oldMark:=m.P33≫B.forget (lane w)) (keepsMark:=markRead)
    (frame:=d.frame) (H:=HN) (C:=CN) (a:=d.a) (b:=d.b) (k:=k h₀ c₀ Ψ)
    (ha:=d.a_ne) (hb:=d.b_ne) (hH:=d.hodgeNorm) (hC:=d.canonicalNorm)
    (η:=d.hodgeCoeff) (δ:=d.canonicalCoeff) (basis_read:=d.frame_read)
    (raw:=d.raw) (injective:=d.rawInj) (regular:=d.regular210) (rangeRaw:=d.rawRange)
    (readRaw:=local_raw_read B m HN CN t h₀ c₀ hT cT Ψ w d)
    (T:=d.T) (dT:=d.dT) (sections:=d.sections)
    (num:=d.numerator) (ratio:=d.ratio) (t:=t) (Tactual:=d.Tactual)
    (noncontact:=noncontact) (frameActual:=d.frameActual)

/-- Exact unchanged v1.1 finite types, over one pre-existing E.
The original archimedean and degree inputs remain separate. -/
structure Output (k' : E) where
  images : ∀ w,OriginalFiveContactExactGauge318.FiniteImage HN CN k' w
  paid : ∀ (w : FinitePlace E) (i : Fin 2),
    w (![(2765952000:E)^2,t*(2765952000:E)^2] i)*CN.finiteNorm w≤1

variable (D : ∀ w,charts B m HN CN t h₀ c₀ hT cT Ψ w)

include noncontact in
/-- The two lower integral charts are supplied around the
already constructed proper centres. This closes the all-place
assembly without another fine-point or height-degree choice. -/
def all_finite : Output HN CN t (k h₀ c₀ Ψ) where
  images w := Classical.choice
    (on_actual_named_trait B m HN CN t h₀ c₀ hT cT Ψ noncontact w (D w)).1
  paid w i :=
    (on_actual_named_trait B m HN CN t h₀ c₀ hT cT Ψ noncontact w (D w)).2.2 i

/-- Exact priority, including ramified primes in the actual E; the
membership test sees residue characteristic, not the value of v(3). -/
theorem level_eleven_exactly_above_three (w : FinitePlace E) :
    lane w=.eleven ↔ (3:𝓞 E)∈(prime w).asIdeal :=
  exactly_three (prime w)

end OriginalYuanAllFinitePlaces318
