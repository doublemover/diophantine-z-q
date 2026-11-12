module
public import ContactQuotientOverlapSelf318
public section
noncomputable section
namespace ContactQuotientTripleData318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (S : CommRingCat.{0}) [Algebra ℚ S] (n : ℕ)
/-- Independently defined WHOLE quotient on three original source charts. -/
abbrev Triple := {I : Ideal c a S n // Supported c a b S n I ∧ Supported c a d S n I}
@[expose] def first (x : Triple c a b d S n) : ContactQuotientOverlapEquiv318.Overlap c a b S n :=
  ⟨x.val,x.property.1⟩
@[expose] def second (x : Triple c a b d S n) : ContactQuotientOverlapEquiv318.Overlap c a d S n :=
  ⟨x.val,x.property.2⟩
@[expose] def rotate (x : Triple c a b d S n) : Triple c b d a S n :=
  ⟨transfer c a b S n x.val x.property.1,
    ContactQuotientTransferSupport318.forward c a b d S n x.val x.property.1 x.property.2,
    ContactQuotientTransferSupport318.reverse c a b S n x.val x.property.1⟩
lemma rotation_leg (x : Triple c a b d S n) : second c b d a S n (rotate c a b d S n x)=
    ContactQuotientOverlapEquiv318.equivalence c a b S n (first c a b d S n x) := rfl
/-- Period-three identity retains the literal whole ideal, not only
its support or a frame isomorphism class. -/
lemma rotation_cycle (x : Triple c a b d S n) :
    rotate c d a b S n (rotate c b d a S n (rotate c a b d S n x))=x := by
  apply Subtype.ext
  change transfer c d a S n
    (transfer c b d S n (transfer c a b S n x.val x.property.1) _) _=x.val
  rw [ContactQuotientTransferCocycle318.cocycle]
  exact ContactQuotientTransferRecovery318.inverse c a d S n x.val x.property.2
variable (T : CommRingCat.{0}) [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
@[expose] def map (x : Triple c a b d S n) : Triple c a b d T n :=
  ⟨ContactQuotientChartCoefficient318.extended c a S T φ n x.val,
    ContactQuotientChartCoefficient318.supported c a S T φ n x.val b x.property.1,
    ContactQuotientChartCoefficient318.supported c a S T φ n x.val d x.property.2⟩
lemma rotation_natural (x : Triple c a b d S n) : rotate c a b d T n (map c a b d S n T φ x)=
    map c b d a S n T φ (rotate c a b d S n x) := by
  apply Subtype.ext
  exact ContactQuotientTransferBaseChange318.natural c a b S T φ n x.val x.property.1
end ContactQuotientTripleData318
