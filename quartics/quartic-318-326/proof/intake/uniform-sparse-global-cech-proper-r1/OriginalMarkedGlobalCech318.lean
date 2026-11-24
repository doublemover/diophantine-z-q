module
public import OriginalGlobalCechCup318
public import OriginalGlobalDualizingClass318
public import OriginalMarkedScalarLocalResidues318
public section
noncomputable section
namespace OriginalMarkedGlobalCech318
open Polynomial OriginalGlobalCechRemainder318 OriginalGlobalDualizingClass318
open OriginalSexticJetMarked318 OriginalMarkedScalarSeparableTrace318 OriginalSeparableSexticJet318
open OriginalUniformCentralTwistTransport318 OriginalUniformMarkedQMSurface318
open OriginalGlobalP1Residue318 OriginalGlobalCechOverlap318
variable {K:Type*} [Field K]
@[expose] def ordinaryQ (J:Data K) : K[X] := (J.relation 0).choose
theorem ordinary_relation (J:Data K) : J.G-J.remainder 0*J.F.derivative=J.F*ordinaryQ J := by
  unfold ordinaryQ
  simpa only [Fin.val_zero,pow_zero,one_mul] using (J.relation 0).choose_spec

@[expose] def detClass (J:Data K) : K :=
  let Z:=splittingCertificate J
  let m:=fun i=>traceClass K (actual Z i)
  m 0*m 2-(m 1)^2

theorem trace_both (J:Data K) (i:Fin 3) :
    algebraMap K J.F.SplittingField (traceClass K (actual (splittingCertificate J) i))=
      branchMoment (splittingCertificate J) i := by
  rw [counit,moment_eq_branch]

theorem computed (J:Data K) : detClass J=detMoment J := by
  unfold detClass
  simp only [counit]
  rfl

/-- Every actual rational scalar and fixed four radical marks: the quotient class of the
actual regular two-chart cup cocycle produces the normalized determinant. This isn't
an analytic PEL period comparison, nor the assertion that an arbitrary 'KS' map is it. -/
theorem from_original [CharZero K] (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343))
    (hv : v^2=5) :
    let d:=row (zCoord r₀ r₁ r₃)
    let R:=discRoot d v r₂
    let h:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
    let J:=sexticData d R (qCoeff d r₀ R) h.actual_laws h.marked
    rawI2 J.F/d.J*detClass J= -10080/(d.X*d.Y) := by
  dsimp only
  rw [computed]
  exact OriginalMarkedScalarSeparableTrace318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
end OriginalMarkedGlobalCech318
#print axioms OriginalMarkedGlobalCech318.trace_both
#print axioms OriginalMarkedGlobalCech318.from_original
