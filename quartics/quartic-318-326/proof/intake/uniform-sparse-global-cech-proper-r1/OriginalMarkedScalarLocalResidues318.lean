module
public import OriginalActualCechLifts318
public import OriginalReciprocalCechInfinity318
public import OriginalMarkedBranchPrincipalSum318
public section
noncomputable section
namespace OriginalMarkedScalarLocalResidues318
open OriginalBranchPlaneLocal318 OriginalBranchResidueLocal318 OriginalSexticJetMarked318
open OriginalMarkedBranchPrincipalSum318 OriginalSparseActualBranch318 OriginalUniversalSparsePolynomial318
open OriginalSeparableSexticJet318 OriginalMarkedScalarSeparableTrace318
open OriginalUniformCentralTwistTransport318 OriginalUniformMarkedQMSurface318
/-- All six labelled local rings of the true sparse curve have their uniformizer
verified: there is no simpleness or local stalk hypothesis supplied by the caller. -/
theorem uniform_at_six {K L : Type*} [Field K] [Field L] [Algebra K L]
    (J : Certificate K L) (s t : K) (hF : J.F=sextic s t) (p : Fin 6) :
    let a:=algebraMap K L s
    let b:=algebraMap K L t
    let φ:=ev a b (J.labels p) (branch_point J s t hF p)
    IsLocalRing.maximalIdeal (stalk (I:=ideal a b) φ)=
      Ideal.span ({toLocal φ (OriginalUniformSparseAffineModel318.y a b)}:Set (stalk φ)) :=
  branch_uniformizer _ _ _ _ (partial_ne J s t hF p)

theorem on_sheet {K : Type*} [Field K] [CharZero K] (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) :
    let J:=sexticData d R u h hh
    let Z:=splittingCertificate J
    let σ:=algebraMap K J.F.SplittingField
    σ (rawI2 J.F/d.J) * determinant Z (d.m+R) (d.m-R) rfl = σ (-10080/(d.X*d.Y)) := by
  let J:=sexticData d R u h hh
  let Z:=splittingCertificate J
  let σ:=algebraMap K J.F.SplittingField
  have hZ : Z.F=sextic (d.m+R) (d.m-R) := rfl
  have hc := det_is_raw Z (d.m+R) (d.m-R) hZ
  calc
    _ = σ (rawI2 J.F/d.J)*σ (rawB Z) := congrArg (fun q=>σ (rawI2 J.F/d.J)*q) hc
    _ = σ (rawI2 J.F/d.J*rawB Z) := (map_mul σ _ _).symm
    _ = _ := congrArg σ (trace_on_sheet d R u h hh)

/-- Every original scalar and root quadruple: literal sum of the specialized
regular logarithmic coefficients on the ORIGINAL six branch stalks. This is
the algebraic local-to-numerical part of the Serre pairing, not a postulated
comparison with an analytically defined Hodge isometry. -/
theorem from_original {K : Type*} [Field K] [CharZero K] (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) (hv : v^2=5) :
    let d:=row (zCoord r₀ r₁ r₃)
    let R:=discRoot d v r₂
    let h:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
    let J:=sexticData d R (qCoeff d r₀ R) h.actual_laws h.marked
    let Z:=splittingCertificate J
    let σ:=algebraMap K J.F.SplittingField
    σ (rawI2 J.F/d.J) * determinant Z (d.m+R) (d.m-R) rfl = σ (-10080/(d.X*d.Y)) :=
  on_sheet _ _ _ _ _
end OriginalMarkedScalarLocalResidues318
#print axioms OriginalMarkedScalarLocalResidues318.uniform_at_six
#print axioms OriginalMarkedScalarLocalResidues318.from_original
