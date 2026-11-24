module
public import OriginalGluedCechTrace318
public section
noncomputable section
namespace OriginalMarkedGluedCech318
open Polynomial OriginalActualQuadraticLaurent318 OriginalSparseQuadraticCharts318
open OriginalGlobalCechOverlap318 OriginalGlobalCechCup318 OriginalGlobalCechRemainder318
open OriginalGluedCechTrace318 OriginalGluedCechRestriction318 OriginalGluedDualizingTransition318
open OriginalMarkedGlobalCech318 OriginalSeparableSexticJet318 OriginalGlobalDualizingClass318
open OriginalMarkedScalarSeparableTrace318 OriginalUniformMarkedQMSurface318 OriginalUniformCentralTwistTransport318
variable {K:Type*} [Field K]

theorem pull_coeff (f:K[X]) (h:LaurentPolynomial K) : pull f h=2*leval f h*yy f := by
  rw [pull,construct,map_zero,zero_add,map_mul,down_base,down_y,map_mul,map_ofNat]

/-- In the Kähler module of the ORIGINAL principal localization, multiplying the
dualizing coefficient produced above by ξ is precisely the actual contracted form. -/
theorem actual_form (J:Data K) (s t:K) (hf: J.F=F s t) (h:LaurentPolynomial K)
    (c:Overlap (F s t)) (hc:2*c=1) :
    pull (F s t) h • OriginalGlobalCechCup318.xi J (xx (F s t)) (yy (F s t)) c =
      leval (F s t) h • KaehlerDifferential.D K (Overlap (F s t)) (xx (F s t)) := by
  have hy: (yy (F s t))^2= aeval (xx (F s t)) J.F := by rw [hf,relation_overlap]
  rw [pull_coeff,←(coframe J _ _ c hy hc).1,smul_smul]
  congr 1
  ring

/-- The right side is the actual traceable section, in the same named affine
ring as the left hand side, not an equality of an isolated Laurent coefficient.
The left side uses the difference of the two honest deformation lifts. -/
theorem actual_cup (J:Data K) (s t:K) (hf:J.F=F s t)
    (c:Overlap (F s t)) (hc:2*c=1) (k:Fin 3) :
    let f:=F s t
    let Z:=splittingCertificate J
    let x:=xx f
    let y:=yy f
    let iv:=OriginalSparseQuadraticCharts318.xi f
    let q:=ordinaryQ J
    let w:=y*iv^3
    let dv:=aeval iv (reflect 5 (P Z))
    let dw:=c*w*aeval iv (reflect 4 (Qstar Z q))
    let tx:= -aeval x (J.remainder 0)-(-x^2*dv)
    let ty:=c*y*aeval x q-(x^3*dw-3*y*x*dv)
    (x^(k:ℕ)*(2*(u J x y c*tx+v J x*ty))) • ((2:Overlap f) • OriginalGlobalCechCup318.xi J x y c)=
      pull f (form Z k) • OriginalGlobalCechCup318.xi J x y c := by
  have hy: (yy (F s t))^2= aeval (xx (F s t)) J.F := by rw [hf,relation_overlap]
  have e:=contraction J (ordinaryQ J) (ordinary_relation J) (V (F s t)) (yy _) c hy hc k
  exact e.trans (actual_form J s t hf (form (splittingCertificate J) k) c hc).symm

@[expose] def entry (J:Data K) (s t:K) (i:Fin 3) : K :=
  trace (F s t) (pull (F s t) (form (splittingCertificate J) i))
theorem entry_eq (J:Data K) (s t:K) (i:Fin 3) :
    entry J s t i=OriginalSexticJetMarked318.moment (splittingCertificate J) i := by
  rw [entry,read_pull,residue]
  unfold OriginalSexticJetMarked318.moment coef; ring

@[expose] def det (J:Data K) (s t:K) : K := entry J s t 0*entry J s t 2-(entry J s t 1)^2
theorem det_eq (J:Data K) (s t:K) : det J s t=detMoment J := by
  simp only [det,entry_eq]; rfl

/-- Both the actual affine scheme equations and the determinant of its explicit
two-affine dualizing counit are obtained on the same four-root mark. -/
theorem from_original [CharZero K] (x:ℚ) (r₀ r₁ r₂ r₃ v:K) (hx:x≠0)
    (h₀:r₀^2= -14*(119136*(x:K)^2)) (h₁:r₁^2= -6*(119136*(x:K)^2-32))
    (h₂:r₂^2=42*(119136*(x:K)^2-76832)) (h₃:r₃^2= -21*(119136*(x:K)^2+343))
    (hv:v^2=5) :
    let d:=row (zCoord r₀ r₁ r₃)
    let R:=discRoot d v r₂
    let H:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
    let J:=sexticData d R (qCoeff d r₀ R) H.actual_laws H.marked
    let s:=d.m+R
    let t:=d.m-R
    J.F=F s t ∧ G s t=reflect 6 J.F ∧ rawI2 J.F/d.J*det J s t= -10080/(d.X*d.Y) := by
  dsimp only
  constructor
  · exact (ordinary_eq _ _).symm
  constructor
  · exact (reciprocal_eq _ _).trans (congrArg (reflect 6) (ordinary_eq _ _))
  · rw [det_eq]
    exact OriginalMarkedScalarSeparableTrace318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
end OriginalMarkedGluedCech318
#print axioms OriginalMarkedGluedCech318.actual_cup
#print axioms OriginalMarkedGluedCech318.from_original
