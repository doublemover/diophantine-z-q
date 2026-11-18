module
public import ArithmeticStandardPeriodX318
public import ActualPrimitiveMarkingClassCount318
public import ActualJInvariant318
public section
noncomputable section
namespace ArithmeticPrimitiveOrbit318
open scoped MatrixGroups
open UpperHalfPlane OpenJComplexEvaluation318 TranscendentalJGenericFiber318
open UniformTranscendentalPrimitiveEquation318 MarkedPeriod318 EllipticTorsion318
open ModularTorsionTransport318 ModularCurveChange318

def weighted (τ:UpperHalfPlane) (P:(ModularWeierstrass318.curve τ).toAffine.Point) : ℂ :=
  (12*ModularForm.E₄ τ / ModularForm.E₆ τ)*valueX P

def branch (N:ℕ) [NeZero N] (τ:UpperHalfPlane) : ℂ := weighted τ (standardPoint N τ)

theorem weighted_transport (g:SL(2,ℤ)) (τ:UpperHalfPlane)
    (P:(ModularWeierstrass318.curve τ).toAffine.Point) :
    weighted (g•τ) (ModularTorusTransport318.pointAddEquiv g τ P)=weighted τ P := by
  let G := (Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g
  have h4 := E4_transform G ⟨g,rfl⟩ τ
  have h6 := E6_transform G ⟨g,rfl⟩ τ
  change ModularForm.E₄ (g•τ)=denom G τ^4*ModularForm.E₄ τ at h4
  change ModularForm.E₆ (g•τ)=denom G τ^6*ModularForm.E₆ τ at h6
  have hx : valueX (ModularTorusTransport318.pointAddEquiv g τ P)=denom G τ^2*valueX P := by
    cases P with
    | zero => change 0=_*0;simp
    | some x y hh => rfl
  rw [weighted,weighted,h4,h6,hx]
  by_cases h:ModularForm.E₆ τ=0
  · simp [h]
  · field_simp [denom_ne_zero G τ,h] <;> ring

theorem relabel_value (N:ℕ) [NeZero N] (g:SL(2,ℤ)) (τ:UpperHalfPlane) :
    weighted τ (torsionMap τ N (residueMap g N (standardLabel N)))=
      branch N (g⁻¹•τ) := by
  have he := weighted_transport g (g⁻¹•τ) (standardPoint N (g⁻¹•τ))
  unfold standardPoint at he
  rw [torsion_transport] at he
  simpa only [smul_inv_smul,branch,standardPoint] using he

/-- At FIXED arithmetic j every actual geometric primitive x is reached by
the same standard analytic branch on its integral modular orbit. -/
theorem all_values (N:ℕ) [NeZero N] (τ:UpperHalfPlane) (h:Admissible τ)
    (P:ArithmeticMarks N τ h) : ∃g:SL(2,ℤ), branch N (g•τ)=valueX P.val := by
  let e := OpenJAnalyticPoints318.pointAddEquiv N τ h
  let M : ActualPrimitiveMarkingClassCount318.Points τ N :=
    ⟨e P.val,(addOrderOf_injective e.toAddMonoidHom e.injective P.val).trans P.property⟩
  obtain ⟨g,hg⟩ := ActualPrimitiveMarkingClassCount318.relabel_onto τ N M
  have hp : torsionMap τ N (residueMap g N (standardLabel N))=e P.val :=
    congrArg Subtype.val hg
  refine ⟨g⁻¹,?_⟩
  rw [←relabel_value,hp]
  have ht := ArithmeticStandardPeriodX318.inverse_x N τ h (e P.val)
  change valueX (e.symm (e P.val))=weighted τ (e P.val) at ht
  simpa only [e.symm_apply_apply] using ht.symm

theorem j_transform (g:SL(2,ℤ)) (τ:UpperHalfPlane) :
    ActualQJ318.jInvariant (g•τ)=ActualQJ318.jInvariant τ :=
  ActualJInvariant318.modular_invariant ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g)
    ⟨g,rfl⟩ τ

theorem embedding_eq (N:ℕ) [NeZero N] (τ σ:UpperHalfPlane) (h:Admissible τ)
    (s:Admissible σ) (ht:Transcendental ℤ (ActualQJ318.jInvariant τ))
    (st:Transcendental ℤ (ActualQJ318.jInvariant σ))
    (hj:ActualQJ318.jInvariant τ=ActualQJ318.jInvariant σ) :
    embedding N τ h ht=embedding N σ s st := by
  have he : evaluation N τ h=evaluation N σ s := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
    simp only [evaluation,IsLocalization.Away.lift_comp,polynomialEval,hj]
  apply IsFractionRing.ringHom_ext (A:=OpenJModel318.Base N)
  intro b
  simpa only [embedding_base] using congrArg (fun f : OpenJModel318.Base N →+* ℂ=>f b) he

/-- Input is an analytic identity for a SINGLE standard branch. Output
is its specialization at ALL primitive arithmetic roots at the same j,
using the same rational-coefficient evaluation without a new assumption. -/
theorem specialize_all (N:ℕ) [NeZero N] (f:Polynomial (K N))
    (hvan:∀(σ:UpperHalfPlane) (s:Admissible σ) (st:Transcendental ℤ (ActualQJ318.jInvariant σ)),
      f.eval₂ (embedding N σ s st) (branch N σ)=0)
    (τ:UpperHalfPlane) (h:Admissible τ) (ht:Transcendental ℤ (ActualQJ318.jInvariant τ))
    (P:ArithmeticMarks N τ h) : f.eval₂ (embedding N τ h ht) (valueX P.val)=0 := by
  obtain ⟨g,hg⟩ := all_values N τ h P
  have hj := j_transform g τ
  have s : Admissible (g•τ) := by simpa only [Admissible,hj] using h
  have st : Transcendental ℤ (ActualQJ318.jInvariant (g•τ)) := by rwa [hj]
  have he := embedding_eq N (g•τ) τ s h st ht hj
  simpa only [he,hg] using hvan (g•τ) s st
end ArithmeticPrimitiveOrbit318
