module
public import ArithmeticPrimitiveOrbit318
public import AnalyticTranscendentalBranchDomain318
public import OpenJLocalComparison318
public section
noncomputable section
namespace ArithmeticBranchRepresentatives318
open UpperHalfPlane OpenJComplexEvaluation318 TranscendentalJGenericFiber318
open AnalyticTranscendentalBranchDomain318 ArithmeticPrimitiveOrbit318
open UniformTranscendentalPrimitiveEquation318
variable (N:ℕ) [NeZero N]
abbrev E (p:T) := embedding N p.val p.property.1 p.property.2
abbrev evB (p:T) := evaluation N p.val p.property.1

/-- Reindexing a representation by an equality on its arithmetic test set
never extends a numerical equality off that set. -/
private theorem congr_rep {a b:T→ℂ} (ha:Rep a) (h:∀p,a p=b p) : Rep b :=
  (funext h) ▸ ha

private theorem rep_J : Rep (fun p:T=>ActualQJ318.jInvariant p.val) := by
  apply congr_rep (rep_holo OpenJLocalComparison318.j
    (fun z hz=>OpenJLocalComparison318.j_analyticAt ⟨z,hz⟩))
  intro p
  simp [OpenJLocalComparison318.j]

theorem rep_poly (a:Polynomial ℤ) : Rep (fun p:T=>polynomialEval p.val a) := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simpa only [map_add] using rep_add ha hb
  | monomial n a =>
    apply congr_rep (rep_mul (rep_const (a:ℂ)) (rep_pow rep_J n))
    intro p
    simp [polynomialEval]

/-- No rational-function-field identification or meromorphic-function
field is postulated: clear the *two actual localizations* in succession. -/
theorem rep_base (a:OpenJModel318.Base N) : Rep (fun p:T=>evB N p a) := by
  obtain ⟨⟨f,s⟩,hs⟩ := IsLocalization.surj (Submonoid.powers (OpenJModel318.denominator N)) a
  have hu (p:T) : (polynomialEval p.val) s.val≠0 := by
    have hh := (IsLocalization.map_units (OpenJModel318.Base N) s).map (evB N p)
    simpa only [evB,evaluation,IsLocalization.Away.lift_eq] using hh.ne_zero
  apply congr_rep (rep_div (rep_poly f) (rep_poly s.val) hu)
  intro p
  apply (div_eq_iff (hu p)).mpr
  have hh := congrArg (evB N p) hs
  simpa only [map_mul,evB,evaluation,IsLocalization.Away.lift_eq] using hh.symm

theorem rep_field (a:K N) : Rep (fun p:T=>E N p a) := by
  obtain ⟨⟨f,s⟩,hs⟩ := IsLocalization.surj (nonZeroDivisors (OpenJModel318.Base N)) a
  have hu (p:T) : evB N p s.val≠0 :=
    (map_ne_zero_iff _ (evaluation_injective N p.val p.property.1 p.property.2)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  apply congr_rep (rep_div (rep_base N f) (rep_base N s.val) hu)
  intro p
  apply (div_eq_iff (hu p)).mpr
  simpa only [map_mul,E,evB,embedding_base] using (congrArg (E N p) hs).symm

private theorem rep_branch (hN:1<N) : Rep (fun p:T=>branch N p.val) := by
  let A : ℂ→ℂ := fun z=>ModularForm.E₄ (ofComplex z)
  let B : ℂ→ℂ := fun z=>ModularForm.E₆ (ofComplex z)
  let X : ℂ→ℂ := fun z=>LatticeInvariants318.xCoord (ofComplex z) (1/(N:ℂ))
  have ha : Holo A := (mdifferentiable_iff.mp
    (ModularForm.E (k:=4) (by norm_num)).holo').analyticOnNhd isOpen_upperHalfPlaneSet
  have hb : Holo B := (mdifferentiable_iff.mp
    (ModularForm.E (k:=6) (by norm_num)).holo').analyticOnNhd isOpen_upperHalfPlaneSet
  have hx : Holo X := fun z hz=>(StandardPeriodAnalytic318.weierstrass_analyticAt N hN
    ⟨z,hz⟩).div_const
  have hn (p:T) : B (p.val:ℂ)≠0 := by
    obtain ⟨_,hs⟩ := OpenJAnalyticPoints318.scaling_spec N p.val p.property.1
    change -ModularForm.E₆ p.val / 864=(_ : ℂ)^6*(fiber N p.val p.property.1).a₆ at hs
    intro hh
    have hz : ModularForm.E₆ p.val=0 := by simpa [B] using hh
    rw [hz] at hs
    apply mul_ne_zero (pow_ne_zero 6 (OpenJAnalyticPoints318.scaling N p.val p.property.1).ne_zero)
      (OpenJScalingAmbiguity318.fiber_a6_ne_zero N p.val p.property.1)
    simpa using hs.symm
  apply congr_rep (rep_mul (rep_div (rep_mul (rep_const 12) (rep_holo A ha)) (rep_holo B hb) hn)
    (rep_holo X hx))
  intro p
  have hh := ArithmeticStandardPeriodX318.standard N p.val p.property.1 hN
  have he := ArithmeticStandardPeriodX318.inverse_x N p.val p.property.1
    (MarkedPeriod318.standardPoint N p.val)
  simpa [A,B,X,branch,weighted] using hh.symm.trans he

theorem rep_specialize (hN:1<N) (f:Polynomial (K N)) :
    Rep (fun p:T=>f.eval₂ (E N p) (branch N p.val)) := by
  induction f using Polynomial.induction_on' with
  | add a b ha hb => simpa only [Polynomial.eval₂_add] using rep_add ha hb
  | monomial n a =>
    apply congr_rep (rep_mul (rep_field N a) (rep_pow (rep_branch N hN) n))
    intro p
    simp

end ArithmeticBranchRepresentatives318
