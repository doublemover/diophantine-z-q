module
public import SelectedFiniteDualityDJ318
public import SelectedWeightedExceptionalFiber318
public import SelectedCanonicalNefAdjunction318
public import SelectedIntegralSectionLine318
public import SelectedBlowupSameMinor318
public import SelectedBadLevelLocalDerivative318
public section
noncomputable section
open Polynomial NumberField
open SelectedNormalizationDualFunctional318 SelectedFiniteDualityDJ318
open SelectedWeightedExceptionalFiber318 SelectedCanonicalNefAdjunction318
open SelectedIntegralSectionLine318 SelectedBlowupSameMinor318
open SelectedJOneExactMinorLoss318
open scoped BigOperators TensorProduct

namespace SelectedSameWitnessFinitePipeline318

/-- Actual fiber and adjunction rows on the same regular resolution.
This is an input interface to geometry, not a realization theorem for
the actual divisors or a construction of any regular surface. -/
structure ExceptionalRows (ι : Type*) [Fintype ι] (P : ι → Prop) [DecidablePred P] where
  Q : ι → ι → ℝ
  mult : ι → ℝ
  symm : ∀ i j, Q i j = Q j i
  offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j
  multPos : ∀ i, 0 < mult i
  principal : ∀ i, (∑ j, Q i j*mult j) = 0
  outside : ι
  outsideNot : ¬P outside
  connected : ∀ i : Subtype P, Relation.ReflTransGen (edge Q) i.1 outside
  ordM : Subtype P → ℝ
  ordDJ : Subtype P → ℝ
  rest : Subtype P → ℝ
  K : Subtype P → ℝ
  d : Subtype P → ℝ
  genus : Subtype P → ℕ
  length : Subtype P → ℕ
  restNonneg : ∀ i, 0 ≤ rest i
  dPos : ∀ i, 0 < d i
  lengthPos : ∀ i, 0 < length i
  diag : ∀ i : Subtype P, Q i.1 i.1 = -d i*(length i:ℝ)
  adj : ∀ i : Subtype P, K i + Q i.1 i.1 = d i*(2*(genus i:ℝ)-2)
  noFirstKind : ∀ i, ¬(genus i = 0 ∧ length i = 1)
  canonicalRow : ∀ i : Subtype P,
    (∑ j : Subtype P, Q i.1 j.1 * (ordM j - ordDJ j)) + rest i = -K i

theorem ExceptionalRows.order_le {ι : Type*} [Fintype ι] {P : ι → Prop} [DecidablePred P]
    (r : ExceptionalRows ι P) : ∀ i, r.ordDJ i ≤ r.ordM i := by
  have hQ := restricted_negative_definite P r.Q r.mult r.symm r.offDiag r.multPos
    r.principal r.outside r.outsideNot r.connected
  exact exceptional_order_of_adjunction (fun i j : Subtype P => r.Q i.1 j.1)
    (fun i j h => r.offDiag i.1 j.1 (fun he => h (Subtype.ext he))) hQ
    r.ordM r.ordDJ r.rest r.K r.d r.genus r.length r.restNonneg r.dPos
    r.lengthPos r.diag r.adj r.noFirstKind r.canonicalRow


/-- The actual integral matrix is built from the stable Hodge basis
and restrictions to the selected section lines. Its generic equality
with the ordered mC is a producer premise, not a change of basis here. -/
@[expose] def stableEvaluationMatrix {O : Type*} [CommRing O] {g : ℕ}
    {Hod : Type*} [AddCommGroup Hod] [Module O Hod]
    {HMin : Fin g → Type*} [∀ i, AddCommGroup (HMin i)] [∀ i, Module O (HMin i)]
    (eMin : ∀ i, HMin i ≃ₗ[O] O) (basis : Module.Basis (Fin g) O Hod)
    (evalMin : ∀ i, Hod →ₗ[O] HMin i) : Matrix (Fin g) (Fin g) O :=
  fun i j => eMin i (evalMin i (basis j))

section FiniteEstimate
variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
local notation "B" => integralClosure R F
local notation "T" => normalizedComplementary (R:=R) (F:=F) K

variable {W V : Type*} [AddCommGroup W] [Module B W]
variable [AddCommGroup V] [Module F V] [Module B V]

variable {L : Type*} [Field L] [NumberField L] (v : FinitePlace L)
local notation "O" => integralAt v

/-- A single finite estimate for the M numerator on the actual
noncollision open. The field F is the common generic function field;
the section scalar extension uses L and never evaluates arbitrary F
elements at a point.

The comparison, rows, extension/pullback operation and stable Hodge
frames are genuine geometric inputs. The extension operation must
extend the SAME rational functional and evaluate on the SAME generic
dj at the selected arithmetic sections. It need not supply any
integral denominator or valuation inequality. -/
theorem finite_estimate
    {x : F} (hx : Algebra.adjoin K ({x} : Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (M : ℕ) (hM : 0 < M) {w : F} (hw : w ∈ Algebra.adjoin R ({x} : Set F))
    (denominator : aeval x p.derivative * w = (M:F))
    (cmp : T ≃ₗ[B] W) (generic : W →ₗ[B] V)
    (frame : F ≃ₗ[F] V) (dj : V) (hdj : frame 1 = dj)
    (same : ∀ z : T, generic (cmp z) = frame (z:F))
    {ι : Type*} [Fintype ι] {P : ι → Prop} [DecidablePred P]
    (rows : ExceptionalRows ι P)
    {g : ℕ} {HMin HRes : Fin g → Type*}
    [∀ i, AddCommGroup (HMin i)] [∀ i, Module O (HMin i)]
    [∀ i, AddCommGroup (HRes i)] [∀ i, Module O (HRes i)]
    (eMin : ∀ i, HMin i ≃ₗ[O] O) (eRes : ∀ i, HRes i ≃ₗ[O] O)
    (djMin : ∀ i, L ⊗[O] HMin i) (djRes : ∀ i, L ⊗[O] HRes i)
    (compare : ∀ i, HMin i →ₗ[O] HRes i)
    (compareDJ : ∀ i, djRes i = (compare i).baseChange L (djMin i))
    (regularFunctions : Fin g → Subring F)
    (specialize : ∀ i, regularFunctions i →+* L)
    (extendAndPull :
      ∀ f : W →ₗ[B] B,
        (∀ y, ((M:F) • frame.symm.toLinearMap) (generic y) = (f y:F)) →
        (∀ i, rows.ordDJ i ≤ rows.ordM i) →
        ∃ φ : ∀ i, HRes i →ₗ[O] O, ∀ i, ∃ a : regularFunctions i,
          (a:F) = ((M:F) • frame.symm.toLinearMap) dj ∧
          scalarEval (φ i) (djRes i) = specialize i a)
    (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
    {Hod : Type*} [AddCommGroup Hod] [Module O Hod]
    (basis : Module.Basis (Fin g) O Hod) (evalMin : ∀ i, Hod →ₗ[O] HMin i)
    (minFrame : baseMatrix v (stableEvaluationMatrix eMin basis evalMin) =
      Matrix.diagonal (fun i => scalarEval (eMin i).toLinearMap (djMin i)) * m * C) :
    -Real.log (v ((m.det*C.det)⁻¹)) ≤
      (g:ℝ)*(-Real.log (v (M:L))) -
        (-Real.log (v (baseMatrix v (stableEvaluationMatrix eMin basis evalMin)).det)) := by
  obtain ⟨f,hGeneric,hDJ,_⟩ := literal_generic_section hx hint p hp M hw denominator
    cmp generic frame dj hdj same
  obtain ⟨φ,hPoint⟩ := extendAndPull f hGeneric rows.order_le
  have hEval (i : Fin g) : scalarEval (φ i) (djRes i) = (M:L) := by
    obtain ⟨a,ha,hβ⟩ := hPoint i
    have h : a = (M : regularFunctions i) := by
      apply Subtype.ext
      change (a:F) = (M:F)
      exact ha.trans hDJ
    rw [hβ,h,map_natCast]
  let uMin : Fin g → L := fun i => scalarEval (eMin i).toLinearMap (djMin i)
  let c : Fin g → O := fun i => eRes i (compare i ((eMin i).symm 1))
  have hComp (i : Fin g) : scalarEval (eRes i).toLinearMap (djRes i) =
      (c i:L) * uMin i := by
    rw [compareDJ i]
    exact scalarEval_canonical_frame (eMin i) (eRes i) (compare i) (djMin i)
  have hClears (i : Fin g) : ∃ t : O, uMin i * algebraMap O L t = (M:L) := by
    obtain ⟨tZ,hZ⟩ := integral_ratio (φ i) (eRes i) (djRes i) (M:L) (hEval i)
    have hZ' : scalarEval (eRes i).toLinearMap (djRes i) * (tZ:L) = (M:L) := hZ
    obtain ⟨tMin,_,hMin⟩ := lift_integral_ratio v (c i) tZ (uMin i)
      (scalarEval (eRes i).toLinearMap (djRes i)) (M:L) (hComp i) hZ'
    exact ⟨tMin,hMin⟩
  have hM_ne : (M:L) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  exact SelectedBadLevelLocalDerivative318.one_place_budget v m C hm hC uMin
    (stableEvaluationMatrix eMin basis evalMin) minFrame (M:L) hM_ne hClears

end FiniteEstimate
end SelectedSameWitnessFinitePipeline318

#print axioms SelectedSameWitnessFinitePipeline318.ExceptionalRows.order_le
#print axioms SelectedSameWitnessFinitePipeline318.finite_estimate
