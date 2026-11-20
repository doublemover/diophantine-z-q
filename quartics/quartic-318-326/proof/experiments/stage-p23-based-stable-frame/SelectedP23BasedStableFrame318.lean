module
public import SelectedBasedSignCodifferent318
public import SelectedSameWitnessFinitePipeline318
public import ContactRadical318
public section
noncomputable section
open NumberField Polynomial
open SelectedDenominatorFreeSignChart318 SelectedSignIdealDescent318
open SelectedBasedSignCodifferent318 SelectedNormalizationDualFunctional318
open SelectedSameWitnessFinitePipeline318 SelectedIntegralSectionLine318
open SelectedJOneExactMinorLoss318
open scoped TensorProduct

namespace SelectedP23BasedStableFrame318

/-- Literally the level of the original ordered selected counterpoint. -/
@[expose] def selectedLevel (u w : ℤ) : ℕ :=
  2^28*3^6*(ContactRadical318.badProduct*ContactRadical318.radical u w)^2

theorem selectedLevel_pos (u w : ℤ) : 0 < selectedLevel u w := by
  unfold selectedLevel
  rw [ContactRadical318.bad_product_exact]
  have h := ContactRadical318.radical_pos u w
  positivity

section LocalUnit
variable {L : Type*} [Field L] [NumberField L] (v : FinitePlace L)

private theorem norm_nat_le_one (n : ℕ) : v (n:L) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  simpa only [map_natCast] using FinitePlace.norm_le_one L v.maximalIdeal (n:𝓞 L)

private theorem no_1728_collision {p : ℕ} (k : ℕ)
    (hc : (k:L)*(p:L) - (1727:L) = 1) (hp : v (p:L) < 1) :
    v (1727:L) = 1 := by
  apply le_antisymm (norm_nat_le_one v 1727)
  by_contra! h
  have hk : v ((k:L)*(p:L)) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg v _) (norm_nat_le_one v k)).trans_lt hp
  have hh := v.add_le ((k:L)*(p:L)) (-(1727:L))
  rw [← sub_eq_add_neg,hc,map_one,map_neg_eq_map] at hh
  exact (not_lt_of_ge hh) (max_lt hk h)

/-- At these actual finite places the literal J=1 section remains
in the J−1728 unit open, independently of wild level reduction. -/
theorem selected_one_unit
    (h : v (2:L) < 1 ∨ v (3:L) < 1) : v (1727:L) = 1 := by
  rcases h with h|h
  · exact no_1728_collision v (p:=2) 864 (by norm_num) h
  · exact no_1728_collision v (p:=3) 576 (by norm_num) h

end LocalUnit

section Generic
variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]
local notation "B" => integralClosure R F
local notation "C" => normalizedComplementary (R:=R) (F:=F) K

/-- The exact finite functional at the named original level and chosen
x. The data are the actual full kernel, actual contracted primitive
order and the same generic function field; no stable model is used. -/
theorem selected_literal_map (u w : ℤ) (J : R) [Nontrivial (XOpen J)]
    (I : Ideal (JSignChart J))
    (stable : ∀ z ∈ I, sign (algebraMap R[X] (XOpen J) (linearX J))
      (algebraMap R[X] (XOpen J) (cubicX J)) z ∈ I)
    [Algebra R (ActualSignOrder J I)] [Algebra R (ActualClosedOrder J I)]
    [IsScalarTower R (ActualSignOrder J I) (ActualClosedOrder J I)]
    {T : Type*} [CommRing T] [Algebra R T]
    (χ : T →ₐ[R] ActualClosedOrder J I) (surjT : Function.Surjective χ)
    (kill : ∀ ω : KaehlerDifferential R T, selectedLevel u w • ω = 0)
    (p : R[X]) (hp : aeval (chosenX J I) p = 0)
    (surj : Function.Surjective (aeval (R:=R) (chosenX J I)))
    (kernel : ∀ q : R[X], aeval (chosenX J I) q = 0 → p ∣ q)
    (φ : ActualSignOrder J I →ₐ[R] F)
    (hx : Algebra.adjoin K ({φ (chosenX J I)} : Set F) = ⊤)
    (hint : IsIntegral R (φ (chosenX J I)))
    (hmin : p.map (algebraMap R K) = minpoly K (φ (chosenX J I))) :
    ∃ c : C →ₗ[B] B, ∀ z : C, (c z:F) = (selectedLevel u w:F)*(z:F) := by
  obtain ⟨_,c,hc⟩ := chosenNormalization J I stable χ surjT (selectedLevel u w)
    kill p hp surj kernel φ hx hint hmin
  exact ⟨c,fun z => (hc z).1⟩

/-- Evaluation on the actual local ring at a selected generic point.
A value on the WHOLE function field F is neither needed nor allowed.
The map fixes the named evaluation field L and sends the literal J to 1. -/
structure SectionAtOne (L F : Type*) [Field L] [Field F] [Algebra L F] (j : F) where
  functions : Subalgebra L F
  containsJ : j ∈ functions
  evaluate : functions →ₐ[L] L
  j_one : evaluate ⟨j,containsJ⟩ = 1

variable {L : Type*} [Field L] [NumberField L] [Algebra L F]
variable (v : FinitePlace L)
local notation "O" => integralAt v
local notation "V" => KaehlerDifferential L F
variable {W : Type*} [AddCommGroup W] [Module B W]
variable [Module B V] [tower : IsScalarTower B F V]

/-- Compose selected_literal_map with the common same-witness frame
continuation, on the SAME literal Kähler differential D J and with
genuine J=1 evaluations. Geometry of the regular resolution, pullback
and stable Hodge line is still given as actual input. No wild model
is constructed by this source. -/
include tower in
theorem finite_selected_one_from_map (u w : ℤ) (J : R)
    (normalized : ∃ c : C →ₗ[B] B, ∀ z : C, (c z:F) = (selectedLevel u w:F)*(z:F))
    (cmp : C ≃ₗ[B] W) (generic : W →ₗ[B] V)
    (frame : F ≃ₗ[F] V) (hdj : frame 1 = KaehlerDifferential.D L F (algebraMap R F J))
    (same : ∀ z : C, generic (cmp z) = frame (z:F))
    {ι : Type*} [Fintype ι] {P : ι → Prop} [DecidablePred P]
    (rows : ExceptionalRows ι P)
    {g : ℕ} {HMin HRes : Fin g → Type*}
    [∀ i, AddCommGroup (HMin i)] [∀ i, Module O (HMin i)]
    [∀ i, AddCommGroup (HRes i)] [∀ i, Module O (HRes i)]
    (eMin : ∀ i, HMin i ≃ₗ[O] O) (eRes : ∀ i, HRes i ≃ₗ[O] O)
    (djMin : ∀ i, L ⊗[O] HMin i) (djRes : ∀ i, L ⊗[O] HRes i)
    (compare : ∀ i, HMin i →ₗ[O] HRes i)
    (compareDJ : ∀ i, djRes i = (compare i).baseChange L (djMin i))
    (points : Fin g → SectionAtOne L F (algebraMap R F J))
    (extendAndPull :
      ∀ f : W →ₗ[B] B,
        (∀ y, ((selectedLevel u w:F) • frame.symm.toLinearMap) (generic y) = (f y:F)) →
        (∀ i, rows.ordDJ i ≤ rows.ordM i) →
        ∃ φ : ∀ i, HRes i →ₗ[O] O, ∀ i, ∃ a : (points i).functions,
          (a:F) = ((selectedLevel u w:F) • frame.symm.toLinearMap)
            (KaehlerDifferential.D L F (algebraMap R F J)) ∧
          scalarEval (φ i) (djRes i) = (points i).evaluate a)
    (m Cb : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : Cb.det ≠ 0)
    {Hod : Type*} [AddCommGroup Hod] [Module O Hod]
    (basis : Module.Basis (Fin g) O Hod) (evalMin : ∀ i, Hod →ₗ[O] HMin i)
    (minFrame : baseMatrix v (stableEvaluationMatrix eMin basis evalMin) =
      Matrix.diagonal (fun i => scalarEval (eMin i).toLinearMap (djMin i)) * m * Cb) :
    -Real.log (v ((m.det*Cb.det)⁻¹)) ≤
      (g:ℝ)*(-Real.log (v (selectedLevel u w:L))) -
        (-Real.log (v (baseMatrix v (stableEvaluationMatrix eMin basis evalMin)).det)) := by
  obtain ⟨c,hc⟩ := normalized
  exact finite_estimate_from_map v (selectedLevel u w) (selectedLevel_pos u w) c hc
    cmp generic frame (KaehlerDifferential.D L F (algebraMap R F J)) hdj same
    rows eMin eRes djMin djRes compare compareDJ
    (fun i => (points i).functions.toSubring) (fun i => (points i).evaluate.toRingHom)
    (fun f hf ho => extendAndPull f hf ho)
    m Cb hm hC basis evalMin minFrame

end Generic
end SelectedP23BasedStableFrame318

#print axioms SelectedP23BasedStableFrame318.selected_one_unit
#print axioms SelectedP23BasedStableFrame318.selected_literal_map
#print axioms SelectedP23BasedStableFrame318.finite_selected_one_from_map
