module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic
public section
noncomputable section
namespace FractionDerivation318
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]

/-- The actual square-zero jet of an integral relative derivation. -/
@[expose] def jet (d : Derivation R B B) : B →ₐ[R] TrivSqZeroExt K K where
  toFun b := (TrivSqZeroExt.inl (algebraMap B K b) : TrivSqZeroExt K K) + TrivSqZeroExt.inr (algebraMap B K (d b))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp [d.map_one_eq_zero]
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [d.leibniz, mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl', IsScalarTower.algebraMap_apply R B K]
    · simp [TrivSqZeroExt.algebraMap_eq_inl', d.map_algebraMap]

/-- All actual nonzero denominators have unit jets in the square-zero ring. -/
theorem jet_denominator_unit (d : Derivation R B B) (s : nonZeroDivisors B) :
    IsUnit (jet (K := K) d s) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  simpa [jet] using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (S := K) s.property)

/-- Actual localization, not a chosen formula on fraction representatives. -/
@[expose] def extendedJet (d : Derivation R B B) : K →ₐ[R] TrivSqZeroExt K K :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors B) (jet_denominator_unit d)

theorem extendedJet_integral (d : Derivation R B B) (b : B) :
    extendedJet (K := K) d (algebraMap B K b) = jet d b := by
  exact IsLocalization.lift_eq (jet_denominator_unit d) b

theorem extendedJet_fst (d : Derivation R B B) (x : K) :
    (extendedJet d x).fst = x := by
  have h : (TrivSqZeroExt.fstHom R K K).comp (extendedJet d) = AlgHom.id R K := by
    apply IsLocalization.algHom_ext (nonZeroDivisors B)
    ext b
    change (extendedJet d (algebraMap B K b)).fst = algebraMap B K b
    rw [extendedJet_integral]
    simp [jet]
  exact congrArg (fun f : K →ₐ[R] K => f x) h

/-- The actual fraction-field extension of the integral derivation. -/
@[expose] def extend (d : Derivation R B B) : Derivation R K K where
  toLinearMap := ((TrivSqZeroExt.sndHom K K).restrictScalars R).comp (extendedJet d).toLinearMap
  map_one_eq_zero' := by
    change (extendedJet d 1).snd = 0
    rw [map_one,TrivSqZeroExt.snd_one]
  leibniz' x y := by
    change (extendedJet d (x*y)).snd = x • (extendedJet d y).snd + y • (extendedJet d x).snd
    rw [map_mul,TrivSqZeroExt.snd_mul,extendedJet_fst,extendedJet_fst]
    simp [smul_eq_mul]
    ring

theorem extend_integral (d : Derivation R B B) (b : B) :
    extend (K := K) d (algebraMap B K b) = algebraMap B K (d b) := by
  change (extendedJet d (algebraMap B K b)).snd = _
  rw [extendedJet_integral]
  simp [jet]

/-- A derivation on the actual fraction field is determined on the integral ring. -/
theorem unique (d : Derivation R B B) (D : Derivation R K K)
    (hD : ∀ b : B, D (algebraMap B K b) = algebraMap B K (d b)) :
    D = extend d := by
  ext x
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective B x
  rw [D.leibniz_div, (extend (K := K) d).leibniz_div, hD, hD, extend_integral, extend_integral]

/-- Actual integral preservation comes from the constructed extension, not an assumption. -/
theorem preserves_integral (d : Derivation R B B) : ∀ b : B, ∃ c : B,
    extend (K := K) d (algebraMap B K b) = algebraMap B K c :=
  fun b => ⟨d b,extend_integral d b⟩

/-- The exact quotient rule on any genuine fraction representation. -/
theorem extend_fraction (d : Derivation R B B) (a b : B) :
    extend (K := K) d (algebraMap B K a / algebraMap B K b) =
      (algebraMap B K b)⁻¹ ^ 2 *
        (algebraMap B K b * algebraMap B K (d a) - algebraMap B K a * algebraMap B K (d b)) := by
  rw [(extend (K := K) d).leibniz_div, extend_integral, extend_integral]
  rfl

end FractionDerivation318
