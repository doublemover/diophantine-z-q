module
public import RationalFourRootFiber318
public import FourRootPointTorsor318
public import SourceGlobalAffine318
public import FiveContactProducer318
public section
noncomputable section
namespace RationalContactPoint318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318 Polynomial
set_option maxHeartbeats 600000
attribute [-instance] DivisionRing.toRatAlgebra
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)

/-- Literal coefficients of the source cover specialized at the supplied t. -/
@[expose] def parameters : Fin 4 → ℚ := fun i => Polynomial.aeval t (coefficient c i)

theorem parameters_eq (i : Fin 4) :
    parameters c t i = (c i : ℚ) * (t - LinearContactSquareclass318.contacts i) := by
  change Polynomial.aeval t (coefficient c i) = _
  simp [coefficient]

abbrev PointField := RationalFourRootFiber318.PointField (parameters c t)
local instance pointBase : Algebra R (PointField c t) :=
  ((algebraMap ℚ (PointField c t)).comp (Polynomial.aeval t).toRingHom).toAlgebra
local instance pointSMul : SMul R (PointField c t) := (pointBase c t).toSMul
local instance pointModule : Module R (PointField c t) := Algebra.toModule

/-- The actual original source-order point, not merely an unrelated tuple of roots. -/
@[expose] def sourcePoint : SourceOrder c →ₐ[R] PointField c t := by
  letI : Algebra R ℚ := (Polynomial.aeval t).toRingHom.toAlgebra
  letI : IsScalarTower R ℚ (PointField c t) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ℚ) (A := PointField c t) (fun _ => rfl)
  exact ((RationalFourRootFiber318.point (parameters c t)).restrictScalars R).comp
    (FourRootSignBaseChange318.coefficientMap (coefficient c) ℚ)

theorem sourcePoint_generator (i : Fin 4) :
    sourcePoint c t (FourRootOrderSigns318.generator (coefficient c) i) =
      RationalFourRootFiber318.root (parameters c t) i := by
  let _ : Algebra R ℚ := (Polynomial.aeval t).toRingHom.toAlgebra
  let _ : IsScalarTower R ℚ (PointField c t) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ℚ) (A := PointField c t) (fun _ => rfl)
  change RationalFourRootFiber318.point (parameters c t)
    (FourRootSignBaseChange318.coefficientMap (coefficient c) ℚ
      (FourRootOrderSigns318.generator (coefficient c) i)) = _
  rw [FourRootSignBaseChange318.coefficientMap_generator]
  rfl

/-- A genuine point of the already constructed whole proper contact model. -/
@[expose] def point : Spec (CommRingCat.of (PointField c t)) ⟶ ContactProjectiveModel318.model c :=
  Spec.map (CommRingCat.ofHom (sourcePoint c t).toRingHom) ≫
    SourceGlobalAffine318.chartEmbedding c

/-- The selected point maps to the original rational contact coordinate. -/
theorem point_over_coordinate : point c t ≫ ContactProjectiveModel318.modelMap c =
    Spec.map (CommRingCat.ofHom
      ((algebraMap ℚ (PointField c t)).comp (Polynomial.aeval t).toRingHom)) ≫
        JLineAtlas318.chart ℚ 1 := by
  unfold point ContactProjectiveModel318.modelMap
  rw [Category.assoc, SourceGlobalAffine318.chartEmbedding_over_contact_line,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (sourcePoint c t).commutes f

theorem point_field_degree_le : Module.finrank ℚ (PointField c t) ≤ 16 :=
  RationalFourRootFiber318.field_degree_le (parameters c t)

/-- Literal five-form avoidance supplies all four nonvanishing specialized
root coefficients at t = 32u/v. The infinity contact is covered by v ≠ 0. -/
theorem parameters_ne_of_forms (u v : ℤ)
    (hn : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    parameters c (32 * ((u : ℚ) / (v : ℚ))) i ≠ 0 := by
  obtain ⟨hv, h0, h1, h2401, hneg⟩ := FiveContactProducer318.source_contact_avoidance u v hn
  rw [parameters_eq]
  apply mul_ne_zero (c i).ne_zero
  fin_cases i
  · change 32 * ((u : ℚ) / (v : ℚ)) - 0 ≠ 0
    intro h
    exact h0 (by linarith)
  · change 32 * ((u : ℚ) / (v : ℚ)) - 32 ≠ 0
    intro h
    exact h1 (by linarith)
  · change 32 * ((u : ℚ) / (v : ℚ)) - 76832 ≠ 0
    intro h
    exact h2401 (by linarith)
  · change 32 * ((u : ℚ) / (v : ℚ)) - (-343) ≠ 0
    intro h
    exact hneg (by linarith)

theorem roots_ne_of_forms (u v : ℤ)
    (hn : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    RationalFourRootFiber318.root (parameters c (32 * ((u : ℚ) / (v : ℚ)))) i ≠ 0 :=
  RationalFourRootFiber318.root_ne_zero _ i (parameters_ne_of_forms c u v hn i)

/-- The actual contact source fiber over a noncontact rational coordinate
has exactly sixteen points over the constructed point field. -/
theorem source_fiber_card_of_forms (u v : ℤ)
    (hn : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) :
    Nat.card (SourceOrder c →ₐ[R] PointField c (32 * ((u : ℚ) / (v : ℚ)))) = 16 := by
  apply FourRootPointTorsor318.point_card (coefficient c) _
    (sourcePoint c (32 * ((u : ℚ) / (v : ℚ))))
  intro i
  change algebraMap ℚ (PointField c (32 * ((u : ℚ) / (v : ℚ))))
    (parameters c (32 * ((u : ℚ) / (v : ℚ))) i) ≠ 0
  simpa only [map_zero] using
    (algebraMap ℚ (PointField c (32 * ((u : ℚ) / (v : ℚ))))).injective.ne
      (parameters_ne_of_forms c u v hn i)

end RationalContactPoint318
