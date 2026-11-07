module
public import KaehlerFrame318
public section
noncomputable section
namespace KaehlerSourceSections318
open KaehlerFrame318 VerticalSection318 IsLocalRing
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]
  (integral : KaehlerDifferential R B ≃ₗ[B] B)
  (generic : KaehlerDifferential R K ≃ₗ[K] K)
  (hne : KaehlerDifferential.map R R B K (integral.symm 1) ≠ 0)

@[expose] def derived : Derivation R K K :=
  frameDerivation (normalizedGenericFrame integral generic hne)

theorem derived_integral (b : B) :
    derived integral generic hne (algebraMap B K b) =
      algebraMap B K (frameDerivation integral b) :=
  field_derivation_on_integral integral _ (normalized_generator integral generic hne) b

theorem derived_preserves : ∀ b : B, ∃ c : B,
    derived integral generic hne (algebraMap B K b) = algebraMap B K c :=
  fun b => ⟨frameDerivation integral b,derived_integral integral generic hne b⟩

/-- The actual vertical source coefficients from Kähler frames, without a
supplied field derivation or integral-preservation hypothesis. -/
theorem vertical_sections [IsDiscreteValuationRing B] (p : ℕ)
    (hp : Irreducible (p : B)) (t : K) :
    (∃ b0 : B, algebraMap B K b0 = section0 (derived integral generic hne) t) ∧
    (∃ b1 : B, algebraMap B K b1 = section1 (derived integral generic hne) t) :=
  VerticalSection318.sections_integral _ (derived_preserves integral generic hne) p hp t

variable [IsLocalRing B] [Algebra ℚ B]

/-- Horizontal branch: actual differential generation supplies the needed
unit derivative coefficient, and actual Kähler frames supply preservation. -/
theorem finite_branch_sections (i : Fin 4) (u z : B) (hu : IsUnit u)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0)
    (hdz : Submodule.span B ({KaehlerDifferential.D R B z} : Set (KaehlerDifferential R B)) = ⊤) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 (derived integral generic hne)
        ((contacts i : K)+algebraMap B K u*(algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 (derived integral generic hne)
        ((contacts i : K)+algebraMap B K u*(algebraMap B K z)^2) := by
  exact UnitRamifiedIntegral318.finite_branch_sections _
    (derived_preserves integral generic hne) i u z (frameDerivation integral z)
    hu hz hz0 (unit_of_differential_generator integral z hdz)
    (derived_integral integral generic hne z)

/-- The same actual producer at infinity, in the original local ring. -/
theorem infinity_sections (u z : B) (hu : IsUnit u)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0)
    (hdz : Submodule.span B ({KaehlerDifferential.D R B z} : Set (KaehlerDifferential R B)) = ⊤) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 (derived integral generic hne)
        (1/(algebraMap B K u*(algebraMap B K z)^2)) ∧
      algebraMap B K c1 = section1 (derived integral generic hne)
        (1/(algebraMap B K u*(algebraMap B K z)^2)) := by
  exact UnitRamifiedIntegral318.infinity_sections _
    (derived_preserves integral generic hne) u z (frameDerivation integral z)
    hu hz hz0 (unit_of_differential_generator integral z hdz)
    (derived_integral integral generic hne z)

theorem regular_sections (t : B)
    (ht : ∀ i : Fin 4, residue B t ≠ residue B (contacts i : B))
    (hdt : Submodule.span B ({KaehlerDifferential.D R B t} : Set (KaehlerDifferential R B)) = ⊤) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 (derived integral generic hne) (algebraMap B K t) ∧
      algebraMap B K c1 = section1 (derived integral generic hne) (algebraMap B K t) := by
  exact UnitFrameHorizontal318.regular_sections _ t (frameDerivation integral t) ht
    (unit_of_differential_generator integral t hdt) (derived_integral integral generic hne t)

end KaehlerSourceSections318
