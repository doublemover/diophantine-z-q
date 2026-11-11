module
public import PELLevelOrbitKernel318
public section
noncomputable section
namespace PELFineLevelFibers318
open QuaternionicJointPeriodTopology318 PELJointNormOneAction318 PELNormOneBaseAction318
open PELPrincipalThreeCovering318 PELEffectiveNormOneAction318 PELUnlevelledComplexBase318
open PELEffectivePositiveLevel318 PELLevelOrbitKernel318
set_option maxHeartbeats 1600000

abbrev LevelFiber (τ : HalfPlane) := {x : ArithmeticBase // forgetLevel x=projection τ}

@[expose] def orbitPoint (τ : HalfPlane) (u : normOneUnits) : LevelFiber τ :=
  ⟨baseQuotient (u • τ),by
    rw [forgetLevel_square]
    exact covering.map_smul (effectiveMap u)⟩

theorem orbitPoint_eq_iff (τ : HalfPlane) (u v : normOneUnits) :
    orbitPoint τ u=orbitPoint τ v ↔ effectiveReduction u=effectiveReduction v := by
  constructor
  · intro h
    exact (orbit_eq_iff u v τ).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((orbit_eq_iff u v τ).mpr h)

theorem orbitPoint_surjective (τ : HalfPlane) : Function.Surjective (orbitPoint τ) := by
  intro p
  obtain ⟨σ,hσ⟩ := baseQuotient_surjective p.val
  have he : projection σ=projection τ := by
    rw [←forgetLevel_square,hσ]
    exact p.property
  obtain ⟨g,hg⟩ := covering.apply_eq_iff_mem_orbit.mp he
  obtain ⟨u,hu⟩ := effectiveMap_surjective g
  refine ⟨u,Subtype.ext ?_⟩
  change baseQuotient (u • τ)=p.val
  have hs : u • τ=σ := by
    rw [←hu] at hg
    exact hg
  rw [hs,hσ]

@[expose] def chosenLift (a : EffectivePositiveLevel) : normOneUnits :=
  (effectiveReduction_surjective a).choose

theorem chosenLift_spec (a : EffectivePositiveLevel) : effectiveReduction (chosenLift a)=a :=
  (effectiveReduction_surjective a).choose_spec

@[expose] def levelToFiber (τ : HalfPlane) (a : EffectivePositiveLevel) : LevelFiber τ :=
  orbitPoint τ (chosenLift a)

theorem levelToFiber_bijective (τ : HalfPlane) : Function.Bijective (levelToFiber τ) := by
  constructor
  · intro a b h
    have he := (orbitPoint_eq_iff τ (chosenLift a) (chosenLift b)).mp h
    simpa only [chosenLift_spec] using he
  · intro p
    obtain ⟨u,hu⟩ := orbitPoint_surjective τ p
    refine ⟨effectiveReduction u,?_⟩
    rw [←hu]
    apply (orbitPoint_eq_iff τ _ u).mpr
    exact chosenLift_spec _

/-- Every fiber of the actual forget-level map is the SAME effective
finite level group, not merely a matching cardinality from a model label. -/
@[expose] def levelFiberEquiv (τ : HalfPlane) : EffectivePositiveLevel ≃ LevelFiber τ :=
  Equiv.ofBijective (levelToFiber τ) (levelToFiber_bijective τ)

theorem every_fiber_card (τ : HalfPlane) : Nat.card (LevelFiber τ)=18 := by
  rw [←Nat.card_congr (levelFiberEquiv τ)]
  exact effective_level_card

/-- All unlevelled points are covered. This counts genuine set-theoretic
fibers; finite étale algebraic degree and compactness are not inferred. -/
theorem all_base_fibers (x : UnlevelledBase) :
    Nat.card {p : ArithmeticBase // forgetLevel p=x}=18 := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  exact every_fiber_card τ
end PELFineLevelFibers318
