module
public import QuaternionicJointPeriodTopology318
public section
noncomputable section
namespace PELJointPeriodFamily318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicJointPeriodTopology318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELComplexPeriodSurface318
open DiscreteComplexPeriodAtlas318
set_option maxHeartbeats 1200000
abbrev ReferenceSurface := Surface (basePoint:ℂ)
abbrev Total := HalfPlane × ReferenceSurface

/-- The full original order lattices, not merely their spans, are carried
by the real period trivialization to the reference lattice. -/
theorem reference_lattice (τ : HalfPlane) :
    (Periods τ).map (referenceMap τ).toAddEquiv.toAddMonoidHom=Periods basePoint := by
  apply le_antisymm
  · rintro z ⟨w,⟨x,hx,rfl⟩,rfl⟩
    change referenceMap τ (period τ (representation x))∈Periods basePoint
    rw [referenceMap_period]
    exact ⟨x,hx,rfl⟩
  · rintro z ⟨x,hx,rfl⟩
    refine ⟨periodHom representation τ x,⟨x,hx,rfl⟩,?_⟩
    exact referenceMap_period τ (representation x)

@[expose] def fiberEquiv (τ : HalfPlane) : Surface τ ≃+ ReferenceSurface :=
  QuotientAddGroup.congr _ _ (referenceMap τ).toAddEquiv (reference_lattice τ)

/-- Each actual original quotient fiber is HOMEOMORPHIC to the corresponding
fiber in the joint family, using its existing quotient topology. -/
@[expose] def fiberHomeomorph (τ : HalfPlane) : Surface τ ≃ₜ ReferenceSurface where
  toEquiv := (fiberEquiv τ).toEquiv
  continuous_toFun := by
    rw [←(QuotientAddGroup.isOpenQuotientMap_mk (N:=Periods τ)).continuous_comp_iff]
    exact QuotientAddGroup.continuous_mk.comp
      (referenceMap τ).toLinearMap.toContinuousLinearMap.continuous
  continuous_invFun := by
    rw [←(QuotientAddGroup.isOpenQuotientMap_mk (N:=Periods basePoint)).continuous_comp_iff]
    exact QuotientAddGroup.continuous_mk.comp
      (referenceMap τ).symm.toLinearMap.toContinuousLinearMap.continuous

@[expose] def fixedProjection (p : Cover) : Total :=
  (p.1,QuotientAddGroup.mk' (Periods basePoint) p.2)
@[expose] def familyProjection (p : Cover) : Total := fixedProjection (realTrivialization.symm p)
@[expose] def baseProjection : Total → HalfPlane := Prod.fst

local instance : DiscreteTopology (Periods basePoint) :=
  PELOriginalPeriodLattice318.original_discrete basePoint basePoint.property

/-- Joint local covering charts are derived from the genuine real bundle
homeomorphism and reference lattice covering, not from fiberwise continuity. -/
theorem fixedProjection_localHomeomorph : IsLocalHomeomorph fixedProjection := by
  intro p
  obtain ⟨e,he,hq⟩ := quotient_localHomeomorph (Periods basePoint) p.2
  refine ⟨(OpenPartialHomeomorph.refl HalfPlane).prod e,⟨Set.mem_univ _,he⟩,?_⟩
  funext q
  exact Prod.ext rfl (congrFun hq q.2)

theorem familyProjection_localHomeomorph : IsLocalHomeomorph familyProjection :=
  fixedProjection_localHomeomorph.comp realTrivialization.symm.isLocalHomeomorph

theorem familyProjection_continuous : Continuous familyProjection :=
  familyProjection_localHomeomorph.continuous

theorem familyProjection_surjective : Function.Surjective familyProjection := by
  rintro ⟨τ,p⟩
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective (Periods basePoint) p
  refine ⟨realTrivialization (τ,z),?_⟩
  change fixedProjection (realTrivialization.symm (realTrivialization (τ,z)))=(τ,p)
  rw [Homeomorph.symm_apply_apply]
  exact Prod.ext rfl hz

theorem projection_fiber (τ : HalfPlane) (z : ComplexVectors) :
    familyProjection (τ,z)=(τ,fiberEquiv τ (QuotientAddGroup.mk' (Periods τ) z)) := rfl

theorem projection_over_base (p : Cover) : baseProjection (familyProjection p)=p.1 := rfl

/-- The equivalence relation of the JOINT projection on each fiber is
exactly the original order-period relation, including every lattice element. -/
theorem projection_eq_iff (τ : HalfPlane) (z w : ComplexVectors) :
    familyProjection (τ,z)=familyProjection (τ,w) ↔ z-w∈Periods τ := by
  rw [projection_fiber,projection_fiber]
  constructor
  · intro h
    have hh := (fiberEquiv τ).injective (congrArg Prod.snd h)
    exact QuotientAddGroup.eq_iff_sub_mem.mp hh
  · intro h
    apply Prod.ext
    · rfl
    · exact congrArg (fiberEquiv τ) (QuotientAddGroup.eq_iff_sub_mem.mpr h)

/-- The reference topological trivialization supplies compact fibers only;
it is deliberately not asserted to be holomorphic in the base. -/
theorem fiber_compact (τ : HalfPlane) : CompactSpace (Surface τ) :=
  PELComplexPeriodSurface318.surface_compact τ τ.property
end PELJointPeriodFamily318
