module
public import OpenSquaredChart318
public section
noncomputable section
namespace PELDescendedInertiaChart318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELCoarseInertiaCoordinate318 PELInertiaSquaredCoordinate318
open PELMaximalSquaredLocalFibers318 OpenQuotientSameFibers318 OpenSquaredChart318
set_option maxHeartbeats 1800000

variable (τ : HalfPlane) (U : Set UnlevelledBase) (hU : IsOpen U)
  (hsub : U⊆(inertiaChart τ).source)
  (hfib : ∀ x∈U,∀ y∈U,
    PELOriginalMaximalQuotient318.projection x=PELOriginalMaximalQuotient318.projection y ↔
    squaredCoordinate τ x=squaredCoordinate τ y)

theorem projection_image_quotient (U : Set UnlevelledBase) (hU : IsOpen U) :
    IsOpenQuotientMap (imageMap PELOriginalMaximalQuotient318.projection U) :=
  imageMap_openQuotient _ U PELOriginalMaximalQuotient318.projection_continuous.continuousOn
    (PELOriginalMaximalQuotient318.projection_open.comp hU.isOpenMap_subtype_val)

include hU hsub in
theorem square_quotient : IsOpenQuotientMap (imageMap (squaredCoordinate τ) U) :=
  square_image_quotient (inertiaChart τ) U hU hsub

include hfib in
theorem image_fibers : ∀ x y : U,
    imageMap PELOriginalMaximalQuotient318.projection U x=
      imageMap PELOriginalMaximalQuotient318.projection U y ↔
    imageMap (squaredCoordinate τ) U x=imageMap (squaredCoordinate τ) U y := by
  intro x y
  constructor
  · intro h
    apply Subtype.ext
    exact (hfib x x.property y y.property).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (hfib x x.property y y.property).mpr (congrArg Subtype.val h)

/-- The actual local squared coordinate DESCENDS to a homeomorphism
between OPEN subsets of the literal full quotient and the complex plane.
Its continuity and inverse continuity follow from actual quotient maps. -/
@[expose] def descendedChart :
    (PELOriginalMaximalQuotient318.projection '' U) ≃ₜ (squaredCoordinate τ '' U) :=
  homeomorph (imageMap PELOriginalMaximalQuotient318.projection U)
    (imageMap (squaredCoordinate τ) U) (projection_image_quotient U hU).isQuotientMap
    (square_quotient τ U hU hsub).isQuotientMap (image_fibers τ U hfib)

theorem descended_value (x : UnlevelledBase) (hx : x∈U) :
    (descendedChart τ U hU hsub hfib
      ⟨PELOriginalMaximalQuotient318.projection x,⟨x,hx,rfl⟩⟩:ℂ)=squaredCoordinate τ x := by
  have h := homeomorph_value (imageMap PELOriginalMaximalQuotient318.projection U)
    (imageMap (squaredCoordinate τ) U) (projection_image_quotient U hU).isQuotientMap
    (square_quotient τ U hU hsub).isQuotientMap (image_fibers τ U hfib) (⟨x,hx⟩:U)
  exact congrArg Subtype.val h

include hU in
theorem source_open : IsOpen (PELOriginalMaximalQuotient318.projection '' U) :=
  PELOriginalMaximalQuotient318.projection_open U hU

include hU hsub in
theorem target_open : IsOpen (squaredCoordinate τ '' U) :=
  square_image_open (inertiaChart τ) U hU hsub

theorem descended_center (hp : PELUnlevelledComplexBase318.projection τ∈U) :
    (descendedChart τ U hU hsub hfib
      ⟨PELOriginalMaximalQuotient318.projection (PELUnlevelledComplexBase318.projection τ),
        ⟨PELUnlevelledComplexBase318.projection τ,hp,rfl⟩⟩:ℂ)=0 := by
  rw [descended_value]
  simp [squaredCoordinate,chart_center]

/-- Every actual labeled fixed point has such a descended chart. All
local-domain, same-fiber, open-map and inverse-continuity inputs are supplied. -/
theorem exists_original_descended_chart (i : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ∈fixedLocus i) :
    ∃ U : Set UnlevelledBase,PELUnlevelledComplexBase318.projection τ∈U ∧
      IsOpen (PELOriginalMaximalQuotient318.projection '' U) ∧
      IsOpen (squaredCoordinate τ '' U) ∧
      ∃ e : (PELOriginalMaximalQuotient318.projection '' U) ≃ₜ (squaredCoordinate τ '' U),
        ∀ x (hx : x∈U),
          (e ⟨PELOriginalMaximalQuotient318.projection x,⟨x,hx,rfl⟩⟩:ℂ)=squaredCoordinate τ x := by
  obtain ⟨U,hU,hpU,hsub,hfib⟩ := original_squared_quotient_fibers i τ hp
  exact ⟨U,hpU,source_open U hU,target_open τ U hU hsub,
    descendedChart τ U hU hsub hfib,descended_value τ U hU hsub hfib⟩
end PELDescendedInertiaChart318
