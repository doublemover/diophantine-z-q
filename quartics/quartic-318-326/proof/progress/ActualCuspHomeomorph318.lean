module
public import HighQParameter318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318 HighQParameter318
namespace ActualCuspHomeomorph318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine height obtained from the proved reciprocal-j asymptotics. -/
@[expose] def height : ℝ := CuspOrbit318.exists_high_recovery.choose

theorem height_positive : 0<height := CuspOrbit318.exists_high_recovery.choose_spec.1

theorem recovery (tau:UpperHalfPlane) (htau:tau∈high height) :
    ReciprocalCuspCoordinate318.inverseGerm ((ActualQJ318.jInvariant tau)⁻¹)=
      Periodic.qParam 1 tau := CuspOrbit318.exists_high_recovery.choose_spec.2 tau htau

/-- The actual coordinate is a fixed function of the canonical quotient j-map,
not a choice of a logarithm branch or a chosen orbit representative. -/
@[expose] def coordinate (N:ℕ) : neighborhood N height → punctured height := fun u =>
  ⟨ReciprocalCuspCoordinate318.inverseGerm ((jMap N u)⁻¹),by
    obtain ⟨tau,htau,he⟩:=u.property
    change ReciprocalCuspCoordinate318.inverseGerm ((jMap N u.val)⁻¹)∈punctured height
    rw [←he,jMap_projection,recovery tau htau]
    exact qParam_maps height htau⟩

theorem coordinate_projection (N:ℕ) (tau:high height) :
    coordinate N (projection N height tau)=qMap height tau := by
  apply Subtype.ext
  exact recovery tau tau.property

theorem coordinate_comp_projection (N:ℕ) :
    coordinate N ∘ projection N height=qMap height := funext (coordinate_projection N)

theorem coordinate_bijective (N:ℕ) : Function.Bijective (coordinate N) := by
  constructor
  · intro u v huv
    obtain ⟨tau,rfl⟩:=projection_surjective N height u
    obtain ⟨sigma,rfl⟩:=projection_surjective N height v
    rw [coordinate_projection,coordinate_projection] at huv
    apply Subtype.ext
    exact CuspOrbit318.quotient_eq_of_q_eq N tau sigma (congrArg Subtype.val huv)
  · intro q
    obtain ⟨tau,htau⟩:=qMap_surjective height height_positive q
    exact ⟨projection N height tau,(coordinate_projection N tau).trans htau⟩

theorem coordinate_continuous (N:ℕ) : Continuous (coordinate N) := by
  apply (projection_quotient N height).continuous_iff.mpr
  rw [coordinate_comp_projection]
  exact qMap_continuous height

theorem coordinate_isOpenMap (N:ℕ) : IsOpenMap (coordinate N) := by
  intro S hS
  have he:coordinate N '' S=qMap height '' ((projection N height) ⁻¹' S) := by
    rw [←coordinate_comp_projection,Set.image_comp,
      (projection_surjective N height).image_preimage]
  rw [he]
  exact qMap_isOpenMap height _ (hS.preimage (projection_continuous N height))

/-- A genuine homeomorphism from an actual open neighborhood of the standard
infinity cusp in the uncompactified quotient to an actual punctured disc. -/
@[expose] def cuspHomeomorph (N:ℕ) : neighborhood N height ≃ₜ punctured height :=
  (Equiv.ofBijective (coordinate N) (coordinate_bijective N)).toHomeomorphOfContinuousOpen
    (coordinate_continuous N) (coordinate_isOpenMap N)

theorem cuspHomeomorph_projection (N:ℕ) (tau:high height) :
    cuspHomeomorph N (projection N height tau)=qMap height tau :=
  coordinate_projection N tau

/-- The genuine j-map has its actual qj expansion in this quotient cusp chart. -/
theorem coordinate_qj (N:ℕ) (u:neighborhood N height) :
    ActualQJ318.G (coordinate N u)=(coordinate N u:ℂ)*jMap N u := by
  obtain ⟨tau,rfl⟩:=projection_surjective N height u
  rw [coordinate_projection]
  exact ActualQJ318.G_qParam tau

theorem jMap_in_coordinate (N:ℕ) (u:neighborhood N height) :
    jMap N u=ActualQJ318.G (coordinate N u)/(coordinate N u:ℂ) := by
  rw [coordinate_qj]
  field_simp [(coordinate N u).property.1]

end ActualCuspHomeomorph318
