module
public import RotatedProjection318
public import ActualThreeCuspOrbit318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 RotatedProjection318
open scoped MatrixGroups
namespace ActualThreeCuspHomeomorph318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def wReal (g:SL(2,ℤ)) : ℝ :=
  RotatedWidths318.width 3 (by decide) g

theorem wReal_pos (g:SL(2,ℤ)) : 0<wReal g := by
  change 0<(RotatedWidths318.width 3 (by decide) g:ℝ)
  exact_mod_cast RotatedWidths318.width_positive 3 (by decide) g

/-- The actual descended width-q coordinate. Representative choice is eliminated
by the proved exact orbit classification in coordinate_projection. -/
@[expose] def coordinate (g:SL(2,ℤ)) :
    neighborhood 3 g→punctured (wReal g) 2 := fun b=>
  qMap (wReal g) 2 (wReal_pos g) ((projection_surjective 3 g b).choose)

theorem coordinate_projection (g:SL(2,ℤ)) (tau:high 2) :
    coordinate g (projection 3 g tau)=qMap (wReal g) 2 (wReal_pos g) tau := by
  let sigma:high 2:=(projection_surjective 3 g (projection 3 g tau)).choose
  have he:projection 3 g sigma=projection 3 g tau :=
    (projection_surjective 3 g (projection 3 g tau)).choose_spec
  apply Subtype.ext
  apply (ActualThreeCuspOrbit318.high_orbit_iff_q g sigma tau (lt_trans (by norm_num : (1:ℝ)<2) sigma.property)
    (lt_trans (by norm_num : (1:ℝ)<2) tau.property)).mp
  exact congrArg Subtype.val he

theorem coordinate_comp_projection (g:SL(2,ℤ)) :
    coordinate g ∘ projection 3 g=qMap (wReal g) 2 (wReal_pos g) :=
  funext (coordinate_projection g)

theorem coordinate_bijective (g:SL(2,ℤ)) : Bijective (coordinate g) := by
  constructor
  · intro u v huv
    obtain ⟨tau,rfl⟩:=projection_surjective 3 g u
    obtain ⟨sigma,rfl⟩:=projection_surjective 3 g v
    rw [coordinate_projection,coordinate_projection] at huv
    apply Subtype.ext
    exact (ActualThreeCuspOrbit318.high_orbit_iff_q g tau sigma (lt_trans (by norm_num : (1:ℝ)<2) tau.property)
      (lt_trans (by norm_num : (1:ℝ)<2) sigma.property)).mpr (congrArg Subtype.val huv)
  · intro q
    obtain ⟨tau,htau⟩:=qMap_surjective (wReal g) 2 (wReal_pos g) (by norm_num) q
    exact ⟨projection 3 g tau,(coordinate_projection g tau).trans htau⟩

theorem coordinate_continuous (g:SL(2,ℤ)) : Continuous (coordinate g) := by
  apply (projection_quotient 3 g).continuous_iff.mpr
  rw [coordinate_comp_projection]
  exact qMap_continuous _ _ _

theorem coordinate_open (g:SL(2,ℤ)) : IsOpenMap (coordinate g) := by
  intro S hS
  have he:coordinate g '' S=
      qMap (wReal g) 2 (wReal_pos g) '' ((projection 3 g) ⁻¹' S) := by
    rw [←coordinate_comp_projection,Set.image_comp,(projection_surjective 3 g).image_preimage]
  rw [he]
  exact qMap_isOpenMap _ _ _ _ (hS.preimage (projection_continuous 3 g))

/-- A genuine punctured-disc chart at every rotated cusp of the actual Gamma1
quotient, with its own constructed conjugate width. -/
@[expose] def cuspHomeomorph (g:SL(2,ℤ)) :
    neighborhood 3 g≃ₜpunctured (wReal g) 2 :=
  (Equiv.ofBijective (coordinate g) (coordinate_bijective g)).toHomeomorphOfContinuousOpen
    (coordinate_continuous g) (coordinate_open g)

theorem cuspHomeomorph_projection (g:SL(2,ℤ)) (tau:high 2) :
    cuspHomeomorph g (projection 3 g tau)=qMap (wReal g) 2 (wReal_pos g) tau :=
  coordinate_projection g tau

end ActualThreeCuspHomeomorph318
