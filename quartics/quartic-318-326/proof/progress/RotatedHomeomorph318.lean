module
public import RotatedProjection318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 RotatedProjection318
open scoped MatrixGroups
namespace RotatedHomeomorph318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def wReal (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : ℝ :=
  RotatedWidths318.width N (by omega) g

theorem wReal_pos (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : 0<wReal N hN g := by
  change 0<(RotatedWidths318.width N (by omega) g:ℝ)
  exact_mod_cast RotatedWidths318.width_positive N (by omega) g

/-- The actual descended width-q coordinate. Representative choice is eliminated
by the proved exact orbit classification in coordinate_projection. -/
@[expose] def coordinate (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    neighborhood N g→punctured (wReal N hN g) 2 := fun b=>
  qMap (wReal N hN g) 2 (wReal_pos N hN g) ((projection_surjective N g b).choose)

theorem coordinate_projection (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (tau:high 2) :
    coordinate N hN g (projection N g tau)=qMap (wReal N hN g) 2 (wReal_pos N hN g) tau := by
  let sigma:high 2:=(projection_surjective N g (projection N g tau)).choose
  have he:projection N g sigma=projection N g tau :=
    (projection_surjective N g (projection N g tau)).choose_spec
  apply Subtype.ext
  apply (RotatedCuspOrbit318.high_orbit_iff_q N hN g sigma tau (lt_trans (by norm_num : (1:ℝ)<2) sigma.property)
    (lt_trans (by norm_num : (1:ℝ)<2) tau.property)).mp
  exact congrArg Subtype.val he

theorem coordinate_comp_projection (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    coordinate N hN g ∘ projection N g=qMap (wReal N hN g) 2 (wReal_pos N hN g) :=
  funext (coordinate_projection N hN g)

theorem coordinate_bijective (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : Bijective (coordinate N hN g) := by
  constructor
  · intro u v huv
    obtain ⟨tau,rfl⟩:=projection_surjective N g u
    obtain ⟨sigma,rfl⟩:=projection_surjective N g v
    rw [coordinate_projection,coordinate_projection] at huv
    apply Subtype.ext
    exact (RotatedCuspOrbit318.high_orbit_iff_q N hN g tau sigma (lt_trans (by norm_num : (1:ℝ)<2) tau.property)
      (lt_trans (by norm_num : (1:ℝ)<2) sigma.property)).mpr (congrArg Subtype.val huv)
  · intro q
    obtain ⟨tau,htau⟩:=qMap_surjective (wReal N hN g) 2 (wReal_pos N hN g) (by norm_num) q
    exact ⟨projection N g tau,(coordinate_projection N hN g tau).trans htau⟩

theorem coordinate_continuous (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : Continuous (coordinate N hN g) := by
  apply (projection_quotient N g).continuous_iff.mpr
  rw [coordinate_comp_projection]
  exact qMap_continuous _ _ _

theorem coordinate_open (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : IsOpenMap (coordinate N hN g) := by
  intro S hS
  have he:coordinate N hN g '' S=
      qMap (wReal N hN g) 2 (wReal_pos N hN g) '' ((projection N g) ⁻¹' S) := by
    rw [←coordinate_comp_projection,Set.image_comp,(projection_surjective N g).image_preimage]
  rw [he]
  exact qMap_isOpenMap _ _ _ _ (hS.preimage (projection_continuous N g))

/-- A genuine punctured-disc chart at every rotated cusp of the actual Gamma1
quotient, with its own constructed conjugate width. -/
@[expose] def cuspHomeomorph (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) :
    neighborhood N g≃ₜpunctured (wReal N hN g) 2 :=
  (Equiv.ofBijective (coordinate N hN g) (coordinate_bijective N hN g)).toHomeomorphOfContinuousOpen
    (coordinate_continuous N hN g) (coordinate_open N hN g)

theorem cuspHomeomorph_projection (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (tau:high 2) :
    cuspHomeomorph N hN g (projection N g tau)=qMap (wReal N hN g) 2 (wReal_pos N hN g) tau :=
  coordinate_projection N hN g tau

end RotatedHomeomorph318
