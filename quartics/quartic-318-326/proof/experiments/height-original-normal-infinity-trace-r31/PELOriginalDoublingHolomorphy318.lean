module
public import ComplexLineLatticeMaps318
public section
noncomputable section
namespace PELOriginalDoublingHolomorphy318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalInvolutionComplexAtlas318
open PELOriginalDeckTwoTorsion318 PELOriginalDoublingFactor318 PELOriginalDoublingTopology318
open ComplexAffineFreeTranslation318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 3000000
variable (i : Fin 4) (L : AddSubgroup ℂ) [DiscreteTopology L]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (CharacterBase i) :=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i
variable (u : InvolutionBase i ≃ₜ Torus L)
variable (basis : RankTwoComplexHalfPeriods318.Coordinates ≃+ L)
variable (hlift : AffineLifts i L u.toEquiv)

/-- Holomorphy of the ACTUAL descended factor from the same original
local covering sheets; no independent analytic compatibility is assumed. -/
theorem factor_holomorphic (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (doublingFactor i L u.toEquiv basis hlift) := by
  intro q
  obtain ⟨p,rfl⟩ := toCharacterBase_surjective i q
  let q := toCharacterBase i p
  let e := sheetChart i p
  let c := chartAt ℂ q
  have hpE : p∈e.source := sheetChart_center i p
  have hqC : q∈c.source := mem_chart_source ℂ q
  have ht : c q∈e.target := by
    rw [←sheetChart_value i p p hpE]
    exact e.map_source hpE
  have hc := contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hqC
  have he := contMDiffAt_symm_of_mem_maximalAtlas (sheetChart_maximal i p) ht
  have hlocal := (ComplexLineLatticeMaps318.doubling_holomorphic L _).comp q
    ((hu _).comp q (he.comp q hc))
  apply hlocal.congr_of_eventuallyEq
  have hnear : ∀ᶠ x in 𝓝 q,c x∈e.target :=
    hc.continuousAt.eventually (e.open_target.mem_nhds ht)
  filter_upwards [c.open_source.mem_nhds hqC,hnear] with x hx hxt
  have hover : toCharacterBase i (e.symm (c x))=x :=
    (sheetChart_over i p (c x) hxt).trans (c.left_inv hx)
  exact (congrArg (doublingFactor i L u.toEquiv basis hlift) hover).symm.trans
    (doublingFactor_square i L u.toEquiv basis hlift (e.symm (c x)))

/-- The inverse is holomorphic by an EXPLICIT local half-period lift,
not by a supplied inverse-compatibility assumption or a bare homeomorphism. -/
theorem factor_inverse_holomorphic
    (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterHomeomorph i L u basis hlift).symm := by
  intro q
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L q
  let c := ComplexLineLatticeAtlas318.localChart L z
  let A : ℂ→ₗ[ℂ]ℂ := (1/2:ℂ) • LinearMap.id
  have hc0 : projection L z∈c.source := ComplexLineLatticeAtlas318.localChart_center L z
  have hc := contMDiffAt_of_mem_maximalAtlas (ComplexLineLatticeMaps318.chart_maximal L z) hc0
  have hA : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω A :=
    contMDiff_iff_contDiff.mpr A.toContinuousLinearMap.contDiff
  have hP := ComplexLineLatticeMaps318.projection_contMDiff L
  have hlocal := (toCharacterBase_holomorphic i _).comp (projection L z)
    ((huinv _).comp (projection L z)
      ((hP _).comp (projection L z) ((hA _).comp (projection L z) hc)))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hc0] with x hx
  let y := toCharacterBase i (u.symm (projection L (A (c x))))
  have hf : characterHomeomorph i L u basis hlift y=x := by
    change doublingFactor i L u.toEquiv basis hlift
      (toCharacterBase i (u.symm (projection L (A (c x)))))=x
    rw [doublingFactor_square,u.apply_symm_apply,←map_zsmul]
    have hhalf : (2:ℤ) • A (c x)=c x := by
      change (2:ℤ) • ((1/2:ℂ)*c x)=c x
      simp only [two_zsmul]
      ring
    rw [hhalf]
    have he := c.left_inv hx
    simpa only [ComplexLineLatticeAtlas318.localChart_symm] using he
  apply (characterHomeomorph i L u basis hlift).injective
  exact ((characterHomeomorph i L u basis hlift).apply_symm_apply x).trans hf.symm

/-- With a genuine biholomorphic uniformization of the original involution
curve and affine lifts, the actual character comparison is biholomorphic
and the original degree-four map is EXACTLY[2]. The source uniformization
and affine-lift theorem remain the only analytic producers here. -/
theorem original_biholomorphic_doubling
    (hu : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u)
    (huinv : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω u.symm) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterHomeomorph i L u basis hlift) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (characterHomeomorph i L u basis hlift).symm ∧
    ∀ p,characterHomeomorph i L u basis hlift (toCharacterBase i p)=(2:ℤ) • u p :=
  ⟨factor_holomorphic i L u basis hlift hu,
    factor_inverse_holomorphic i L u basis hlift huinv,
    original_doubling_square i L u basis hlift⟩
end PELOriginalDoublingHolomorphy318
