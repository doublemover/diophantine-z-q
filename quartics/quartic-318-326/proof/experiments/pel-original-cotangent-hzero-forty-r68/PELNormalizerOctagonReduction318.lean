module
public import PELNormalizerOctagonDomain318
public import PELFullNormalizerAction318
public import PELOriginalOrbitHeightMinimum318
public import PELOriginalVertexStratum318
public section
noncomputable section
namespace PELNormalizerOctagonReduction318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELJointNormOneAction318 PELNormOneBaseAction318
open PELUnlevelledComplexBase318 PELUnlevelledNormalizerAction318
open PELOriginalElementaryAction318 PELFullNormalizerAction318
open PELOriginalOrbitHeightMinimum318 PELOriginalVertexStratum318
open PELNormalizerOctagonDomain318 PELNormalizerOctagonAffine318
set_option maxHeartbeats 2400000

/-- The finite parity reduction is used only AFTER minimizing each whole
original norm-one orbit. Thus the sixteen words are not mistaken for the
whole normalizer group or for all its height inequalities. -/
theorem full_original_minimum (τ : HalfPlane) :
    ∃ g : positiveNormalizer,∀ h : positiveNormalizer,
      height (baseAction g τ)≤height (baseAction h (baseAction g τ)) := by
  choose u hu using fun v : InertiaLabels318.V => original_minimum (baseAction (word v) τ)
  let p : InertiaLabels318.V → HalfPlane := fun v => u v • baseAction (word v) τ
  have hf : (Set.range p).Finite := Set.finite_range p
  have hn : (Set.range p).Nonempty := ⟨p 0,0,rfl⟩
  obtain ⟨σ,⟨v,hv⟩,hm⟩ := hf.isCompact.exists_isMinOn hn height_continuous.continuousOn
  subst σ
  let g : positiveNormalizer := originalNormalizer (u v)*word v
  have hg : baseAction g τ=p v := by rw [baseAction_mul,normalizer_action]; rfl
  refine ⟨g,fun h => ?_⟩
  let k := h*g
  let w := Multiplicative.toAdd (PELPositiveOrderNormalizer318.parity k)
  have hp : projection (baseAction k τ)=projection (baseAction (word w) τ) := by
    change coarseAction k (projection τ)=coarseAction (word w) (projection τ)
    exact congrFun (original_words_exhaust k) (projection τ)
  obtain ⟨z,hz⟩ := (projection_eq_iff_unit _ _).mp hp
  have hh : height (p w)≤height (baseAction k τ) := by
    have hb := hu w (z*(u w)⁻¹)
    have he : (z*(u w)⁻¹) • (u w • baseAction (word w) τ)=baseAction k τ := by
      rw [mul_smul,inv_smul_smul,hz]
    rw [he] at hb
    exact hb
  have hvw : height (p v)≤height (p w) := hm ⟨w,rfl⟩
  rw [hg]
  have hk : baseAction h (p v)=baseAction k τ := by rw [←hg,←baseAction_mul]
  rw [hk]
  exact hvw.trans hh

/-- Every orbit of the FULL original positive normalizer meets the actual
octagon. Both the reduction and the all-element inequalities are produced. -/
theorem every_original_orbit_meets_octagon (τ : HalfPlane) :
    ∃ g : positiveNormalizer,
      inequalities (scaledFirst (baseAction g τ)) (scaledSecond (baseAction g τ)) := by
  obtain ⟨g,hg⟩ := full_original_minimum τ
  exact ⟨g,(octagon_iff_full_minimum _).mpr hg⟩
end PELNormalizerOctagonReduction318
