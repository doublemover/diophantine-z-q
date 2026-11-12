module
public import PELNormalizerOctagonOrbitSigns318
public section
noncomputable section
namespace PELNormalizerHalfCutOrbit318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELNormalizerOctagonAffine318 PELNormalizerOctagonStrata318
open PELNormalizerOctagonRealImages318 PELNormalizerOctagonOrbitSigns318
set_option maxHeartbeats 2500000

/-- After the actual center210 half-turn cut, the full arithmetic orbit
relation contains NO identifications except identity or horizontal
reflection on the actual upper-cut boundary. The boundary condition is
expressed intrinsically as bottom cut OR non-strict original octagon. -/
theorem no_hidden_halfcut_identifications (g : positiveNormalizer) (τ : HalfPlane)
    (hτ : inequalities (scaledFirst τ) (scaledSecond τ))
    (hg : inequalities (scaledFirst (baseAction g τ)) (scaledSecond (baseAction g τ)))
    (hY : 0≤scaledSecond τ) (hYg : 0≤scaledSecond (baseAction g τ)) :
    (scaledFirst (baseAction g τ),scaledSecond (baseAction g τ))=
      (scaledFirst τ,scaledSecond τ) ∨
    ((scaledFirst (baseAction g τ),scaledSecond (baseAction g τ))=
      (-scaledFirst τ,scaledSecond τ) ∧
      (scaledSecond τ=0 ∨ ¬strict (scaledFirst τ,scaledSecond τ))) := by
  obtain ⟨a,b,hab,hs⟩ := original_octagon_signs g τ hτ hg
  cases a <;> cases b <;> simp only [signR,ite_true,ite_false] at hab
  · right
    have hy : scaledSecond (baseAction g τ)=-scaledSecond τ := congrArg Prod.snd hab
    have hz : scaledSecond τ=0 := by linarith
    exact ⟨by simpa only [hz,neg_zero] using hab,Or.inl hz⟩
  · right
    refine ⟨hab,Or.inr ?_⟩
    intro h
    have hh := hs h
    cases hh
  · left
    have hy : scaledSecond (baseAction g τ)=-scaledSecond τ := congrArg Prod.snd hab
    have hz : scaledSecond τ=0 := by linarith
    simpa only [hz,neg_zero] using hab
  · exact Or.inl hab
end PELNormalizerHalfCutOrbit318
