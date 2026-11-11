module
public import OriginalAffineUnitLogarithm318
public section
noncomputable section
namespace OriginalAffineLogarithmNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318 OriginalAffineUnitLogarithm318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
/-- Actual infinitesimal units commute with the actual thickened scheme map,
not an abstract coordinate-labelled map. Both projections are used. -/
lemma exp_naturality (a : Γ(Y,⊤)) :
    Units.map (map R p q f hf).appTop.hom.toMonoidHom (exp R q a) = exp R p (f.appTop a) := by
  rw [exp_original, exp_original]
  apply Units.ext
  change (map R p q f hf).appTop
    (1 + DualNumberInfinitesimalLines318.epsilon R q *
      (pullback.fst q (structureMap R)).appTop a) =
    1 + DualNumberInfinitesimalLines318.epsilon R p *
      (pullback.fst p (structureMap R)).appTop (f.appTop a)
  rw [map_add, map_one, map_mul, DualNumberCocycleNaturality318.epsilon_naturality,
    OriginalDualSectionLift318.coefficient_naturality]
/-- Every original reduced unit has a functorial logarithm. No replacement of
restriction maps by a convenient coordinate homomorphism is assumed. -/
lemma log_naturality (z : Γ(thickening R q,⊤)ˣ)
    (hz : (reduction R q).appTop (z : Γ(thickening R q,⊤)) = 1) :
    log R p (Units.map (map R p q f hf).appTop.hom.toMonoidHom z) = f.appTop (log R q z) := by
  have h := exp_naturality R p q f hf (log R q z)
  rw [exp_log R q z hz] at h
  rw [h, log_exp]
/-- The full actual multiplicative three-term transition law becomes the
additive three-term law, with all original pullback maps retained. -/
lemma transition_iff (a b c : Γ(Y,⊤)) :
    Units.map (map R p q f hf).appTop.hom.toMonoidHom (exp R q a) *
      Units.map (map R p q f hf).appTop.hom.toMonoidHom (exp R q b) =
      Units.map (map R p q f hf).appTop.hom.toMonoidHom (exp R q c) ↔
    f.appTop a + f.appTop b = f.appTop c := by
  rw [exp_naturality, exp_naturality, exp_naturality, ← exp_add]
  exact (exp_injective R p).eq_iff
end OriginalAffineLogarithmNaturality318
