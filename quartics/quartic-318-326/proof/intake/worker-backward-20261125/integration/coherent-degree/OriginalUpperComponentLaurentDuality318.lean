module
public import OriginalUpperComponentLaurentResidue318

public section
noncomputable section
namespace OriginalUpperComponentLaurentDuality318

open LaurentPolynomial LaurentVectorFiltration318 LaurentTransitionBounds318
open OriginalUpperComponentLaurentResidue318
open scoped BigOperators
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- The true annihilator of the two affine restriction images. -/
def annihilator (e : V k n ≃ₗ[LaurentPolynomial k] V k n) : Submodule k (V k n) where
  carrier := {v | ∀ u ∈ LaurentCechFinite318.boundary e, residuePair u v = 0}
  zero_mem' := by
    intro u _
    rw [pair_comm, ← linearLeft_apply, map_zero]
  add_mem' := by
    intro v w hv hw u hu
    change ∀ u ∈ LaurentCechFinite318.boundary e, residuePair u v = 0 at hv
    change ∀ u ∈ LaurentCechFinite318.boundary e, residuePair u w = 0 at hw
    change residuePair u (v + w) = 0
    rw [pair_comm, ← linearLeft_apply, map_add, linearLeft_apply, linearLeft_apply,
      pair_comm v u, pair_comm w u, hv u hu, hw u hu, add_zero]
  smul_mem' := by
    intro a v hv u hu
    change ∀ u ∈ LaurentCechFinite318.boundary e, residuePair u v = 0 at hv
    change residuePair u (a • v) = 0
    rw [pair_comm, ← linearLeft_apply, map_smul, linearLeft_apply, pair_comm v u, hv u hu,
      smul_zero]

/-- The coefficient functional descends along the actual quotient map. -/
def descend (e : V k n ≃ₗ[LaurentPolynomial k] V k n) (v : annihilator e) :
    LaurentCechFinite318.H1 e →ₗ[k] k :=
  (LaurentCechFinite318.boundary e).liftQ (linearLeft v.1)
    (fun u hu => v.2 u hu)

@[simp]
theorem descend_on (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (v : annihilator e) (u : V k n) :
    descend e v ((LaurentCechFinite318.boundary e).mkQ u) = residuePair u v.1 := rfl

/-- This is the actual residue pairing, linear in its gluing coefficient. -/
def descendLinear (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    annihilator e →ₗ[k] (LaurentCechFinite318.H1 e →ₗ[k] k) where
  toFun := descend e
  map_add' v w := by
    apply LinearMap.ext
    intro y
    obtain ⟨u, rfl⟩ := (LaurentCechFinite318.boundary e).mkQ_surjective y
    change descend e (v + w) _ = descend e v _ + descend e w _
    simp only [descend_on, Submodule.coe_add]
    rw [pair_comm u (v.1 + w.1), ← linearLeft_apply, map_add, linearLeft_apply,
      linearLeft_apply, pair_comm v.1 u, pair_comm w.1 u]
  map_smul' a v := by
    apply LinearMap.ext
    intro y
    obtain ⟨u, rfl⟩ := (LaurentCechFinite318.boundary e).mkQ_surjective y
    change descend e (a • v) _ = a • descend e v _
    simp only [descend_on, Submodule.coe_smul]
    rw [pair_comm u (a • v.1), ← linearLeft_apply, map_smul, linearLeft_apply,
      pair_comm v.1 u]

/-- Perfect duality on the genuine finite Laurent Čech quotient, not its
completion, and not an assumed isomorphism with any dualizing sheaf. -/
def residueEquiv (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    annihilator e ≃ₗ[k] (LaurentCechFinite318.H1 e →ₗ[k] k) :=
  LinearEquiv.ofBijective (descendLinear e) (by
    constructor
    · intro v w h
      apply Subtype.ext
      funext i
      apply LaurentPolynomial.ext
      intro a
      let u := monomial (k := k) i (-1 - a)
      have he := congrArg
        (fun f : LaurentCechFinite318.H1 e →ₗ[k] k =>
          f ((LaurentCechFinite318.boundary e).mkQ u)) h
      change descend e v _ = descend e w _ at he
      simpa only [descend_on, u, pair_monomial, show -1 - (-1 - a) = a by omega] using he
    · intro f
      obtain ⟨v, hv, _⟩ := represents e f
      have hm : v ∈ annihilator e := by
        intro u hu
        rw [hv, Submodule.Quotient.eq_zero_iff_mem.mpr hu, map_zero]
      refine ⟨⟨v, hm⟩, LinearMap.ext fun y => ?_⟩
      obtain ⟨u, rfl⟩ := (LaurentCechFinite318.boundary e).mkQ_surjective y
      change descend e ⟨v, hm⟩ _ = f _
      rw [descend_on]
      exact hv u)

@[simp]
theorem residueEquiv_on (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (v : annihilator e) (u : V k n) :
    residueEquiv e v ((LaurentCechFinite318.boundary e).mkQ u) = residuePair u v.1 := rfl

end OriginalUpperComponentLaurentDuality318
