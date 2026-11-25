module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic
public section
noncomputable section

namespace OriginalUpperR40PullbackChart318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
universe u

variable {B D E C : Scheme.{u}} (p : D ⟶ B) (r : E ⟶ B) (j : C ⟶ D)

abbrev P := pullback p r
abbrev Pj := pullback r (j ≫ p)
abbrev localRead : Pj p r j ⟶ C := pullback.snd _ _

/-- The actual base change of one R40 chart, with the field factor on
the left so the affine ring is precisely k tensor over old with chart. -/
@[expose] def lift : Pj p r j ⟶ P p r :=
  pullback.lift (localRead p r j ≫ j) (pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition])

@[reassoc, simp] theorem overChart :
    lift p r j ≫ pullback.fst p r = localRead p r j ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc, simp] theorem overField :
    lift p r j ≫ pullback.snd p r = pullback.fst r (j ≫ p) :=
  pullback.lift_snd _ _ _

theorem cartesian : IsPullback (lift p r j) (localRead p r j) (pullback.fst p r) j := by
  apply IsPullback.of_right ?_ (overChart p r j) (IsPullback.of_hasPullback p r).flip
  rw [overField]
  exact IsPullback.of_hasPullback r (j ≫ p)

/-- No scheme-valued point has to be selected on overlaps. This is the
image of the actual Cartesian lift, with the true downstairs point. -/
theorem range_eq :
    Set.range (lift p r j) = (pullback.fst p r) ⁻¹' Set.range j := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨localRead p r j v, ?_⟩
    have hw := congrArg (fun f : Pj p r j ⟶ D => f v) (overChart p r j)
    simpa only [Scheme.Hom.comp_apply] using hw.symm
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv, _⟩ :=
      Scheme.exists_preimage_of_isPullback (cartesian p r j) z y hy.symm
    exact ⟨v, hv⟩

/-- The genuine field pullback keeps the entire three-chart R40 cover. -/
theorem cover (c : C ⟶ D) {E₁ E₂ : Scheme.{u}} (a₁ : E₁ ⟶ D) (a₂ : E₂ ⟶ D)
    (h : ∀ x : D, x ∈ Set.range c ∨ x ∈ Set.range a₁ ∨ x ∈ Set.range a₂)
    (z : P p r) :
    z ∈ Set.range (lift p r c) ∨ z ∈ Set.range (lift p r a₁) ∨ z ∈ Set.range (lift p r a₂) := by
  simpa only [range_eq, Set.mem_preimage] using h (pullback.fst p r z)

omit p r j in
/-- One connected centre already fills the closure of this fibre. It
suffices that each outer line's single generic point lies in the
centre image, rather than constructing maps between different arms. -/
theorem connected_of_dense_arms {X C A₁ A₂ : Type u}
    [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace A₁] [TopologicalSpace A₂]
    [ConnectedSpace C]
    (c : C → X) (a₁ : A₁ → X) (a₂ : A₂ → X)
    (hc : Continuous c) (ha₁ : Continuous a₁) (ha₂ : Continuous a₂)
    (hcover : ∀ z : X, z ∈ Set.range c ∨ z ∈ Set.range a₁ ∨ z ∈ Set.range a₂)
    (t₁ : A₁) (t₂ : A₂)
    (ht₁ : IsGenericPoint t₁ (Set.univ : Set A₁))
    (ht₂ : IsGenericPoint t₂ (Set.univ : Set A₂))
    (hm₁ : a₁ t₁ ∈ Set.range c) (hm₂ : a₂ t₂ ∈ Set.range c) :
    ConnectedSpace X := by
  have ht {A : Type u} [TopologicalSpace A] (a : A → X) (ha : Continuous a)
      (t : A) (hg : IsGenericPoint t (Set.univ : Set A)) (hmem : a t ∈ Set.range c) :
      Set.range a ⊆ closure (Set.range c) := by
    rintro _ ⟨x, rfl⟩
    have hS := (hg.specializes (Set.mem_univ x)).map ha
    exact hS.mem_closed isClosed_closure (subset_closure hmem)
  have hU : closure (Set.range c) = Set.univ :=
    Set.eq_univ_of_forall (fun z => (hcover z).elim (fun hz => subset_closure hz)
      (fun h => h.elim (fun hz => ht a₁ ha₁ t₁ ht₁ hm₁ hz) (fun hz => ht a₂ ha₂ t₂ ht₂ hm₂ hz)))
  apply connectedSpace_iff_univ.mpr
  rw [← hU]
  exact (isConnected_range hc).closure

end OriginalUpperR40PullbackChart318

#print axioms OriginalUpperR40PullbackChart318.range_eq
#print axioms OriginalUpperR40PullbackChart318.cover
#print axioms OriginalUpperR40PullbackChart318.connected_of_dense_arms
