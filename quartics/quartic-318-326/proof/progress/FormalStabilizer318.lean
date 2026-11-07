module
public import TameCoordinate318
public section
noncomputable section
namespace FormalStabilizer318
open PowerSeries
set_option maxHeartbeats 0
variable {k G:Type*} [Field k] [Group G]

/-- An actual formal-coordinate action, with the composition law on power
series rather than an assumed faithful tangent representation. -/
structure Action (G k:Type*) [Group G] [Field k] where
  series:G→k⟦X⟧
  constant:∀g,(series g).constantCoeff=0
  identity:series 1=X
  composition:∀g h,series (g*h)=(series g).subst (series h)
  faithful:Function.Injective series

@[expose] def Action.tangent (A:Action G k) : G→*k where
  toFun g:=coeff 1 (A.series g)
  map_one':=by rw [A.identity];simp
  map_mul' g h:=by rw [A.composition,TameCoordinate318.coeff_one_subst _ _ (A.constant h)]

theorem Action.period_two (A:Action G k) (g:G) (hg:g*g=1) :
    (PowerSeries.subst (A.series g))^[2] (X:k⟦X⟧)=X := by
  rw [Function.iterate_succ_apply',Function.iterate_succ_apply',Function.iterate_zero_apply]
  rw [PowerSeries.subst_X (HasSubst.of_constantCoeff_zero' (A.constant g)),
    ←A.composition,hg,A.identity]

/-- A tame involution acting trivially on the tangent is the identity. -/
theorem Action.eq_one_of_tangent_one (A:Action G k) (hchar:(2:k)≠0)
    (g:G) (hg:g*g=1) (ht:A.tangent g=1) : g=1 := by
  apply A.faithful
  rw [A.identity]
  exact TameCoordinate318.finite_substitution_tangent_one (A.series g) (A.constant g)
    ht 2 hchar (A.period_two g hg)

/-- For an exponent-two stabilizer, faithful action on formal coordinates
forces an injective tangent character; it is not an input assumption. -/
theorem Action.tangent_injective (A:Action G k) (hchar:(2:k)≠0)
    (hperiod:∀g:G,g*g=1) : Function.Injective A.tangent := by
  apply (injective_iff_map_eq_one A.tangent).mpr
  intro g hg
  exact A.eq_one_of_tangent_one hchar g (hperiod g) hg

theorem Action.tangent_sign (A:Action G k) (hperiod:∀g:G,g*g=1) (g:G) :
    A.tangent g=1 ∨ A.tangent g= -1 := by
  have hs:A.tangent g*A.tangent g=1 := by rw [←map_mul,hperiod,map_one]
  have hf:(A.tangent g-1)*(A.tangent g+1)=0 := by
    calc
      _ = A.tangent g*A.tangent g-1 := by ring
      _ = 0 := by rw [hs];ring
  rcases mul_eq_zero.mp hf with h|h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The precise local group-size consequence used by the five-contact
Atkin–Lehner quotient: a faithful tame exponent-two stabilizer has at most2 elements. -/
theorem Action.card_le_two [Fintype G] (A:Action G k) (hchar:(2:k)≠0)
    (hperiod:∀g:G,g*g=1) : Fintype.card G≤2 := by
  classical
  let S:Finset k:={1,-1}
  let f:G→S:=fun g=>⟨A.tangent g,by simpa [S] using A.tangent_sign hperiod g⟩
  have hi:Function.Injective f:=by
    intro g h he
    exact A.tangent_injective hchar hperiod (congrArg Subtype.val he)
  have hc:=Fintype.card_le_of_injective f hi
  have hs:S.card≤2:=by
    dsimp [S]
    calc
      _ ≤ ({-1}:Finset k).card+1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  have hc' : Fintype.card G≤S.card := by simpa only [Fintype.card_coe] using hc
  exact hc'.trans hs

end FormalStabilizer318
