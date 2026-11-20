module
public import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel
public section

namespace CTCyclicTwoBar318

variable {G A : Type*} [Group G] [AddCommGroup A]

/-- Degree-two bar differential equals zero, written without a
topological coefficient or a second choice of differential. -/
def IsCycle (R : G →* AddMonoid.End A) (c : G → G → A) : Prop :=
  ∀ g h k, R g (c h k) - c (g*h) k + c g (h*k) - c g h = 0

def coboundary (R : G →* AddMonoid.End A) (b : G → A) (g h : G) : A :=
  R g (b h) - b (g*h) + b g

section
variable (R : G →* AddMonoid.End A) (s : G)

private theorem act_one (a : A) : R 1 a = a := by
  simp only [map_one,AddMonoid.End.one_apply]

/-- Evaluate at (s,s) after subtracting the boundary of the constant
cochain c(1,1), with the action on the first variable retained. -/
def normalizedValue (c : G → G → A) : A :=
  c s s - R s (c 1 1)

theorem left_one (c : G → G → A) (hc : IsCycle R c) (g : G) :
    c 1 g = c 1 1 := by
  have h := hc 1 1 g
  simp only [act_one, one_mul, sub_self, zero_add] at h
  exact sub_eq_zero.mp h

theorem right_one (c : G → G → A) (hc : IsCycle R c) (g : G) :
    c g 1 = R g (c 1 1) := by
  have h := hc g 1 1
  simp only [mul_one, sub_add_cancel] at h
  exact (sub_eq_zero.mp h).symm

theorem fixed_value (hs : s*s=1) (c : G → G → A) (hc : IsCycle R c) :
    R s (normalizedValue R s c) = normalizedValue R s c := by
  have hh : R s (R s (c 1 1)) = c 1 1 := by
    calc
      R s (R s (c 1 1)) = R (s*s) (c 1 1) := by rw [map_mul] <;> rfl
      _ = c 1 1 := by rw [hs, act_one]
  have h := hc s s s
  rw [hs, left_one R c hc s, right_one R c hc s] at h
  unfold normalizedValue
  rw [map_sub, hh]
  exact sub_eq_zero.mp (by
    calc
      (R s (c s s) - c 1 1) - (c s s - R s (c 1 1)) =
          R s (c s s) - c 1 1 + R s (c 1 1) - c s s := by abel
      _ = 0 := h)

theorem normalized_boundary (hs : s*s=1) (b : G → A) :
    normalizedValue R s (coboundary R b) =
      R s (b s - b 1) + (b s - b 1) := by
  unfold normalizedValue coboundary
  rw [hs, one_mul, act_one, sub_self, zero_add, map_sub]
  abel

/-- Full boundary criterion on the original two-element group:
there is no normalization assumption on the input cocycle. -/
theorem exists_boundary_iff
    (hs : s*s=1) (hne : s≠1) (hG : ∀ g : G, g=1 ∨ g=s)
    (c : G → G → A) (hc : IsCycle R c) :
    (∃ b : G → A, coboundary R b = c) ↔
      ∃ u : A, R s u + u = normalizedValue R s c := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨b s-b 1,(normalized_boundary R s hs b).symm⟩
  · intro h
    classical
    obtain ⟨u,hu⟩ := h
    let b (g : G) := c 1 1 + if g=s then u else 0
    have h1 : b 1=c 1 1 := by simp [b,Ne.symm hne]
    have h2 : b s=c 1 1+u := by simp [b]
    refine ⟨b,?_⟩
    funext g h
    rcases hG g with rfl | rfl <;> rcases hG h with rfl | rfl
    · simp only [coboundary, one_mul, act_one, sub_self, zero_add,h1]
    · rw [left_one R c hc s]
      simp only [coboundary, one_mul, act_one, sub_self, zero_add,h1]
    · rw [right_one R c hc s]
      simp only [coboundary, mul_one, sub_add_cancel,h1]
    · unfold coboundary
      rw [hs,h1,h2,map_add]
      have hv : (R s u + u) + R s (c 1 1) = c s s := by
        rw [hu,normalizedValue,sub_add_cancel]
      calc
        R s (c 1 1) + R s u - c 1 1 + (c 1 1 + u) =
            (R s u + u) + R s (c 1 1) := by abel
        _ = _ := hv

/-- The signed carry class with any fixed value exists already
on the unnormalized bar complex. -/
theorem carry_cycle (hs : s*s=1) (hne : s≠1)
    (hG : ∀ g : G, g=1 ∨ g=s)
    (a : A) (ha : R s a=a) :
    ∃ c : G → G → A, IsCycle R c ∧ normalizedValue R s c=a := by
  classical
  let c (g h : G) := if g=s ∧ h=s then a else 0
  have hOne : 1 ≠ s := Ne.symm hne
  refine ⟨c,?_,?_⟩
  · intro g h k
    rcases hG g with rfl | rfl <;> rcases hG h with rfl | rfl <;>
      rcases hG k with rfl | rfl <;>
      simp [c,hOne,hs,act_one,ha]
  · simp [normalizedValue,c,hOne]

end

end CTCyclicTwoBar318
