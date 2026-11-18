module
public import Mathlib
public section
namespace EffectiveDiamondQuotientFactor318
open scoped BigOperators
variable {G J K A : Type*} [Fintype G] [AddCommGroup J] [AddCommGroup K] [AddCommGroup A]

/-- On geometric point groups, the finite effective norm and H-invariance of the
*original* q give (q∘pull)∘push = [n]∘q. No division by n is involved. -/
theorem factor_identity (act : G → J → J) (push : J →+ K) (pull : K →+ J) (q : J →+ A)
    (norm : ∀ x, pull (push x)=∑ g : G, act g x)
    (fixed : ∀ g x, q (act g x)=q x) (x : J) :
    q (pull (push x))=Fintype.card G • q x := by
  classical
  rw [norm,map_sum]
  simp [fixed]

/-- If multiplication by effective degree is onto on geometric target points,
the *same* q-target is a quotient via q∘pull. Not a splitting of integral
Tate modules; not a construction of Jacobians from finite abelian groups. -/
theorem factor_surjective (act : G → J → J) (push : J →+ K) (pull : K →+ J) (q : J →+ A)
    (norm : ∀ x, pull (push x)=∑ g : G, act g x)
    (fixed : ∀ g x, q (act g x)=q x) (hq : Function.Surjective q)
    (hn : Function.Surjective (fun a : A => Fintype.card G • a)) :
    Function.Surjective (q.comp pull) := by
  intro a
  obtain ⟨b,hb⟩ := hn a
  obtain ⟨x,hx⟩ := hq b
  refine ⟨push x,?_⟩
  change q (pull (push x))=a
  rw [factor_identity act push pull q norm fixed,hx]
  exact hb

end EffectiveDiamondQuotientFactor318
