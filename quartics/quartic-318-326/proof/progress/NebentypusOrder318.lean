module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Tactic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.Index
public section
noncomputable section
namespace NebentypusOrder318
set_option maxHeartbeats 0

variable {G Q A : Type*} [Group G] [Group Q] [Fintype Q] [CommGroup A]

/-- If the square of a character is trivial on the kernel of a finite
restriction map, its order divides twice the cardinality of that actual
finite group. No bound on a coefficient field is used. -/
theorem character_pow (q : G →* Q) (epsilon : G →* A)
    (h : ∀g, q g=1 → epsilon g ^ 2=1) :
    epsilon ^ (2 * Fintype.card Q)=1 := by
  ext g
  change epsilon g ^ (2 * Fintype.card Q)=1
  have hg : q (g ^ Fintype.card Q)=1 := by
    rw [map_pow, pow_card_eq_one]
  have he := h (g ^ Fintype.card Q) hg
  rw [map_pow, ← pow_mul] at he
  simpa only [Nat.mul_comm] using he

theorem character_order_dvd (q : G →* Q) (epsilon : G →* A)
    (h : ∀g, q g=1 → epsilon g ^ 2=1) :
    orderOf epsilon ∣ 2 * Fintype.card Q :=
  orderOf_dvd_of_pow_eq_one (character_pow q epsilon h)

theorem character_order_le (q : G →* Q) (epsilon : G →* A)
    (h : ∀g, q g=1 → epsilon g ^ 2=1) :
    orderOf epsilon ≤ 2 * Fintype.card Q :=
  orderOf_le_of_pow_eq_one (by positivity) (character_pow q epsilon h)

/-- Exact 4608R consequence of the controlled normal field degree. -/
theorem source_order_bound (q : G →* Q) (epsilon : G →* A)
    (h : ∀g, q g=1 → epsilon g ^ 2=1) (R : ℕ)
    (hd : Fintype.card Q ≤ 2304 * R) :
    orderOf epsilon ≤ 4608 * R := by
  have hh := character_order_le q epsilon h
  omega

/-- The determinant-square relation on the restriction kernel supplies
precisely the character-square relation; the cyclotomic factor cancels. -/
theorem determinant_square (q : G →* Q) (epsilon cyclotomic determinant : G →* A)
    (hdet : ∀g, determinant g=epsilon g * cyclotomic g)
    (hsq : ∀g, q g=1 → determinant g ^ 2=cyclotomic g ^ 2) :
    ∀g, q g=1 → epsilon g ^ 2=1 := by
  intro g hg
  have hh := hsq g hg
  rw [hdet,mul_pow] at hh
  exact mul_right_cancel (show epsilon g^2 * cyclotomic g^2=1 * cyclotomic g^2 by simpa using hh)

theorem determinant_order_bound (q : G →* Q) (epsilon cyclotomic determinant : G →* A)
    (hdet : ∀g, determinant g=epsilon g * cyclotomic g)
    (hsq : ∀g, q g=1 → determinant g ^ 2=cyclotomic g ^ 2)
    (R : ℕ) (hd : Fintype.card Q ≤ 2304 * R) :
    orderOf epsilon ≤ 4608 * R :=
  source_order_bound q epsilon (determinant_square q epsilon cyclotomic determinant hdet hsq) R hd

/-- The kernel index, not merely the character's exponent, is bounded.
This uses the actual field root bound and is false for arbitrary commutative
target groups without such an extra property. -/
theorem kernel_index_le_of_pow {K : Type*} [Field K] (epsilon : G →* Kˣ)
    (n : ℕ) (hn : 0<n) (hpow : epsilon ^ n=1) : epsilon.ker.index≤n := by
  letI : NeZero n := ⟨hn.ne'⟩
  let f : epsilon.range → rootsOfUnity n K := fun x => ⟨x.1, by
    rw [mem_rootsOfUnity]
    obtain ⟨g,hg⟩ := x.2
    rw [←hg]
    exact congrArg (fun e : G →* Kˣ => e g) hpow⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    change (f x).val=(f y).val
    exact congrArg (fun z : rootsOfUnity n K => z.val) hxy
  rw [Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective f hinj).trans (card_rootsOfUnity K n)

theorem character_kernel_index_bound {K : Type*} [Field K]
    (q : G →* Q) (epsilon : G →* Kˣ)
    (h : ∀g, q g=1 → epsilon g ^ 2=1) (R : ℕ)
    (hd : Fintype.card Q≤2304*R) : epsilon.ker.index≤4608*R := by
  have hh := kernel_index_le_of_pow epsilon (2*Fintype.card Q)
    (by positivity) (character_pow q epsilon h)
  omega

/-- Pullback along the surjective cyclotomic quotient loses no index bound:
this is the finite Dirichlet-character kernel used for Gamma_H. -/
theorem finite_character_index_bound {U K : Type*} [Group U] [Field K]
    (q : G →* Q) (pi : G →* U) (hpi : Function.Surjective pi)
    (epsilon : U →* Kˣ)
    (h : ∀g, q g=1 → epsilon (pi g)^2=1)
    (R : ℕ) (hd : Fintype.card Q≤2304*R) : epsilon.ker.index≤4608*R := by
  have hp := character_pow q (epsilon.comp pi) h
  have hp' : epsilon^(2*Fintype.card Q)=1 := by
    apply MonoidHom.ext
    intro u
    obtain ⟨g,rfl⟩ := hpi u
    exact congrArg (fun e : G →* Kˣ => e g) hp
  have hh := kernel_index_le_of_pow epsilon (2*Fintype.card Q) (by positivity) hp'
  omega

/-- Complete group-theoretic determinant-to-Dirichlet-kernel bridge. -/
theorem determinant_finite_index_bound {U K : Type*} [Group U] [Field K]
    (q : G →* Q) (pi : G →* U) (hpi : Function.Surjective pi)
    (epsilon : U →* Kˣ) (cyclotomic determinant : G →* Kˣ)
    (hdet : ∀g, determinant g=epsilon (pi g)*cyclotomic g)
    (hsq : ∀g, q g=1 → determinant g^2=cyclotomic g^2)
    (R : ℕ) (hd : Fintype.card Q≤2304*R) : epsilon.ker.index≤4608*R :=
  finite_character_index_bound q pi hpi epsilon
    (determinant_square q (epsilon.comp pi) cyclotomic determinant hdet hsq) R hd

end NebentypusOrder318
#print axioms NebentypusOrder318.character_pow
#print axioms NebentypusOrder318.character_order_dvd
#print axioms NebentypusOrder318.character_order_le
#print axioms NebentypusOrder318.source_order_bound
#print axioms NebentypusOrder318.determinant_square
#print axioms NebentypusOrder318.determinant_order_bound

#print axioms NebentypusOrder318.kernel_index_le_of_pow
#print axioms NebentypusOrder318.character_kernel_index_bound
#print axioms NebentypusOrder318.finite_character_index_bound

#print axioms NebentypusOrder318.determinant_finite_index_bound
