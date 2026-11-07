module
public import OrdinaryPoleNormalization
public section
namespace ThreeHelperPoleNormalization
variable {K : Type*} [Field K]

@[expose] def first (b p e : K) : K := 17*p^2-b*(17-e)*(17+3*e)
@[expose] def second (b e s q : K) : K :=
  17*q^2-b*(s^2-e*(17-b))*(s^2+3*e*(17-b))
@[expose] def liftedFirst (b p e h : K) : K :=
  17*p^2-289*b-578*e+34*h+51*e^2-3*e*h

/-- The p witness is unchanged; only e,s,q are scaled. -/
theorem first_identity (b p e : K) :
    OrdinaryPoleNormalization.oldFirst b p (b*e)=b*first b p e := by
  unfold OrdinaryPoleNormalization.oldFirst first
  ring

theorem second_identity (b e s q : K) :
    OrdinaryPoleNormalization.oldSecond b (b*e) (b*s) (b*q)=b^3*second b e s q := by
  unfold OrdinaryPoleNormalization.oldSecond second
  ring

theorem lifted_first_identity (b p e : K) :
    liftedFirst b p e (e*(17-b))=first b p e := by
  unfold liftedFirst first
  ring

/-- Exact existential equivalence for all b, including the zero branch. -/
theorem existential_equivalence (b : K) :
    (∃ p e s q : K, OrdinaryPoleNormalization.oldFirst b p e=0 ∧
      OrdinaryPoleNormalization.oldSecond b e s q=0) ↔
    (∃ p e s q : K, first b p e=0 ∧ second b e s q=0) := by
  by_cases hb : b=0
  · subst b
    constructor
    · intro _
      exact ⟨0,0,0,0,by simp [first],by simp [second]⟩
    · intro _
      exact ⟨0,0,0,0,by simp [OrdinaryPoleNormalization.oldFirst],
        by simp [OrdinaryPoleNormalization.oldSecond]⟩
  · have cancel (a : K) : b*(a/b)=a := by field_simp
    constructor
    · rintro ⟨p,e,s,q,hf,hg⟩
      refine ⟨p,e/b,s/b,q/b,?_,?_⟩
      · have hi := first_identity b p (e/b)
        rw [cancel,hf] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left hb
      · have hi := second_identity b (e/b) (s/b) (q/b)
        rw [cancel,cancel,cancel,hg] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 3 hb)
    · rintro ⟨p,e,s,q,hf,hg⟩
      refine ⟨p,b*e,b*s,b*q,?_,?_⟩
      · rw [first_identity,hf,mul_zero]
      · rw [second_identity,hg,mul_zero]

/-- The three assigned helper coordinates h,ss,t reproduce the exact gadget. -/
theorem three_helper_equivalence (b p e s q : K) :
    (first b p e=0 ∧ second b e s q=0) ↔
    ∃ h ss t : K, h=e*(17-b) ∧ ss=s^2 ∧ t=(ss-h)*(ss+3*h) ∧
      liftedFirst b p e h=0 ∧ 17*q^2-b*t=0 := by
  constructor
  · rintro ⟨hf,hs⟩
    refine ⟨e*(17-b),s^2,(s^2-e*(17-b))*(s^2+3*e*(17-b)),rfl,rfl,by ring,?_,?_⟩
    · rw [lifted_first_identity]
      exact hf
    · simpa only [second, mul_assoc] using hs
  · rintro ⟨h,ss,t,rfl,rfl,rfl,hf,hs⟩
    rw [lifted_first_identity] at hf
    exact ⟨hf, by simpa only [second, mul_assoc] using hs⟩
end ThreeHelperPoleNormalization
