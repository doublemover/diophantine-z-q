module
public import QuarticOptimization
public section
namespace OrdinaryPoleNormalization
variable {K : Type*} [Field K]

@[expose] def oldFirst (b p e : K) : K :=
  17*b*p^2-(17*b-e)*(17*b+3*e)
@[expose] def oldSecond (b e s q : K) : K :=
  17*b*q^2-(s^2-e*(17*b-b^2))*(s^2+3*e*(17*b-b^2))
@[expose] def newFirst (b p e : K) : K :=
  17*b*p^2-(17-e)*(17+3*e)
@[expose] def newSecond (b e s q : K) : K :=
  17*q^2-b*(s^2-e*(17-b))*(s^2+3*e*(17-b))

theorem first_identity (b p e : K) :
    oldFirst b (b*p) (b*e)=b^2*newFirst b p e := by
  unfold oldFirst newFirst
  ring

theorem second_identity (b e s q : K) :
    oldSecond b (b*e) (b*s) (b*q)=b^3*newSecond b e s q := by
  unfold oldSecond newSecond
  ring

/-- Exact rational-witness equivalence for every b. The b=0 branch is
constructed explicitly, with no global arithmetic or positivity assumption. -/
theorem existential_equivalence (b : K) :
    (∃ p e s q : K, oldFirst b p e=0 ∧ oldSecond b e s q=0) ↔
    (∃ p e s q : K, newFirst b p e=0 ∧ newSecond b e s q=0) := by
  by_cases hb : b=0
  · subst b
    constructor
    · intro _
      exact ⟨0,17,0,0,by simp [newFirst],by simp [newSecond]⟩
    · intro _
      exact ⟨0,0,0,0,by simp [oldFirst],by simp [oldSecond]⟩
  · have cancel (a : K) : b*(a/b)=a := by field_simp
    constructor
    · rintro ⟨p,e,s,q,hf,hg⟩
      refine ⟨p/b,e/b,s/b,q/b,?_,?_⟩
      · have hi := first_identity b (p/b) (e/b)
        rw [cancel,cancel,hf] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 2 hb)
      · have hi := second_identity b (e/b) (s/b) (q/b)
        rw [cancel,cancel,cancel,hg] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 3 hb)
    · rintro ⟨p,e,s,q,hf,hg⟩
      refine ⟨b*p,b*e,b*s,b*q,?_,?_⟩
      · rw [first_identity,hf,mul_zero]
      · rw [second_identity,hg,mul_zero]

end OrdinaryPoleNormalization
