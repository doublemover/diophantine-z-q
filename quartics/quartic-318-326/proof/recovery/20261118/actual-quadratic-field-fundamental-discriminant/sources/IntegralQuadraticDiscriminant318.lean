module
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.Tactic
public section
noncomputable section
namespace IntegralQuadraticDiscriminant318
open NumberField Polynomial

/-- Elementary congruence for the discriminant of a monic quadratic. -/
theorem mod_four (t n : ℤ) : (t^2-4*n)%4=0 ∨ (t^2-4*n)%4=1 := by
  rcases Int.even_or_odd t with ⟨k,hk⟩ | ⟨k,hk⟩
  · left
    rw [show t^2-4*n=4*(k^2-n) by rw [hk];ring]
    omega
  · right
    rw [show t^2-4*n=4*(k^2+k-n)+1 by rw [hk];ring]
    omega

/-- A monic quadratic relation for an algebraic integer θ in the *full*
ring of integers, with a primitive integral coefficient functional killing
1 and sending θ to 1, has fundamental discriminant. If t²−4n=p²e is a
candidate larger-order defect, adjoining the putative half-difference gives
an integral element with this same coefficient 1/p. No prior squarefree,
congruence at 2, or maximal-order discriminant hypothesis is used. -/
theorem fundamental (K : Type*) [Field K] [NumberField K]
    (θ : NumberField.RingOfIntegers K) (t n : ℤ)
    (l : NumberField.RingOfIntegers K →ₗ[ℤ] ℤ) (lone : l 1=0) (ltheta : l θ=1)
    (rel : (θ:K)^2-(t:K)*(θ:K)+(n:K)=0) :
    Int.IsFundamentalDiscr (t^2-4*n) := by
  apply Int.isFundamentalDiscr_iff_forall_prime.mpr
  refine ⟨mod_four t n,?_⟩
  intro p hp
  rintro ⟨e,hfactor,hmod⟩
  let b : ℤ := e%4
  let k : ℤ := e/4
  have hbe : b^2=b := by rcases hmod with h|h <;> simp [b,h]
  have he : b^2+4*k=e := by rw [hbe]; dsimp [b,k]; omega
  have heK : (b:K)^2+4*(k:K)=(e:K) := by exact_mod_cast he
  have hfK : (t:K)^2-4*(n:K)=(p:K)^2*(e:K) := by exact_mod_cast hfactor
  have hdK : (2*(θ:K)-(t:K))^2=(p:K)^2*(e:K) := by
    rw [←hfK]; linear_combination 4*rel
  have hpK : (p:K)≠0 := by exact_mod_cast hp.ne_zero
  let x : K := (2*(θ:K)-(t:K)+(p:K)*(b:K))/(2*(p:K))
  have hmul : (2*(p:K))*x=2*(θ:K)-(t:K)+(p:K)*(b:K) := by
    dsimp [x]; field_simp [hpK] <;> ring
  have hsq : (2*(p:K))^2*(x^2-(b:K)*x-(k:K))=0 := by
    calc _ = ((2*(p:K))*x-(p:K)*(b:K))^2-(p:K)^2*((b:K)^2+4*(k:K)) := by ring
         _ = (2*(θ:K)-(t:K))^2-(p:K)^2*(e:K) := by rw [hmul,heK] <;> ring
         _ = 0 := by rw [hdK] <;> ring
  have hx : x^2-(b:K)*x-(k:K)=0 := (mul_eq_zero.mp hsq).resolve_left
    (pow_ne_zero _ (mul_ne_zero (by norm_num : (2:K)≠0) hpK))
  have hint : IsIntegral ℤ x := by
    refine ⟨X^2+C (-b)*X+C (-k),by monicity,?_⟩
    simp [aeval_def] <;> push_cast <;> linear_combination hx
  let Xo : NumberField.RingOfIntegers K := ⟨x,hint⟩
  have hO : ((2:ℤ)*(p:ℤ)) • Xo = (2:ℤ) • θ - t • (1:NumberField.RingOfIntegers K)
      + ((p:ℤ)*b) • (1:NumberField.RingOfIntegers K) := by
    apply Subtype.ext
    simpa [zsmul_eq_mul,Xo] using hmul
  have hi := congrArg l hO
  simp [map_smul,lone,ltheta,smul_eq_mul] at hi
  have hp1 : (p:ℤ)∣1 := ⟨l Xo,by nlinarith [hi]⟩
  have hp1' : p∣(1:ℕ) := by exact_mod_cast hp1
  exact hp.ne_one (Nat.dvd_one.mp hp1')

/-- A literal integral basis (1,θ) supplies the functional above. The actual
field discriminant is still to be identified with t²−4n separately. -/
theorem fundamental_of_basis (K : Type*) [Field K] [NumberField K]
    (B : Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers K))
    (h1 : B 0=1) (t n : ℤ)
    (hrel : ((B 1: NumberField.RingOfIntegers K):K)^2-(t:K)*(B 1:K)+(n:K)=0) :
    Int.IsFundamentalDiscr (t^2-4*n) := by
  apply fundamental K (B 1) t n (B.coord 1) _ _ hrel
  · rw [←h1]; simp
  · simp

end IntegralQuadraticDiscriminant318
