module
public import AnchorNorm318
public import ConcretePadic318
public import Mathlib.Data.ZMod.Basic
public section
namespace InertPlace318
open ConcreteG8Domain AnchorNorm318 ConcretePadic318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0

/-- Nonsquareness of two in the actual residue field prevents norm
cancellation after the common p-power has been removed. -/
theorem inert_norm_unit (p:ℕ) [Fact p.Prime]
    (nonsquare:¬ ∃ x:ZMod p, x^2=2) (a b:ℤ)
    (hab:¬((p:ℤ)∣a ∧ (p:ℤ)∣b)) : ¬(p:ℤ)∣a^2-2*b^2 := by
  intro hd
  have hz : ((a:ℤ):ZMod p)^2-2*((b:ℤ):ZMod p)^2=0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (a^2-2*b^2) p).mpr hd
    push_cast at hh
    exact hh
  by_cases hb : (b:ZMod p)=0
  · have ha : (a:ZMod p)=0 := by
      have hh : (a:ZMod p)^2=0 := by simpa [hb] using hz
      exact mul_self_eq_zero.mp (by simpa [pow_two] using hh)
    exact hab ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
      (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩
  · apply nonsquare
    refine ⟨(a:ZMod p)/(b:ZMod p),?_⟩
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero _ hb)).mpr (sub_eq_zero.mp hz)

theorem norm_inert_int_value (p:ℕ) [hp:Fact p.Prime] (nonsquare:¬ ∃ x:ZMod p, x^2=2) (a b : ℤ) (ha : a≠0) (hb : b≠0) :
    padicValRat p (((a^2-2*b^2:ℤ):ℚ))=
      2*(min (padicValInt p a) (padicValInt p b):ℕ) := by
  let k := min (padicValInt p a) (padicValInt p b)
  have haD : (p:ℤ)^k∣a := (padicValInt_dvd_iff k a).mpr (Or.inr (min_le_left _ _))
  have hbD : (p:ℤ)^k∣b := (padicValInt_dvd_iff k b).mpr (Or.inr (min_le_right _ _))
  obtain ⟨A,hA⟩ := haD
  obtain ⟨B,hB⟩ := hbD
  have hab : ¬((p:ℤ)∣A ∧ (p:ℤ)∣B) := by
    rintro ⟨⟨aa,haa⟩,⟨bb,hbb⟩⟩
    have haD' : (p:ℤ)^(k+1)∣a := ⟨aa,by rw [hA,haa,pow_succ]; ring⟩
    have hbD' : (p:ℤ)^(k+1)∣b := ⟨bb,by rw [hB,hbb,pow_succ]; ring⟩
    have haL := ((padicValInt_dvd_iff (k+1) a).mp haD').resolve_left ha
    have hbL := ((padicValInt_dvd_iff (k+1) b).mp hbD').resolve_left hb
    dsimp [k] at *
    omega
  have hu := inert_norm_unit p nonsquare A B hab
  have hu0 : A^2-2*B^2≠0 := fun h => hu (h ▸ dvd_zero _)
  have hvu : padicValRat p (((A^2-2*B^2:ℤ):ℚ))=0 := by
    rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hu]
    norm_num
  have he : (((a^2-2*b^2:ℤ):ℚ))=(p:ℚ)^(2*k)*(((A^2-2*B^2:ℤ):ℚ)) := by
    rw [hA,hB]
    push_cast
    rw [show 2*k=k*2 by omega,pow_mul]
    ring
  have h3 : padicValRat p (p:ℚ)=1 := padicValRat.self hp.out.one_lt
  rw [he,padicValRat.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) (by exact_mod_cast hu0),hvu,
    padicValRat.pow,h3]
  norm_num [k]

/-- The inert quadratic norm has twice the minimum rational coefficient
valuation. The hypotheses avoid padicValRat's artificial value at zero. -/
theorem norm_inert_value (p:ℕ) [hp:Fact p.Prime] (nonsquare:¬ ∃ x:ZMod p, x^2=2) (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    padicValRat p (norm (pair a b))=
      2*min (padicValRat p a) (padicValRat p b) := by
  let A : ℤ := a.num*b.den
  let B : ℤ := b.num*a.den
  let D : ℤ := a.den*b.den
  have hd : D≠0 := by dsimp [D]; positivity
  have had : a.den≠0 := a.den_ne_zero
  have hbd : b.den≠0 := b.den_ne_zero
  have han : a.num≠0 := Rat.num_ne_zero.mpr ha
  have hbn : b.num≠0 := Rat.num_ne_zero.mpr hb
  have hA : A≠0 := mul_ne_zero han (by exact_mod_cast hbd)
  have hB : B≠0 := mul_ne_zero hbn (by exact_mod_cast had)
  have haeq : (A:ℚ)=a*(D:ℚ) := by
    dsimp [A,D]
    push_cast
    rw [←mul_assoc,Rat.mul_den_eq_num]
  have hbeq : (B:ℚ)=b*(D:ℚ) := by
    dsimp [B,D]
    push_cast
    rw [mul_left_comm b,←Rat.mul_den_eq_num]
    ring
  have hvA : (padicValInt p A:ℤ)=padicValRat p a+padicValRat p (D:ℚ) := by
    rw [←padicValRat.of_int,haeq,padicValRat.mul ha (by exact_mod_cast hd)]
  have hvB : (padicValInt p B:ℤ)=padicValRat p b+padicValRat p (D:ℚ) := by
    rw [←padicValRat.of_int,hbeq,padicValRat.mul hb (by exact_mod_cast hd)]
  have hq : norm (pair a b)≠0 := by
    simpa only [norm_pair] using ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero a b ha
  have he : (((A^2-2*B^2:ℤ):ℚ))=norm (pair a b)*(D:ℚ)^2 := by
    push_cast
    rw [haeq,hbeq,norm_pair]
    ring
  have heval := norm_inert_int_value p nonsquare A B hA hB
  rw [he,padicValRat.mul hq (pow_ne_zero _ (by exact_mod_cast hd)),padicValRat.pow] at heval
  rw [Nat.cast_min,hvA,hvB,min_add_add_right] at heval
  norm_num at heval
  rw [norm_pair]
  linarith only [heval]


section Place
variable (p:ℕ) [hp:Fact p.Prime] (nonsquare:¬ ∃ x:ZMod p, x^2=2)

theorem prime_ne_two (nonsquare:¬ ∃ x:ZMod p, x^2=2) : p≠2 := by
  intro heq
  subst p
  have ht : (2:ZMod 2)=0 := ZMod.natCast_self 2
  exact nonsquare ⟨0,by simpa using ht.symm⟩

theorem rational_two (nonsquare:¬ ∃ x:ZMod p, x^2=2) : rationalPlace p 2=0 := by
  apply rational_nat_unit p 2
  intro hd
  exact prime_ne_two p nonsquare ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)

/-- The normalized inert value, including zero coordinates. Rational
scalars retain their usual p-valuation, not twice that valuation. -/
@[expose] noncomputable def value (x:K) : WithTop ℤ :=
  min (rationalPlace p x.re) (rationalPlace p x.im)

theorem value_pair (a b:ℚ) : value p (pair a b)=min (rationalPlace p a) (rationalPlace p b) := rfl

/-- The norm has residue degree two. This zero-aware equality is the only
step using inertness in the subsequent AddValuation construction. -/
theorem norm_value (nonsquare:¬ ∃ x:ZMod p, x^2=2) (x:K) : rationalPlace p (norm x)=2 • value p x := by
  obtain ⟨a,b⟩ := x
  change rationalPlace p (norm (pair a b))=2 • value p (pair a b)
  by_cases ha:a=0
  · subst a
    simp only [norm_pair,zero_pow (by decide : 2≠0),zero_sub,
      AddValuation.map_neg,AddValuation.map_mul,AddValuation.map_pow,
      rational_two p nonsquare,value_pair,AddValuation.map_zero]
    simp
  by_cases hb:b=0
  · subst b
    simp only [norm_pair,zero_pow (by decide : 2≠0),mul_zero,sub_zero,
      AddValuation.map_pow,value_pair,AddValuation.map_zero]
    simp
  have hn : norm (pair a b)≠0 := by
    simpa only [norm_pair] using ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero a b ha
  rw [rational_value p _ hn,norm_inert_value p nonsquare a b ha hb,value_pair,
    rational_value p _ ha,rational_value p _ hb]
  norm_cast

private theorem double_injective (x y:WithTop ℤ) (h:2 • x=2 • y) : x=y := by
  cases x with
  | top =>
    cases y with
    | top => rfl
    | coe b =>
      have he : (⊤:WithTop ℤ)=((b+b:ℤ):WithTop ℤ) := by simpa only [two_nsmul,top_add,← WithTop.coe_add] using h
      exact False.elim (WithTop.top_ne_coe he)
  | coe a =>
    cases y with
    | top => simp [two_nsmul] at h
    | coe b =>
      change 2 • (a:WithTop ℤ)=2 • (b:WithTop ℤ) at h
      have hh : (2:ℤ)*a=2*b := by exact_mod_cast h
      have hab:a=b := by omega
      simp [hab]

theorem value_mul (nonsquare:¬ ∃ x:ZMod p, x^2=2) (x y:K) : value p (x*y)=value p x+value p y := by
  apply double_injective
  rw [← norm_value p nonsquare,norm_mul,AddValuation.map_mul,
    norm_value p nonsquare,norm_value p nonsquare,nsmul_add]

theorem value_add (x y:K) : min (value p x) (value p y)≤value p (x+y) := by
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  change min (value p (pair a b)) (value p (pair c d))≤value p (pair (a+c) (b+d))
  rw [value_pair,value_pair,value_pair]
  apply le_min
  · exact le_trans (min_le_min (min_le_left _ _) (min_le_left _ _))
      ((rationalPlace p).map_add a c)
  · exact le_trans (min_le_min (min_le_right _ _) (min_le_right _ _))
      ((rationalPlace p).map_add b d)

@[expose] noncomputable def place : AddValuation K (WithTop ℤ) :=
  AddValuation.of (value p)
    (by simp [value]) (by simp [value]) (value_add p) (value_mul p nonsquare)

theorem place_pair (a b:ℚ) : place p nonsquare (pair a b)=
    min (rationalPlace p a) (rationalPlace p b) := rfl

theorem place_rational (a:ℚ) : place p nonsquare (pair a 0)=rationalPlace p a := by
  rw [place_pair]
  simp

theorem place_prime : place p nonsquare (p:K)=1 := by
  have heq:(p:K)=pair (p:ℚ) 0 := rfl
  rw [heq,place_rational,rational_value p _ (by exact_mod_cast hp.out.ne_zero),
    padicValRat.self hp.out.one_lt]
  rfl

theorem place_two : place p nonsquare (2:K)=0 := by
  change place p nonsquare (pair 2 0)=0
  rw [place_rational,rational_two p nonsquare]

theorem place_i : place p nonsquare i=0 := by
  change place p nonsquare (pair 0 1)=0
  rw [place_pair]
  simp

theorem place_norm (x:K) : rationalPlace p (norm x)=2 • place p nonsquare x :=
  norm_value p nonsquare x

end Place

end InertPlace318

#print axioms InertPlace318.inert_norm_unit
#print axioms InertPlace318.norm_inert_int_value
#print axioms InertPlace318.norm_inert_value

#print axioms InertPlace318.norm_value
#print axioms InertPlace318.value_mul
#print axioms InertPlace318.value_add
#print axioms InertPlace318.place
#print axioms InertPlace318.place_rational
#print axioms InertPlace318.place_prime
#print axioms InertPlace318.place_two
#print axioms InertPlace318.place_i
#print axioms InertPlace318.place_norm
