module
public import AuxiliaryCommonValue318
public import PadicSquareNormalization318
public import AuxiliaryFiniteSquareclasses318
public section
noncomputable section
namespace AuxiliaryActualFiniteValues318
open scoped BigOperators

/-- Normalize an actual nonzero local quaternary vector. Neither a nonzero
initial common value, a unit representative nor integral coordinates are
assumed. The exponent is constructed in {0,1}. -/
theorem normalized_local_value (p : ℕ) [Fact p.Prime] (C : ℤ) (hC : C≠0)
    (x z T y : ℚ_[p]) (hne : ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0))
    (he : x^2-2*z^2=(C:ℚ_[p])*T^2-6*y^2) :
    ∃ (a : ℕ) (u : ℤ_[p]) (X Z U V : ℚ_[p]), a≤1 ∧ ‖u‖=1 ∧
      X^2-2*Z^2=(p:ℚ_[p])^a*(u:ℚ_[p]) ∧
      (C:ℚ_[p])*U^2-6*V^2=(p:ℚ_[p])^a*(u:ℚ_[p]) := by
  have hCp : (C:ℚ_[p])≠0 := by exact_mod_cast hC
  obtain ⟨t,X,Z,U,V,ht,hA,hB⟩ :=
    AuxiliaryCommonValue318.nonzero_common_value (C:ℚ_[p]) x z T y hCp hne he
  obtain ⟨a,u,s,ha,hu,hs,heq⟩ := PadicSquareNormalization318.parity_unit p t ht
  have hh := PadicSquareNormalization318.normalize_common_value
    (C:ℚ_[p]) t ((p:ℚ_[p])^a*(u:ℚ_[p])) s X Z V U hs heq hA hB
  rcases ha with rfl | rfl
  · exact ⟨0,u,X/s,Z/s,U/s,V/s,by omega,hu,by simpa using hh.1,by simpa using hh.2⟩
  · exact ⟨1,u,X/s,Z/s,U/s,V/s,by omega,hu,by simpa using hh.1,by simpa using hh.2⟩

/-- A finite family of actual local quaternary solutions gives a prime
above an arbitrary bound and a signed selected integer actually represented
by both binary forms at each specified prime. All parity exponents, unit
classes, residue choices and square multipliers are constructed. This does
not establish compatibility at the new prime or a global representation. -/
theorem prime_with_actual_finite_values (C : ℤ) (hC : C≠0)
    (S : Finset ℕ) (hS : ∀ p∈S,p.Prime)
    (hlocal : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩;
      ∃ x z T y : ℚ_[p], ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0) ∧
        x^2-2*z^2=(C:ℚ_[p])*T^2-6*y^2)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) (N : ℕ) :
    ∃ (α : ℕ → ℕ) (q : ℕ), (∀ p, α p≤1) ∧ N<q ∧ q.Prime ∧
      ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩;
        ∃ X Z T Y : ℚ_[p],
          X^2-2*Z^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p]) ∧
          (C:ℚ_[p])*T^2-6*Y^2=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p]) := by
  classical
  have hchoices : ∀ p : ℕ, ∃ a : ℕ, ∃ u : ∀ [Fact p.Prime], ℤ_[p], a≤1 ∧
      ∀ hp : p∈S, letI : Fact p.Prime := ⟨hS p hp⟩;
        ‖u‖=1 ∧ ∃ X Z T Y : ℚ_[p],
          X^2-2*Z^2=(p:ℚ_[p])^a*(u:ℚ_[p]) ∧
          (C:ℚ_[p])*T^2-6*Y^2=(p:ℚ_[p])^a*(u:ℚ_[p]) := by
    intro p
    by_cases hp : p∈S
    · letI : Fact p.Prime := ⟨hS p hp⟩
      obtain ⟨x,z,T,y,hne,he⟩ := hlocal p hp
      obtain ⟨a,u,X,Z,U,V,ha,hu,hA,hB⟩ := normalized_local_value p C hC x z T y hne he
      exact ⟨a,(fun {_ : Fact p.Prime} => u),ha,fun _ => ⟨hu,X,Z,U,V,hA,hB⟩⟩
    · exact ⟨0,(fun {_ : Fact p.Prime} => 1),by omega,fun h => False.elim (hp h)⟩
  choose α u hα hdata using hchoices
  have hu : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩; ‖u p‖=1 :=
    fun p hp => (hdata p hp).1
  obtain ⟨q,hN,hq,htrans⟩ := AuxiliaryFiniteSquareclasses318.prime_preserving_units
    S α hS σ hσ u hu N
  refine ⟨α,q,hα,hN,hq,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hS p hp⟩
  obtain ⟨X,Z,T,Y,hA,hB⟩ := (hdata p hp).2
  obtain ⟨s,_,he⟩ := htrans p hp
  refine ⟨X*s,Z*s,T*s,Y*s,?_,?_⟩
  · calc
      (X*s)^2-2*(Z*s)^2=(X^2-2*Z^2)*s^2 := by ring
      _=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p]) := by rw [hA,←he]
  · calc
      (C:ℚ_[p])*(T*s)^2-6*(Y*s)^2=((C:ℚ_[p])*T^2-6*Y^2)*s^2 := by ring
      _=((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p]) := by rw [hB,←he]

end AuxiliaryActualFiniteValues318
