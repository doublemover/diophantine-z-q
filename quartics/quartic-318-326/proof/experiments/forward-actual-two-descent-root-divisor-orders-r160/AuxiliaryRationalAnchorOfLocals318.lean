module
public import AuxiliaryActualSelectedValue318
public import AuxiliarySelectedCompatibility318
public import AuxiliaryActualGlobalNorm318
public import AuxiliaryGlobalBinary318
public import AuxiliaryCombinedAnchor318
public section
noncomputable section
namespace AuxiliaryRationalAnchorOfLocals318
open scoped BigOperators

/-- Specialized rational anchor production from the actual coefficient
conditions and finite local vectors. Neither a prime, a global norm,
exceptional-prime compatibility nor a local-global axiom is an input. -/
theorem rational_of_finite_local_data (C : ℤ) (hC : C%24=1) (hCs : Squarefree C)
    (hsix : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣C → IsSquare (6:ZMod p))
    (hlocal : ∀ p (hp : p∈insert 2 (insert 3 C.natAbs.primeFactors)),
      ∀ [Fact p.Prime], ∃ x z T y : ℚ_[p],
        ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0) ∧
        x^2-2*z^2=(C:ℚ_[p])*T^2-6*y^2) :
    ∃ x y z : ℚ, x^2+6*y^2-2*z^2=(C:ℚ) := by
  classical
  have hC0 : C≠0 := by intro hz; subst C; norm_num at hC
  obtain ⟨σ,α,q,hσ,hCσ,hα,_,hq,hqS,hqunit,ht,hpos,hvalues,hsupport⟩ :=
    AuxiliaryActualSelectedValue318.select C hC0 0 hlocal
  let S := insert 2 (insert 3 C.natAbs.primeFactors)
  let t : ℤ := σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)
  have hS : ∀ p∈S,p.Prime := by
    intro p hp
    simp only [S,Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact Nat.prime_two
    · decide
    · exact (Nat.mem_primeFactors.mp hp).1
  obtain ⟨hq24,hqsquare⟩ := AuxiliarySelectedCompatibility318.compatible
    C σ α q hC hCs hσ hCσ hα hq hqS hsix hvalues
  have hA : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩;
      ∃ X Z : ℚ_[p], X^2-2*Z^2=(t:ℚ_[p]) := by
    intro p hp
    letI : Fact p.Prime := ⟨hS p hp⟩
    obtain ⟨X,Z,T,Y,he,_⟩ := hvalues p hp
    exact ⟨X,Z,he⟩
  obtain ⟨x,z,hxz⟩ := AuxiliaryActualGlobalNorm318.integer_norm_of_selected_locals
    S α hS (fun p _ => hα p) σ hσ q hq hqS hq24 hA
  have hB : ∀ p [Fact p.Prime], p∈S →
      ∃ T Y : ℚ_[p], (C:ℚ_[p])*T^2-6*Y^2=(t:ℚ_[p]) := by
    intro p inst hp
    obtain ⟨X,Z,T,Y,_,he⟩ := hvalues p hp
    exact ⟨T,Y,he⟩
  have hsup : ∀ (p : ℕ) [Fact p.Prime], (p:ℤ)∣(6*C)*(C*t) → p∈S ∨ p=q := by
    intro p inst hd
    exact hsupport p (Fact.out : p.Prime) hd
  obtain ⟨T,Y,hTY⟩ := AuxiliaryGlobalBinary318.rational_B_of_finite_locals
    C t hC0 S (Finset.mem_insert_self _ _) q hqS hqunit hqsquare hsup hB hpos
  have hxzQ : (x:ℚ)^2-2*(z:ℚ)^2=(t:ℚ) := by exact_mod_cast hxz
  have htQ : (t:ℚ)≠0 := by exact_mod_cast ht
  exact AuxiliaryCombinedAnchor318.representation_of_common_global_value
    (C:ℚ) (t:ℚ) x z T Y htQ hxzQ hTY

end AuxiliaryRationalAnchorOfLocals318
