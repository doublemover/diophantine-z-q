module
public import ActualGaussianDegreeOneGenerator318
public section
noncomputable section
namespace ActualGaussianDegreeFromFrobenius318

open Polynomial ActualGaussianDegreeOneGenerator318

/-- The trivial projected arithmetic Frobenius has a concrete usable
numerical consequence: the actual prime quotient has cardinal p. Only
the literal p-th-power formula on that quotient is an input. -/
theorem residue_card_of_rational_power
    {p : ℕ} (hp : p.Prime) (P : Ideal GaussianInt) (hP : P.IsPrime)
    (hpP : (p:GaussianInt)∈P)
    (frobenius : ∀ a : GaussianInt ⧸ P, a^p=a) :
    Nat.card (GaussianInt ⧸ P)=p := by
  classical
  let Q := GaussianInt ⧸ P
  letI : P.IsPrime := hP
  letI : IsDomain Q := Ideal.Quotient.isDomain P
  let f : Q[X] := X^p-X
  have hDegLt : (X:Q[X]).degree < (X^p:Q[X]).degree := by
    rw [degree_X_pow,degree_X]
    exact_mod_cast hp.one_lt
  have hDeg : f.natDegree=p := by
    change (X^p-X:Q[X]).natDegree=p
    rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hDegLt),natDegree_X_pow]
  have hFne : f≠0 := ne_zero_of_natDegree_gt (by rw [hDeg]; exact hp.pos)
  have hRoot (a : Q) : f.IsRoot a := by
    simp only [f,IsRoot.def,eval_sub,eval_pow,eval_X,frobenius a,sub_self]
  have hFin : (Set.univ:Set Q).Finite :=
    (finite_setOfPred_isRoot hFne).subset (fun a _ => hRoot a)
  letI : Finite Q := Set.finite_univ_iff.mp hFin
  letI : Fintype Q := Fintype.ofFinite _
  have hUpper : Fintype.card Q≤p := by
    have h := card_le_degree_of_subset_roots (p:=f) (Z:=(Finset.univ : Finset Q))
      (fun a _ => (mem_roots hFne).mpr (hRoot a))
    simpa only [Finset.card_univ,hDeg] using h
  have hCast : (p:Q)=0 := by
    simpa only [map_natCast] using
      (Ideal.Quotient.eq_zero_iff_mem (I:=P)).mpr hpP
  letI : CharP Q p := (CharP.charP_iff_prime_eq_zero hp).mpr hCast
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hLower : p≤Fintype.card Q := by
    have h := Fintype.card_le_of_injective (ZMod.castHom (dvd_refl p) Q)
      (ZMod.castHom_injective Q)
    simpa only [ZMod.card] using h
  calc
    Nat.card (GaussianInt ⧸ P)=Fintype.card Q := Nat.card_eq_fintype_card
    _ = p := le_antisymm hUpper hLower

theorem quotient_power_of_integer_congruence {p : ℕ} (P : Ideal GaussianInt)
    (h : ∀ z : GaussianInt, (Ideal.Quotient.mk P z)^p=Ideal.Quotient.mk P z) :
    ∀ a : GaussianInt ⧸ P,a^p=a := by
  intro a
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact h z

def ofRationalPower {p : ℕ} (hp : p.Prime) (P : Ideal GaussianInt) (hP : P.IsPrime)
    (hpP : (p:GaussianInt)∈P)
    (frobenius : ∀ a : GaussianInt ⧸ P,a^p=a) :
    DegreeOne p :=
  ofCard P hP hp (residue_card_of_rational_power hp P hP hpP frobenius)

end ActualGaussianDegreeFromFrobenius318
