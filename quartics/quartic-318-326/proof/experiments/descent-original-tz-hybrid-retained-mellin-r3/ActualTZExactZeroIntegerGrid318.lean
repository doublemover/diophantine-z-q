module
public import ActualTZHeterogeneousGridRoots318
public section
noncomputable section
namespace ActualTZExactZeroIntegerGrid318
open ActualTZHeterogeneousGridRoots318
open scoped BigOperators
variable {n : ℕ}
abbrev Grid (L : Fin n→ℕ) := (i : Fin n)→Fin (L i)

def point (L : Fin n→ℕ) (s : Fin n→ℤ) (t : Grid L) : Fin n→ℤ :=
  fun i=>s i+(t i).val

def uniform (L : Fin n→ℕ) : ℚ≥0 := ∏ i : Fin n,1/(L i:ℚ≥0)

def axis (L : Fin n→ℕ) (s : Fin n→ℤ) (i : Fin n) : Finset ℤ :=
  Finset.univ.image (fun t : Fin (L i)=>s i+t.val)

theorem axis_card (L : Fin n→ℕ) (s : Fin n→ℤ) (i : Fin n) : (axis L s i).card=L i := by
  have H : Function.Injective (fun t : Fin (L i)=>s i+(t.val:ℤ)) := by
    intro a b h
    apply Fin.ext
    omega
  rw [axis,Finset.card_image_of_injOn H.injOn,Finset.card_univ,Fintype.card_fin]

private theorem injective (L : Fin n→ℕ) (s : Fin n→ℤ) : Function.Injective (point L s) := by
  intro t t' h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change s i+(t i).val=s i+(t' i).val at hi
  omega

private theorem roots_image (L : Fin n→ℕ) (s : Fin n→ℤ) (P : MvPolynomial (Fin n) ℤ) :
    roots (axis L s) P = ((Finset.univ : Finset (Grid L)).filter
      (fun t=>MvPolynomial.eval (point L s t) P=0)).image (point L s) := by
  classical
  let T : Finset (Grid L) := Finset.univ.filter (fun t=>MvPolynomial.eval (point L s t) P=0)
  ext z
  rw [roots,Finset.mem_filter]
  change z∈Fintype.piFinset (axis L s) ∧ MvPolynomial.eval z P=0 ↔ z∈T.image (point L s)
  constructor
  · rintro ⟨hz,h0⟩
    have h (i : Fin n) : ∃ t : Fin (L i),s i+(t.val:ℤ)=z i := by
      obtain ⟨t,_,ht⟩ := Finset.mem_image.mp (Fintype.mem_piFinset.mp hz i)
      exact ⟨t,ht⟩
    choose t ht using h
    have he : point L s t=z := funext ht
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,by rw [he]; exact h0⟩,he⟩
  · rintro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), (Finset.mem_filter.mp ht).2⟩
    exact Finset.mem_image.mpr ⟨t i,Finset.mem_univ _,rfl⟩

/-- Identically-zero cells are removed using an INTEGER evaluation,
not a bound after conditioning on residues or on the chosen wrap. -/
theorem integer_zero_le (L : Fin n→ℕ) (s : Fin n→ℤ) (P : MvPolynomial (Fin n) ℤ)
    (hP : P≠0) (M d : ℕ) (hM : 0<M) (hL : ∀ i,M≤L i) (hd : P.totalDegree≤d) :
    (∑ t : Grid L,if MvPolynomial.eval (point L s t) P=0 then uniform L else 0)≤
      (n:ℚ≥0)*((d:ℚ≥0)/(M:ℚ≥0)) := by
  classical
  let T : Finset (Grid L) := Finset.univ.filter (fun t=>MvPolynomial.eval (point L s t) P=0)
  have H := weighted_degree (axis L s) P hP d M hd hM
    (fun i => by rw [axis_card]; exact hL i)
    (fun i (_ : ℤ)=>1/(L i:ℚ≥0)) 1
    (fun i _ _=>by rw [axis_card])
  rw [roots_image,Finset.sum_image (injective L s).injOn,one_pow,one_mul] at H
  have hEq : (∑ t : Grid L,if MvPolynomial.eval (point L s t) P=0 then uniform L else 0)=
      ∑ t∈T,∏ i : Fin n,1/(L i:ℚ≥0) := by
    rw [T,Finset.sum_filter]
    rfl
  rw [hEq]
  exact H

theorem uniform_one (L : Fin n→ℕ) (hL : ∀ i,0<L i) :
    (∑ _t : Grid L,uniform L)=1 := by
  simp only [Grid,uniform,Finset.sum_const,Finset.card_univ,Fintype.card_pi,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  have h : (L i:ℚ≥0)≠0 := by exact_mod_cast (hL i).ne'
  rw [one_div,mul_inv_cancel₀ h]

end ActualTZExactZeroIntegerGrid318
