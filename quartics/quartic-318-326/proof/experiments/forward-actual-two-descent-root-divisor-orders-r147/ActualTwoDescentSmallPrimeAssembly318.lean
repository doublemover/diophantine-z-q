module
public import ActualTwoDescentSmallCore318
public section
noncomputable section
namespace ActualTwoDescentSmallPrimeAssembly318
open ActualTwoDescentSmallPattern318 ActualTwoDescentSmallCore318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentFamilyProducts318
open ActualTwoDescentSymbolTable318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentAuxiliaryTypes318 ActualTwoDescentEdgeAction318
open ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

def encode (z : ZMod 2) : Bool := decide (z=1)
lemma boolBit_encode (z : ZMod 2) : boolBit (encode z)=z := by
  fin_cases z <;> norm_num [boolBit,encode]
def prescribedBits (d k : ℕ) (b : BetaIndex d) : Bool :=
  if h : k<d then encode (incidence d b ⟨k,h⟩) else encode (∑ i, incidence d b i)
abbrev Family (d : ℕ) (q : BetaIndex d → ℕ) (forbidden : Finset ℕ) (N : ℕ) :=
  PrimeFamily q (prescribedBits d) (fun _ _ => false) (fun k => decide (k=d)) forbidden N (d+1)

def assembled {d : ℕ} {q : BetaIndex d → ℕ} {forbidden : Finset ℕ} {N : ℕ}
    (F : Family d q forbidden N) : Index d → ℕ
  | none => F.value (Fin.last d)
  | some (Sum.inl b) => q b
  | some (Sum.inr i) => F.value i.castSucc

instance assembled_prime {d : ℕ} {q : BetaIndex d → ℕ} [∀ b, Fact (q b).Prime]
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) (i : Index d) :
    Fact (assembled F i).Prime := ⟨by
  cases i with
  | none => exact F.prime _
  | some i =>
    cases i with
    | inl b => exact Fact.out
    | inr i => exact F.prime _⟩

lemma assembled_injective {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N)
    (hq : Function.Injective q) : Function.Injective (assembled F) := by
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases y with
      | inl b => exact False.elim (F.seed_ne (Fin.last d) b he)
      | inr i =>
        have hh := congrArg Fin.val (F.injective he)
        simp only [Fin.val_last,Fin.val_castSucc] at hh
        exact False.elim (by omega)
  | some x =>
    cases x with
    | inl b =>
      cases y with
      | none => exact False.elim (F.seed_ne (Fin.last d) b he.symm)
      | some y =>
        cases y with
        | inl c => exact congrArg bIndex (hq he)
        | inr i => exact False.elim (F.seed_ne i.castSucc b he.symm)
    | inr i =>
      cases y with
      | none =>
        have hh := congrArg Fin.val (F.injective he)
        simp only [Fin.val_last,Fin.val_castSucc] at hh
        exact False.elim (by omega)
      | some y =>
        cases y with
        | inl b => exact False.elim (F.seed_ne i.castSucc b he)
        | inr j =>
          apply congrArg iIndex
          apply Fin.ext
          exact congrArg Fin.val (F.injective he)

lemma assembled_coprime {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N)
    (hq : ∀ b, Nat.Coprime (q b) 12) : ∀ i, Nat.Coprime (assembled F i) 12 := by
  intro i
  cases i with
  | none => exact F.coprime _
  | some i =>
    cases i with
    | inl b => exact hq b
    | inr i => exact F.coprime _

lemma assembled_product {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) :
    (∏ i, assembled F i)=(∏ b, q b)*multiplier F := by
  simp only [Fintype.prod_option,Fintype.prod_sum_type,assembled,multiplier,Fin.prod_univ_castSucc]
  ring

lemma assembled_type_I {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) (i : Fin d) :
    (assembled F (iIndex i) : ZMod 12)=1 := by
  simpa [assembled,iIndex,Nat.ne_of_lt i.isLt] using F.residue i.castSucc
lemma assembled_type_Q {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) :
    (assembled F none : ZMod 12)=7 := by
  simpa [assembled] using F.residue (Fin.last d)

lemma assembled_cross {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N)
    (b : BetaIndex d) (i : Fin d) :
    edges (assembled F) (bIndex b) (iIndex i)=incidence d b i := by
  have h := actual_bit_of_sign _ _ _ (F.old_symbol i.castSucc b)
  simpa [edges,assembled,bIndex,iIndex,prescribedBits,i.isLt,boolBit_encode] using h
lemma assembled_q0_at_beta {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) (b : BetaIndex d) :
    edges (assembled F) (bIndex b) none=∑ i, incidence d b i := by
  have h := actual_bit_of_sign _ _ _ (F.old_symbol (Fin.last d) b)
  simpa [edges,assembled,bIndex,prescribedBits,boolBit_encode] using h
lemma assembled_to_q0 {d : ℕ} {q : BetaIndex d → ℕ}
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N) (i : Fin d) :
    edges (assembled F) (iIndex i) none=0 := by
  have h := actual_bit_of_sign _ _ _ (F.earlier_symbol (Fin.last d) i.castSucc i.isLt)
  simpa [edges,assembled,iIndex,boolBit] using h

/-- Every symbol/type hypothesis of the small arithmetic core is supplied
by the actual finite Dirichlet family. No prescribed prime pattern remains
as an external assumption in the next producer. -/
theorem actual_assembled_pattern {d : ℕ} {q : BetaIndex d → ℕ} [∀ b, Fact (q b).Prime]
    {forbidden : Finset ℕ} {N : ℕ} (F : Family d q forbidden N)
    (hq : Function.Injective q) (hqc : ∀ b, Nat.Coprime (q b) 12) :
    Pattern d (assembled F) := by
  have hd := assembled_injective F hq
  have hc := assembled_coprime F hqc
  have hp2 : ∀ i, assembled F i ≠ 2 := by
    intro i he
    have h := hc i
    rw [he] at h
    norm_num at h
  refine ⟨assembled_cross F,?_,assembled_to_q0 F,assembled_q0_at_beta F,
    assembled_type_I F,assembled_type_Q F⟩
  intro i j
  by_cases he : i=j
  · subst j
    simp [edges]
  have hn : i.val ≠ j.val := fun h => he (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hn with hij | hji
  · have h := actual_bit_of_sign _ _ _ (F.earlier_symbol j.castSucc i.castSucc hij)
    simpa [edges,assembled,iIndex,he,boolBit] using h
  · have hs : parity (assembled F) (iIndex i)=0 :=
      (actual_type_one _ (assembled_type_I F i)).1
    rw [actual_edge_reverse_zero (assembled F) hd hp2 _ _ hs]
    have h := actual_bit_of_sign _ _ _ (F.earlier_symbol i.castSucc j.castSucc hji)
    simpa [edges,assembled,iIndex,Ne.symm he,boolBit] using h

end ActualTwoDescentSmallPrimeAssembly318
