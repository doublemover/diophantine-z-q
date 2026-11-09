module
public import ScalarPreparedResidues318
public section
noncomputable section
namespace FixedArithmeticLabels318
open ScalarPreparedResidues318
set_option maxHeartbeats 1000000

/-- Literal beta used by the318 detector source, not the older2X²+3 stage. -/
@[expose] def inputBeta (a : ℤ) : ℤ := 3723*(2*a+1)^2

lemma beta_positive_odd (a : ℤ) : 0<inputBeta a ∧ Odd (inputBeta a) := by
  have hm : (2*a+1)%2=1 := by omega
  have hn : 2*a+1≠0 := by omega
  refine ⟨by unfold inputBeta; positivity,?_⟩
  apply Int.odd_iff.mpr
  simp only [inputBeta,Int.mul_emod,Int.pow_emod,hm]
  norm_num

structure LucasData (s : ℤ) where
  t : ℤ
  z : ℤ
  t_pos : 0<t
  z_pos : 0<z
  t_odd : Odd t
  z_odd : Odd z
  equation : t^2-s*(s-2)*t*z+(s-2)^2*z^2=1

/-- The actual positive odd Lucas pair is produced before any real/contact choice. -/
noncomputable def lucasData (A B d : ℕ) (hd : d≠0) : LucasData (scalarLabel A B d) :=
  Classical.choice (by
    obtain ⟨hs,ho,hm,_⟩ := label_domains A B d hd
    obtain ⟨t,z,ht,hz,hot,hoz,he⟩ :=
      LucasSequence318.source_positive_odd_witness (scalarLabel A B d) hs ho hm
    exact ⟨⟨t,z,ht,hz,hot,hoz,he⟩⟩)

/-- Every root label is now constructed from the same integer input and the
single freely enlargeable scalar multiplier. -/
@[expose] def labels (a : ℤ) (A B d : ℕ) (hd : d≠0) : Fin 4 → ℤ :=
  ![inputBeta a,scalarLabel A B d,(lucasData A B d hd).t,(lucasData A B d hd).z]

lemma labels_positive (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    ∀ j, 0<labels a A B d hd j := by
  intro j
  fin_cases j <;> simp only [labels,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact (beta_positive_odd a).1
  · have h := (label_domains A B d hd).1; omega
  · exact (lucasData A B d hd).t_pos
  · exact (lucasData A B d hd).z_pos

lemma labels_nonzero (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    ∀ j, labels a A B d hd j≠0 := fun j => ne_of_gt (labels_positive a A B d hd j)

lemma labels_odd (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    ∀ j, Odd (labels a A B d hd j) := by
  intro j
  fin_cases j <;> simp only [labels,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact (beta_positive_odd a).2
  · exact (label_domains A B d hd).2.1
  · exact (lucasData A B d hd).t_odd
  · exact (lucasData A B d hd).z_odd

lemma labels_one (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    labels a A B d hd 1=scalarLabel A B d := rfl

/-- Both literal integer detector relations hold on the same fixed labels. -/
theorem detector_relations (a : ℤ) (A B d : ℕ) (hd : d≠0) :
    labels a A B d hd 0=3723*(2*a+1)^2 ∧
    (labels a A B d hd 2)^2-
      labels a A B d hd 1*(labels a A B d hd 1-2)*
        labels a A B d hd 2*labels a A B d hd 3+
      (labels a A B d hd 1-2)^2*(labels a A B d hd 3)^2=1 := by
  exact ⟨rfl,(lucasData A B d hd).equation⟩

/-- The same labels carry the produced scalar preparation at the selected h. -/
theorem actual_units (a : ℤ) (A B d h : ℕ) (hA : 6≤A) (hd : d≠0)
    (hc : Nat.ModEq (modulus A B) h (residue A B)) :
    padicValRat 2 (ScalarForwardWitness318.W
      (DetectorGateWitness318.witness (a:ℚ) (labels a A B d hd) (h:ℤ))
      ((labels a A B d hd) 1))=0 ∧
    padicValRat 3 (ScalarForwardWitness318.W
      (DetectorGateWitness318.witness (a:ℚ) (labels a A B d hd) (h:ℤ))
      ((labels a A B d hd) 1))=0 :=
  ScalarPreparedResidues318.actual_units a (labels a A B d hd) A B d h hA hd rfl hc

end FixedArithmeticLabels318
