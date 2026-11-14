module
public import ActualTwoDescentFourActualTorsionPoints318
public section
noncomputable section
namespace ActualTwoDescentActualTwoTorsionCardinality318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentFourActualTorsionPoints318

abbrev ActualTwoTorsion (n : ℚ) := {P : Point n // P+P=0}

def fourTorsionEquiv (n : ℚ) (hn : n ≠ 0) : Fin 4 ≃ ActualTwoTorsion n :=
  Equiv.ofBijective (fun i => ⟨fourTorsion n hn i,actual_four_torsion_double n hn i⟩)
    ⟨fun i j h => actual_four_torsion_injective n hn (congrArg Subtype.val h),by
      rintro ⟨P,hP⟩
      obtain ⟨i,hi⟩ := actual_two_torsion_exhaustion n hn P hP
      exact ⟨i,Subtype.ext hi.symm⟩⟩

lemma actual_two_torsion_card (n : ℚ) (hn : n ≠ 0) : Nat.card (ActualTwoTorsion n)=4 := by
  rw [←Nat.card_congr (fourTorsionEquiv n hn)]
  exact Nat.card_fin 4

lemma actual_doubling_kernel_card (n : ℚ) (hn : n ≠ 0) :
    Nat.card (nsmulAddMonoidHom (α:=Point n) 2).ker=4 := by
  have e : (nsmulAddMonoidHom (α:=Point n) 2).ker ≃ ActualTwoTorsion n :=
    Equiv.subtypeEquivRight (fun P => by simp only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul])
  exact (Nat.card_congr e).trans (actual_two_torsion_card n hn)

end ActualTwoDescentActualTwoTorsionCardinality318
