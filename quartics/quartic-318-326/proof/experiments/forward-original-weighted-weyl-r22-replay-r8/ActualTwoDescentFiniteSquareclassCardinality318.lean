module
public import ActualTwoDescentFinitePointCardinality318
public section
noncomputable section
namespace ActualTwoDescentFiniteSquareclassCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentFiniteEllipticModel318
variable {K : Type*} [Field K] [NeZero (2 : K)]

def signUnit : Fin 2 → Kˣ := ![1,-1]

lemma actual_sign_unit_injective : Function.Injective (signUnit (K:=K)) := by
  have hne : (1 : Kˣ) ≠ -1 := by
    intro h
    exact good_ne_neg (one_ne_zero : (1 : K) ≠ 0) (congrArg (fun u : Kˣ => (u : K)) h)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [signUnit,hne,Ne.symm hne]

lemma actual_unit_two_torsion_exhaustion (u : Kˣ) (hu : u^2=1) :
    ∃ i : Fin 2, u=signUnit i := by
  have he : (u : K)^2=1 := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg (fun v : Kˣ => (v : K)) hu
  have hf : ((u : K)-1)*((u : K)+1)=0 := by linear_combination he
  rcases mul_eq_zero.mp hf with h|h
  · refine ⟨0,?_⟩
    apply Units.ext
    exact sub_eq_zero.mp h
  · refine ⟨1,?_⟩
    apply Units.ext
    change (u : K)= -1
    linear_combination h

lemma actual_unit_doubling_kernel_card : Nat.card (powMonoidHom (α:=Kˣ) 2).ker=2 := by
  let e : Fin 2 ≃ (powMonoidHom (α:=Kˣ) 2).ker :=
    Equiv.ofBijective (fun i => ⟨signUnit i,by fin_cases i <;> simp [signUnit]⟩)
      ⟨fun i j h => actual_sign_unit_injective (congrArg Subtype.val h),by
        rintro ⟨u,hu⟩
        obtain ⟨i,hi⟩ := actual_unit_two_torsion_exhaustion u hu
        exact ⟨i,Subtype.ext hi.symm⟩⟩
  rw [←Nat.card_congr e]
  exact Nat.card_fin 2

/-- Exactly two actual unit squareclasses over any finite field of odd characteristic. -/
theorem actual_finite_squareclass_card [Finite K] : Nat.card (SquareClass K)=2 := by
  change (powMonoidHom (α:=Kˣ) 2).range.index=2
  rw [Subgroup.index_range]
  exact actual_unit_doubling_kernel_card

end ActualTwoDescentFiniteSquareclassCardinality318
