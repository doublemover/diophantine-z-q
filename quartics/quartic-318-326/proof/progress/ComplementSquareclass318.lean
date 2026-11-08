module
public import SourceTwistArithmetic318
public section
noncomputable section
namespace ComplementSquareclass318
set_option maxHeartbeats 500000
open SourceTwistArithmetic318
variable {F:Type*} [Field F]
@[expose] def complementaryProduct (b:Fin 4→F) (i:Fin 4) : F :=
  ∏j:Fin 3,b (complement i j)
@[expose] def allProduct (b:Fin 4→F) : F := ∏i:Fin 4,b i

theorem complement_twice (b:Fin 4→F) (i:Fin 4) :
    complementaryProduct (complementaryProduct b) i=b i*allProduct b^2 := by
  fin_cases i <;> simp [complementaryProduct,allProduct,complement,Fin.prod_univ_succ] <;> ring

/-- The four complementary squareclasses determine the original four
classes uniquely; no choice of signs or twist representative is assumed. -/
theorem recover_squareclasses (b:Fin 4→F) (hb:∀i,b i≠0)
    (h:∀i,IsSquare (complementaryProduct b i)) (i:Fin 4) : IsSquare (b i) := by
  have hs:IsSquare (complementaryProduct (complementaryProduct b) i):=
    Finset.isSquare_prod _ (fun j _=>h (complement i j))
  rw [complement_twice] at hs
  have hn:allProduct b≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hb i)
  have hd:=hs.div (IsSquare.sq (allProduct b))
  simpa only [mul_div_cancel_right₀ _ (pow_ne_zero 2 hn)] using hd

theorem complementary_ratio (a b:Fin 4→F) (i:Fin 4) :
    complementaryProduct (fun j=>a j/b j) i=
      complementaryProduct a i/complementaryProduct b i := by
  simp only [complementaryProduct,Finset.prod_div_distrib]

theorem recover_twist_ratios (a b:Fin 4→F) (ha:∀i,a i≠0) (hb:∀i,b i≠0)
    (h:∀i,IsSquare (complementaryProduct a i/complementaryProduct b i)) (i:Fin 4) :
    IsSquare (a i/b i) := by
  apply recover_squareclasses (fun j=>a j/b j) (fun j=>div_ne_zero (ha j) (hb j))
  intro j
  rw [complementary_ratio]
  exact h j
end ComplementSquareclass318
