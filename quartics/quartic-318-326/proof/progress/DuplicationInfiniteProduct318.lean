module
public import DuplicationFiniteProduct318
public import ActualQuadraticEmbeddings318
public section
namespace DuplicationInfiniteProduct318
open ConcreteG8Domain LocalGenerator318 NumberField RelativeDuplicationHeight318 DuplicationProjective318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

theorem degree_two : Module.finrank ℚ K=2 := by
  simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (2:ℚ) 0)

theorem infinite_mult_one (w:InfinitePlace K) : w.mult=1 :=
  (ActualQuadraticEmbeddings318.every_infinite_place_real w).mult_eq_one

theorem infinite_card_two : Fintype.card (InfinitePlace K)=2 := by
  have hh:=InfinitePlace.sum_mult_eq (K:=K)
  simpa [infinite_mult_one,degree_two] using hh

@[expose] def infinitePair (a b:K) : ℝ := ∏w:InfinitePlace K,(max (w a) (w b))^w.mult

theorem infinite_duplication_bounds (w:InfinitePlace K) (a b:K) :
    (max (w a) (w b))^4≤max (w ((a^2+D*b^2)^2)) (w (4*a*b*(a^2-D*b^2))) ∧
    max (w ((a^2+D*b^2)^2)) (w (4*a*b*(a^2-D*b^2)))≤676*(max (w a) (w b))^4 := by
  obtain ⟨σ,hσ⟩:=ActualQuadraticEmbeddings318.infinite_place_real_value w
  simpa only [hσ] using DuplicationHeightArch318.embedding_duplication_bounds σ a b

theorem infinite_forms_bounds (a b:K) :
    (infinitePair a b)^4 ≤ infinitePair (F a b) (G a b) ∧
    infinitePair (F a b) (G a b)≤(676:ℝ)^2*(infinitePair a b)^4 := by
  have hlo:=Finset.prod_le_prod₀
    (fun w (_:w∈(Finset.univ:Finset (InfinitePlace K))) =>
      pow_nonneg ((apply_nonneg w a).trans (le_max_left _ _)) 4)
    (fun w (_:w∈(Finset.univ:Finset (InfinitePlace K))) =>(infinite_duplication_bounds w a b).1)
  have hup:=Finset.prod_le_prod₀
    (fun w (_:w∈(Finset.univ:Finset (InfinitePlace K))) =>
      (apply_nonneg w (F a b)).trans (le_max_left _ _))
    (fun w (_:w∈(Finset.univ:Finset (InfinitePlace K))) =>(infinite_duplication_bounds w a b).2)
  rw [Finset.prod_pow] at hlo
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,infinite_card_two,Finset.prod_pow] at hup
  constructor
  · simpa only [infinitePair,infinite_mult_one,pow_one,F,G] using hlo
  · simpa only [infinitePair,infinite_mult_one,pow_one,F,G] using hup

end
end DuplicationInfiniteProduct318
