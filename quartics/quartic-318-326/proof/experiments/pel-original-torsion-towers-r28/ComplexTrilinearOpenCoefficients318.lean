module
public import ComplexBilinearOpenCoefficients318
public section
noncomputable section
namespace ComplexTrilinearOpenCoefficients318
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} (π : Y ⟶ Spec (CommRingCat.of ℂ))
variable (f : Fin 3 → Y ⟶ X) (U : Fin 3 → X.Opens)
@[expose] def domain : Y.Opens := ⨅ t : Fin 3,f t ⁻¹ᵁ U t
lemma domain_le (t : Fin 3) : domain f U≤f t ⁻¹ᵁ U t := iInf_le _ t
@[expose] def pulled (t : Fin 3) (r : Γ(X,U t)) : Γ(Y,domain f U) :=
  Y.presheaf.map (homOfLE (domain_le f U t)).op ((f t).app (U t) r)
lemma pulled_evaluation (t : Fin 3) (r : Γ(X,U t))
    (p : Spec (CommRingCat.of ℂ) ⟶ (domain f U).toScheme)
    (q : Spec (CommRingCat.of ℂ) ⟶ (U t).toScheme)
    (he : p≫(domain f U).ι≫f t=q≫(U t).ι) :
    ComplexOpenPointEvaluation318.evaluation (domain f U) p (pulled f U t r)=
      ComplexOpenPointEvaluation318.evaluation (U t) q r := by
  rw [pulled,ComplexOpenPointEvaluation318.restriction]
  apply ComplexOpenPointEvaluation318.pullback (f t) (U t) _ q _ r
  simpa only [Category.assoc,Scheme.homOfLE_ι_assoc] using he
variable {I : Type} [Fintype I]
@[expose] def sum (C : I → I → I → ℂ) (r : ∀ t : Fin 3,I → Γ(X,U t)) : Γ(Y,domain f U) :=
  ∑ i,∑ j,∑ k,ComplexBilinearOpenCoefficients318.scalar π (domain f U) (C i j k)*
    pulled f U 0 (r 0 i)*pulled f U 1 (r 1 j)*pulled f U 2 (r 2 k)
lemma sum_evaluation (C : I → I → I → ℂ) (r : ∀ t : Fin 3,I → Γ(X,U t))
    (p : Spec (CommRingCat.of ℂ) ⟶ (domain f U).toScheme)
    (hp : p≫(domain f U).ι≫π=𝟙 _)
    (q : ∀ t : Fin 3,Spec (CommRingCat.of ℂ) ⟶ (U t).toScheme)
    (he : ∀ t,p≫(domain f U).ι≫f t=q t≫(U t).ι) :
    ComplexOpenPointEvaluation318.evaluation (domain f U) p (sum π f U C r)=
      ∑ i,∑ j,∑ k,C i j k*ComplexOpenPointEvaluation318.evaluation (U 0) (q 0) (r 0 i)*
        ComplexOpenPointEvaluation318.evaluation (U 1) (q 1) (r 1 j)*
        ComplexOpenPointEvaluation318.evaluation (U 2) (q 2) (r 2 k) := by
  simp only [sum,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [ComplexBilinearOpenCoefficients318.scalar_evaluation π _ _ p hp,
    pulled_evaluation f U 0 _ p (q 0) (he 0),pulled_evaluation f U 1 _ p (q 1) (he 1),
    pulled_evaluation f U 2 _ p (q 2) (he 2)]
end ComplexTrilinearOpenCoefficients318
