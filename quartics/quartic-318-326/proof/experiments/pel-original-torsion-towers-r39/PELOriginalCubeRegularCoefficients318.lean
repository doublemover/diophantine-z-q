module
public import PELOriginalCubeThetaProducts318
public import PELOriginalCubeBasisCoefficients318
public import PELOriginalCubeOpenCover318
public section
noncomputable section
namespace PELOriginalCubeRegularCoefficients318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318 PELOriginalMixedRatioCover318
open PELOriginalTripleProductReduced318 PELOriginalTripleComplexPoints318 PELOriginalCubeSchemeMaps318
open PELOriginalCubeOpenCover318 PELOriginalCubeBasisCoefficients318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (N : ℕ) [NeZero N] [NeZero (4*N)]
variable (D : Data τ hτ N)
@[expose] def selected (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) : Fin 7 → Label N :=
  if side then ![D.label (b 3),D.label (b 0),D.label (b 1),D.label (b 2),
    D.label (b 8),D.label (b 9),D.label (b 10)]
  else ![D.label (b 4),D.label (b 5),D.label (b 6),D.label (b 7),
    D.label (b 8),D.label (b 9),D.label (b 10)]
@[expose] def function (side : Bool) (i : Fin 7 → Label N) : ComplexVectors → ComplexVectors → ComplexVectors → ℂ :=
  if side then PELOriginalCubeThetaProducts318.positive τ hτ N i
  else PELOriginalCubeThetaProducts318.negative τ hτ N i
lemma expansion (side : Bool) (i : Fin 7 → Label N) :
    ∃ C : Label (4*N) → Label (4*N) → Label (4*N) → ℂ,∀ x y z,
      function τ hτ N side i x y z=∑ a,∑ b,∑ c,C a b c*
        PELOriginalLevelPowerSections318.value τ hτ (4*N) a x*
        PELOriginalLevelPowerSections318.value τ hτ (4*N) b y*
        PELOriginalLevelPowerSections318.value τ hτ (4*N) c z := by
  cases side
  · exact PELOriginalCubeThetaProducts318.negative_expansion τ hτ N i
  · exact PELOriginalCubeThetaProducts318.positive_expansion τ hτ N i
@[expose] def constants (side : Bool) (i : Fin 7 → Label N) := (expansion τ hτ N side i).choose
@[expose] def regular (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :
    Γ(Triple τ hτ,chart τ hτ b) :=
  (Triple τ hτ).presheaf.map (homOfLE (source_le τ hτ b)).op
    (ComplexTrilinearOpenCoefficients318.sum (structureMap τ hτ) (sourceMaps τ hτ) (sourceOpens τ hτ b)
      (constants τ hτ N side (selected τ hτ N D side b))
      (fun t => D.basis (b ⟨t.val,by omega⟩)))

/-- Whole regular sevenfold coefficients retain all three original
point coordinates, every theta factor and the literal common denominator. -/
lemma regular_evaluation (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ b).toScheme) (x y z : ComplexVectors)
    (hp : p≫(chart τ hτ b).ι=triple τ hτ (projection (P τ) x) (projection (P τ) y) (projection (P τ) z)) :
    ComplexOpenPointEvaluation318.evaluation (chart τ hτ b) p (regular τ hτ N D side b)=
      function τ hτ N side (selected τ hτ N D side b) x y z/
        ((D.lineData.g (b 0) x)^4*(D.lineData.g (b 1) y)^4*(D.lineData.g (b 2) z)^4) := by
  let tpoint : Fin 3 → ComplexVectors := ![x,y,z]
  have hm (t : Fin 3) : tpoint t∈domain τ hτ (opens τ hτ (b ⟨t.val,by omega⟩)) := by
    have h := point_mem τ hτ b p x y z hp ⟨t.val,by omega⟩
    fin_cases t <;> exact h
  let q (t : Fin 3) := point τ hτ (opens τ hτ (b ⟨t.val,by omega⟩)) (tpoint t) (hm t)
  let p' := p≫(Triple τ hτ).homOfLE (source_le τ hτ b)
  have hq (t : Fin 3) : p'≫(sourceDomain τ hτ b).ι≫sourceMaps τ hτ t=
      q t≫(sourceOpens τ hτ b t).ι := by
    rw [p',Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,hp,sourceMaps,point_action,point_ι]
    fin_cases t <;> rfl
  have hC : p'≫(sourceDomain τ hτ b).ι≫structureMap τ hτ=𝟙 _ := by
    rw [p',Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,hp,triple_over]
  rw [regular,ComplexOpenPointEvaluation318.restriction,
    ComplexTrilinearOpenCoefficients318.sum_evaluation (structureMap τ hτ)
      (sourceMaps τ hτ) (sourceOpens τ hτ b) _ _ p' hC q hq]
  have hv (t : Fin 3) (r : Label (4*N)) :
      ComplexOpenPointEvaluation318.evaluation (sourceOpens τ hτ b t) (q t)
        (D.basis (b ⟨t.val,by omega⟩) r)=
      PELOriginalLevelPowerSections318.value τ hτ (4*N) r (tpoint t)/
        (D.lineData.g (b ⟨t.val,by omega⟩) (tpoint t))^4 :=
    (value_at_point τ hτ _ _ _ (q t) (point_ι τ hτ _ _ (hm t))).symm.trans
      (D.basis_value _ r _ (hm t))
  simp_rw [hv]
  rw [(expansion τ hτ N side (selected τ hτ N D side b)).choose_spec x y z,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b' hb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  change _=_
  field_simp [D.lineData.nonzero _ _ (hm 0),D.lineData.nonzero _ _ (hm 1),D.lineData.nonzero _ _ (hm 2)]
  <;> ring

@[expose] def numerator (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ)
    (x y z : ComplexVectors) : ℂ :=
  if side then D.lineData.g (b 3) (x+y+z)*D.lineData.g (b 0) x*D.lineData.g (b 1) y*
    D.lineData.g (b 2) z*D.lineData.g (b 8) (x-y)*D.lineData.g (b 9) (x-z)*D.lineData.g (b 10) (y-z)
  else D.lineData.g (b 4) (x+y)*D.lineData.g (b 5) (x+z)*D.lineData.g (b 6) (y+z)*
    D.lineData.g (b 7) 0*D.lineData.g (b 8) (x-y)*D.lineData.g (b 9) (x-z)*D.lineData.g (b 10) (y-z)
lemma selected_value (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) (x y z : ComplexVectors) :
    function τ hτ N side (selected τ hτ N D side b) x y z=numerator τ hτ N D side b x y z := by
  cases side <;> simp only [function,selected,numerator,Bool.false_eq_true,if_false,if_true,
    PELOriginalCubeThetaProducts318.positive,PELOriginalCubeThetaProducts318.negative,
    Matrix.cons_val_zero,Matrix.cons_val_succ,←D.gauge]
lemma regular_unit (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :
    IsUnit (regular τ hτ N D side b) := by
  apply ComplexOpenPointEvaluation318.isUnit (structureMap τ hτ) (chart τ hτ b)
  intro p hp
  obtain ⟨x,y,z,he⟩ := point_representation τ hτ _ p hp
  rw [regular_evaluation τ hτ N D side b p x y z he,selected_value]
  have hn (t : Fin 11) : D.lineData.g (b t) (argument x y z t)≠0 :=
    D.lineData.nonzero _ _ (point_mem τ hτ b p x y z he t)
  have h0 := hn 0;have h1 := hn 1;have h2 := hn 2;have h3 := hn 3;have h4 := hn 4
  have h5 := hn 5;have h6 := hn 6;have h7 := hn 7;have h8 := hn 8;have h9 := hn 9;have h10 := hn 10
  dsimp only [argument,Matrix.cons_val_zero,Matrix.cons_val_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hd := mul_ne_zero (mul_ne_zero (pow_ne_zero 4 h0) (pow_ne_zero 4 h1)) (pow_ne_zero 4 h2)
  cases side
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero h4 h5) h6) h7) h8) h9) h10) hd
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero h3 h0) h1) h2) h8) h9) h10) hd
@[expose] def unit (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) := (regular_unit τ hτ N D side b).unit
lemma unit_value (side : Bool) (b : PELOriginalCubeOpenCover318.Index τ hτ) :
    (unit τ hτ N D side b).val=regular τ hτ N D side b := IsUnit.unit_spec _
end PELOriginalCubeRegularCoefficients318
