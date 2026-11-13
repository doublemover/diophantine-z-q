module
public import OriginalPeriodNativeChartGerms318
public section
noncomputable section
namespace OriginalPeriodSchemeChartPoints318
open CategoryTheory AlgebraicGeometry MvPolynomial
open OriginalComplexPeriodPair318 OriginalPeriodWeierstrassCoordinates318
open OriginalPeriodProjectiveModel318 OriginalPeriodNativeChartGerms318
open ComplexAffineFreeTranslation318 Filter Topology
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Actual evaluation of the finite algebraic coordinate ring at the
original torus coordinates. It factors through the literal equation. -/
@[expose] def finiteEvaluation (q : {q : Torus L // q≠0}) :
    ShortAffineJacobian318.Ring (A L) (B L) →ₐ[ℂ] ℂ := by
  let e : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ := aeval ![x L q.val,y L q.val/2]
  have hk : Ideal.span (Set.range (ShortAffineJacobian318.equations (A L) (B L))) ≤
      RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (ShortAffineJacobian318.equation (A L) (B L))=0
    simp only [e,ShortAffineJacobian318.equation,map_sub,map_pow,map_mul,aeval_X,aeval_C,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    have h := cubic L q.val q.property
    dsimp [A,B]
    linear_combination h/4
  exact Ideal.Quotient.liftₐ _ e (fun f hf => hk hf)

lemma finite_x (q : {q : Torus L // q≠0}) :
    finiteEvaluation L q (ShortAffineJacobian318.x (A L) (B L))=x L q.val := by
  simp [finiteEvaluation,ShortAffineJacobian318.x,Ideal.Quotient.liftₐ_apply]
lemma finite_y (q : {q : Torus L // q≠0}) :
    finiteEvaluation L q (ShortAffineJacobian318.y (A L) (B L))=y L q.val/2 := by
  simp [finiteEvaluation,ShortAffineJacobian318.y,Ideal.Quotient.liftₐ_apply]

/-- The native analytic finite coordinates produce genuine scheme-valued
complex points, not just elements of an abstract cubic solution set. -/
@[expose] def finitePoint (q : {q : Torus L // q≠0}) :
    Spec (CommRingCat.of ℂ) ⟶ model L :=
  Spec.map (CommRingCat.ofHom (finiteEvaluation L q).toRingHom) ≫
    WeierstrassGluing318.finiteChart (A L) (B L)

lemma finitePoint_over_base (q : {q : Torus L // q≠0}) :
    finitePoint L q ≫ structure L=𝟙 _ := by
  rw [finitePoint,Category.assoc,WeierstrassGluing318.finiteChart_structure]
  change Spec.map (CommRingCat.ofHom (finiteEvaluation L q).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (ShortAffineJacobian318.Ring (A L) (B L))))=𝟙 _
  rw [←Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap ℂ (ShortAffineJacobian318.Ring (A L) (B L))) ≫
      CommRingCat.ofHom (finiteEvaluation L q).toRingHom=𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (finiteEvaluation L q).commutes c
  rw [he,Spec.map_id]

/-- The infinity coordinate-ring evaluation retains the actual native
regularized coordinates and their literal algebraic equation. -/
@[expose] def infinityEvaluation (q : Torus L)
    (hq : nativeV L q-nativeU L q^3-A L*nativeU L q*nativeV L q^2-B L*nativeV L q^3=0) :
    InfinityChart318.Ring (A L) (B L) →ₐ[ℂ] ℂ := by
  let e : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ := aeval ![nativeU L q,nativeV L q]
  have hk : Ideal.span (Set.range (InfinityChart318.equations (A L) (B L))) ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (InfinityChart318.equation (A L) (B L))=0
    simpa [e,InfinityChart318.equation] using hq
  exact Ideal.Quotient.liftₐ _ e (fun f hf => hk hf)

lemma infinity_x (q : Torus L) (hq) :
    infinityEvaluation L q hq (InfinityChart318.x (A L) (B L))=nativeU L q := by
  simp [infinityEvaluation,InfinityChart318.x,Ideal.Quotient.liftₐ_apply]
lemma infinity_z (q : Torus L) (hq) :
    infinityEvaluation L q hq (InfinityChart318.z (A L) (B L))=nativeV L q := by
  simp [infinityEvaluation,InfinityChart318.z,Ideal.Quotient.liftₐ_apply]

/-- Such evaluations exist on an actual original neighborhood of infinity;
the equation premise is discharged by the constructed analytic germ. -/
theorem infinity_evaluations : ∀ᶠ q in 𝓝 (0:Torus L),
    ∃ e : InfinityChart318.Ring (A L) (B L) →ₐ[ℂ] ℂ,
      e (InfinityChart318.x (A L) (B L))=nativeU L q ∧
      e (InfinityChart318.z (A L) (B L))=nativeV L q := by
  filter_upwards [infinity_equation L] with q hq
  exact ⟨infinityEvaluation L q hq,infinity_x L q hq,infinity_z L q hq⟩
end OriginalPeriodSchemeChartPoints318
