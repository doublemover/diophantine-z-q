module
public import OriginalAffineFrameEvaluation318
public import ContactOriginalGeneratedPositiveLine318
public section
noncomputable section
namespace ContactPositiveChartEvaluation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L

/-- Same original global restrictions, reconciled with the native
structural R action on each ACTUAL affine pulled section module. -/
@[expose] def finiteRestriction : Γ(L.object,⊤) →ₗ[R] structuralFinite R c L :=
  (finiteIdentity R c L).toLinearMap.comp
    ((LinearMap.fst R _ _).comp (ContactRelativeOriginalHZero318.pair R c L))
@[expose] def infinityRestriction : Γ(L.object,⊤) →ₗ[R] structuralInfinity R c L :=
  (infinityIdentity R c L).toLinearMap.comp
    ((LinearMap.snd R _ _).comp (ContactRelativeOriginalHZero318.pair R c L))

lemma finite_span {r : ℕ} (s : Fin r → Γ(L.object,⊤))
    (hs : Submodule.span (Polynomial R) (Set.range (fun i =>
      (ContactRelativeOriginalHZero318.pair R c L (s i)).1))=⊤) :
    Submodule.span (R ⊗[ℚ] finiteRing c) (Set.range (finiteRestriction R c L))=⊤ := by
  letI : IsScalarTower (Polynomial R) (R ⊗[ℚ] finiteRing c) (finiteSections R c L) :=
    IsScalarTower.of_compHom ..
  have hg := OriginalAffineGeneratorPullback318.span_of_restriction
    (Polynomial R) (R ⊗[ℚ] finiteRing c) (finiteSections R c L)
    (fun i => (ContactRelativeOriginalHZero318.pair R c L (s i)).1) hs
  apply top_unique
  rw [← hg]
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  exact ⟨s i,rfl⟩

lemma infinity_span {r : ℕ} (s : Fin r → Γ(L.object,⊤))
    (hs : Submodule.span (Polynomial R) (Set.range (fun i =>
      (ContactRelativeOriginalHZero318.pair R c L (s i)).2))=⊤) :
    Submodule.span (R ⊗[ℚ] infinityRing c) (Set.range (infinityRestriction R c L))=⊤ := by
  letI : IsScalarTower (Polynomial R) (R ⊗[ℚ] infinityRing c) (infinitySections R c L) :=
    IsScalarTower.of_compHom ..
  have hg := OriginalAffineGeneratorPullback318.span_of_restriction
    (Polynomial R) (R ⊗[ℚ] infinityRing c) (infinitySections R c L)
    (fun i => (ContactRelativeOriginalHZero318.pair R c L (s i)).2) hs
  apply top_unique
  rw [← hg]
  apply Submodule.span_mono
  rintro x ⟨i,rfl⟩
  exact ⟨s i,rfl⟩

/-- The generation hypotheses needed at the actual local framed
evaluation consumer are now PRODUCED for every sufficiently positive
original line. This is the same index as original H1 vanishing. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ)),x=0) ∧
    Submodule.span (R ⊗[ℚ] finiteRing c)
      (Set.range (finiteRestriction R c (twist R c L n)))=⊤ ∧
    Submodule.span (R ⊗[ℚ] infinityRing c)
      (Set.range (infinityRestriction R c (twist R c L n)))=⊤ := by
  obtain ⟨N,r,q,hN⟩ := ContactOriginalGeneratedPositiveLine318.exists_bound R c L
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨hz,⟨s,hs⟩,⟨t,ht⟩⟩ := hN n hn
  exact ⟨hz,finite_span R c _ s hs,infinity_span R c _ t ht⟩
end ContactPositiveChartEvaluation318
