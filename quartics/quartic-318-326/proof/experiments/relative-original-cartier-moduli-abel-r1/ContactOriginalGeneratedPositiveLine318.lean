module
public import ContactTwistPolynomialCoordinates318
public section
noncomputable section
namespace ContactOriginalGeneratedPositiveLine318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- Every original line admits a single sufficiently positive twist
whose ACTUAL global sections generate both original whole-chart modules.
The same bound also gives the H1 vanishing required by the existing
finite-projective section parameter and universal zero-family producers.
This is not a claim that every specialized section is regular or flat. -/
theorem exists_bound : ∃ N r q : ℕ, ∀ n : ℕ, N ≤ n →
    (∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ)),x=0) ∧
    (∃ s : Fin r → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i =>
        (ContactRelativeOriginalHZero318.pair R c (twist R c L (n : ℤ)) (s i)).1)) = ⊤) ∧
    (∃ s : Fin q → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i =>
        (ContactRelativeOriginalHZero318.pair R c (twist R c L (n : ℤ)) (s i)).2)) = ⊤) := by
  obtain ⟨N,r,q,hN⟩ := ContactPositiveGlobalGenerators318.exists_uniform_bound R c L
  refine ⟨N,r,q,fun n hn => ?_⟩
  obtain ⟨hz,⟨s,hs⟩,⟨t,ht⟩⟩ := hN n hn
  refine ⟨hz,⟨s,?_⟩,⟨t,?_⟩⟩
  · apply ContactTwistPolynomialCoordinates318.span_of_equiv R
      (ContactTwistPolynomialCoordinates318.finite R c L n)
    simpa only [ContactTwistPolynomialCoordinates318.finite_apply,
      ContactTwistGlobalCoordinates318.finiteValue,LinearMap.comp_apply,LinearMap.fst_apply,
      LinearEquiv.coe_coe] using hs
  · apply ContactTwistPolynomialCoordinates318.span_of_equiv R
      (ContactTwistPolynomialCoordinates318.infinity R c L n)
    simpa only [ContactTwistPolynomialCoordinates318.infinity_apply,
      ContactTwistGlobalCoordinates318.infinityValue,LinearMap.comp_apply,LinearMap.snd_apply,
      LinearEquiv.coe_coe] using ht
end ContactOriginalGeneratedPositiveLine318
