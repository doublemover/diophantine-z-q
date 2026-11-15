module
public import ContactRelativeGlobalSectionLifting318
public import RelativeTwoChartGeneratorLifting318
public section
noncomputable section
namespace ContactRelativeGlobalGenerators318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalRelativeOverlapSpan318 ContactRelativeGeometricTwist318
open ContactRelativeGlobalSectionLifting318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) :=
  Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) :=
  Module.compHom (infinitySections R c L) Polynomial.C

/-- Actual finitely many GLOBAL sections generate both entire polynomial
charts of every sufficiently positive original twist. The two finite
families can be united; no global-generation or lifting premise is supplied. -/
theorem exists_generators : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (r s : ℕ) (a : Fin r → Γ((twist R c L (n : ℤ)).object,⊤))
      (b : Fin s → Γ((twist R c L (n : ℤ)).object,⊤)),
      Submodule.span (Polynomial R) (Set.range (fun i => finiteGlobal R c L (n : ℤ) (a i))) = ⊤ ∧
      Submodule.span (Polynomial R) (Set.range (fun j => infinityGlobal R c L (n : ℤ) (b j))) = ⊤ := by
  obtain ⟨r,g,hg⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := finiteSections R c L)
  obtain ⟨s,h,hh⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := infinitySections R c L)
  obtain ⟨N,hN⟩ := RelativeTwoChartGeneratorLifting318.exists_bound R (originalSections R c L)
    (finiteMap R c L).range (infinityMap R c L).range
    (fun i => finiteRestriction R c L (g i)) (fun j => infinityRestriction R c L (h j))
    (RelativePolynomialChartGenerators318.positive_stable R (originalSections R c L)
      (finiteSections R c L) (finiteMap R c L) (finite_polynomial R c L))
    (RelativePolynomialChartBound318.negative_stable R (originalSections R c L)
      (infinitySections R c L) (infinityMap R c L) (infinity_polynomial R c L))
    (finite_span R c L) (infinity_span R c L)
  refine ⟨N,fun n hn => ?_⟩
  have ha : ∀ i : Fin r, ∃ a : Γ((twist R c L (n : ℤ)).object,⊤),
      finiteGlobal R c L (n : ℤ) a = g i := by
    intro i
    obtain ⟨v,hv⟩ := (hN n hn).1 i
    have hab : finiteRestriction R c L (g i) =
        (T (n : ℤ) : LaurentPolynomial R) • infinityRestriction R c L v := by
      change infinityRestriction R c L v =
        (T (-(n : ℤ)) : LaurentPolynomial R) • finiteRestriction R c L (g i) at hv
      rw [hv,RelativeLaurentScalar318.shift_add,add_neg_cancel,T_zero,one_smul]
    obtain ⟨a,hai,_⟩ := exists_section R c L (n : ℤ) (g i) v hab
    exact ⟨a,hai⟩
  have hb : ∀ j : Fin s, ∃ b : Γ((twist R c L (n : ℤ)).object,⊤),
      infinityGlobal R c L (n : ℤ) b = h j := by
    intro j
    obtain ⟨u,hu⟩ := (hN n hn).2 j
    obtain ⟨b,_,hbj⟩ := exists_section R c L (n : ℤ) u (h j) hu
    exact ⟨b,hbj⟩
  choose a ha using ha
  choose b hb using hb
  refine ⟨r,s,a,b,?_,?_⟩
  · rw [show (fun i => finiteGlobal R c L (n : ℤ) (a i)) = g from funext ha]
    exact hg
  · rw [show (fun j => infinityGlobal R c L (n : ℤ) (b j)) = h from funext hb]
    exact hh
end ContactRelativeGlobalGenerators318
