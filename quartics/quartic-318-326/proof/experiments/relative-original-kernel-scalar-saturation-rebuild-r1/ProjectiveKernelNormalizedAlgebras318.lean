module
public import ProjectiveKernelNormalizedTrivialization318
public section
noncomputable section
namespace ProjectiveKernelNormalizedAlgebras318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i : Fin F.size)
abbrev principalRing := AlgebraEquationQuotientPoints318.algebra R (H i)
  (ProjectiveKernelNormalizationEquations318.principalEquation R P Q d i)
abbrev sliceRing := AlgebraEquationQuotientPoints318.algebra R (B i)
  (ProjectiveKernelNormalizationEquations318.sliceEquation R P Q d i)
abbrev principalQuotient : H i →ₐ[R] principalRing R P Q d i :=
  AlgebraEquationQuotientPoints318.quotient R (H i) _
abbrev sliceQuotient : B i →ₐ[R] sliceRing R P Q d i :=
  AlgebraEquationQuotientPoints318.quotient R (B i) _
variable (S : Type) [CommRing S] [Algebra R S]
/-- ACTUAL affine quotient rings for both the principal kernel chart and
its normalized slice; all equations are retained, not only their radical. -/
@[expose] def points : (principalRing R P Q d i →ₐ[R] S) ≃
    Sˣ × (sliceRing R P Q d i →ₐ[R] S) :=
  (AlgebraEquationQuotientPoints318.points R (H i) _ S).trans
    ((ProjectiveKernelNormalizedTrivialization318.equivalence R P Q d i S).trans
      (Equiv.prodCongr (Equiv.refl _) (AlgebraEquationQuotientPoints318.points R (B i) _ S).symm))
lemma slice_quotient (a : principalRing R P Q d i →ₐ[R] S) :
    (points R P Q d i S a).2.comp (sliceQuotient R P Q d i)=
      (ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of S)
        (a.comp (principalQuotient R P Q d i))).2 :=
  AlgebraEquationQuotientPoints318.backward_quotient R (B i) _ S _
variable {T : Type} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
lemma unit_natural (a : principalRing R P Q d i →ₐ[R] S) :
    (points R P Q d i T (g.comp a)).1=Units.map g.toMonoidHom (points R P Q d i S a).1 := rfl
lemma slice_natural (a : principalRing R P Q d i →ₐ[R] S) :
    (points R P Q d i T (g.comp a)).2=g.comp (points R P Q d i S a).2 := by
  apply Ideal.Quotient.algHom_ext
  change (points R P Q d i T (g.comp a)).2.comp (sliceQuotient R P Q d i)=
    g.comp ((points R P Q d i S a).2.comp (sliceQuotient R P Q d i))
  rw [slice_quotient,slice_quotient]
  exact ProjectivePrincipalTrivializationNatural318.slice_natural R P i
    (CommRingCat.of S) (CommRingCat.of T) g (a.comp (principalQuotient R P Q d i))

end ProjectiveKernelNormalizedAlgebras318
