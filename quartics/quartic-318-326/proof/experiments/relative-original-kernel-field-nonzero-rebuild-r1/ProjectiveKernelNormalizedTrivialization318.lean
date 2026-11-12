module
public import ProjectiveKernelNormalizationEquations318
public import AlgebraEquationQuotientPoints318
public section
noncomputable section
namespace ProjectiveKernelNormalizedTrivialization318
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
abbrev PrincipalPoint (S : Type) [CommRing S] [Algebra R S] :=
  AlgebraEquationQuotientPoints318.Points R (H i)
    (ProjectiveKernelNormalizationEquations318.principalEquation R P Q d i) S
abbrev SlicePoint (S : Type) [CommRing S] [Algebra R S] :=
  AlgebraEquationQuotientPoints318.Points R (B i)
    (ProjectiveKernelNormalizationEquations318.sliceEquation R P Q d i) S
variable (S : Type) [CommRing S] [Algebra R S]
local notation "E" => ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of S)
@[expose] def forward (a : PrincipalPoint R P Q d i S) : Sˣ × SlicePoint R P Q d i S :=
  ((E a.val).1,⟨(E a.val).2,(ProjectiveKernelNormalizationEquations318.vanishing_iff R P Q d i S a.val).mp a.property⟩)
@[expose] def backward (a : Sˣ × SlicePoint R P Q d i S) : PrincipalPoint R P Q d i S :=
  ⟨E.symm (a.1,a.2.val),by
    apply (ProjectiveKernelNormalizationEquations318.vanishing_iff R P Q d i S _).mpr
    rw [Equiv.apply_symm_apply]
    exact a.2.property⟩
/-- Principal charts of the ACTUAL differential kernel split as a true
unit and an actual normalized kernel point, without H0 projectivity. -/
@[expose] def equivalence : PrincipalPoint R P Q d i S ≃ Sˣ × SlicePoint R P Q d i S where
  toFun := forward R P Q d i S
  invFun := backward R P Q d i S
  left_inv a := by
    apply Subtype.ext
    exact E.symm_apply_apply a.val
  right_inv a := by
    apply Prod.ext
    · exact congrArg Prod.fst (E.apply_symm_apply (a.1,a.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd (E.apply_symm_apply (a.1,a.2.val))
variable {T : Type} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
lemma unit_natural (a : PrincipalPoint R P Q d i S) :
    (equivalence R P Q d i T (AlgebraEquationQuotientPoints318.map _ _ _ _ g a)).1=
      Units.map g.toMonoidHom (equivalence R P Q d i S a).1 := rfl
lemma slice_natural (a : PrincipalPoint R P Q d i S) :
    (equivalence R P Q d i T (AlgebraEquationQuotientPoints318.map _ _ _ _ g a)).2=
      AlgebraEquationQuotientPoints318.map _ _ _ _ g (equivalence R P Q d i S a).2 := by
  apply Subtype.ext
  exact ProjectivePrincipalTrivializationNatural318.slice_natural R P i
    (CommRingCat.of S) (CommRingCat.of T) g a.val

end ProjectiveKernelNormalizedTrivialization318
