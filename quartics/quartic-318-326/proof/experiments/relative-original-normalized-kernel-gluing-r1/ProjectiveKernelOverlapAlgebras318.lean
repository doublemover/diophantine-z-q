module
public import ProjectiveKernelPrincipalCartesian318
public import ProjectiveParameterSliceSchemes318
public section
noncomputable section
namespace ProjectiveKernelOverlapAlgebras318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i j : Fin F.size)
@[expose] def equation (φ : Module.Dual R Q) : O i j :=
  ProjectiveParameterSliceLocalization318.point R P i j (eqn φ)
abbrev ideal := AlgebraEquationQuotientPoints318.ideal R (O i j) (equation R P Q d i j)
abbrev ring := AlgebraEquationQuotientPoints318.algebra R (O i j) (equation R P Q d i j)
abbrev quotient : O i j →ₐ[R] ring R P Q d i j :=
  AlgebraEquationQuotientPoints318.quotient R (O i j) _
local notation "I" => AlgebraEquationQuotientPoints318.ideal R (B i)
  (ProjectiveKernelNormalizationEquations318.sliceEquation R P Q d i)
local notation "f" => CommRingCat.ofHom (algebraMap (B i) (O i j))
/-- Every localized overlap carries the FULL extension of the old
normalized kernel ideal, including nilpotents. -/
lemma ideal_map : ideal R P Q d i j=Ideal.map f.hom I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨φ,rfl⟩
    exact Ideal.mem_map_of_mem f.hom (Ideal.subset_span (Set.mem_range_self φ))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro a ⟨φ,rfl⟩
    exact Ideal.subset_span (Set.mem_range_self φ)
@[expose] def leftRing : CommRingCat.of (C i) ⟶ CommRingCat.of (ring R P Q d i j) :=
  AffineQuotientPullback318.arrow f I (ideal R P Q d i j) (ideal_map R P Q d i j)
abbrev scheme : Scheme := Spec (CommRingCat.of (ring R P Q d i j))
@[expose] def left : scheme R P Q d i j ⟶ Spec (CommRingCat.of (C i)) :=
  Spec.map (leftRing R P Q d i j)
@[expose] def into : scheme R P Q d i j ⟶ ProjectiveParameterSliceSchemes318.overlap R P i j :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ideal R P Q d i j)))
@[expose] def sliceInto (i : Fin F.size) : Spec (CommRingCat.of (C i)) ⟶
    ProjectiveParameterSliceSchemes318.chart R P i :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (AlgebraEquationQuotientPoints318.ideal R (B i)
      (ProjectiveKernelNormalizationEquations318.sliceEquation R P Q d i))))
instance slice_closed (i : Fin F.size) : IsClosedImmersion (sliceInto R P Q d i) := by
  unfold sliceInto
  infer_instance
lemma cartesian : IsPullback (left R P Q d i j) (into R P Q d i j)
    (sliceInto R P Q d i) (ProjectiveParameterSliceSchemes318.inclusion R P i j) :=
  (AffineQuotientPullback318.pullback_square f I (ideal R P Q d i j)
    (ideal_map R P Q d i j)).flip
instance left_open : IsOpenImmersion (left R P Q d i j) :=
  MorphismProperty.of_isPullback (cartesian R P Q d i j).flip inferInstance

end ProjectiveKernelOverlapAlgebras318
