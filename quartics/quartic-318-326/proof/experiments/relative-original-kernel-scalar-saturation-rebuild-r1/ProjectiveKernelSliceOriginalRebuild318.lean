module
public import ProjectiveKernelNormalizedAlgebras318
public section
noncomputable section
namespace ProjectiveKernelSliceOriginalRebuild318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "K" => ProjectiveKernelParameter318.algebra R P Q d
variable (i : Fin F.size)
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i
local notation "qb" => ProjectiveKernelNormalizedAlgebras318.sliceQuotient R P Q d i
local notation "q" => Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P i)
def ambient : A →ₐ[R] C := qb.comp q
lemma equation_zero (φ : Module.Dual R Q) :
    ambient R P Q d i (ProjectiveKernelEquations318.equation R P Q d φ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self φ))
lemma ideal_le_kernel : ProjectiveKernelParameter318.ideal R P Q d ≤
    RingHom.ker (ambient R P Q d i).toRingHom := by
  apply Ideal.span_le.mpr
  rintro z ⟨φ,rfl⟩
  exact equation_zero R P Q d i φ
/-- The ACTUAL coordinate-one slice has an original full-kernel point.
No reduced quotient or assumed inclusion of point sets replaces it. -/
def intoAlgebra : K →ₐ[R] C :=
  Ideal.Quotient.liftₐ (ProjectiveKernelParameter318.ideal R P Q d)
    (ambient R P Q d i) (fun z hz => ideal_le_kernel R P Q d i hz)
lemma into_quotient : (intoAlgebra R P Q d i).comp (ProjectiveKernelParameter318.quotient R P Q d) =
    ambient R P Q d i := Ideal.Quotient.liftₐ_comp _ _ _
lemma coordinate_one : intoAlgebra R P Q d i
    (ProjectiveKernelParameter318.quotient R P Q d
      (ProjectiveParameterZeroCoordinates318.coordinate R P i)) = 1 := by
  change qb (q (ProjectiveParameterZeroCoordinates318.coordinate R P i)) = 1
  rw [ProjectiveParameterSliceAlgebra318.coordinate_one,map_one]
def into : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (intoAlgebra R P Q d i).toRingHom)
end ProjectiveKernelSliceOriginalRebuild318
