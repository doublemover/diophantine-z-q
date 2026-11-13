module
public import ProjectiveKernelNormalizedLaurent318
public import AffineQuotientPullback318
public section
noncomputable section
namespace ProjectiveKernelPrincipalCartesian318
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
local notation "f" => CommRingCat.ofHom (ProjectiveParameterPrincipalNormalization318.point R P i).toRingHom
local notation "I" => ProjectiveKernelParameter318.ideal R P Q d
local notation "J" => AlgebraEquationQuotientPoints318.ideal R (H i)
  (ProjectiveKernelNormalizationEquations318.principalEquation R P Q d i)
/-- The principal equations are EXACTLY the extension of the old full
kernel ideal, not a new ideal with only the same support. -/
lemma ideal_map : J=Ideal.map f.hom I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨φ,rfl⟩
    exact Ideal.mem_map_of_mem f.hom (Ideal.subset_span (Set.mem_range_self φ))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro x ⟨φ,rfl⟩
    exact Ideal.subset_span (Set.mem_range_self φ)
@[expose] def intoRing : CommRingCat.of (ProjectiveKernelParameter318.algebra R P Q d) ⟶
    CommRingCat.of (ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i) :=
  AffineQuotientPullback318.arrow f I J (ideal_map R P Q d i)
@[expose] def intoAlgebra : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R]
    ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i :=
  Ideal.Quotient.liftₐ I
    ((ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i).comp
      (ProjectiveParameterPrincipalNormalization318.point R P i)) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [ideal_map]
        exact Ideal.mem_map_of_mem f.hom ha)
lemma intoAlgebra_comp : (intoAlgebra R P Q d i).comp (ProjectiveKernelParameter318.quotient R P Q d)=
    (ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i).comp
      (ProjectiveParameterPrincipalNormalization318.point R P i) :=
  Ideal.Quotient.liftₐ_comp _ _ _
lemma intoAlgebra_ring : CommRingCat.ofHom (intoAlgebra R P Q d i).toRingHom=intoRing R P Q d i := by
  apply CommRingCat.hom_ext
  ext z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl
@[expose] def into : Spec (CommRingCat.of (ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i)) ⟶
    Spec (CommRingCat.of (ProjectiveKernelParameter318.algebra R P Q d)) := Spec.map (intoRing R P Q d i)
/-- Actual Cartesian square with the original kernel closed immersion
and the original ambient principal open. -/
lemma cartesian : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) (into R P Q d i)
    (Spec.map f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  AffineQuotientPullback318.pullback_square f I J (ideal_map R P Q d i)
instance open : IsOpenImmersion (into R P Q d i) := by
  haveI : IsOpenImmersion (Spec.map f) := Scheme.isOpenImmersion_SpecMap_localizationAway
  exact MorphismProperty.of_isPullback (cartesian R P Q d i) inferInstance

end ProjectiveKernelPrincipalCartesian318
