module
public import ProjectiveParameterSliceSchemes318
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace ProjectiveParameterSliceNonzero318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
abbrev locus : (Spec (CommRingCat.of A)).Opens := ProjectiveParameterNonzeroOpen318.locus R P
variable (i : Fin F.size)

/-- Every prime of an ACTUAL coordinate-one slice lies in the original
nonzero parameter open: the zero ideal cannot contain a coordinate equal
to one, even when the base or the slice has nilpotents. -/
lemma prime_nonzero (p : PrimeSpectrum (B i)) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i)) p ∈
      ProjectiveParameterNonzeroOpen318.locus R P := by
  rw [ProjectiveParameterNonzeroOpen318.mem_locus]
  intro h
  have hx := h (Ideal.subset_span (show x i∈Set.range (ProjectiveParameterZeroCoordinates318.coordinate R P) from ⟨i,rfl⟩))
  change Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) (x i)∈p.asIdeal at hx
  rw [ProjectiveParameterSliceAlgebra318.coordinate_one] at hx
  exact p.isPrime.ne_top (Ideal.eq_top_iff_one.mpr hx)

@[expose] def parameterMap : ProjectiveParameterSliceSchemes318.chart R P i ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i)))
lemma range_nonzero : Set.range (parameterMap R P i) ⊆
    (ProjectiveParameterNonzeroOpen318.locus R P : Set (Spec (CommRingCat.of A))) := by
  rintro _ ⟨p,rfl⟩
  exact prime_nonzero R P i p

/-- Genuine factorization of each actual normalized slice through the
existing nonzero universal parameter OPEN, not a new locus definition. -/
@[expose] def intoNonzero : ProjectiveParameterSliceSchemes318.chart R P i ⟶
    (locus R P).toScheme :=
  IsOpenImmersion.lift (locus R P).ι (parameterMap R P i) (by
    rw [Scheme.Opens.range_ι]
    exact range_nonzero R P i)
@[reassoc] lemma intoNonzero_fac : intoNonzero R P i ≫
    (locus R P).ι=parameterMap R P i :=
  IsOpenImmersion.lift_fac _ _ _
end ProjectiveParameterSliceNonzero318
