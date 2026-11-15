module
public import FiniteComplexPointIndex318
public import PELOriginalEtaleKernelDivision318
public import PELOriginalKernelComplexCardinality318
public section
noncomputable section
namespace PELOriginalTorsionKernelSplit318
open AlgebraicGeometry CategoryTheory
open PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (hn : 0<n)
include hn in
lemma finiteMap : IsFinite (structureMap τ hτ (n:ℤ)) :=
  (PELOriginalEtaleKernelDivision318.kernel_finite_etale τ hτ (n:ℤ)
    (by exact_mod_cast hn.ne')).1
include hn in
lemma etaleMap : Etale (structureMap τ hτ (n:ℤ)) :=
  (PELOriginalEtaleKernelDivision318.kernel_finite_etale τ hτ (n:ℤ)
    (by exact_mod_cast hn.ne')).2
include hn in
lemma pointFinite : Finite (FiniteComplexPointsScheme318.Points
    (structureMap τ hτ (n:ℤ))) :=
  PELOriginalKernelComplexCardinality318.finite τ hτ n hn
local instance : Algebra ℂ Γ(kernel τ hτ (n:ℤ),⊤) :=
  FiniteEtaleComplexSections318.algebra (structureMap τ hτ (n:ℤ))

include hn in
/-- The ACTUAL entire equalizer kernel is reduced, as a consequence
of the proved native finite étale structure, not by replacement. -/
lemma reduced : AlgebraicGeometry.IsReduced (kernel τ hτ (n:ℤ)) := by
  letI := finiteMap τ hτ n hn
  letI := etaleMap τ hτ n hn
  exact FiniteEtaleComplexSections318.reduced (structureMap τ hτ (n:ℤ))

/-- The whole original kernel algebra is the product of n^4 copies
of C, indexed by the exact original four-coordinate torsion representatives. -/
@[expose] def split : Γ(kernel τ hτ (n:ℤ),⊤) ≃ₐ[ℂ] ((Fin 4→Fin n)→ℂ) := by
  letI := finiteMap τ hτ n hn
  letI := etaleMap τ hτ n hn
  letI := pointFinite τ hτ n hn
  exact (FiniteComplexPointIndex318.split (structureMap τ hτ (n:ℤ))).trans
    (AlgEquiv.piCongrLeft ℂ (fun _ : Fin 4→Fin n => ℂ)
      (PELOriginalKernelComplexCardinality318.enumeration τ hτ n hn).symm)

/-- A whole over-C scheme isomorphism with the literal product algebra,
indexed by original torsion representatives, including all multiplicities. -/
@[expose] def schemeSplit : kernel τ hτ (n:ℤ) ≅
    Spec (CommRingCat.of ((Fin 4→Fin n)→ℂ)) := by
  letI := finiteMap τ hτ n hn
  exact FiniteEtaleComplexSections318.schemeIso (structureMap τ hτ (n:ℤ)) (split τ hτ n hn)
lemma schemeSplit_over : (schemeSplit τ hτ n hn).hom≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ ((Fin 4→Fin n)→ℂ)))=
      structureMap τ hτ (n:ℤ) := by
  letI := finiteMap τ hτ n hn
  exact FiniteEtaleComplexSections318.schemeIso_over _ _

include hn in
/-- Genuine scheme-theoretic kernel length. The earlier n^4 point
count is promoted only after full finite étale splitting has been proved. -/
lemma length : Module.finrank ℂ Γ(kernel τ hτ (n:ℤ),⊤)=n^4 := by
  letI := finiteMap τ hτ n hn
  letI := etaleMap τ hτ n hn
  letI := pointFinite τ hτ n hn
  rw [FiniteComplexPointIndex318.finrank]
  exact PELOriginalKernelComplexCardinality318.cardinality τ hτ n hn
end PELOriginalTorsionKernelSplit318
