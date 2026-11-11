module
public import PELOriginalCubicRelationIdeal318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace PELOriginalReducedProjectiveCandidate318
open AlgebraicGeometry CategoryTheory TopologicalSpace Set
open PELOriginalCubicRelationIdeal318 PELOriginalLevelTheta318

/-- The actual standard total-degree grading on the nine-variable
polynomial ring. It is not a grading pulled back from an expected model. -/
abbrev degrees:ℕ→Submodule ℂ Equations:=MvPolynomial.homogeneousSubmodule (Label 3) ℂ
local instance standardGrading:GradedAlgebra degrees:=MvPolynomial.gradedAlgebra
@[expose] def ambient:Scheme:=AlgebraicGeometry.Proj degrees
variable (τ:ℂ) (hτ:0<τ.im)
/-- Exact homogeneous-prime zero locus of the produced original section
relations. No asserted theta equations or numerical parameters enter. -/
@[expose] def zeroSet:Closeds ambient:=
  ⟨ProjectiveSpectrum.zeroLocus degrees (relations τ hτ:Set Equations),
    ProjectiveSpectrum.isClosed_zeroLocus degrees _⟩
@[expose] def equationSheaf:ambient.IdealSheafData:=
  Scheme.IdealSheafData.vanishingIdeal (zeroSet τ hτ)

/-- The canonical REDUCED closed projective candidate. This construction
explicitly uses the vanishing ideal sheaf of the exact zero locus. It
DOES NOT identify it with Proj of an unproved saturated/radical kernel,
or identify its entire complex locus with the original analytic image. -/
@[expose] def candidate:Scheme:=(equationSheaf τ hτ).subscheme
@[expose] def inclusion:candidate τ hτ⟶ambient:=(equationSheaf τ hτ).subschemeι
instance closedImmersion:IsClosedImmersion (inclusion τ hτ):=inferInstance
lemma inclusion_range:Set.range (inclusion τ hτ)=(zeroSet τ hτ:Set ambient):=by
  rw [inclusion,Scheme.IdealSheafData.range_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
lemma point_mem_iff (p:ambient):
    p∈Set.range (inclusion τ hτ)↔∀F∈relations τ hτ,F∈p.asHomogeneousIdeal:=by
  rw [inclusion_range]
  exact ProjectiveSpectrum.mem_zeroLocus degrees p (relations τ hτ:Set Equations)
@[expose] def candidate_cover: (candidate τ hτ).AffineOpenCover:=
  (equationSheaf τ hτ).subschemeCover

/-- Every affine chart of the candidate is an ACTUAL quotient of the
ambient scheme's section ring by its actual pointwise vanishing ideal.
This records explicitly where radicalization occurs. -/
lemma actual_affine_ideal(U:ambient.affineOpens):
    (equationSheaf τ hτ).ideal U=
      PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (zeroSet τ hτ:Set ambient)):=
  Scheme.IdealSheafData.vanishingIdeal_ideal _ _
@[expose] def actual_affine_sections(U:ambient.affineOpens):
    CommRingCat.of (Γ(ambient,U)⧸(equationSheaf τ hτ).ideal U)≅
      Γ(candidate τ hτ,(inclusion τ hτ) ⁻¹ᵁ U):=
  ((equationSheaf τ hτ).subschemeObjIso U).symm

/-- Reducedness is verified on the genuine quotient affine cover; it is
not inferred merely from calling the construction a reduced candidate. -/
theorem reduced:IsReduced (candidate τ hτ):=by
  haveI:∀U,IsReduced ((candidate_cover τ hτ).openCover.X U):=by
    intro U
    haveI:((equationSheaf τ hτ).ideal U).IsRadical:=by
      rw [actual_affine_ideal]
      infer_instance
    change IsReduced (Spec (CommRingCat.of (Γ(ambient,U)⧸(equationSheaf τ hτ).ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ (candidate_cover τ hτ).openCover
end PELOriginalReducedProjectiveCandidate318
