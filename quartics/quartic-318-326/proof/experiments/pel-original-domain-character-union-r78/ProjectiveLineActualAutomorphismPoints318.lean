module
public import ProjectiveLineGradedPointAction318
public import ProjectiveLineIndependentPointTopology318
public import ComplexSphereAffineAutomorphisms318
public section
noncomputable section
namespace ProjectiveLineActualAutomorphismPoints318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal
open ProjectiveLineGradedPointAction318
open ProjectiveLineComplexSchemePoints318 ComplexSphereAffineAutomorphisms318
open scoped OnePoint
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1600000
local notation "P" => MvPolynomial (Fin 2) ℂ
local notation "G" => ProjectiveJLine318.grading ℂ

private lemma point_action (f:G→+*ᵍ G) (hf:G₊≤G₊.map f)
    (φ ψ:P→ₐ[ℂ]ℂ) (hψ:ψ.toRingHom=φ.toRingHom.comp f.toRingHom)
    (j k:Fin 2) (hj:IsUnit (φ (X j))) (hk:IsUnit (ψ (X k)))
    (v w:ℂ) (hv:φ (X j)*v=1) (hw:ψ (X k)*w=1) :
    (chartPoint j (φ (X (j.succAbove 0))*v)).val ≫ Proj.map f hf =
      (chartPoint k (ψ (X (k.succAbove 0))*w)).val := by
  simpa only [chartPoint,affinePoint_value] using
    coordinate_action f hf φ ψ hψ j k hj hk v w hv hw

/-- The action is equality of actual Scheme morphisms at every finite point. -/
theorem affine_finite (a:ℂˣ) (b z:ℂ) :
    (chartPoint 1 z).val ≫ (ProjectiveAffineLine318.iso ℂ a b).hom=
      (chartPoint 1 ((a:ℂ)*z+b)).val := by
  let φ:P→ₐ[ℂ]ℂ:=MvPolynomial.aeval ![z,1]
  let ψ:P→ₐ[ℂ]ℂ:=φ.comp (GradedAffineLine318.hom ℂ a b)
  have hj:IsUnit (φ (X 1)):=by simp [φ]
  have hk:IsUnit (ψ (X 1)):=by simp [ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,φ]
  have hψ:ψ.toRingHom=φ.toRingHom.comp (ProjectiveAffineLine318.gh ℂ a b).toRingHom:=rfl
  have he:=point_action (ProjectiveAffineLine318.gh ℂ a b)
    (ProjectiveAffineLine318.irrelevant_le ℂ a b) φ ψ hψ 1 1 hj hk 1 1
    (by simp [φ]) (by simp [ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,φ])
  simpa [φ,ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,ProjectiveAffineLine318.iso,ProjectiveAffineLine318.map] using he

/-- Projective infinity remains the original chart-zero point, including
its complete Scheme-valued structure, under the affine automorphism. -/
theorem affine_infinity (a:ℂˣ) (b:ℂ) :
    (chartPoint 0 0).val ≫ (ProjectiveAffineLine318.iso ℂ a b).hom=(chartPoint 0 0).val := by
  let φ:P→ₐ[ℂ]ℂ:=MvPolynomial.aeval ![1,0]
  let ψ:P→ₐ[ℂ]ℂ:=φ.comp (GradedAffineLine318.hom ℂ a b)
  have hj:IsUnit (φ (X 0)):=by simp [φ]
  have hk:IsUnit (ψ (X 0)):=by simpa [ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,φ] using a.isUnit
  have hψ:ψ.toRingHom=φ.toRingHom.comp (ProjectiveAffineLine318.gh ℂ a b).toRingHom:=rfl
  have he:=point_action (ProjectiveAffineLine318.gh ℂ a b)
    (ProjectiveAffineLine318.irrelevant_le ℂ a b) φ ψ hψ 0 0 hj hk 1 (↑a⁻¹)
    (by simp [φ]) (by simp [ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,φ])
  simpa [φ,ψ,GradedAffineLine318.hom,GradedAffineLine318.variableImage,ProjectiveAffineLine318.iso,ProjectiveAffineLine318.map] using he

/-- Coordinate inversion sends the whole finite chart to the opposite
original chart, including zero. There is no deleted exceptional point. -/
theorem inversion_finite (z:ℂ) :
    (chartPoint 1 z).val ≫ (ProjectiveSwap318.iso ℂ).hom=(chartPoint 0 z).val := by
  let φ:P→ₐ[ℂ]ℂ:=MvPolynomial.aeval ![z,1]
  let ψ:P→ₐ[ℂ]ℂ:=φ.comp (ProjectiveSwap318.hom ℂ)
  have hj:IsUnit (φ (X 1)):=by simp [φ]
  have hk:IsUnit (ψ (X 0)):=by simp [ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,φ]
  have hψ:ψ.toRingHom=φ.toRingHom.comp (ProjectiveSwap318.gh ℂ).toRingHom:=rfl
  have he:=point_action (ProjectiveSwap318.gh ℂ)
    (ProjectiveSwap318.irrelevant_le ℂ) φ ψ hψ 1 0 hj hk 1 1
    (by simp [φ]) (by simp [ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,φ])
  simpa [φ,ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,ProjectiveSwap318.iso,ProjectiveSwap318.map] using he

theorem inversion_infinity :
    (chartPoint 0 0).val ≫ (ProjectiveSwap318.iso ℂ).hom=(chartPoint 1 0).val := by
  let φ:P→ₐ[ℂ]ℂ:=MvPolynomial.aeval ![1,0]
  let ψ:P→ₐ[ℂ]ℂ:=φ.comp (ProjectiveSwap318.hom ℂ)
  have hj:IsUnit (φ (X 0)):=by simp [φ]
  have hk:IsUnit (ψ (X 1)):=by simp [ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,φ]
  have hψ:ψ.toRingHom=φ.toRingHom.comp (ProjectiveSwap318.gh ℂ).toRingHom:=rfl
  have he:=point_action (ProjectiveSwap318.gh ℂ)
    (ProjectiveSwap318.irrelevant_le ℂ) φ ψ hψ 0 1 hj hk 1 1
    (by simp [φ]) (by simp [ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,φ])
  simpa [φ,ψ,ProjectiveSwap318.hom,ProjectiveSwap318.variableImage,ProjectiveSwap318.iso,ProjectiveSwap318.map] using he

/-- Full original complex-point action of the actual affine Scheme iso
agrees with the independently constructed holomorphic sphere automorphism. -/
theorem affine_sphere (a:ℂˣ) (b:ℂ) (p:OnePoint ℂ) :
    (spherePoint p).val ≫ (ProjectiveAffineLine318.iso ℂ a b).hom=
      (spherePoint (affineSphere (a:ℂ) b a.ne_zero p)).val := by
  induction p using OnePoint.rec with
  | infty => simpa only [spherePoint_infty,affineSphere_infty] using affine_infinity a b
  | coe z => simpa only [spherePoint_coe,affineSphere_coe] using affine_finite a b z

theorem inversion_sphere (p:OnePoint ℂ) :
    (spherePoint p).val ≫ (ProjectiveSwap318.iso ℂ).hom=
      (spherePoint (SphereInversion318.inversionHomeomorph p)).val := by
  induction p using OnePoint.rec with
  | infty => simpa only [spherePoint_infty,SphereInversion318.inversion_infty,
      spherePoint_coe] using inversion_infinity
  | coe z =>
    rw [spherePoint_coe,inversion_finite]
    exact congrArg Subtype.val (ProjectiveLineIndependentPointTopology318.spherePoint_inversion z).symm
end ProjectiveLineActualAutomorphismPoints318
