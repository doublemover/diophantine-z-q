module
public import ComplexSphereAffineAutomorphisms318
public section
noncomputable section
namespace ComplexSphereAffineNormalization318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ComplexSphereCharts318 SphereInversion318
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

-- Shared implementation: genuine finite removability, not a second
-- competing affine sphere proof. These aliases retain existing consumers.
abbrev affineSphere := ComplexSphereAffineAutomorphisms318.affineSphere
abbrev affineSphere_coe := ComplexSphereAffineAutomorphisms318.affineSphere_coe
abbrev affineSphere_infty := ComplexSphereAffineAutomorphisms318.affineSphere_infty
abbrev affineSphere_holomorphic := ComplexSphereAffineAutomorphisms318.affineSphere_holomorphic
abbrev inversion_holomorphic := ComplexSphereAffineAutomorphisms318.inversion_holomorphic

/-- Send any chosen actual sphere point to infinity by a genuine
biholomorphic coordinate change, without prescribing another branch value. -/
@[expose] def poleCoordinate (p:OnePoint ℂ) : OnePoint ℂ≃ₜOnePoint ℂ:=
  p.elim (Homeomorph.refl _) (fun z=>
    (affineSphere 1 (-z) one_ne_zero).trans inversionHomeomorph)
lemma poleCoordinate_at (p:OnePoint ℂ) : poleCoordinate p p=∞:=by
  induction p using OnePoint.rec with
  | infty=>rfl
  | coe z=>change inversion ((1*z+-z:ℂ):OnePoint ℂ)=∞;simp only [one_mul,add_neg_cancel,inversion_zero]

theorem poleCoordinate_holomorphic (p:OnePoint ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (poleCoordinate p) := by
  induction p using OnePoint.rec with
  | infty=>exact contMDiff_id
  | coe z=>exact inversion_holomorphic.comp (affineSphere_holomorphic 1 (-z) one_ne_zero)
end ComplexSphereAffineNormalization318
