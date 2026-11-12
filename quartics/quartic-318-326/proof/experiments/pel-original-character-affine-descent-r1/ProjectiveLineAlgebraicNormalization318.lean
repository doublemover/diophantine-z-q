module
public import ProjectiveLineActualAutomorphismPoints318
public import ProjectiveLineStandardSphereComparison318
public section
noncomputable section
namespace ProjectiveLineAlgebraicNormalization318
open AlgebraicGeometry CategoryTheory
open ProjectiveLineComplexSchemePoints318 ProjectiveLineIndependentPointTopology318
open ProjectiveLineIndependentComplexAtlas318 ProjectiveLineStandardSphereComparison318
open ProjectiveLineActualAutomorphismPoints318 ComplexSphereAffineAutomorphisms318
open scoped OnePoint Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : TopologicalSpace SchemePoints:=pointTopology
local instance : ChartedSpace ℂ SchemePoints:=pointCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω SchemePoints:=complex_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=ComplexSphereCharts318.sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=ComplexSphereCharts318.sphere_manifold

/-- Actual postcomposition on base-preserving complex Scheme points. -/
@[expose] def pointMap (f:ProjectiveJLine318.scheme ℂ⟶ProjectiveJLine318.scheme ℂ)
    (hf:f≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ)
    (p:SchemePoints) : SchemePoints:=⟨p.val≫f,by
  rw [Category.assoc,hf]
  exact p.property⟩

lemma inverse_over_base (e:ProjectiveJLine318.scheme ℂ≅ProjectiveJLine318.scheme ℂ)
    (he:e.hom≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ) :
    e.inv≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ := by
  calc
    _ = e.inv≫(e.hom≫ProjectiveJLine318.structureMap ℂ) := congrArg (fun f=>e.inv≫f) he.symm
    _ = _ := by rw [←Category.assoc,e.inv_hom_id,Category.id_comp]

@[expose] def pointEquiv (e:ProjectiveJLine318.scheme ℂ≅ProjectiveJLine318.scheme ℂ)
    (he:e.hom≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ) :
    SchemePoints≃SchemePoints where
  toFun:=pointMap e.hom he
  invFun:=pointMap e.inv (inverse_over_base e he)
  left_inv p:=by apply Subtype.ext;change (p.val≫e.hom)≫e.inv=p.val;rw [Category.assoc,e.hom_inv_id,Category.comp_id]
  right_inv p:=by apply Subtype.ext;change (p.val≫e.inv)≫e.hom=p.val;rw [Category.assoc,e.inv_hom_id,Category.comp_id]

@[expose] def affinePoints (a:ℂˣ) (b:ℂ) : SchemePoints≃SchemePoints:=
  pointEquiv (ProjectiveAffineLine318.iso ℂ a b) (ProjectiveAffineCharts318.map_over_base ℂ a b)
@[expose] def inversionPoints : SchemePoints≃SchemePoints:=
  pointEquiv (ProjectiveSwap318.iso ℂ) (ProjectiveSwapCharts318.over_base ℂ)

/-- Exact intertwining with the existing algebraic Scheme automorphism,
not an automorphism invented by transporting a point set. -/
theorem affinePoints_sphere (a:ℂˣ) (b:ℂ) (p:OnePoint ℂ) :
    affinePoints a b (spherePoint p)=spherePoint (affineSphere (a:ℂ) b a.ne_zero p) :=
  Subtype.ext (affine_sphere a b p)
theorem inversionPoints_sphere (p:OnePoint ℂ) :
    inversionPoints (spherePoint p)=spherePoint (SphereInversion318.inversionHomeomorph p) :=
  Subtype.ext (inversion_sphere p)

/-- Original polynomial-chart holomorphy of the actual algebraic action.
The target retains its independent atlas; equality to the holomorphic
comparison is proved using every actual Scheme point. -/
theorem affinePoints_holomorphic (a:ℂˣ) (b:ℂ) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (affinePoints a b) := by
  have he : (affinePoints a b:SchemePoints→SchemePoints)=
      sphereSchemeHomeomorph ∘ affineSphere (a:ℂ) b a.ne_zero ∘ sphereSchemeHomeomorph.symm := by
    funext p
    obtain ⟨z,rfl⟩:=spherePoint_bijective.2 p
    simpa only [Function.comp_apply,Homeomorph.symm_apply_apply] using affinePoints_sphere a b z
  rw [he]
  exact sphereSchemeHomeomorph_biholomorphic.1.comp
    ((affineSphere_holomorphic (a:ℂ) b a.ne_zero).comp sphereSchemeHomeomorph_biholomorphic.2)

theorem inversionPoints_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω inversionPoints := by
  have he : (inversionPoints:SchemePoints→SchemePoints)=
      sphereSchemeHomeomorph ∘ SphereInversion318.inversionHomeomorph ∘ sphereSchemeHomeomorph.symm := by
    funext p
    obtain ⟨z,rfl⟩:=spherePoint_bijective.2 p
    simpa only [Function.comp_apply,Homeomorph.symm_apply_apply] using inversionPoints_sphere z
  rw [he]
  exact sphereSchemeHomeomorph_biholomorphic.1.comp
    (inversion_holomorphic.comp sphereSchemeHomeomorph_biholomorphic.2)
end ProjectiveLineAlgebraicNormalization318
