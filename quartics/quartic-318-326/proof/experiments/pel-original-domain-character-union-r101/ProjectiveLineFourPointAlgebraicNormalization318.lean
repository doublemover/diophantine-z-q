module
public import ProjectiveLineAlgebraicNormalization318
public import ComplexSphereFourPointNormalization318
public section
noncomputable section
namespace ProjectiveLineFourPointAlgebraicNormalization318
open AlgebraicGeometry CategoryTheory
open ProjectiveLineComplexSchemePoints318 ProjectiveLineActualAutomorphismPoints318
open ProjectiveLineAlgebraicNormalization318 ComplexSphereAffineAutomorphisms318
open scoped OnePoint
set_option maxHeartbeats 1600000

/-- A concrete algebraic realization on the ORIGINAL Proj target. The
comparison is equality of full complex Scheme-valued morphisms. -/
structure Realization (h:OnePoint ℂ≃ₜOnePoint ℂ) where
  schemeIso : ProjectiveJLine318.scheme ℂ≅ProjectiveJLine318.scheme ℂ
  over_base : schemeIso.hom≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ
  action : ∀p:OnePoint ℂ,(spherePoint p).val≫schemeIso.hom=(spherePoint (h p)).val

@[expose] def identity : Realization (Homeomorph.refl (OnePoint ℂ)) where
  schemeIso:=Iso.refl _
  over_base:=Category.id_comp _
  action p:=Category.comp_id _

@[expose] def compose {h k:OnePoint ℂ≃ₜOnePoint ℂ} (a:Realization h) (b:Realization k) :
    Realization (h.trans k) where
  schemeIso:=a.schemeIso.trans b.schemeIso
  over_base:=by change (a.schemeIso.hom≫b.schemeIso.hom)≫_=_;rw [Category.assoc,b.over_base,a.over_base]
  action p:=by
    change (spherePoint p).val≫(a.schemeIso.hom≫b.schemeIso.hom)=_
    calc
      _ = (spherePoint (h p)).val≫b.schemeIso.hom := by rw [←Category.assoc,a.action]
      _ = _ := b.action (h p)

@[expose] def affine (a b:ℂ) (ha:a≠0) : Realization (affineSphere a b ha) where
  schemeIso:=ProjectiveAffineLine318.iso ℂ (Units.mk0 a ha) b
  over_base:=ProjectiveAffineCharts318.map_over_base ℂ (Units.mk0 a ha) b
  action p:=by simpa only [Units.val_mk0] using affine_sphere (Units.mk0 a ha) b p

@[expose] def inversion : Realization SphereInversion318.inversionHomeomorph where
  schemeIso:=ProjectiveSwap318.iso ℂ
  over_base:=ProjectiveSwapCharts318.over_base ℂ
  action:=inversion_sphere

/-- The exact same chosen-pole normalization is algebraic on the target,
including the case where the chosen original point is already infinity. -/
@[expose] def pole (p:OnePoint ℂ) :
    Realization (ComplexSphereAffineNormalization318.poleCoordinate p) := by
  induction p using OnePoint.rec with
  | infty=>exact identity
  | coe z=>exact compose (affine 1 (-z) one_ne_zero) inversion

/-- The genuine three-point normalization already used for actual branch
values is represented by an actual base-preserving Scheme isomorphism. -/
@[expose] def fourPoints (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p) :
    Realization (ComplexSphereFourPointNormalization318.normalization p hp) :=
  compose (pole (p 0)) (affine
    (ComplexSphereFourPointNormalization318.finiteCoordinate p hp 1-
      ComplexSphereFourPointNormalization318.finiteCoordinate p hp 0)⁻¹
    (-ComplexSphereFourPointNormalization318.finiteCoordinate p hp 0/
      (ComplexSphereFourPointNormalization318.finiteCoordinate p hp 1-
        ComplexSphereFourPointNormalization318.finiteCoordinate p hp 0))
    (inv_ne_zero (ComplexSphereFourPointNormalization318.denominator_ne p hp)))

/-- Four exact marked-point images on the actual projective Scheme target.
The fourth coordinate is the constructed complex cross-ratio, not an
assumed rational or preselected arithmetic coefficient. -/
theorem four_actual_images (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p) :
    let e:=(fourPoints p hp).schemeIso
    (spherePoint (p 0)).val≫e.hom=(chartPoint 0 0).val ∧
    (spherePoint (p 1)).val≫e.hom=(chartPoint 1 0).val ∧
    (spherePoint (p 2)).val≫e.hom=(chartPoint 1 1).val ∧
    (spherePoint (p 3)).val≫e.hom=
      (chartPoint 1 (ComplexSphereFourPointNormalization318.parameter p hp)).val := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [ComplexSphereFourPointNormalization318.normalization_zero,spherePoint_infty]
      using (fourPoints p hp).action (p 0)
  · simpa only [ComplexSphereFourPointNormalization318.normalization_one,spherePoint_coe]
      using (fourPoints p hp).action (p 1)
  · simpa only [ComplexSphereFourPointNormalization318.normalization_two,spherePoint_coe]
      using (fourPoints p hp).action (p 2)
  · simpa only [ComplexSphereFourPointNormalization318.normalization_three,spherePoint_coe]
      using (fourPoints p hp).action (p 3)
end ProjectiveLineFourPointAlgebraicNormalization318
