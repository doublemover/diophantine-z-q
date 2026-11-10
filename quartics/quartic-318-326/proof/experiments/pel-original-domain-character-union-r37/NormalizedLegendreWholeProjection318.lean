module
public import NormalizedLegendreFiniteProjection318
public import WeierstrassActualInfinityProjection318
public import ProjectiveLineActualAutomorphismPoints318
public section
noncomputable section
namespace NormalizedLegendreWholeProjection318
open AlgebraicGeometry CategoryTheory
open NormalizedLegendreProjectiveModel318 NormalizedLegendreFieldPoints318
open NormalizedLegendreFiniteProjection318 ProjectiveLineComplexSchemePoints318
open scoped OnePoint
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The infinity fiber is attached to the SAME full Scheme morphism. -/
lemma infinity_projection (l:ℂ) :
    project l (schemeEquiv l none)=spherePoint (∞:OnePoint ℂ) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) ≫
    WeierstrassGluing318.infinity (A l) (B l)) ≫
      NormalizedLegendreSchemeProjection318.projection l=(chartPoint 0 0).val
  rw [show Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))=𝟙 _ from Spec.map_id _,
    Category.id_comp]
  change WeierstrassGluing318.infinity (A l) (B l) ≫
    (WeierstrassXProjection318.xMap (A l) (B l) ≫
      ProjectiveAffineLine318.map ℂ 1 (shift l))=(chartPoint 0 0).val
  rw [←Category.assoc,WeierstrassActualInfinityProjection318.infinity_projection]
  exact ProjectiveLineActualAutomorphismPoints318.affine_infinity 1 (shift l)

@[expose] def coordinate (l:ℂ) : Option (FinitePoints l)→OnePoint ℂ
  | none=>∞
  | some p=>(p.val.1:ℂ)
@[expose] def deck (l:ℂ) : Option (FinitePoints l)≃Option (FinitePoints l):=
  Equiv.optionCongr (sign l)

/-- Complete comparison with the actual Scheme projection on ALL complex
points, including infinity and every exceptional finite coordinate. -/
theorem whole_projection (l:ℂ) (p:Option (FinitePoints l)) :
    project l (schemeEquiv l p)=spherePoint (coordinate l p) := by
  cases p with
  | none=>exact infinity_projection l
  | some p=>exact finite_projection l p

/-- The entire completed projection is the actual sign quotient on points.
This does not promote a point correspondence to a Scheme isomorphism. -/
theorem same_coordinate (l:ℂ) (p q:Option (FinitePoints l)) :
    coordinate l p=coordinate l q ↔ p=q ∨ deck l p=q := by
  cases p with
  | none=>
    cases q with
    | none=>simp [coordinate,deck]
    | some q=>simp [coordinate,deck]
  | some p=>
    cases q with
    | none=>simp [coordinate,deck]
    | some q=>
      change (p.val.1:OnePoint ℂ)=(q.val.1:OnePoint ℂ) ↔
        some p=some q ∨ some (sign l p)=some q
      simpa only [OnePoint.coe_eq_coe,Option.some.injEq] using
        NormalizedLegendreFieldPoints318.same_coordinate l p q

theorem same_projected_scheme_point (l:ℂ) (p q:Option (FinitePoints l)) :
    project l (schemeEquiv l p)=project l (schemeEquiv l q) ↔ p=q ∨ deck l p=q := by
  simp only [whole_projection,spherePoint_bijective.1.eq_iff]
  exact same_coordinate l p q

/-- Four branch values and their fixed points are attached to this same
completed Scheme projection, with the true original infinity retained. -/
theorem fixed_iff_branch (l:ℂ) (p:Option (FinitePoints l)) :
    deck l p=p ↔ coordinate l p=∞ ∨ coordinate l p=(0:ℂ) ∨
      coordinate l p=(1:ℂ) ∨ coordinate l p=(l:ℂ) := by
  cases p with
  | none=>simp [coordinate,deck]
  | some p=>
    change some (sign l p)=some p ↔ (p.val.1:OnePoint ℂ)=∞ ∨
      (p.val.1:OnePoint ℂ)=(0:ℂ) ∨ (p.val.1:OnePoint ℂ)=(1:ℂ) ∨
      (p.val.1:OnePoint ℂ)=(l:ℂ)
    simp only [Option.some.injEq,OnePoint.coe_ne_infty,OnePoint.coe_eq_coe,false_or,
      sign_fixed_iff,zero_iff_branch]
end NormalizedLegendreWholeProjection318
