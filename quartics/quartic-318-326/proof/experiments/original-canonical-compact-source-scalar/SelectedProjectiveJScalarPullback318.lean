module
public import SelectedProjectiveJScalar318
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
import all JLineAtlas318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SelectedProjectiveJScalarPullback318
universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
local notation "b" => Spec.algebraMap R S
local notation "c" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R S)))
local notation "q" => SelectedProjectiveJScalar318.scalarMap (algebraMap R S)
local notation "T" => S ⊗[R] Polynomial R
local notation "πR" => Spec.algebraMap R (Polynomial R)
local notation "πS" => Spec.algebraMap S (Polynomial S)

/-- The affine scalar square is the actual tensor product over the
coefficient ring, with both actual projections. -/
theorem affine_pullback : IsPullback c πS πR b := by
  let ψ := (polyEquivTensor' R S).symm.toRingEquiv.toCommRingCatIso
  let e : Spec (CommRingCat.of (Polynomial S)) ≅ Spec (CommRingCat.of T) :=
    Scheme.Spec.mapIso ψ.op
  have he : e.hom = Spec.map ψ.hom := by
    simp only [e, Functor.mapIso_hom, Iso.op_hom, ← Scheme.Spec_map, Quiver.Hom.unop_op]
  have hLeft : e.hom ≫ Spec.algebraMap S T = πS := by
    rw [he, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (polyEquivTensor' R S).symm (algebraMap S T x) = algebraMap S (Polynomial S) x
    exact (polyEquivTensor' R S).symm.commutes x
  have hRight : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : Polynomial R →ₐ[R] T).toRingHom) = c := by
    rw [he, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change (polyEquivTensor' R S).symm ((1:S) ⊗ₜ[R] p) = Polynomial.map (algebraMap R S) p
    simp only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  have hComm : πS ≫ b = c ≫ πR := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change Polynomial.C (algebraMap R S x) = Polynomial.map (algebraMap R S) (Polynomial.C x)
    exact (Polynomial.map_C _ _).symm
  have h : IsPullback πS c b πR := by
    refine IsPullback.of_iso_pullback ⟨hComm⟩
      (e ≪≫ (pullbackSpecIso R S (Polynomial R)).symm) ?_ ?_
    · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst'] using hLeft
    · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd] using hRight
  exact h.flip

/-- The actual inverse image of each original basic chart is the
same-index original basic chart after scalar extension. -/
theorem chart_pullback (i : Fin 2) :
    IsPullback (JLineAtlas318.chart S i) c q (JLineAtlas318.chart R i) := by
  refine (IsOpenImmersion.isPullback c (JLineAtlas318.chart S i) (JLineAtlas318.chart R i)
    q (SelectedProjectiveJScalar318.chart_natural (algebraMap R S) i) ?_).flip
  rw [JLineAtlas318.chart_range R i, JLineAtlas318.chart_range S i,
    SelectedProjectiveJScalar318.scalarMap, Proj.map_preimage_basicOpen,
    SelectedProjectiveJScalar318.graded_X]

/-- The canonical map on the original Proj is its actual universal
scalar pullback. The two verified original affine charts cover the
whole target, including the cusp. -/
theorem projective_pullback :
    IsPullback q (ProjectiveJLine318.structureMap S) (ProjectiveJLine318.structureMap R) b := by
  refine Scheme.isPullback_of_openCover q (ProjectiveJLine318.structureMap S)
    (ProjectiveJLine318.structureMap R) b (JLineAtlas318.cover R) ?_
  intro i
  change Fin 2 at i
  change IsPullback (pullback.snd q (JLineAtlas318.chart R i))
    (pullback.fst q (JLineAtlas318.chart R i) ≫ ProjectiveJLine318.structureMap S)
    (JLineAtlas318.chart R i ≫ ProjectiveJLine318.structureMap R) b
  let e := (chart_pullback R S i).isoPullback
  refine (affine_pullback R S).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom,Category.comp_id,e,IsPullback.isoPullback_hom_snd]
  · simp only [Iso.refl_hom,Category.comp_id,← Category.assoc,e,
      IsPullback.isoPullback_hom_fst,JLineAtlas318.chart_over_base]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id,JLineAtlas318.chart_over_base]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]

section ChangedCompact
variable {X X' : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R)
  (p : X' ⟶ X) (s : X' ⟶ Spec (CommRingCat.of S))
  (h : IsPullback p s (j ≫ ProjectiveJLine318.structureMap R) b)

/-- The actual base-changed modular morphism is constructed by the
universal pullback, not given independently or up to a scalar. -/
@[expose] def changedJ : X' ⟶ ProjectiveJLine318.scheme S :=
  (projective_pullback R S).lift (p ≫ j) s (by simpa only [Category.assoc] using h.w)

@[reassoc] theorem changedJ_q :
    changedJ R S j p s h ≫ q = p ≫ j :=
  (projective_pullback R S).lift_fst _ _ _

@[reassoc] theorem changedJ_base :
    changedJ R S j p s h ≫ ProjectiveJLine318.structureMap S = s :=
  (projective_pullback R S).lift_snd _ _ _

/-- A genuine constant-field pullback of the source automatically
gives the required compact j-square above the fixed original map. -/
theorem changedJ_pullback : IsPullback p (changedJ R S j p s h) j q := by
  have outer : IsPullback p (changedJ R S j p s h ≫ ProjectiveJLine318.structureMap S)
      (j ≫ ProjectiveJLine318.structureMap R) b := by
    rw [changedJ_base]
    exact h
  exact outer.of_bot (changedJ_q R S j p s h).symm (projective_pullback R S)

end ChangedCompact
end SelectedProjectiveJScalarPullback318

#print axioms SelectedProjectiveJScalarPullback318.affine_pullback
#print axioms SelectedProjectiveJScalarPullback318.chart_pullback
#print axioms SelectedProjectiveJScalarPullback318.projective_pullback
#print axioms SelectedProjectiveJScalarPullback318.changedJ_pullback
