module
public import ProjectiveJLine318
public import ProjectiveChart318
public import Mathlib.Logic.Equiv.Fin.Basic
public section
noncomputable section
namespace JLineAtlas318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]

/-- Actual dehomogenization of any standard projective line chart. -/
@[expose] def chartEquiv (j : Fin 2) : Away (ProjectiveJLine318.grading R) (X j) ≃ₐ[R] Polynomial R :=
  (ProjectiveChart318.chartEquiv R (Fin 2) j).trans ((renameEquiv R (finSuccAboveEquiv j).symm).trans (uniqueAlgEquiv R (Fin 1)))

@[expose] def chart (j : Fin 2) : Spec (CommRingCat.of (Polynomial R)) ⟶ ProjectiveJLine318.scheme R :=
  Spec.map (chartEquiv R j).toRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (ProjectiveJLine318.grading R) (X j) (isHomogeneous_X R j) (by omega)
instance chart_open (j : Fin 2) : IsOpenImmersion (chart R j) := by
  unfold chart
  infer_instance

lemma chart_range (j : Fin 2) : (chart R j).opensRange=Proj.basicOpen (ProjectiveJLine318.grading R) (X j) := by
  change (Spec.map (chartEquiv R j).toRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (ProjectiveJLine318.grading R) (X j) (isHomogeneous_X R j) (by omega)).opensRange=_
  rw [Scheme.Hom.opensRange_comp_of_isIso,Proj.opensRange_awayι]

/-- The actual degree-one coordinates generate the ambient homogeneous algebra over its degree zero. -/
lemma coordinates_adjoin : Algebra.adjoin (ProjectiveJLine318.grading R 0)
    (Set.range (X : Fin 2 → MvPolynomial (Fin 2) R))=⊤ := by
  let A := Algebra.adjoin (ProjectiveJLine318.grading R 0)
    (Set.range (X : Fin 2 → MvPolynomial (Fin 2) R))
  suffices ∀ p, p ∈ A from top_unique (fun p _ => this p)
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact A.algebraMap_mem (ProjectiveJLine318.zeroEquiv R r)
  | add p q hp hq => exact A.add_mem hp hq
  | mul_X p i hp => exact A.mul_mem hp (Algebra.subset_adjoin ⟨i,rfl⟩)

lemma standard_opens_cover : (⨆ j : Fin 2, Proj.basicOpen (ProjectiveJLine318.grading R) (X j))=⊤ :=
  Proj.iSup_basicOpen_eq_top' (ProjectiveJLine318.grading R) X
    (fun j => ⟨1,isHomogeneous_X R j⟩) (coordinates_adjoin R)

/-- The two explicit polynomial affine schemes actually cover the proper projective line. -/
def cover : (ProjectiveJLine318.scheme R).OpenCover where
  I₀ := Fin 2
  X _ := Spec (CommRingCat.of (Polynomial R))
  f := chart R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    have hp : p ∈ (⊤ : (ProjectiveJLine318.scheme R).Opens) := trivial
    rw [←standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at hp
    obtain ⟨j,hj⟩ := hp
    rw [←chart_range] at hj
    obtain ⟨q,hq⟩ := hj
    exact ⟨j,q,hq⟩

/-- Actual chart maps commute with the same base ring, not a degree-zero surrogate. -/
theorem chart_over_base (j : Fin 2) : chart R j ≫ ProjectiveJLine318.structureMap R=
    Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) := by
  unfold chart ProjectiveJLine318.structureMap
  rw [Category.assoc,←Category.assoc (Proj.awayι _ _ _ _),Proj.awayι_toSpecZero]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (chartEquiv R j).commutes r


theorem chartEquiv_symm_X (j : Fin 2) :
    (chartEquiv R j).symm Polynomial.X=
      ProjectiveChart318.coordinate R (Fin 2) j (finSuccAboveEquiv j 0) := by
  simp [chartEquiv,ProjectiveChart318.chartEquiv,ProjectiveChart318.toChart,
    MvPolynomial.uniqueAlgEquiv]

end JLineAtlas318
