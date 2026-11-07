module
public import ProjectivePlane318
public import ProjectiveChart318
public import Mathlib.Logic.Equiv.Fin.Basic
public section
noncomputable section
namespace ProjectiveAtlas318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]

/-- Actual dehomogenization of any standard projective plane chart. -/
@[expose] def chartEquiv (j : Fin 3) : Away (ProjectivePlane318.grading R) (X j) ≃ₐ[R] MvPolynomial (Fin 2) R :=
  (ProjectiveChart318.chartEquiv R (Fin 3) j).trans (renameEquiv R (finSuccAboveEquiv j).symm)

@[expose] def chart (j : Fin 3) : Spec (CommRingCat.of (MvPolynomial (Fin 2) R)) ⟶ ProjectivePlane318.scheme R :=
  Spec.map (chartEquiv R j).toRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (ProjectivePlane318.grading R) (X j) (isHomogeneous_X R j) (by omega)
instance chart_open (j : Fin 3) : IsOpenImmersion (chart R j) := by
  unfold chart
  infer_instance

lemma chart_range (j : Fin 3) : (chart R j).opensRange=Proj.basicOpen (ProjectivePlane318.grading R) (X j) := by
  change (Spec.map (chartEquiv R j).toRingEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (ProjectivePlane318.grading R) (X j) (isHomogeneous_X R j) (by omega)).opensRange=_
  rw [Scheme.Hom.opensRange_comp_of_isIso,Proj.opensRange_awayι]

/-- The actual degree-one coordinates generate the ambient homogeneous algebra over its degree zero. -/
lemma coordinates_adjoin : Algebra.adjoin (ProjectivePlane318.grading R 0)
    (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R))=⊤ := by
  let A := Algebra.adjoin (ProjectivePlane318.grading R 0)
    (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R))
  suffices ∀ p, p ∈ A from top_unique (fun p _ => this p)
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact A.algebraMap_mem (ProjectivePlane318.zeroEquiv R r)
  | add p q hp hq => exact A.add_mem hp hq
  | mul_X p i hp => exact A.mul_mem hp (Algebra.subset_adjoin ⟨i,rfl⟩)

lemma standard_opens_cover : (⨆ j : Fin 3, Proj.basicOpen (ProjectivePlane318.grading R) (X j))=⊤ :=
  Proj.iSup_basicOpen_eq_top' (ProjectivePlane318.grading R) X
    (fun j => ⟨1,isHomogeneous_X R j⟩) (coordinates_adjoin R)

/-- The three explicit polynomial affine schemes actually cover the proper projective plane. -/
def cover : (ProjectivePlane318.scheme R).OpenCover where
  I₀ := Fin 3
  X _ := Spec (CommRingCat.of (MvPolynomial (Fin 2) R))
  f := chart R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    have hp : p ∈ (⊤ : (ProjectivePlane318.scheme R).Opens) := trivial
    rw [←standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at hp
    obtain ⟨j,hj⟩ := hp
    rw [←chart_range] at hj
    obtain ⟨q,hq⟩ := hj
    exact ⟨j,q,hq⟩

/-- Actual chart maps commute with the same base ring, not a degree-zero surrogate. -/
theorem chart_over_base (j : Fin 3) : chart R j ≫ ProjectivePlane318.structureMap R=
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 2) R))) := by
  unfold chart ProjectivePlane318.structureMap
  rw [Category.assoc,←Category.assoc (Proj.awayι _ _ _ _),Proj.awayι_toSpecZero]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (chartEquiv R j).commutes r

theorem chartEquiv_symm_X (j : Fin 3) (i : Fin 2) :
    (chartEquiv R j).symm (X i)=ProjectiveChart318.coordinate R (Fin 3) j (finSuccAboveEquiv j i) := by
  simp [chartEquiv,ProjectiveChart318.chartEquiv,ProjectiveChart318.toChart]

section HomExt
variable {T : Type*} [CommRing T] [Algebra R T]
lemma chart_hom_ext (j : Fin 3) {f g : Away (ProjectivePlane318.grading R) (X j) →ₐ[R] T}
    (h : ∀ i : Fin 2, f ((chartEquiv R j).symm (X i))=g ((chartEquiv R j).symm (X i))) : f=g := by
  have hh : f.comp (chartEquiv R j).symm.toAlgHom=g.comp (chartEquiv R j).symm.toAlgHom :=
    MvPolynomial.algHom_ext h
  apply AlgHom.ext
  intro a
  obtain ⟨b,rfl⟩ := (chartEquiv R j).symm.surjective a
  exact AlgHom.congr_fun hh b
end HomExt

end ProjectiveAtlas318
