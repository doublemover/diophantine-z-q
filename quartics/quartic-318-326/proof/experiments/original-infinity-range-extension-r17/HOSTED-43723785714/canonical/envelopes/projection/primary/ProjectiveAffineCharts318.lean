module
public import ProjectiveAffineLine318
public section
noncomputable section
namespace ProjectiveAffineCharts318
open MvPolynomial Graded HomogeneousIdeal AlgebraicGeometry CategoryTheory HomogeneousLocalization
open ProjectiveAffineLine318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
lemma map_over_base (a:Rˣ) (b:R) :
    ProjectiveAffineLine318.map R a b ≫ ProjectiveJLine318.structureMap R = ProjectiveJLine318.structureMap R := by
  refine (Proj.mapAffineOpenCover (gh R a b) (irrelevant_le R a b)).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    ProjectiveAffineLine318.map]
  rw [← Category.assoc, Proj.awayι_comp_map (gh R a b) (irrelevant_le R a b) s.1.2 s.2.1 s.2.2, Category.assoc]
  unfold ProjectiveJLine318.structureMap
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change HomogeneousLocalization.Away.map (gh R a b) s.2.1
    (fromZeroRingHom _ _ (ProjectiveJLine318.zeroEquiv R r)) =
    fromZeroRingHom _ _ (ProjectiveJLine318.zeroEquiv R r)
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, ProjectiveJLine318.zeroEquiv, gh_C, map_one]
@[expose] def awayMapAt (f : grading R →+*ᵍ grading R) (x y : MvPolynomial (Fin 2) R)
    (h : f x=y) : Away (grading R) x →+* Away (grading R) y := h ▸ Away.map f x
lemma awayMapAt_mk (f : grading R →+*ᵍ grading R) (x y : MvPolynomial (Fin 2) R)
    (h : f x=y) {d : ℕ} (hx : x ∈ grading R d) (n : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p ∈ grading R (n • d)) :
    awayMapAt R f x y h (Away.mk (grading R) hx n p hp) =
      Away.mk (grading R) (h ▸ Graded.map_mem f hx) n (f p) (Graded.map_mem f hp) := by
  subst y
  exact Away.map_mk f x hx n p hp
lemma awayMapAt_naturality (f : grading R →+*ᵍ grading R)
    (hf : (grading R)₊ ≤ (grading R)₊.map f)
    (x y : MvPolynomial (Fin 2) R) (h : f x=y) {d : ℕ} (hd : 0<d) (hx : x ∈ grading R d) :
    Proj.awayι (grading R) y (h ▸ Graded.map_mem f hx) hd ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom (awayMapAt R f x y h)) ≫ Proj.awayι (grading R) x hx hd := by
  subst y
  exact Proj.awayι_comp_map f hf hd x hx
@[expose] def awayMap (a:Rˣ) (b:R) :
    Away (grading R) (X (1:Fin 2)) →+* Away (grading R) (X (1:Fin 2)) :=
  awayMapAt R (gh R a b) (X 1) (X 1) (gh_X1 R a b)
lemma away_naturality (a:Rˣ) (b:R) :
    Proj.awayι (grading R) (X (1:Fin 2)) (isHomogeneous_X R 1) (by omega) ≫ ProjectiveAffineLine318.map R a b =
      Spec.map (CommRingCat.ofHom (awayMap R a b)) ≫
        Proj.awayι (grading R) (X (1:Fin 2)) (isHomogeneous_X R 1) (by omega) :=
  awayMapAt_naturality R (gh R a b) (irrelevant_le R a b) (X 1) (X 1) (gh_X1 R a b)
    (by decide : 0<1) (isHomogeneous_X R 1)
lemma awayMap_C (a:Rˣ) (b r:R) :
    awayMap R a b (algebraMap R (Away (grading R) (X (1:Fin 2))) r)=
      algebraMap R (Away (grading R) (X (1:Fin 2))) r := by
  change awayMap R a b (Away.mk (grading R) (isHomogeneous_X R 1) 0 (C r) _) =
    Away.mk (grading R) (isHomogeneous_X R 1) 0 (C r) _
  rw [awayMap, awayMapAt_mk]
  simp only [gh_C]
lemma chart_mapped_X (a:Rˣ) (b:R) :
    JLineAtlas318.chartEquiv R 1 (awayMap R a b ((JLineAtlas318.chartEquiv R 1).symm Polynomial.X)) =
      Polynomial.C (a:R)*Polynomial.X+Polynomial.C b := by
  rw [JLineAtlas318.chartEquiv_symm_X]
  change JLineAtlas318.chartEquiv R 1 (awayMap R a b
    (Away.mk (grading R) (isHomogeneous_X R 1) 1 (X (0:Fin 2)) _)) = _
  rw [awayMap, awayMapAt_mk]
  change (uniqueAlgEquiv R (Fin 1)) ((renameEquiv R (finSuccAboveEquiv (1:Fin 2)).symm)
    (ProjectiveChart318.fromChart R (Fin 2) 1 (Away.mk (grading R) (isHomogeneous_X R 1) 1
      (gh R a b (X 0)) _))) = _
  rw [ProjectiveChart318.fromChart_mk]
  change (uniqueAlgEquiv R (Fin 1)) ((renameEquiv R (finSuccAboveEquiv (1:Fin 2)).symm)
    (ProjectiveChart318.dehomogenize R (Fin 2) 1 (GradedAffineLine318.hom R a b (X 0)))) = _
  rw [GradedAffineLine318.hom_X0]
  simp [ProjectiveChart318.dehomogenize, renameEquiv, uniqueAlgEquiv]
@[expose] def awayAlgHom (a:Rˣ) (b:R) :
    Away (grading R) (X (1:Fin 2)) →ₐ[R] Away (grading R) (X (1:Fin 2)) where
  __ := awayMap R a b
  commutes' := awayMap_C R a b
@[expose] def chartHom (a:Rˣ) (b:R) : Polynomial R →ₐ[R] Polynomial R :=
  (JLineAtlas318.chartEquiv R 1).toAlgHom.comp ((awayAlgHom R a b).comp
    (JLineAtlas318.chartEquiv R 1).symm.toAlgHom)
lemma chartHom_eq (a:Rˣ) (b:R) : chartHom R a b =
    Polynomial.aeval (Polynomial.C (a:R)*Polynomial.X+Polynomial.C b) := by
  apply Polynomial.algHom_ext
  rw [Polynomial.aeval_X]
  change JLineAtlas318.chartEquiv R 1 (awayMap R a b ((JLineAtlas318.chartEquiv R 1).symm Polynomial.X)) = _
  exact chart_mapped_X R a b
lemma chart_naturality (a:Rˣ) (b:R) :
    JLineAtlas318.chart R 1 ≫ ProjectiveAffineLine318.map R a b =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval
        (Polynomial.C (a:R)*Polynomial.X+Polynomial.C b)).toRingHom) ≫ JLineAtlas318.chart R 1 := by
  unfold JLineAtlas318.chart
  rw [Category.assoc, away_naturality]
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change JLineAtlas318.chartEquiv R 1 (awayMap R a b p) =
    Polynomial.aeval (Polynomial.C (a:R)*Polynomial.X+Polynomial.C b) (JLineAtlas318.chartEquiv R 1 p)
  have h := congrArg (fun f : Polynomial R →ₐ[R] Polynomial R => f (JLineAtlas318.chartEquiv R 1 p)) (chartHom_eq R a b)
  change JLineAtlas318.chartEquiv R 1 (awayMap R a b
    ((JLineAtlas318.chartEquiv R 1).symm (JLineAtlas318.chartEquiv R 1 p))) = _ at h
  simpa only [AlgEquiv.symm_apply_apply] using h
end ProjectiveAffineCharts318
