module
public import JLineAtlas318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section

open MvPolynomial Graded HomogeneousIdeal AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace SelectedProjectiveJScalar318
variable {R S : Type*} [CommRing R] [CommRing S]
local notation "gr" => ProjectiveJLine318.grading

/-- The actual graded coefficient map of the original homogeneous
model. Both of its literal projective coordinates are unchanged. -/
@[expose] def graded (f : R →+* S) : gr R →+*ᵍ gr S where
  __ := MvPolynomial.map f
  map_mem {d} {p} hp := by
    change (MvPolynomial.map f p).IsHomogeneous d
    exact (show p.IsHomogeneous d from hp).map f

theorem graded_X (f : R →+* S) (i : Fin 2) :
    graded f (X i) = X i := by
  change MvPolynomial.map f (X i) = X i
  simp

theorem graded_C (f : R →+* S) (r : R) :
    graded f (C r) = C (f r) := by
  change MvPolynomial.map f (C r) = C (f r)
  simp

theorem irrelevant_le (f : R →+* S) : (gr S)₊ ≤ (gr R)₊.map (graded f) := by
  let I : Ideal (MvPolynomial (Fin 2) S) := ((gr R)₊.map (graded f)).toIdeal
  let generators : Set (MvPolynomial (Fin 2) S) := X '' (Set.univ : Set (Fin 2))
  have hgen : Ideal.span generators ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,_,rfl⟩
    rw [← graded_X f i]
    exact Ideal.mem_map_of_mem (graded f).toRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1:ℕ)) (isHomogeneous_X R i))
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro d hd p hp
  change p ∈ I
  apply hgen
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro m hm
  have hdegree := (show p.IsHomogeneous d from hp).degree_eq_sum_deg_support hm
  have hsome : ∃ i, (m : Fin 2 →₀ ℕ) i ≠ 0 := by
    by_contra! hz
    have hm0 : m = 0 := Finsupp.ext (by intro i; simpa using hz i)
    simp [hm0] at hdegree
    omega
  obtain ⟨i, hi⟩ := hsome
  exact ⟨i,Set.mem_univ i,hi⟩

/-- Canonical scalar projection on the original projective model, via
Proj's contravariant graded ring map. -/
@[expose] def scalarMap (f : R →+* S) : ProjectiveJLine318.scheme S ⟶ ProjectiveJLine318.scheme R :=
  Proj.map (graded f) (irrelevant_le f)

section Away
variable (f : R →+* S)

@[expose] def awayAt (x : MvPolynomial (Fin 2) R) (y : MvPolynomial (Fin 2) S)
    (h : graded f x=y) : Away (gr R) x →+* Away (gr S) y :=
  h ▸ Away.map (graded f) x

theorem awayAt_mk (x : MvPolynomial (Fin 2) R) (y : MvPolynomial (Fin 2) S)
    (h : graded f x=y) {d : ℕ} (hx : x ∈ gr R d)
    (n : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p ∈ gr R (n • d)) :
    awayAt f x y h (Away.mk (gr R) hx n p hp) =
      Away.mk (gr S) (h ▸ Graded.map_mem (graded f) hx) n (graded f p) (Graded.map_mem (graded f) hp) := by
  subst y
  exact Away.map_mk (graded f) x hx n p hp

theorem awayAt_natural (x : MvPolynomial (Fin 2) R) (y : MvPolynomial (Fin 2) S)
    (h : graded f x=y) {d : ℕ} (hd : 0 < d) (hx : x ∈ gr R d) :
    Proj.awayι (gr S) y (h ▸ Graded.map_mem (graded f) hx) hd ≫ scalarMap f =
      Spec.map (CommRingCat.ofHom (awayAt f x y h)) ≫ Proj.awayι (gr R) x hx hd := by
  subst y
  exact Proj.awayι_comp_map (graded f) (irrelevant_le f) hd x hx

@[expose] def awayScalar (i : Fin 2) : Away (gr R) (X i) →+* Away (gr S) (X i) :=
  awayAt f (X i) (X i) (graded_X f i)

theorem away_natural (i : Fin 2) :
    Proj.awayι (gr S) (X i) (isHomogeneous_X S i) (by decide : 0 < 1) ≫ scalarMap f =
      Spec.map (CommRingCat.ofHom (awayScalar f i)) ≫
        Proj.awayι (gr R) (X i) (isHomogeneous_X R i) (by decide : 0 < 1) :=
  awayAt_natural f (X i) (X i) (graded_X f i) (by decide : 0 < 1) (isHomogeneous_X R i)

theorem away_scalar_C (i : Fin 2) (r : R) :
    awayScalar f i (algebraMap R (Away (gr R) (X i)) r) =
      algebraMap S (Away (gr S) (X i)) (f r) := by
  change awayScalar f i (Away.mk (gr R) (isHomogeneous_X R i) 0 (C r) _) =
    Away.mk (gr S) (isHomogeneous_X S i) 0 (C (f r)) _
  rw [awayScalar, awayAt_mk]
  apply HomogeneousLocalization.val_injective
  rw [ProjectiveChart318.val_mk, ProjectiveChart318.val_mk, graded_C]

theorem away_scalar_X (i : Fin 2) :
    awayScalar f i ((JLineAtlas318.chartEquiv R i).symm Polynomial.X) =
      (JLineAtlas318.chartEquiv S i).symm Polynomial.X := by
  rw [JLineAtlas318.chartEquiv_symm_X R i, JLineAtlas318.chartEquiv_symm_X S i]
  unfold ProjectiveChart318.coordinate
  rw [awayScalar, awayAt_mk]
  apply HomogeneousLocalization.val_injective
  rw [ProjectiveChart318.val_mk, ProjectiveChart318.val_mk, graded_X]

/-- Dehomogenizing the literal coefficient map gives the polynomial
coefficient map, not X scaled or translated. -/
theorem chart_ring (i : Fin 2) :
    (JLineAtlas318.chartEquiv S i).toRingEquiv.toRingHom.comp
      ((awayScalar f i).comp (JLineAtlas318.chartEquiv R i).symm.toRingEquiv.toRingHom) =
    Polynomial.mapRingHom f := by
  apply Polynomial.ringHom_ext'
  · apply RingHom.ext
    intro r
    change JLineAtlas318.chartEquiv S i (awayScalar f i
      ((JLineAtlas318.chartEquiv R i).symm (algebraMap R (Polynomial R) r))) =
      Polynomial.map f (Polynomial.C r)
    rw [(JLineAtlas318.chartEquiv R i).symm.commutes, away_scalar_C,
      (JLineAtlas318.chartEquiv S i).commutes, Polynomial.map_C] <;> rfl
  · change JLineAtlas318.chartEquiv S i (awayScalar f i
      ((JLineAtlas318.chartEquiv R i).symm Polynomial.X)) = Polynomial.map f Polynomial.X
    rw [away_scalar_X, AlgEquiv.apply_symm_apply, Polynomial.map_X]

/-- The actual map on BOTH original charts, including chart 1 used
by the modular j-coordinate. -/
@[reassoc] theorem chart_natural (i : Fin 2) :
    JLineAtlas318.chart S i ≫ scalarMap f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫ JLineAtlas318.chart R i := by
  unfold JLineAtlas318.chart
  rw [Category.assoc, away_natural f i, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change JLineAtlas318.chartEquiv S i (awayScalar f i p) =
    Polynomial.map f (JLineAtlas318.chartEquiv R i p)
  have h := congrArg (fun g : Polynomial R →+* Polynomial S => g (JLineAtlas318.chartEquiv R i p))
    (chart_ring f i)
  change JLineAtlas318.chartEquiv S i (awayScalar f i
    ((JLineAtlas318.chartEquiv R i).symm (JLineAtlas318.chartEquiv R i p))) = _ at h
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- The same projective scalar morphism is over the actual Spec of
the coefficient map, checked on the existing full two-chart cover. -/
@[reassoc] theorem scalar_over :
    scalarMap f ≫ ProjectiveJLine318.structureMap R =
      ProjectiveJLine318.structureMap S ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (JLineAtlas318.cover S).hom_ext
  intro i
  change JLineAtlas318.chart S i ≫ (scalarMap f ≫ ProjectiveJLine318.structureMap R) =
    JLineAtlas318.chart S i ≫ (ProjectiveJLine318.structureMap S ≫ Spec.map (CommRingCat.ofHom f))
  rw [← Category.assoc, chart_natural, Category.assoc, JLineAtlas318.chart_over_base,
    ← Category.assoc, JLineAtlas318.chart_over_base, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change Polynomial.map f (Polynomial.C r) = Polynomial.C (f r)
  exact Polynomial.map_C _ _

end Away
end SelectedProjectiveJScalar318

#print axioms SelectedProjectiveJScalar318.scalarMap
#print axioms SelectedProjectiveJScalar318.chart_natural
#print axioms SelectedProjectiveJScalar318.scalar_over
