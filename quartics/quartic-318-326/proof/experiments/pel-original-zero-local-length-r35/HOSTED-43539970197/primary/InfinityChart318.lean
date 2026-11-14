module
public import JacobianLocalSmooth318
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic
public section
noncomputable section
namespace InfinityChart318
open MvPolynomial Algebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R]

/-- The actual Y=1 homogeneous short-Weierstrass equation. -/
@[expose] def equation (A B : R) : MvPolynomial (Fin 2) R :=
  X 1-X 0^3-C A*X 0*X 1^2-C B*X 1^3
@[expose] def equations (A B : R) : Unit → MvPolynomial (Fin 2) R := fun _ => equation A B
abbrev Ring (A B : R) := MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (equations A B))
@[expose] def x (A B : R) : Ring A B := Ideal.Quotient.mk _ (X 0)
@[expose] def z (A B : R) : Ring A B := Ideal.Quotient.mk _ (X 1)

lemma relation (A B : R) : z A B-x A B^3-algebraMap R (Ring A B) A*x A B*z A B^2-
    algebraMap R (Ring A B) B*z A B^3=0 := by
  have hh : Ideal.Quotient.mk (Ideal.span (Set.range (equations A B))) (equation A B)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(),rfl⟩)
  simp only [equation,map_sub,map_pow,map_mul] at hh
  change z A B-x A B^3-algebraMap R (Ring A B) A*x A B*z A B^2-
    algebraMap R (Ring A B) B*z A B^3=0 at hh
  exact hh

@[expose] def presentation (A B : R) : PreSubmersivePresentation R (Ring A B) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations A B) (fun _ => 1)
    (fun _ _ _ => Subsingleton.elim _ _)

lemma pderiv_z (A B : R) : pderiv 1 (equation A B)=
    1-2*C A*X 0*X 1-3*C B*X 1^2 := by
  simp [equation]
  ring

lemma jacobian_formula (A B : R) : (presentation A B).jacobian=
    1-2*algebraMap R (Ring A B) A*x A B*z A B-3*algebraMap R (Ring A B) B*z A B^2 := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [presentation,Matrix.det_unique,PreSubmersivePresentation.jacobiMatrix_naive,equations]
  change Ideal.Quotient.mk (Ideal.span (Set.range (equations A B))) (pderiv 1 (equation A B))=_
  rw [pderiv_z]
  simp only [map_sub,map_mul,map_pow,map_one,map_ofNat]
  rfl

/-- The smooth infinity neighborhood is an actual localization of the Y=1 chart. -/
abbrev SmoothRing (A B : R) := Localization.Away (presentation A B).jacobian
instance smooth (A B : R) : Algebra.Smooth R (SmoothRing A B) := by
  have := JacobianLocalSmooth318.localization_jacobian (presentation A B)
  infer_instance

/-- The point [0:1:0] is an actual R-algebra point of the original Y=1 chart. -/
@[expose] def origin (A B : R) : Ring A B →ₐ[R] R := by
  let e : MvPolynomial (Fin 2) R →ₐ[R] R := MvPolynomial.aeval fun _ => 0
  have hk : Ideal.span (Set.range (equations A B)) ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (equation A B)=0
    simp [e,equation]
  exact Ideal.Quotient.liftₐ _ e (fun f hf => hk hf)

@[simp] theorem origin_x (A B : R) : origin A B (x A B)=0 := by
  simp [origin,x,Ideal.Quotient.liftₐ_apply]
@[simp] theorem origin_z (A B : R) : origin A B (z A B)=0 := by
  simp [origin,z,Ideal.Quotient.liftₐ_apply]
@[simp] theorem origin_jacobian (A B : R) : origin A B (presentation A B).jacobian=1 := by
  rw [jacobian_formula]
  simp

@[expose] def smoothOrigin (A B : R) : SmoothRing A B →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (f := origin A B) (presentation A B).jacobian (by
    rw [origin_jacobian]
    exact isUnit_one)

@[simp] theorem smoothOrigin_map (A B : R) (a : Ring A B) :
    smoothOrigin A B (algebraMap (Ring A B) (SmoothRing A B) a)=origin A B a := by
  simp [smoothOrigin, IsLocalization.Away.liftAlgHom_apply]

open CategoryTheory AlgebraicGeometry in
abbrev scheme (A B : R) : Scheme := Spec (CommRingCat.of (SmoothRing A B))
open CategoryTheory AlgebraicGeometry in
@[expose] def structureMap (A B : R) : scheme A B ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (SmoothRing A B)))
open CategoryTheory AlgebraicGeometry in
@[expose] def sectionAtInfinity (A B : R) : Spec (CommRingCat.of R) ⟶ scheme A B :=
  Spec.map (CommRingCat.ofHom (smoothOrigin A B).toRingHom)

open CategoryTheory AlgebraicGeometry in
theorem structure_smooth (A B : R) : AlgebraicGeometry.Smooth (structureMap A B) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

open CategoryTheory AlgebraicGeometry in
theorem infinity_section (A B : R) : sectionAtInfinity A B ≫ structureMap A B=𝟙 _ := by
  unfold sectionAtInfinity structureMap
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((smoothOrigin A B).toRingHom.comp
    (algebraMap R (SmoothRing A B))))=𝟙 _
  have h : (smoothOrigin A B).toRingHom.comp (algebraMap R (SmoothRing A B))=RingHom.id R := by
    ext r
    exact (smoothOrigin A B).commutes r
  rw [h]
  exact Spec.map_id _

open CategoryTheory AlgebraicGeometry in
theorem infinity_closed (A B : R) : IsClosedImmersion (sectionAtInfinity A B) := by
  apply IsClosedImmersion.spec_of_surjective
  intro r
  exact ⟨algebraMap R (SmoothRing A B) r, (smoothOrigin A B).commutes r⟩

section Lift
variable {S : Type*} [CommRing S] [Algebra R S]

/-- Universal algebra map for the actual infinity chart equation. -/
@[expose] def lift (A B : R) (a c : S)
    (h : c-a^3-algebraMap R S A*a*c^2-algebraMap R S B*c^3=0) : Ring A B →ₐ[R] S := by
  let e : MvPolynomial (Fin 2) R →ₐ[R] S := MvPolynomial.aeval ![a,c]
  have hk : Ideal.span (Set.range (equations A B)) ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (equation A B)=0
    simpa [e,equation] using h
  exact Ideal.Quotient.liftₐ _ e (fun f hf => hk hf)

@[simp] theorem lift_x (A B : R) (a c : S) (h) : lift A B a c h (x A B)=a := by
  simp [lift,x,Ideal.Quotient.liftₐ_apply]
@[simp] theorem lift_z (A B : R) (a c : S) (h) : lift A B a c h (z A B)=c := by
  simp [lift,z,Ideal.Quotient.liftₐ_apply]

@[ext] theorem hom_ext (A B : R) {f g : Ring A B →ₐ[R] S}
    (hx : f (x A B)=g (x A B)) (hz : f (z A B)=g (z A B)) : f=g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hz

end Lift

end InfinityChart318
