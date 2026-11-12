module
public import ComplexProjectiveCrossRatio318
public section
noncomputable section
namespace ComplexSphereActualCrossRatio318
open scoped OnePoint
open ComplexProjectiveCrossRatio318 ComplexSphereAffineNormalization318
open SphereInversion318 ComplexSphereFourPointNormalization318

lemma affine_action (a b : ℂ) (ha : a≠0) (p : OnePoint ℂ) :
    ∃ s : ℂ, s≠0 ∧ lift (affineSphere a b ha p)=scale s (matrix a b 0 1 (lift p)) := by
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨a⁻¹,inv_ne_zero ha,?_⟩
    rw [affineSphere_infty]
    apply Prod.ext <;> simp [lift,scale,matrix,ha]
  | coe z =>
    refine ⟨1,one_ne_zero,?_⟩
    rw [affineSphere_coe]
    simp [lift,scale,matrix]

lemma inversion_action (p : OnePoint ℂ) :
    ∃ s : ℂ, s≠0 ∧ lift (inversion p)=scale s (matrix 0 1 1 0 (lift p)) := by
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨1,one_ne_zero,?_⟩
    rw [inversion_infty]
    simp [lift,scale,matrix]
  | coe z =>
    by_cases hz : z=0
    · subst z
      refine ⟨1,one_ne_zero,?_⟩
      rw [inversion_zero]
      simp [lift,scale,matrix]
    · refine ⟨z⁻¹,inv_ne_zero hz,?_⟩
      rw [inversion_coe hz]
      apply Prod.ext <;> simp [lift,scale,matrix,hz]

lemma crossRatio_affine (a b : ℂ) (ha : a≠0) (p : Fin 4 → OnePoint ℂ) :
    crossRatio (fun i=>affineSphere a b ha (p i))=crossRatio p :=
  crossRatio_of_action _ a b 0 1 (by simpa using ha) (affine_action a b ha) p
lemma crossRatio_inversion (p : Fin 4 → OnePoint ℂ) :
    crossRatio (fun i=>inversion (p i))=crossRatio p :=
  crossRatio_of_action _ 0 1 1 0 (by norm_num) inversion_action p
lemma crossRatio_pole (z : OnePoint ℂ) (p : Fin 4 → OnePoint ℂ) :
    crossRatio (fun i=>poleCoordinate z (p i))=crossRatio p := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change crossRatio (fun i=>inversion (affineSphere 1 (-z) one_ne_zero (p i)))=_
    rw [crossRatio_inversion,crossRatio_affine]

lemma crossRatio_normalization (p : Fin 4 → OnePoint ℂ) (hp : Function.Injective p)
    (q : Fin 4 → OnePoint ℂ) :
    crossRatio (fun i=>normalization p hp (q i))=crossRatio q := by
  change crossRatio (fun i=>affineSphere _ _ _ (poleCoordinate (p 0) (q i)))=_
  rw [crossRatio_affine,crossRatio_pole]

/-- The previously CHOSEN finite fourth parameter equals the intrinsic
homogeneous cross-ratio of the SAME original ordered points. This proof
uses the actual constructed normalization and includes infinity. -/
theorem parameter_eq_crossRatio (p : Fin 4 → OnePoint ℂ) (hp : Function.Injective p) :
    parameter p hp=crossRatio p := by
  have images : (fun i=>normalization p hp (p i))=
      ![∞,(0:ℂ),(1:ℂ),(parameter p hp:ℂ)] := by
    funext i
    fin_cases i
    · exact normalization_zero p hp
    · exact normalization_one p hp
    · exact normalization_two p hp
    · exact normalization_three p hp
  have h:=crossRatio_normalization p hp p
  rw [images,crossRatio_normalized] at h
  exact h
end ComplexSphereActualCrossRatio318
