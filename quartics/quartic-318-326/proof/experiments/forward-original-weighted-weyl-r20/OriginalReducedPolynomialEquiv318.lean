module
public import OriginalReducedContentProducer318
public section
noncomputable section
namespace OriginalReducedPolynomialEquiv318
open MvPolynomial TernaryQuadraticLineCover318 LiteralSievePolynomial318
set_option maxHeartbeats 6000000

@[expose] def cross (u v : Vector ℚ) : Vector ℚ :=
  (u.2.1*v.2.2-u.2.2*v.2.1,u.2.2*v.1-u.1*v.2.2,u.1*v.2.1-u.2.1*v.1)
@[expose] def triple (u v z : Vector ℚ) : ℚ :=
  (cross u v).1*z.1+(cross u v).2.1*z.2.1+(cross u v).2.2*z.2.2
@[expose] def linear (a : Vector ℚ) : Poly := C a.1*X 0+C a.2.1*X 1+C a.2.2*X 2
@[expose] def variables (u v z : Vector ℚ) (i : Fin 3) : Poly :=
  if i=0 then linear (u.1,v.1,z.1) else if i=1 then linear (u.2.1,v.2.1,z.2.1)
  else linear (u.2.2,v.2.2,z.2.2)
@[expose] def cofactor (u v z : Vector ℚ) (i : Fin 3) : Vector ℚ :=
  if i=0 then cross v z else if i=1 then cross z u else cross u v
@[expose] def inverseVariables (u v z : Vector ℚ) (i : Fin 3) : Poly :=
  C (triple u v z)⁻¹*linear (cofactor u v z i)
@[expose] def forward (u v z : Vector ℚ) : Poly →ₐ[ℚ] Poly := aeval (variables u v z)
@[expose] def backward (u v z : Vector ℚ) : Poly →ₐ[ℚ] Poly := aeval (inverseVariables u v z)

/-- Explicit cofactor identity inside the ACTUAL polynomial algebra,
not just equality after selected numerical evaluations. -/
lemma forward_cofactor (u v z : Vector ℚ) (i : Fin 3) :
    forward u v z (linear (cofactor u v z i))=C (triple u v z)*X i := by
  fin_cases i <;> simp [forward,variables,linear,cofactor,cross,triple,algebraMap_eq,
    map_add,map_sub,map_mul] <;> ring

lemma backward_generator (u v z : Vector ℚ) (i : Fin 3) :
    backward u v z (variables u v z i)=
      C (triple u v z)⁻¹*(C (triple u v z)*X i) := by
  fin_cases i <;> simp [backward,variables,inverseVariables,linear,cofactor,cross,triple,
    algebraMap_eq,map_add,map_sub,map_mul] <;> ring

lemma inverse_coefficient (u v z : Vector ℚ) (hd : triple u v z≠0) :
    (C (triple u v z)⁻¹:Poly)*C (triple u v z)=1 := by
  rw [←map_mul,inv_mul_cancel₀ hd,map_one]

/-- Both polynomial compositions are proved on all three generators. -/
theorem forward_backward (u v z : Vector ℚ) (hd : triple u v z≠0) :
    (forward u v z).comp (backward u v z)=AlgHom.id ℚ Poly := by
  ext i
  simp only [AlgHom.comp_apply,AlgHom.id_apply,backward,aeval_X]
  change forward u v z (inverseVariables u v z i)=X i
  have hc : forward u v z (C (triple u v z)⁻¹)=C (triple u v z)⁻¹ := by
    simp [forward,algebraMap_eq]
  rw [inverseVariables,map_mul,hc,forward_cofactor,←mul_assoc,inverse_coefficient u v z hd,one_mul]

theorem backward_forward (u v z : Vector ℚ) (hd : triple u v z≠0) :
    (backward u v z).comp (forward u v z)=AlgHom.id ℚ Poly := by
  ext i
  simp only [AlgHom.comp_apply,AlgHom.id_apply,forward,aeval_X]
  change backward u v z (variables u v z i)=X i
  rw [backward_generator,←mul_assoc,inverse_coefficient u v z hd,one_mul]

@[expose] def equivalence (u v z : Vector ℚ) (hd : triple u v z≠0) : Poly ≃ₐ[ℚ] Poly :=
  AlgEquiv.ofAlgHom (forward u v z) (backward u v z)
    (forward_backward u v z hd) (backward_forward u v z hd)

theorem preserves_relPrime (u v z : Vector ℚ) (hd : triple u v z≠0)
    (f g : Poly) (hfg : IsRelPrime f g) :
    IsRelPrime (forward u v z f) (forward u v z g) := by
  let e := equivalence u v z hd
  change IsRelPrime (e f) (e g)
  apply IsRelPrime.of_map e.symm
  simpa only [AlgEquiv.symm_apply_apply] using hfg

/-- Evaluation of the substituted polynomial is the same literal linear
coordinate combination used in the integer and Euclidean basis maps. -/
theorem forward_evaluation (u v z : Vector ℚ) (c : Fin 3 → ℚ) (f : Poly) :
    eval c (forward u v z f)=eval
      (fun i : Fin 3 => if i=0 then u.1*c 0+v.1*c 1+z.1*c 2
        else if i=1 then u.2.1*c 0+v.2.1*c 1+z.2.1*c 2
        else u.2.2*c 0+v.2.2*c 1+z.2.2*c 2) f := by
  have hh := comp_aeval_apply (f := variables u v z) (aeval c) f
  simpa [forward,variables,linear,algebraMap_eq] using hh

end OriginalReducedPolynomialEquiv318
