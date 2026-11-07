module
public import NormalizedContactOrder318
public import ActualDVRCompletion318
public section
noncomputable section
namespace ContactTensor318
set_option maxHeartbeats 900000
open scoped TensorProduct
open QuadraticPresentation318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]

@[expose] def mappedUnit (u:Rˣ):Sˣ:=Units.map (algebraMap R S).toMonoidHom u

@[simp] theorem mappedUnit_val (u:Rˣ) : (mappedUnit (S:=S) u:S)=algebraMap R S (u:R) := rfl

/-- The genuine scalar base change of the quadratic quotient, with its generator. -/
@[expose] def rootBaseChange (f:R) :
    S⊗[R]RootRing f ≃ₐ[S] RootRing (algebraMap R S f) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S≃ₐ[S]S) (presentationEquiv f).symm).trans
    ((QuadraticAlgebra.baseChangeEquiv S f 0).trans
      ((ContactBaseChange318.parameterEquiv rfl (map_zero _)).trans
        (presentationEquiv (algebraMap R S f))))

@[simp] theorem rootBaseChange_root (f:R) :
    rootBaseChange (S:=S) f (1⊗ₜ[R]AdjoinRoot.root (polynomial f))=
      AdjoinRoot.root (polynomial (algebraMap R S f)) := by
  have hh:(presentationEquiv f).symm (AdjoinRoot.root (polynomial f))=QuadraticAlgebra.omega := by
    rw [←presentationEquiv_generator,AlgEquiv.symm_apply_apply]
  simp only [rootBaseChange,AlgEquiv.trans_apply,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,AlgEquiv.coe_toAlgHom,map_one,hh,
    QuadraticAlgebra.baseChangeEquiv_tmul]
  simp

@[expose] def unitBaseChange (u:Rˣ) :
    S⊗[R]EvenContactEtale318.RootRing u ≃ₐ[S] EvenContactEtale318.RootRing (mappedUnit (S:=S) u) :=
  rootBaseChange (u:R)

@[simp] theorem unitBaseChange_root (u:Rˣ) :
    unitBaseChange (S:=S) u (1⊗ₜ[R]EvenContactEtale318.root u)=
      EvenContactEtale318.root (mappedUnit (S:=S) u) := rootBaseChange_root (u:R)

@[expose] def orderBaseChange (u:Rˣ) (pi:R) (m:ℕ) :
    S⊗[R]RootRing ((u:R)*pi^(2*m)) ≃ₐ[S]
      RootRing ((mappedUnit (S:=S) u:S)*(algebraMap R S pi)^(2*m)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S≃ₐ[S]S)
    (presentationEquiv ((u:R)*pi^(2*m))).symm).trans
      (ContactBaseChange318.baseChange ((u:R)*pi^(2*m)) (mappedUnit (S:=S) u)
        (algebraMap R S pi) m (by simp))

@[simp] theorem orderBaseChange_root (u:Rˣ) (pi:R) (m:ℕ) :
    orderBaseChange (S:=S) u pi m
      (1⊗ₜ[R]AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))=
        AdjoinRoot.root (polynomial ((mappedUnit (S:=S) u:S)*(algebraMap R S pi)^(2*m))) := by
  have hh:(presentationEquiv ((u:R)*pi^(2*m))).symm
      (AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))=QuadraticAlgebra.omega := by
    rw [←presentationEquiv_generator,AlgEquiv.symm_apply_apply]
  simp only [orderBaseChange,AlgEquiv.trans_apply,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,AlgEquiv.coe_toAlgHom,map_one,hh,
    ContactBaseChange318.baseChange_generator]

@[expose] def tensorContact (u:Rˣ) (pi:R) (m:ℕ) :
    S⊗[R]RootRing ((u:R)*pi^(2*m)) →ₐ[S] S⊗[R]EvenContactEtale318.RootRing u :=
  Algebra.TensorProduct.map (AlgHom.id S S) (ContactBaseChange318.contactMap u pi m)

/-- The entire actual normalization map commutes with scalar base change,
not merely its value on one chosen root. -/
theorem contact_square (u:Rˣ) (pi:R) (m:ℕ) :
    (unitBaseChange (S:=S) u).toAlgHom.comp (tensorContact u pi m)=
      (ContactBaseChange318.contactMap (mappedUnit (S:=S) u) (algebraMap R S pi) m).comp
        (orderBaseChange u pi m).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AdjoinRoot.algHom_ext
    change unitBaseChange (S:=S) u
      (1⊗ₜ[R]ContactBaseChange318.contactMap u pi m
        (AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))) =
      ContactBaseChange318.contactMap (mappedUnit (S:=S) u) (algebraMap R S pi) m
        (orderBaseChange (S:=S) u pi m
          (1⊗ₜ[R]AdjoinRoot.root (polynomial ((u:R)*pi^(2*m)))))
    rw [ContactBaseChange318.contactMap_generator,orderBaseChange_root,
      ContactBaseChange318.contactMap_generator]
    have hh:(1:S)⊗ₜ[R](algebraMap R (EvenContactEtale318.RootRing u) pi^m*
        EvenContactEtale318.root u)=
        algebraMap S (S⊗[R]EvenContactEtale318.RootRing u) ((algebraMap R S pi)^m)*
          (1⊗ₜ[R]EvenContactEtale318.root u) := by
      rw [←map_pow,Algebra.TensorProduct.algebraMap_apply]
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one]
      rw [←Algebra.smul_def,TensorProduct.tmul_smul]
      simp [Algebra.smul_def]
    rw [hh,map_mul,AlgEquiv.commutes,unitBaseChange_root,map_pow]

end ContactTensor318
