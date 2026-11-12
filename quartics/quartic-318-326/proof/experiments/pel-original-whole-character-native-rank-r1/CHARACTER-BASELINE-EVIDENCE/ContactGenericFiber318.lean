module
public import ContactBaseChange318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ContactGenericFiber318
set_option maxHeartbeats 700000
open scoped TensorProduct
open QuadraticPresentation318 ContactBaseChange318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]

@[expose] def inverseContactMap (u:Rˣ) (pi:R) (m:ℕ) (hp:IsUnit pi) :
    EvenContactEtale318.RootRing u →ₐ[R] RootRing ((u:R)*pi^(2*m)) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (RootRing ((u:R)*pi^(2*m))) (↑(hp.unit⁻¹):R)^m *
      AdjoinRoot.root (polynomial ((u:R)*pi^(2*m)))) (by
        change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C (u:R))=0
        simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
        apply sub_eq_zero.mpr
        rw [mul_pow,root_square,←map_pow,←map_pow,←map_mul]
        congr 1
        have hi:(↑(hp.unit⁻¹):R)*pi=1 := by simpa only [hp.unit_spec] using hp.unit.inv_mul
        calc
          ((↑(hp.unit⁻¹):R)^m)^2*((u:R)*pi^(2*m))=
            (u:R)*((↑(hp.unit⁻¹):R)*pi)^(2*m) := by
              rw [mul_pow,←pow_mul]; ring
          _=(u:R) := by rw [hi,one_pow,mul_one])

theorem inverseContactMap_generator (u:Rˣ) (pi:R) (m:ℕ) (hp:IsUnit pi) :
    inverseContactMap u pi m hp (EvenContactEtale318.root u)=
      algebraMap R (RootRing ((u:R)*pi^(2*m))) (↑(hp.unit⁻¹):R)^m *
        AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def scaleEquiv (u:Rˣ) (pi:R) (m:ℕ) (hp:IsUnit pi) :
    RootRing ((u:R)*pi^(2*m)) ≃ₐ[R] EvenContactEtale318.RootRing u where
  __ := contactMap u pi m
  invFun:=inverseContactMap u pi m hp
  left_inv z:=by
    have h:(inverseContactMap u pi m hp).comp (contactMap u pi m)=AlgHom.id R _ := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply,contactMap_generator,map_mul,map_pow,AlgHom.commutes,
        inverseContactMap_generator,AlgHom.id_apply]
      have hi:pi*(↑(hp.unit⁻¹):R)=1 := by simpa only [hp.unit_spec] using hp.unit.mul_inv
      rw [←mul_assoc,←mul_pow,←map_mul,hi,map_one,one_pow,one_mul]
    exact AlgHom.congr_fun h z
  right_inv z:=by
    have h:(contactMap u pi m).comp (inverseContactMap u pi m hp)=AlgHom.id R _ := by
      apply AdjoinRoot.algHom_ext
      change contactMap u pi m (inverseContactMap u pi m hp (EvenContactEtale318.root u))=_
      rw [inverseContactMap_generator,map_mul,map_pow,AlgHom.commutes,contactMap_generator]
      have hi:(↑(hp.unit⁻¹):R)*pi=1 := by simpa only [hp.unit_spec] using hp.unit.inv_mul
      rw [←mul_assoc,←mul_pow,←map_mul,hi,map_one,one_pow,one_mul]
      rfl
    exact AlgHom.congr_fun h z

@[simp] theorem scaleEquiv_generator (u:Rˣ) (pi:R) (m:ℕ) (hp:IsUnit pi) :
    scaleEquiv u pi m hp (AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))=
      algebraMap R (EvenContactEtale318.RootRing u) pi^m*EvenContactEtale318.root u :=
  contactMap_generator u pi m

/-- Actual base change of the polynomial quotient, not a generic-fiber identification premise. -/
@[expose] def rootBaseChange (b:R) :
    S ⊗[R] RootRing b ≃ₐ[S] RootRing (algebraMap R S b) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (presentationEquiv b).symm).trans
    ((QuadraticAlgebra.baseChangeEquiv S b 0).trans
      ((parameterEquiv rfl (map_zero _)).trans (presentationEquiv (algebraMap R S b))))

theorem rootBaseChange_generator (b:R) :
    rootBaseChange (S:=S) b (1 ⊗ₜ[R] AdjoinRoot.root (polynomial b))=
      AdjoinRoot.root (polynomial (algebraMap R S b)) := by
  have hi:(presentationEquiv b).symm (AdjoinRoot.root (polynomial b))=QuadraticAlgebra.omega := by
    apply (presentationEquiv b).injective
    simp
  simp [rootBaseChange,hi]

@[expose] def rootParameterEquiv {b c:R} (h:b=c) : RootRing b ≃ₐ[R] RootRing c :=
  (presentationEquiv b).symm.trans ((parameterEquiv h rfl).trans (presentationEquiv c))

@[simp] theorem rootParameterEquiv_generator {b c:R} (h:b=c) :
    rootParameterEquiv h (AdjoinRoot.root (polynomial b))=AdjoinRoot.root (polynomial c) := by
  subst c
  simp [rootParameterEquiv,parameterEquiv]

@[expose] def unitRootBaseChange (u:Rˣ) :
    S ⊗[R] EvenContactEtale318.RootRing u ≃ₐ[S]
      EvenContactEtale318.RootRing (Units.map (algebraMap R S).toMonoidHom u) :=
  rootBaseChange (u:R)

theorem unitRootBaseChange_generator (u:Rˣ) :
    unitRootBaseChange (S:=S) u (1 ⊗ₜ[R] EvenContactEtale318.root u)=
      EvenContactEtale318.root (Units.map (algebraMap R S).toMonoidHom u) :=
  rootBaseChange_generator (u:R)

@[expose] def contactBaseChange (u:Rˣ) (pi:R) (m:ℕ) :
    S ⊗[R] RootRing ((u:R)*pi^(2*m)) ≃ₐ[S]
      RootRing ((↑(Units.map (algebraMap R S).toMonoidHom u):S)*algebraMap R S pi^(2*m)) :=
  (rootBaseChange ((u:R)*pi^(2*m))).trans
    (rootParameterEquiv (by simp))

theorem contactBaseChange_generator (u:Rˣ) (pi:R) (m:ℕ) :
    contactBaseChange (S:=S) u pi m (1 ⊗ₜ[R] AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))=
      AdjoinRoot.root (polynomial ((↑(Units.map (algebraMap R S).toMonoidHom u):S)*algebraMap R S pi^(2*m))) := by
  simp only [contactBaseChange,AlgEquiv.trans_apply,rootBaseChange_generator,
    rootParameterEquiv_generator]

/-- The actual generic-fiber identification after any base change making the
contact parameter a unit. It is an isomorphism of actual tensor products. -/
@[expose] def genericFiberEquiv (u:Rˣ) (pi:R) (m:ℕ)
    (hp:IsUnit (algebraMap R S pi)) :
    S ⊗[R] RootRing ((u:R)*pi^(2*m)) ≃ₐ[S]
      S ⊗[R] EvenContactEtale318.RootRing u :=
  (contactBaseChange u pi m).trans
    ((scaleEquiv (Units.map (algebraMap R S).toMonoidHom u) (algebraMap R S pi) m hp).trans
      (unitRootBaseChange u).symm)

theorem genericFiberEquiv_generator (u:Rˣ) (pi:R) (m:ℕ)
    (hp:IsUnit (algebraMap R S pi)) :
    genericFiberEquiv u pi m hp
      (1 ⊗ₜ[R] AdjoinRoot.root (polynomial ((u:R)*pi^(2*m))))=
      (algebraMap R S pi)^m • (1 ⊗ₜ[R] EvenContactEtale318.root u) := by
  apply (unitRootBaseChange (S:=S) u).injective
  simp only [genericFiberEquiv,AlgEquiv.trans_apply,contactBaseChange_generator,
    AlgEquiv.apply_symm_apply,scaleEquiv_generator,map_smul,unitRootBaseChange_generator]
  rw [Algebra.smul_def,map_pow]

theorem genericFiberEquiv_on_order (u:Rˣ) (pi:R) (m:ℕ)
    (hp:IsUnit (algebraMap R S pi)) (x:RootRing ((u:R)*pi^(2*m))) :
    genericFiberEquiv u pi m hp (1 ⊗ₜ[R] x)=1 ⊗ₜ[R] contactMap u pi m x := by
  have h: ((genericFiberEquiv u pi m hp).restrictScalars R).toAlgHom.comp
      (Algebra.TensorProduct.includeRight : RootRing ((u:R)*pi^(2*m)) →ₐ[R]
        S ⊗[R] RootRing ((u:R)*pi^(2*m)))=
      (Algebra.TensorProduct.includeRight : EvenContactEtale318.RootRing u →ₐ[R]
        S ⊗[R] EvenContactEtale318.RootRing u).comp (contactMap u pi m) := by
    apply AdjoinRoot.algHom_ext
    change genericFiberEquiv u pi m hp (1 ⊗ₜ[R] AdjoinRoot.root _)=
      1 ⊗ₜ[R] contactMap u pi m (AdjoinRoot.root _)
    rw [genericFiberEquiv_generator,contactMap_generator,←map_pow,←map_pow,←Algebra.smul_def,
      TensorProduct.tmul_smul,Algebra.smul_def]
    simp only [Algebra.smul_def,map_pow]
    rw [←IsScalarTower.algebraMap_apply R S (S ⊗[R] EvenContactEtale318.RootRing u)]
  exact AlgHom.congr_fun h x

/-- Inverting the actual contact parameter supplies the unit premise internally. -/
@[expose] def awayEquiv (u:Rˣ) (pi:R) (m:ℕ) :
    Localization.Away pi ⊗[R] RootRing ((u:R)*pi^(2*m)) ≃ₐ[Localization.Away pi]
      Localization.Away pi ⊗[R] EvenContactEtale318.RootRing u :=
  genericFiberEquiv u pi m (IsLocalization.Away.algebraMap_isUnit pi)

end ContactGenericFiber318
