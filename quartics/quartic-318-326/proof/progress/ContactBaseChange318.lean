module
public import QuadraticPresentation318
public import RingQuadraticBasis318
public import EvenContactEtale318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace ContactBaseChange318
set_option maxHeartbeats 600000
open scoped TensorProduct
open QuadraticAlgebra PowerSeries
variable {A R:Type*} [CommRing A] [CommRing R] [Algebra A R]

@[expose] def parameterEquiv {a b c d:R} (ha:a=c) (hb:b=d) :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R c d := by
  subst c; subst d; exact AlgEquiv.refl

@[simp] theorem parameterEquiv_generator {a b c d:R} (ha:a=c) (hb:b=d) :
    parameterEquiv ha hb omega=omega := by subst c; subst d; rfl

/-- The actual tensor product of a quadratic model under a specified contact map. -/
@[expose] def baseChange (s:A) (u:Rˣ) (pi:R) (m:ℕ)
    (hs:algebraMap A R s=(u:R)*pi^(2*m)) :
    R ⊗[A] QuadraticAlgebra A s 0 ≃ₐ[R]
      QuadraticPresentation318.RootRing ((u:R)*pi^(2*m)) :=
  (QuadraticAlgebra.baseChangeEquiv R s 0).trans
    ((parameterEquiv hs (map_zero _)).trans
      (QuadraticPresentation318.presentationEquiv ((u:R)*pi^(2*m))))

theorem baseChange_generator (s:A) (u:Rˣ) (pi:R) (m:ℕ)
    (hs:algebraMap A R s=(u:R)*pi^(2*m)) :
    baseChange s u pi m hs (1 ⊗ₜ[A] omega)=
      AdjoinRoot.root (QuadraticPresentation318.polynomial ((u:R)*pi^(2*m))) := by
  simp [baseChange]

/-- The map to the actual finite etale unit-root algebra, with no chosen square root. -/
@[expose] def contactMap (u:Rˣ) (pi:R) (m:ℕ) :
    QuadraticPresentation318.RootRing ((u:R)*pi^(2*m)) →ₐ[R]
      EvenContactEtale318.RootRing u :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (EvenContactEtale318.RootRing u) pi^m*EvenContactEtale318.root u) (by
      change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C ((u:R)*pi^(2*m)))=0
      simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
      rw [mul_comm,EvenContactEtale318.even_contact_root,sub_self])

theorem contactMap_generator (u:Rˣ) (pi:R) (m:ℕ) :
    contactMap u pi m (AdjoinRoot.root
      (QuadraticPresentation318.polynomial ((u:R)*pi^(2*m))))=
      algebraMap R (EvenContactEtale318.RootRing u) pi^m*EvenContactEtale318.root u :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Base change of the actual formal cover with its nonidentity S-to-T-squared algebra. -/
@[expose] def formalBaseChange (k:Type*) [CommRing k] [IsDomain k]
    [Algebra k⟦X⟧ R] (u:Rˣ) (pi:R) (m:ℕ)
    (hs:algebraMap k⟦X⟧ R PowerSeries.X=(u:R)*pi^(2*m)) :
    R ⊗[k⟦X⟧] RingQuadraticBasis318.Cover k ≃ₐ[R]
      QuadraticPresentation318.RootRing ((u:R)*pi^(2*m)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R)
    (RingQuadraticBasis318.quadraticAlgEquiv k).symm).trans
    (baseChange PowerSeries.X u pi m hs)

theorem formalBaseChange_generator (k:Type*) [CommRing k] [IsDomain k]
    [Algebra k⟦X⟧ R] (u:Rˣ) (pi:R) (m:ℕ)
    (hs:algebraMap k⟦X⟧ R PowerSeries.X=(u:R)*pi^(2*m)) :
    formalBaseChange k u pi m hs (1 ⊗ₜ[k⟦X⟧] RingQuadraticBasis318.root k)=
      AdjoinRoot.root (QuadraticPresentation318.polynomial ((u:R)*pi^(2*m))) := by
  have hg:RingQuadraticBasis318.quadraticAlgEquiv k omega=RingQuadraticBasis318.root k := by
    simpa only [RingQuadraticBasis318.basis,Module.Basis.map_apply,
      QuadraticAlgebra.basis_apply_one,AlgEquiv.toLinearEquiv_apply] using
      RingQuadraticBasis318.basis_one k
  have hi:(RingQuadraticBasis318.quadraticAlgEquiv k).symm (RingQuadraticBasis318.root k)=omega := by
    rw [←hg,AlgEquiv.symm_apply_apply]
  simp only [formalBaseChange,AlgEquiv.trans_apply,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,AlgEquiv.coe_toAlgHom,map_one,hi,
    baseChange_generator]

end ContactBaseChange318
