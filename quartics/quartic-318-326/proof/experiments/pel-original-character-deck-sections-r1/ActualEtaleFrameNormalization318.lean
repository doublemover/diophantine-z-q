module
public import EtaleDifferentialFrame318
public section
noncomputable section
namespace ActualEtaleFrameNormalization318
open TensorProduct Polynomial
open scoped TensorProduct
section Generic
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

theorem ofAlgEquiv_D_image (f : S ≃ₐ[R] T) (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    EtaleDifferentialFrame318.ofAlgEquiv f e (KaehlerDifferential.D R T (f s)) =
      f (e (KaehlerDifferential.D R S s)) := by
  change f (e (AlgHomDifferential318.map f.symm.toAlgHom (KaehlerDifferential.D R T (f s))))=_
  rw [AlgHomDifferential318.map_D]
  change f (e (KaehlerDifferential.D R S (f.symm (f s))))=_
  rw [f.symm_apply_apply]

variable [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]
theorem ofFormallyEtale_D (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    EtaleDifferentialFrame318.ofFormallyEtale e
      (KaehlerDifferential.D R T (algebraMap S T s))=
        algebraMap S T (e (KaehlerDifferential.D R S s)) := by
  simp only [EtaleDifferentialFrame318.ofFormallyEtale,LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def,mul_one]
end Generic
end ActualEtaleFrameNormalization318
