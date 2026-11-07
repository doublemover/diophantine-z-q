module
public import AffineEquationFunctor318
public import Mathlib.RingTheory.TensorProduct.Basic
public section
noncomputable section
namespace AffineBaseChange318
open ShortAffineJacobian318 AffineEquationFunctor318
open scoped TensorProduct
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

abbrev Changed (A B:R) := Ring (algebraMap R S A) (algebraMap R S B)

@[expose] def coefficientMap (A B:R) : Ring A B →ₐ[R] Changed (S:=S) A B :=
  toHom A B ⟨(x _ _,y _ _),by
    change (y (algebraMap R S A) (algebraMap R S B))^2 -
      (x (algebraMap R S A) (algebraMap R S B))^3 -
      algebraMap R (Changed (S:=S) A B) A * x _ _ -
      algebraMap R (Changed (S:=S) A B) B = 0
    rw [IsScalarTower.algebraMap_apply R S (Changed (S:=S) A B) A,
      IsScalarTower.algebraMap_apply R S (Changed (S:=S) A B) B]
    exact relation _ _⟩

@[simp] lemma coefficientMap_x (A B:R) :
    coefficientMap (S:=S) A B (x A B)=x (algebraMap R S A) (algebraMap R S B) :=
  toHom_x _ _ _
@[simp] lemma coefficientMap_y (A B:R) :
    coefficientMap (S:=S) A B (y A B)=y (algebraMap R S A) (algebraMap R S B) :=
  toHom_y _ _ _

@[expose] def forward (A B:R) : S ⊗[R] Ring A B →ₐ[S] Changed (S:=S) A B :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (coefficientMap A B)
    (fun _ _ => Commute.all _ _)

@[expose] def backward (A B:R) : Changed (S:=S) A B →ₐ[S] S ⊗[R] Ring A B :=
  toHom (R:=S) (S:=S ⊗[R] Ring A B) (algebraMap R S A) (algebraMap R S B)
    ⟨(Algebra.TensorProduct.includeRight (x A B),
    Algebra.TensorProduct.includeRight (y A B)),by
    have hh := congrArg (Algebra.TensorProduct.includeRight : Ring A B →ₐ[R] S ⊗[R] Ring A B)
      (relation A B)
    simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] at hh
    rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B) A,
      IsScalarTower.algebraMap_apply R S (S ⊗[R] Ring A B) B] at hh
    exact hh⟩

@[simp] lemma backward_x (A B:R) : backward (S:=S) A B (x _ _)=
    Algebra.TensorProduct.includeRight (x A B) := toHom_x _ _ _
@[simp] lemma backward_y (A B:R) : backward (S:=S) A B (y _ _)=
    Algebra.TensorProduct.includeRight (y A B) := toHom_y _ _ _

@[simp] lemma forward_includeRight (A B:R) (t:Ring A B) :
    forward (S:=S) A B (Algebra.TensorProduct.includeRight t)=coefficientMap A B t := by
  simp [forward,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

@[simp] lemma forward_includeLeft (A B:R) (s:S) :
    forward (S:=S) A B ((Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] Ring A B) s)=algebraMap S _ s := by
  simp [forward,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]

theorem forward_backward (A B:R) : (forward (S:=S) A B).comp (backward A B)=AlgHom.id S _ := by
  apply hom_ext
  · simp only [AlgHom.comp_apply,backward_x,forward_includeRight,coefficientMap_x,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,backward_y,forward_includeRight,coefficientMap_y,AlgHom.id_apply]

theorem backward_forward (A B:R) : (backward (S:=S) A B).comp (forward A B)=AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply hom_ext (R:=R) (S:=S ⊗[R] Ring A B) A B
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_x,backward_x,AlgHom.id_apply]
    · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,forward_includeRight,
        coefficientMap_y,backward_y,AlgHom.id_apply]

/-- The genuine tensor base change is the actual equation ring with mapped coefficients. -/
@[expose] def baseChangeEquiv (A B:R) :
    S ⊗[R] Ring A B ≃ₐ[S] Ring (algebraMap R S A) (algebraMap R S B) :=
  AlgEquiv.ofAlgHom (forward A B) (backward A B)
    (forward_backward A B) (backward_forward A B)

@[simp] theorem baseChangeEquiv_x (A B:R) :
    baseChangeEquiv (S:=S) A B (1 ⊗ₜ[R] x A B)=x (algebraMap R S A) (algebraMap R S B) := by
  change forward (S:=S) A B (Algebra.TensorProduct.includeRight (x A B))= _
  rw [forward_includeRight,coefficientMap_x]
@[simp] theorem baseChangeEquiv_y (A B:R) :
    baseChangeEquiv (S:=S) A B (1 ⊗ₜ[R] y A B)=y (algebraMap R S A) (algebraMap R S B) := by
  change forward (S:=S) A B (Algebra.TensorProduct.includeRight (y A B))= _
  rw [forward_includeRight,coefficientMap_y]

/-- Actual coordinate algebra of every base-changed literal OpenJ affine fiber. -/
@[expose] def literalFiberEquiv (N:ℕ) (T:Type*) [CommRing T]
    [Algebra (OpenJModel318.Base N) T] :
    T ⊗[OpenJModel318.Base N] OpenJAffineScheme318.CoordinateRing N ≃ₐ[T]
      Ring (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.A N))
        (algebraMap (OpenJModel318.Base N) T (OpenJAffineScheme318.B N)) :=
  baseChangeEquiv (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end AffineBaseChange318
