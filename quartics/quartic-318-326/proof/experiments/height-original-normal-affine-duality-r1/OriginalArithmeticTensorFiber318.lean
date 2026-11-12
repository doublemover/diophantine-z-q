module
public import OriginalArchimedeanComplexFiber318
public section
noncomputable section
namespace OriginalArithmeticTensorFiber318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalArchimedeanCotangentFiber318
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i : Fin 4)
abbrev square := OriginalArchimedeanComplexFiber318.square c i
@[expose] def point : A c i →+* K c t := ContactBranchPoint318.branchPoint c t hn i

/-- The actual number-field fiber of the original intrinsic tensor square,
through the entire original branch-point ring map. -/
abbrev fiber := (ModuleCat.extendScalars (point c t hn i)).obj
  (ModuleCat.of (A c i) (square c i))
@[expose] def frame : fiber c t hn i ≃ₗ[K c t] K c t := by
  letI : Algebra (A c i) (K c t) := (point c t hn i).toAlgebra
  exact ScalarExtensionTensor318.tensorEquiv (T:=K c t) (ModuleCat.of (A c i) (square c i)) ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl (K c t) (K c t))
      (OriginalArchimedeanComplexFiber318.squareFrame c i) ≪≫ₗ
        AlgebraTensorModule.rid (A c i) (K c t) (K c t)

lemma frame_tmul (z : K c t) (θ : square c i) :
    frame c t hn i (z ⊗ₜ[A c i,point c t hn i] θ)=
      z*point c t hn i (OriginalArchimedeanComplexFiber318.squareFrame c i θ) := by
  letI : Algebra (A c i) (K c t) := (point c t hn i).toAlgebra
  change AlgebraTensorModule.rid (A c i) (K c t) (K c t)
    (AlgebraTensorModule.congr (LinearEquiv.refl (K c t) (K c t))
      (OriginalArchimedeanComplexFiber318.squareFrame c i)
      (ScalarExtensionTensor318.tensorEquiv (T:=K c t) (ModuleCat.of (A c i) (square c i))
        (z ⊗ₜ[A c i,point c t hn i] θ)))=_
  rw [ScalarExtensionTensor318.tensorEquiv_tmul,AlgebraTensorModule.congr_tmul,
    AlgebraTensorModule.rid_tmul]
  simp only [LinearEquiv.refl_apply,Algebra.smul_def]

@[expose] def globalFiber (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : fiber c t hn i :=
  (1:K c t) ⊗ₜ[A c i,point c t hn i] ContactTrueGlobalTensorPullback318.chartTensor c i s

/-- Every true proper-curve global section has exactly its original
arithmetic value in this BOTH-INVERSE frame of the genuine fiber. -/
lemma frame_globalFiber (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    frame c t hn i (globalFiber c t hn i s)=ContactBicanonicalPointValue318.value c t hn i s := by
  rw [globalFiber,frame_tmul,one_mul,ContactTrueGlobalTensorPullback318.chartTensor,
    IntrinsicFramedTensorSections318.tensor,map_smul]
  rw [OriginalArchimedeanComplexFiber318.squareFrame_pure,
    ContactFrameNormalization318.source_coordinate_normalized,one_mul,smul_eq_mul,mul_one]
  rfl

lemma globalFiber_scaled0_ne :
    globalFiber c t hn i (ContactScaledBicanonicalPoint318.scaledQ0 c)≠0 := by
  intro h
  apply ContactBicanonicalPointHeight318.a0_ne c t hn i
  change ContactBicanonicalPointValue318.value c t hn i _=0
  rw [←frame_globalFiber c t hn i,h,map_zero]
end OriginalArithmeticTensorFiber318
