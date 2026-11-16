module
public import KummerTensorField318
public section
noncomputable section
namespace FourRootAutomorphisms318
set_option maxHeartbeats 900000
open scoped TensorProduct
open QuadraticPresentation318 KummerTensorField318
variable {F:Type*} [Field F] [CharZero F]
@[expose] def negateHom (a:F) : RootRing a→ₐ[F]RootRing a :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F _) (-AdjoinRoot.root (polynomial a)) (by
    change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C a)=0
    simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,neg_sq,root_square,sub_self])
@[simp] theorem negateHom_root (a:F) :
    negateHom a (AdjoinRoot.root (polynomial a))=-AdjoinRoot.root (polynomial a) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _
@[expose] def negateEquiv (a:F) : RootRing a≃ₐ[F]RootRing a :=
  AlgEquiv.ofAlgHom (negateHom a) (negateHom a)
    (by apply AdjoinRoot.algHom_ext; simp)
    (by apply AdjoinRoot.algHom_ext; simp)
@[simp] theorem negateEquiv_root (a:F) :
    negateEquiv a (AdjoinRoot.root (polynomial a))=-AdjoinRoot.root (polynomial a) :=
  negateHom_root a
@[expose] def bitEquiv (a:F) (b:Bool) : RootRing a≃ₐ[F]RootRing a :=
  if b then negateEquiv a else AlgEquiv.refl

variable (a:Fin 4→F)
@[expose] def generator : Fin 4→Raw a :=
  ![((AdjoinRoot.root (polynomial (a 0))⊗ₜ[F]1)⊗ₜ[F]1),
    ((1⊗ₜ[F]AdjoinRoot.root (polynomial (a 1)))⊗ₜ[F]1),
    (1⊗ₜ[F](AdjoinRoot.root (polynomial (a 2))⊗ₜ[F]1)),
    (1⊗ₜ[F](1⊗ₜ[F]AdjoinRoot.root (polynomial (a 3))))]
@[expose] def signEquiv (s:Fin 4→Bool) : Raw a≃ₐ[F]Raw a :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr (bitEquiv (a 0) (s 0)) (bitEquiv (a 1) (s 1)))
    (Algebra.TensorProduct.congr (bitEquiv (a 2) (s 2)) (bitEquiv (a 3) (s 3)))

theorem scalar_right {A B:Type*} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (r:F) :
    (1:A)⊗ₜ[F](algebraMap F B r)=(algebraMap F A r)⊗ₜ[F](1:B) :=
  (Algebra.TensorProduct.algebraMap_apply' r).symm.trans
    (Algebra.TensorProduct.algebraMap_apply r)

theorem generator_square (i:Fin 4) : generator a i^2=algebraMap F (Raw a) (a i) := by
  fin_cases i <;> simp [generator,Algebra.TensorProduct.tmul_pow,root_square,
    Algebra.TensorProduct.algebraMap_def, ←AdjoinRoot.algebraMap_eq, scalar_right]
  · exact scalar_right (A:=RootRing (a 0)⊗[F]RootRing (a 1)) (B:=RootRing (a 2)⊗[F]RootRing (a 3)) (a 2)
  · exact scalar_right (A:=RootRing (a 0)⊗[F]RootRing (a 1)) (B:=RootRing (a 2)⊗[F]RootRing (a 3)) (a 3)

theorem signEquiv_generator (s:Fin 4→Bool) (i:Fin 4) :
    signEquiv a s (generator a i)=if s i then -generator a i else generator a i := by
  fin_cases i <;> simp [signEquiv,generator,bitEquiv] <;> split <;> simp_all [TensorProduct.neg_tmul, TensorProduct.tmul_neg]

theorem bitEquiv_trans_self (b:Bool) (r:F) :
    (bitEquiv r b).trans (bitEquiv r b)=AlgEquiv.refl := by
  cases b
  · rfl
  · apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    simp [bitEquiv,AlgEquiv.trans_apply]

theorem signEquiv_trans_self (s:Fin 4→Bool) :
    (signEquiv a s).trans (signEquiv a s)=AlgEquiv.refl := by
  simp only [signEquiv,←Algebra.TensorProduct.congr_trans,
    bitEquiv_trans_self,Algebra.TensorProduct.congr_refl]

variable [Fact (QuadraticTower318.Independent a)]
theorem generator_ne_zero (i:Fin 4) : generator a i≠0 := by
  letI:Field (Raw a):=(actual_field a).toField
  have hai:a i≠0 := by
    have h:=Fact.out (p:=QuadraticTower318.Independent a)
    intro hz
    fin_cases i
    · exact h.1 ⟨0,by simpa using hz⟩
    · exact h.2.1 (Or.inl ⟨0,by simpa using hz⟩)
    · exact h.2.2.1 (Or.inl (Or.inl ⟨0,by simpa using hz⟩))
    · exact h.2.2.2 (Or.inl (Or.inl (Or.inl ⟨0,by simpa using hz⟩)))
  intro hg
  apply hai
  apply (algebraMap F (Raw a)).injective
  rw [←generator_square,hg,zero_pow (by decide : 2≠0),map_zero]

/-- All sixteen actual root-sign automorphisms are distinct. -/
theorem signEquiv_injective : Function.Injective (signEquiv a) := by
  letI:Field (Raw a):=(actual_field a).toField
  letI:CharZero (Raw a):=Algebra.charZero_of_charZero F (Raw a)
  intro s t h
  funext i
  have hh:=congrArg (fun e:Raw a≃ₐ[F]Raw a=>e (generator a i)) h
  rw [signEquiv_generator,signEquiv_generator] at hh
  cases hs:s i <;> cases ht:t i
  · rfl
  · simp only [hs,ht,Bool.false_eq_true,ite_false,ite_true] at hh
    have hz:(2:Raw a)*generator a i=0 := by linear_combination hh
    exact False.elim ((mul_ne_zero (by norm_num) (generator_ne_zero a i)) hz)
  · simp only [hs,ht,Bool.false_eq_true,ite_false,ite_true] at hh
    have hz:(2:Raw a)*generator a i=0 := by linear_combination -hh
    exact False.elim ((mul_ne_zero (by norm_num) (generator_ne_zero a i)) hz)
  · rfl
end FourRootAutomorphisms318
