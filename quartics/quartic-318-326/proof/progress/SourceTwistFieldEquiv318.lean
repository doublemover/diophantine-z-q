module
public import SourceTwistRecovery318
public import FourRootAutomorphisms318
public section
noncomputable section
namespace SourceTwistFieldEquiv318
open scoped TensorProduct
open QuadraticPresentation318
set_option maxHeartbeats 900000
variable {F:Type*} [Field F]

/-- A specified nonzero square scaling gives an actual isomorphism of
quadratic root algebras, not merely equality of squareclasses. -/
@[expose] def scaleHom (a b u:F) (h:a=b*u^2) : RootRing a→ₐ[F]RootRing b :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId F _) 
    (algebraMap F (RootRing b) u*AdjoinRoot.root (polynomial b)) (by
      change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C a)=0
      simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,mul_pow,root_square]
      rw [h,map_mul,map_pow]
      ring)
@[simp] theorem scaleHom_root (a b u:F) (h:a=b*u^2) :
    scaleHom a b u h (AdjoinRoot.root (polynomial a))=
      algebraMap F (RootRing b) u*AdjoinRoot.root (polynomial b) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def scaleEquiv (a b u:F) (hu:u≠0) (h:a=b*u^2) : RootRing a≃ₐ[F]RootRing b := by
  have hi:b=a*(u⁻¹)^2 := by rw [h]; field_simp
  exact AlgEquiv.ofAlgHom (scaleHom a b u h) (scaleHom b a u⁻¹ hi)
    (by
      apply AdjoinRoot.algHom_ext
      change scaleHom a b u h (scaleHom b a u⁻¹ hi (AdjoinRoot.root (polynomial b)))=_
      rw [scaleHom_root,map_mul,AlgHom.commutes,scaleHom_root,←mul_assoc,
        ←map_mul,inv_mul_cancel₀ hu,map_one,one_mul]
      rfl)
    (by
      apply AdjoinRoot.algHom_ext
      change scaleHom b a u⁻¹ hi (scaleHom a b u h (AdjoinRoot.root (polynomial a)))=_
      rw [scaleHom_root,map_mul,AlgHom.commutes,scaleHom_root,←mul_assoc,
        ←map_mul,mul_inv_cancel₀ hu,map_one,one_mul]
      rfl)

variable [CharZero F]
@[expose] def fourRootEquiv (a b u:Fin 4→F) (hu:∀i,u i≠0) (h:∀i,a i=b i*u i^2) :
    KummerTensorField318.Raw a≃ₐ[F]KummerTensorField318.Raw b :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr (scaleEquiv (a 0) (b 0) (u 0) (hu 0) (h 0))
      (scaleEquiv (a 1) (b 1) (u 1) (hu 1) (h 1)))
    (Algebra.TensorProduct.congr (scaleEquiv (a 2) (b 2) (u 2) (hu 2) (h 2))
      (scaleEquiv (a 3) (b 3) (u 3) (hu 3) (h 3)))

/-- Pointwise constant squareclasses produce an actual isomorphism over
Q(t) between the original four-root function fields. -/
theorem source_equiv_of_squareclasses (a b:Fin 4→ℚˣ)
    (h:∀i,IsSquare ((a i:ℚ)/(b i:ℚ))) :
    Nonempty (KummerTensorField318.Raw (SourceKummerField318.parameter a)≃ₐ[RatFunc ℚ]
      KummerTensorField318.Raw (SourceKummerField318.parameter b)) := by
  have hs:∀i,∃u:ℚ,(a i:ℚ)=(b i:ℚ)*u^2 ∧ u≠0 := by
    intro i
    obtain ⟨u,hu⟩:=(isSquare_iff_exists_sq _).mp (h i)
    have he:(a i:ℚ)=(b i:ℚ)*u^2 := by rw [←hu]; field_simp
    refine ⟨u,he,?_⟩
    intro hz
    rw [hz,zero_pow (by decide : 2≠0),mul_zero] at he
    exact (a i).ne_zero he
  choose u he hu using hs
  refine ⟨fourRootEquiv _ _ (fun i=>RatFunc.C (u i))
    (fun i=>by simpa only [map_zero] using RatFunc.C_injective.ne (hu i)) ?_⟩
  intro i
  simp only [SourceKummerField318.parameter,he,map_mul,map_pow,RatFunc.algebraMap_C]
  ring

/-- The remaining geometric coefficient-scaling interface now concludes
an actual Q(t)-algebra equivalence with the fixed arithmetic model. -/
theorem source_equiv_of_published_scalings (a:Fin 4→ℚˣ)
    (h:∀i,∃u:ℚ,u≠0 ∧
      ComplementSquareclass318.complementaryProduct (fun j=>(a j:ℚ)) i^2*
        SourceTwistArithmetic318.cubicA i=u^4*SourceTwistArithmetic318.publishedA i ∧
      ComplementSquareclass318.complementaryProduct (fun j=>(a j:ℚ)) i^3*
        SourceTwistArithmetic318.cubicB i=u^6*SourceTwistArithmetic318.publishedB i) :
    Nonempty (KummerTensorField318.Raw (SourceKummerField318.parameter a)≃ₐ[RatFunc ℚ]
      KummerTensorField318.Raw (SourceKummerField318.parameter SourceTwistArithmetic318.units)) :=
  source_equiv_of_squareclasses _ _
    (SourceTwistRecovery318.recover_source_twists _ (fun i=>(a i).ne_zero) h)
end SourceTwistFieldEquiv318
