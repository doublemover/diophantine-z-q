module
public import FiniteDualTransport318
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace FiniteDualDifferentialRealization318
open FiniteDualModuleAction318 FiniteDualTransport318
open scoped TensorProduct
variable {R A B K ι : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing K]
  [Algebra R A] [Algebra K B] [Fintype ι] [DecidableEq ι]
  (F : TensorCoefficientDuality318.Frame R A ι) (f : A →+* B)
  (ω : KaehlerDifferential K B)

/-- Whole semilinear realization of the genuine finite-dual module in
actual generic Kaehler differentials, with an explicit chosen dual-generator image. -/
@[expose] def realization : Dual R A →ₛₗ[f] KaehlerDifferential K B where
  toFun x := f ((frame R A F).symm x) • ω
  map_add' x y := by rw [map_add,map_add,add_smul]
  map_smul' a x := by rw [map_smul]; change f (a*((frame R A F).symm x)) • ω=_; rw [map_mul,mul_smul]

theorem realization_frame (a : A) : realization F f ω (frame R A F a)=f a • ω := by
  change f ((frame R A F).symm (frame R A F a)) • ω=_
  rw [LinearEquiv.symm_apply_apply]

@[expose] def squareRealization : Square (R:=R) (A:=A) →ₛₗ[f]
    KaehlerDifferential K B ⊗[B] KaehlerDifferential K B :=
  TensorProduct.map (realization F f ω) (realization F f ω)

theorem squareRealization_frame (a : A) : squareRealization F f ω (squareFrame F a)=
    f a • (ω ⊗ₜ[B] ω) := by
  rw [squareFrame_scalar,map_smul,squareFrame_one]
  change f a • (realization F f ω (frame R A F 1) ⊗ₜ[B]
    realization F f ω (frame R A F 1))=_
  rw [realization_frame,map_one,one_smul]
end FiniteDualDifferentialRealization318
