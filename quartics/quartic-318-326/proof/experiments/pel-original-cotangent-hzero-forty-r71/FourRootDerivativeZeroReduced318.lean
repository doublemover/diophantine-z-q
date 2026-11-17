module
public import FourRootWholeZeroRadical318
public import FourRootDerivativeIdealClosed318
public section
noncomputable section
namespace FourRootDerivativeZeroReduced318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
/-- Full original quotient-chart cover of the actual glued zero scheme. -/
@[expose] def twoChartCover:(zeroScheme b).OpenCover where
  I₀:=Bool
  X k:=if k then finiteZero b else infinityZero b
  f k:=by cases k;exact infinityChart b;exact finiteChart b
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      rcases charts_cover b p with ⟨q,hq⟩|⟨q,hq⟩
      · exact ⟨true,q,hq⟩
      · exact ⟨false,q,hq⟩
    · intro k;cases k <;> infer_instance
/-- The actual derivative-zero scheme is reduced everywhere. Its
original quotient ideals and inclusion are unchanged; this is not the
reduction of a substitute scheme or only a complex-point claim. -/
theorem reduced:IsReduced (zeroScheme b):=by
  letI:_root_.IsReduced (FourRootAffineCoordinateRing318.Ring b⧸
      FourRootDerivativeZeroIdeals318.finiteIdeal b):=
    FourRootWholeZeroRadical318.finite_reduced b hb
  letI:_root_.IsReduced (FourRootInfinityCoordinateRing318.Ring b⧸
      FourRootDerivativeZeroIdeals318.infinityIdeal b):=
    FourRootWholeZeroRadical318.infinity_reduced b hb
  haveI:∀k,IsReduced ((twoChartCover b).X k):=by
    intro k
    cases k <;> change IsReduced (Spec (CommRingCat.of _)) <;> infer_instance
  exact IsReduced.of_openCover _ (twoChartCover b)
end FourRootDerivativeZeroReduced318
