module
public import DyadicFourRatioMarkedOrder318
public import Mathlib.RingTheory.Smooth.IntegralClosure
public section
noncomputable section
namespace DyadicNormalizedRatioCharts318
open scoped TensorProduct
open DyadicFourRatioMarkedOrder318
variable {R : Type*} [CommRing R]
variable (K : Type*) [CommRing K] [Algebra R K]
/-- For R the affine parameter ring and K its fraction field, this is the
usual generic chart algebra. The integral closure below is computed over R,
not over K and not over the marked raw order. -/
abbrev Ambient (a : Fin 4 → R) := K ⊗[R] FourRootOrder318.Order a

/-- A square correction may involve negative uniformizer valuation: it is
required to be a unit only in the generic parameter algebra K. -/
@[expose] def genericScale (m a : Fin 4 → R) (v : Fin 4 → Kˣ)
    (hv : ∀ i, algebraMap R K (m i) = algebraMap R K (a i) * (v i : K)^2) :
    Ambient K m ≃ₐ[K] Ambient K a := by
  let e (i : Fin 4) := UnitRootScaling318.equiv _ _ (v i) (hv i)
  exact (FourRootOrder318.baseChange m K).trans
    ((Algebra.TensorProduct.congr (Algebra.TensorProduct.congr (e 0) (e 1))
      (Algebra.TensorProduct.congr (e 2) (e 3))).trans (FourRootOrder318.baseChange a K).symm)

variable (c : Fin 4 → R) (hu : ∀ i, IsUnit (1+4*c i))
/-- Actual ambient isomorphism after the marked etale cover: a square in K
first, then the unit ratio using the four half-coordinates. -/
@[expose] def ambientComparison (m a b : Fin 4 → R) (v : Fin 4 → Kˣ)
    (hv : ∀ i, algebraMap R K (m i) = algebraMap R K (a i) * (v i : K)^2)
    (hab : ∀ i, a i = b i * (1+4*c i)) :
    Joint c ⊗[R] Ambient K m ≃ₐ[Joint c] Joint c ⊗[R] Ambient K b :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Joint c ≃ₐ[Joint c] Joint c)
    ((genericScale K m a v hv).restrictScalars R)).trans
      (TensorPairBaseChange318.tensorEquiv
        (AlgEquiv.refl : Joint c ⊗[R] K ≃ₐ[Joint c] Joint c ⊗[R] K)
        (markedOrderEquiv c hu a b hab))

variable {S B D : Type*} [CommRing S] [CommRing B] [CommRing D] [Algebra S B] [Algebra S D]
@[expose] def restrictClosure (e : B ≃ₐ[S] D) :
    integralClosure S B ≃ₐ[S] integralClosure S D where
  toFun x := ⟨e x,x.property.map e.toAlgHom⟩
  invFun x := ⟨e.symm x,x.property.map e.symm.toAlgHom⟩
  left_inv x := Subtype.ext (e.left_inv x)
  right_inv x := Subtype.ext (e.right_inv x)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  map_add' x y := Subtype.ext (e.map_add x y)
  commutes' r := Subtype.ext (e.commutes r)

@[expose] def normalizeAfterCover (B : Type*) [CommRing B] [Algebra R B] :
    Joint c ⊗[R] integralClosure R B ≃ₐ[Joint c] integralClosure (Joint c) (Joint c ⊗[R] B) := by
  letI : Algebra.Etale R (Joint c) := DyadicFourRatioMarkedOrder318.etale c hu
  exact AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R (Joint c) B)
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R:=R) (S:=Joint c) (B:=B))

/-- The normalized parameter charts themselves become isomorphic by their
actual etale base-change maps, even when the square correction is not a
unit or an element of R. No normality assumption on a raw order is used. -/
@[expose] def comparison (m a b : Fin 4 → R) (v : Fin 4 → Kˣ)
    (hv : ∀ i, algebraMap R K (m i) = algebraMap R K (a i) * (v i : K)^2)
    (hab : ∀ i, a i = b i * (1+4*c i)) :
    Joint c ⊗[R] integralClosure R (Ambient K m) ≃ₐ[Joint c]
      Joint c ⊗[R] integralClosure R (Ambient K b) :=
  (normalizeAfterCover c hu (Ambient K m)).trans
    ((restrictClosure (ambientComparison K c hu m a b v hv hab)).trans
      (normalizeAfterCover c hu (Ambient K b)).symm)

theorem comparison_marking (m a b : Fin 4 → R) (v : Fin 4 → Kˣ)
    (hv : ∀ i, algebraMap R K (m i) = algebraMap R K (a i) * (v i : K)^2)
    (hab : ∀ i, a i = b i * (1+4*c i)) (x : Joint c ⊗[R] integralClosure R (Ambient K m)) :
    ((normalizeAfterCover c hu (Ambient K b)
      (comparison K c hu m a b v hv hab x)) : Joint c ⊗[R] Ambient K b) =
    ambientComparison K c hu m a b v hv hab
      (normalizeAfterCover c hu (Ambient K m) x : Joint c ⊗[R] Ambient K m) := by
  simp only [comparison,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply] <;> rfl

end DyadicNormalizedRatioCharts318
