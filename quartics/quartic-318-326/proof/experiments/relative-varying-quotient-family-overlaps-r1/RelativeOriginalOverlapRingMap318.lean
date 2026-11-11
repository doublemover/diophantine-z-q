module
public import RelativeOriginalLaurentAlgebra318
public section
noncomputable section
namespace RelativeOriginalOverlapRingMap318
open LaurentPolynomial
open scoped TensorProduct
universe u
variable (k R B O : Type u) [CommRing k] [CommRing R] [CommRing B] [CommRing O]
  [Algebra k R] [Algebra k B] [Algebra k O]
  [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B]
  [Algebra (LaurentPolynomial k) O] [IsScalarTower k (LaurentPolynomial k) O]

/-- Literal coefficient extension of the original chart-to-overlap ring map. -/
def map (g : B →ₐ[k] O) : R ⊗[k] B →ₐ[k] R ⊗[k] O :=
  Algebra.TensorProduct.map (AlgHom.id k R) g

lemma map_tmul (g : B →ₐ[k] O) (r : R) (b : B) :
    map k R B O g (r ⊗ₜ[k] b) = r ⊗ₜ[k] g b := by
  simp [map]

/-- Actual finite or reciprocal polynomial restriction square. Its
coordinate equation is the OLD chart equation, not a new module assumption. -/
lemma polynomial_square (g : B →ₐ[k] O) (s : Polynomial R →+* LaurentPolynomial R)
    (hC : ∀ r, s (Polynomial.C r) = C r) (n : ℤ) (hX : s Polynomial.X = T n)
    (hg : g (algebraMap (Polynomial k) B Polynomial.X) =
      algebraMap (LaurentPolynomial k) O (T n)) :
    (map k R B O g).toRingHom.comp
        (RelativeOriginalPolynomialAlgebra318.polynomialMap k R B) =
      (RelativeOriginalLaurentAlgebra318.laurentMap k R O).comp s := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,RelativeOriginalPolynomialAlgebra318.polynomialMap_C,
      hC,RelativeOriginalLaurentAlgebra318.laurentMap_C]
    change map k R B O g (r ⊗ₜ[k] (1 : B)) = r ⊗ₜ[k] (1 : O)
    rw [map_tmul,map_one]
  · simp only [RingHom.comp_apply,RelativeOriginalPolynomialAlgebra318.polynomialMap_X,
      hX,RelativeOriginalLaurentAlgebra318.laurentMap_T]
    change map k R B O g (1 ⊗ₜ[k] algebraMap (Polynomial k) B Polynomial.X) =
      1 ⊗ₜ[k] algebraMap (LaurentPolynomial k) O (T n)
    rw [map_tmul,hg]

lemma finite_square (g : B →ₐ[k] O)
    (hg : g (algebraMap (Polynomial k) B Polynomial.X) =
      algebraMap (LaurentPolynomial k) O (T 1)) :
    (map k R B O g).toRingHom.comp
        (RelativeOriginalPolynomialAlgebra318.polynomialMap k R B) =
      (RelativeOriginalLaurentAlgebra318.laurentMap k R O).comp Polynomial.toLaurent :=
  polynomial_square k R B O g Polynomial.toLaurent Polynomial.toLaurent_C 1
    Polynomial.toLaurent_X hg

/-- The entire original infinity coordinate goes to T⁻¹. -/
lemma infinity_square (g : B →ₐ[k] O)
    (hg : g (algebraMap (Polynomial k) B Polynomial.X) =
      algebraMap (LaurentPolynomial k) O (T (-1))) :
    (map k R B O g).toRingHom.comp
        (RelativeOriginalPolynomialAlgebra318.polynomialMap k R B) =
      (RelativeOriginalLaurentAlgebra318.laurentMap k R O).comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
  apply polynomial_square k R B O g _ (fun r => by simp) (-1) (by simp) hg
end RelativeOriginalOverlapRingMap318
