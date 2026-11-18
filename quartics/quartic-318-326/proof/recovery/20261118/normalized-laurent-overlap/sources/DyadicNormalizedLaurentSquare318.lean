module
public import DyadicLaurentOrderSquare318
public import DyadicNormalizedRatioCharts318
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace DyadicNormalizedLaurentSquare318
open DyadicLaurentOrderSquare318 DyadicNormalizedRatioCharts318

variable (D : Type*) [CommRing D] {K : Type*} [CommRing K] [Algebra D K]

local instance ambientAlg (a : Fin 4 → K) : Algebra D (FourRootOrder318.Order a) :=
  ((algebraMap K (FourRootOrder318.Order a)).comp (algebraMap D K)).toAlgebra

local instance ambientTower (a : Fin 4 → K) : IsScalarTower D K (FourRootOrder318.Order a) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

abbrev Closure (a : Fin 4 → K) := integralClosure D (FourRootOrder318.Order a)

/-- The actual isomorphism of the two D-integral subrings in the generic
four-root algebras is given by the same coefficients as the generic map. -/
@[expose] def onClosure (a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i, a i=b i*(u i:K)^2) : Closure D a ≃ₐ[D] Closure D b :=
  restrictClosure ((four a b u h).restrictScalars D)

theorem normalized_square (m a b : Fin 4 → K) (u : Fin 4 → Kˣ)
    (h : ∀ i,m i=a i*(u i:K)^2) (t : Kˣ) :
    (onClosure D _ _ u (inverse_ratio m a b u h t)).trans
      (onClosure D _ _ (fun _ => t⁻¹) (inverse_relation a b t)) =
    (onClosure D _ _ (fun _ => t⁻¹) (inverse_relation m b t)).trans
      (onClosure D _ _ u (finite_ratio m a b u h t)) := by
  ext1 x
  apply Subtype.ext
  exact DFunLike.congr_fun (actual_laurent_square m a b u h t)
    (x : FourRootOrder318.Order (inverseRat m b t))

section Laurent
variable (A : Type*) [CommRing A]
abbrev Overlap := LaurentPolynomial A
@[expose] def parameter : (Overlap A)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [←LaurentPolynomial.T_add] <;> norm_num
  inv_val := by rw [←LaurentPolynomial.T_add] <;> norm_num

/-- In an algebra over the common Laurent chart, the two parameter factors
are literally the images of the monomials T¹ and T⁻¹. -/
@[expose] def markedParameter (L : Type*) [CommRing L] [Algebra (Overlap A) L] : Lˣ :=
  Units.map (algebraMap (Overlap A) L).toMonoidHom (parameter A)

theorem parameter_values (L : Type*) [CommRing L] [Algebra (Overlap A) L] :
    ((markedParameter A L:L)=algebraMap (Overlap A) L (LaurentPolynomial.T 1)) ∧
    ((↑(markedParameter A L)⁻¹:L)=algebraMap (Overlap A) L (LaurentPolynomial.T (-1))) :=
  ⟨rfl,rfl⟩

/-- Actual parameter on G_m; K/L need not be fields after an etale extension.
When L is the chosen generic scalar ring this compares both routes on the
algebras normalized over the Laurent ring itself. -/
theorem original_overlap_square (L : Type*) [CommRing L] [Algebra (Overlap A) L]
    (m a b : Fin 4 → L) (u : Fin 4 → Lˣ) (h : ∀ i,m i=a i*(u i:L)^2) :
    (onClosure (Overlap A) _ _ u (inverse_ratio m a b u h (markedParameter A L))).trans
      (onClosure (Overlap A) _ _ (fun _ => (markedParameter A L)⁻¹) (inverse_relation a b (markedParameter A L))) =
    (onClosure (Overlap A) _ _ (fun _ => (markedParameter A L)⁻¹) (inverse_relation m b (markedParameter A L))).trans
      (onClosure (Overlap A) _ _ u (finite_ratio m a b u h (markedParameter A L))) :=
  normalized_square (Overlap A) m a b u h (markedParameter A L)
end Laurent
end DyadicNormalizedLaurentSquare318
