module
public import OriginalCanonicalContactOpenRecognition318
public import OriginalCanonicalContactFieldComparison318

@[expose] public section
noncomputable section

namespace OriginalContactGenericToOpen318
open AlgebraicGeometry CategoryTheory
open ContactKummerOrder318 (R K OpenBase OpenOrder denominator)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "U" => OpenBase
local notation "c" => SourceTwistArithmetic318.units
local notation "A" => OpenOrder c
local notation "L" => SourceOpenFractionField318.L c

local instance originalBaseAlgebra : Algebra U L :=
  ((SourceOpenFractionField318.openEmbedding c).comp (algebraMap U A)).toAlgebra

variable {M : Type} [Field M] [Algebra K M] [Algebra U M]

/-- The generic comparison automatically respects the whole open
coefficient ring when the canonical function-field scalar and
canonical affine scalar agree on the retained polynomial coordinate. -/
theorem scalar_on_open (e : L ≃ₐ[K] M)
    (h : (algebraMap U M).comp (algebraMap R U) =
      (algebraMap K M).comp (algebraMap R K)) :
    e.toRingEquiv.toRingHom.comp (algebraMap U L) = algebraMap U M := by
  apply IsLocalization.ringHom_ext (Submonoid.powers denominator)
  apply RingHom.ext
  intro p
  change e (SourceOpenFractionField318.openEmbedding c
      (algebraMap U A (algebraMap R U p))) = algebraMap U M (algebraMap R U p)
  rw [SourceOpenFractionField318.openEmbedding_on_polynomial, e.commutes]
  exact (RingHom.congr_fun h p).symm

/-- Equality on the polynomial constants and the single *same* T
suffices. This does not substitute a numerical evaluation of T. -/
theorem scalar_agreement
    (hQ : ∀ a : ℚ, algebraMap U M (algebraMap R U (Polynomial.C a)) =
      algebraMap K M (algebraMap R K (Polynomial.C a)))
    (hT : algebraMap U M (algebraMap R U Polynomial.X) =
      algebraMap K M (algebraMap R K Polynomial.X)) :
    (algebraMap U M).comp (algebraMap R U) =
      (algebraMap K M).comp (algebraMap R K) :=
  Polynomial.ringHom_ext hQ hT

/-- There is no second field isomorphism to choose for the open. -/
def over_open (e : L ≃ₐ[K] M)
    (h : (algebraMap U M).comp (algebraMap R U) =
      (algebraMap K M).comp (algebraMap R K)) : L ≃ₐ[U] M where
  __ := e.toRingEquiv
  commutes' x := RingHom.congr_fun (scalar_on_open e h) x

theorem over_open_read (e : L ≃ₐ[K] M)
    (h : (algebraMap U M).comp (algebraMap R U) =
      (algebraMap K M).comp (algebraMap R K)) (x : L) :
    over_open e h x = e x := rfl

variable {D : Type} [CommRing D] [Algebra U D] [Algebra D M]
    [IsScalarTower U D M] [IsFractionRing D M] [IsIntegrallyClosed D] [Module.Finite U D]
variable {C Z : Scheme} (j : Spec (CommRingCat.of D) ⟶ C)
  (chi : C ⟶ ProjectiveJLine318.scheme ℚ)
  (hj : j ≫ chi = Spec.algebraMap U D ≫ ContactProjectiveModel318.baseOpen)
  (f : Z ⟶ C) [Surjective f] [Module.Finite K M]

/-- The four genuine rational eigenfunctions of the canonical coarse
curve supply its fine point over the original q directly. No input
order comparison, scheme isomorphism, or selected coarse point. -/
theorem lift_from_eigenfunctions
    (y : Fin 4 → M)
    (hy : ∀ i, y i ^ 2 = algebraMap K M (OriginalCanonicalContactFieldComparison318.parameter i))
    (d : Module.finrank K M = 16)
    (h : (algebraMap U M).comp (algebraMap R U) =
      (algebraMap K M).comp (algebraMap R K))
    (u v : ℤ) (hne : ∀ i : Fin 5, ContactRadical318.forms u v i ≠ 0) :
    ∃ z : Z, (f ≫ chi) z =
      OriginalLiteralContactQuotientPoint318.point u v (⊥ : PrimeSpectrum ℚ) :=
  OriginalCanonicalContactOpenRecognition318.fine_point_over_original
    (over_open (OriginalCanonicalContactFieldComparison318.comparison y hy d) h)
    j chi hj f u v hne

end OriginalContactGenericToOpen318

#print axioms OriginalContactGenericToOpen318.scalar_on_open
#print axioms OriginalContactGenericToOpen318.scalar_agreement
#print axioms OriginalContactGenericToOpen318.over_open
#print axioms OriginalContactGenericToOpen318.over_open_read
#print axioms OriginalContactGenericToOpen318.lift_from_eigenfunctions
