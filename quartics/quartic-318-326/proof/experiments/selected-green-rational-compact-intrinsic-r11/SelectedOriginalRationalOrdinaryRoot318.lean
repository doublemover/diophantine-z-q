module
public import SelectedOriginalRationalOrdinary318
public import SelectedNormalizedEtaleDJ318
public import SelectedMonicReducedFiber318
import all SelectedMonicReducedFiber318
public section
noncomputable section

open Polynomial
open scoped TensorProduct
open SelectedOriginalRationalOrdinary318 SelectedRationalGenericFromComplex318

namespace SelectedOriginalRationalOrdinaryRoot318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev ordinaryPolynomial : Base[X] := p.map (toRational N)
abbrev ordinaryRoot := AdjoinRoot (ordinaryPolynomial N p)
abbrev genericRoot := AdjoinRoot (p.map (rationalGenericMap N))

/-- Whole root quotient before and after rationalizing coefficients.
This arrow sends the original generating x, not one chosen geometric root. -/
@[expose] def rationalRootMap : AdjoinRoot p →+* ordinaryRoot N p :=
  AdjoinRoot.map (toRational N) p (ordinaryPolynomial N p) (dvd_refl _)

theorem rationalRootMap_mk (w : (OpenJModel318.Base N)[X]) :
    rationalRootMap N p (AdjoinRoot.mk p w) =
      AdjoinRoot.mk (ordinaryPolynomial N p) (w.map (toRational N)) := by
  rw [rationalRootMap,AdjoinRoot.map,AdjoinRoot.lift_mk,← Polynomial.eval₂_map,
    ← AdjoinRoot.algebraMap_eq,← Polynomial.aeval_def,AdjoinRoot.aeval_eq]

theorem rationalRootMap_x :
    rationalRootMap N p (AdjoinRoot.root p) = AdjoinRoot.root (ordinaryPolynomial N p) :=
  AdjoinRoot.map_root _ _ _ _

/-- The same derivative unit survives the whole scalar map, BEFORE
the passage to the field. That is what gives normality on the ordinary
chart; generic separability alone would not suffice. -/
theorem ordinary_etale (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    Algebra.Etale Base (ordinaryRoot N p) := by
  have hu := hd.map (rationalRootMap N p)
  rw [rationalRootMap_mk,← Polynomial.derivative_map] at hu
  exact SelectedNormalizedEtaleDJ318.etale_of_derivative _ (hp.map _) hu

theorem ordinary_finite (hp : p.Monic) : Module.Finite Base (ordinaryRoot N p) :=
  (hp.map (toRational N)).finite_adjoinRoot

theorem generic_polynomial :
    letI : Algebra Base QJ := ratscalar
    (ordinaryPolynomial N p).map (algebraMap Base QJ) = p.map (rationalGenericMap N) := by
  letI : Algebra Base QJ := ratscalar
  rw [Polynomial.map_map,generic_factor]

/-- Generic fiber of the actual rational ordinary root chart. This is
the full tensor and maps to the exact compact-normalization field,
with no auxiliary choice of a root or an irreducible factor. -/
def genericEquiv :
    letI : Algebra Base QJ := ratscalar
    QJ ⊗[Base] ordinaryRoot N p ≃ₐ[QJ] genericRoot N p := by
  letI : Algebra Base QJ := ratscalar
  let E := SelectedMonicReducedFiber318.mappedRootEquiv QJ (ordinaryPolynomial N p)
  exact E.trans (AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : QJ ≃ₐ[QJ] QJ) _ _
    (by
      change Associated (((ordinaryPolynomial N p).map (algebraMap Base QJ)).map
        (RingHom.id QJ)) (p.map (rationalGenericMap N))
      rw [Polynomial.map_id,generic_polynomial] <;> exact Associated.refl _))

theorem genericEquiv_x :
    letI : Algebra Base QJ := ratscalar
    genericEquiv N p ((1 : QJ) ⊗ₜ[Base] AdjoinRoot.root (ordinaryPolynomial N p)) =
      AdjoinRoot.root (p.map (rationalGenericMap N)) := by
  letI : Algebra Base QJ := ratscalar
  simp only [genericEquiv,SelectedMonicReducedFiber318.mappedRootEquiv,AlgEquiv.trans_apply,
    AdjoinRoot.tensorAlgEquiv_root,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_root]

end SelectedOriginalRationalOrdinaryRoot318

#print axioms SelectedOriginalRationalOrdinaryRoot318.ordinary_etale
#print axioms SelectedOriginalRationalOrdinaryRoot318.genericEquiv_x
