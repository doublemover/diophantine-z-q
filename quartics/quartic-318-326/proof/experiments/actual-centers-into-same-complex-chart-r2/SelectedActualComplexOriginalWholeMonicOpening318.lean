module

public import SelectedActualComplexPolynomialOrdinaryBase318
public import Mathlib.RingTheory.AdjoinRoot

public section

noncomputable section

open scoped TensorProduct Polynomial
open SelectedActualComplexPolynomialOrdinaryBase318

namespace SelectedActualComplexOriginalWholeMonicOpening318

universe u

variable (k C : Type u) [CommRing k] [CommRing C] [Algebra k C] (d : k[X])

abbrev S := baseRing k d
abbrev T := complexPolynomialBase k C d
abbrev baseInclude : S k d →+* (C ⊗[k] S k d) :=
  (Algebra.TensorProduct.includeRight : S k d →ₐ[k] C ⊗[k] S k d).toRingHom

def ordinaryScalar : S k d →+* T k C d :=
  (scalarOrdinaryBase k C d).toRingHom.comp (baseInclude k C d)

abbrev tensorPolynomial (p : (S k d)[X]) := p.map (baseInclude k C d)

abbrev originalMappedPolynomial (p : (S k d)[X]) := p.map (ordinaryScalar k C d)

private theorem mapping_chain (p : (S k d)[X]) :
    (tensorPolynomial k C d p).map (scalarOrdinaryBase k C d) =
      originalMappedPolynomial k C d p := by
  unfold tensorPolynomial originalMappedPolynomial ordinaryScalar
  rw [Polynomial.map_map] <;> rfl

/-- The actual original ordinary root chart after scalar change is
the entire monic quotient over the true complex polynomial base. -/
def originalWholeMonicOpening (p : (S k d)[X]) :
    C ⊗[k] AdjoinRoot p ≃+* AdjoinRoot (originalMappedPolynomial k C d p) :=
  (AdjoinRoot.tensorAlgEquiv p (tensorPolynomial k C d p) rfl).toRingEquiv.trans
    (AdjoinRoot.mapRingEquiv (scalarOrdinaryBase k C d) (tensorPolynomial k C d p)
      (originalMappedPolynomial k C d p) (by rw [mapping_chain]; exact Associated.refl _))

theorem originalWholeMonicOpening_root (p : (S k d)[X]) :
    originalWholeMonicOpening k C d p ((1 : C) ⊗ₜ[k] AdjoinRoot.root p) =
      AdjoinRoot.root (originalMappedPolynomial k C d p) := by
  simp [originalWholeMonicOpening]

theorem originalWholeMonicOpening_base (p : (S k d)[X]) (r : S k d) :
    originalWholeMonicOpening k C d p ((1 : C) ⊗ₜ[k] AdjoinRoot.of p r) =
      AdjoinRoot.of (originalMappedPolynomial k C d p) (ordinaryScalar k C d r) := by
  simp [originalWholeMonicOpening, ordinaryScalar, baseInclude]

private def fromOldRoot (p : (S k d)[X]) :
    AdjoinRoot p →+* AdjoinRoot (originalMappedPolynomial k C d p) :=
  (originalWholeMonicOpening k C d p).toRingHom.comp
    (Algebra.TensorProduct.includeRight : AdjoinRoot p →ₐ[k] C ⊗[k] AdjoinRoot p).toRingHom

theorem originalWholeMonicOpening_mk (p f : (S k d)[X]) :
    originalWholeMonicOpening k C d p ((1 : C) ⊗ₜ[k] AdjoinRoot.mk p f) =
      AdjoinRoot.mk (originalMappedPolynomial k C d p) (f.map (ordinaryScalar k C d)) := by
  let F := (fromOldRoot k C d p).comp (AdjoinRoot.mk p)
  let G := (AdjoinRoot.mk (originalMappedPolynomial k C d p)).comp
    (Polynomial.mapRingHom (ordinaryScalar k C d))
  have h : F = G := by
    apply Polynomial.ringHom_ext
    · intro r
      change fromOldRoot k C d p (AdjoinRoot.of p r) =
        AdjoinRoot.mk (originalMappedPolynomial k C d p)
          ((Polynomial.C r).map (ordinaryScalar k C d))
      rw [Polynomial.map_C]
      exact originalWholeMonicOpening_base k C d p r
    · change fromOldRoot k C d p (AdjoinRoot.root p) =
        AdjoinRoot.mk (originalMappedPolynomial k C d p) (Polynomial.X.map (ordinaryScalar k C d))
      rw [Polynomial.map_X]
      exact originalWholeMonicOpening_root k C d p
  exact DFunLike.congr_fun h f

/-- The already proved derivative unit survives in the exact
same root quotient and at the exact base-coordinate comparison. -/
theorem actual_mapped_derivative_unit (p : (S k d)[X])
    (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    IsUnit (AdjoinRoot.mk (originalMappedPolynomial k C d p)
      (originalMappedPolynomial k C d p).derivative) := by
  have h := hd.map (fromOldRoot k C d p)
  change IsUnit (originalWholeMonicOpening k C d p ((1 : C) ⊗ₜ[k] AdjoinRoot.mk p p.derivative)) at h
  rw [originalWholeMonicOpening_mk] at h
  simpa only [originalMappedPolynomial, Polynomial.derivative_map] using h

end SelectedActualComplexOriginalWholeMonicOpening318

#print axioms SelectedActualComplexOriginalWholeMonicOpening318.originalWholeMonicOpening_root
#print axioms SelectedActualComplexOriginalWholeMonicOpening318.originalWholeMonicOpening_mk
#print axioms SelectedActualComplexOriginalWholeMonicOpening318.actual_mapped_derivative_unit
