module
public import BasePreservingAffinePoints318
public section
noncomputable section
namespace MonogenicOriginalCoordinates318
open Polynomial
variable {R L : Type} [CommRing R] [CommRing L]
variable (g : R →+* L) (Q : Polynomial R) (e : AdjoinRoot Q ≃+* L)
variable (he : ∀a, e (AdjoinRoot.of Q a) = g a)

/-- Evaluation of every original quotient representative is exactly
its polynomial in the original primitive coordinate, with the original
base evaluation. All points of the whole original order are covered. -/
theorem evaluate_representative (P : Polynomial R) (v : R →+* ℂ)
    (f : BasePreservingAffinePoints318.Points g v) :
    f.val (e (AdjoinRoot.mk Q P)) =
      P.eval₂ v (f.val (e (AdjoinRoot.root Q))) := by
  let p := BasePreservingAffinePoints318.monogenicPointsEquiv g v Q e he f
  have hr : Q.eval₂ v (p.val (AdjoinRoot.root Q)) = 0 := by
    simpa only [Polynomial.eval_map] using AdjoinRootSpecializedPoints318.point_root Q v p
  have hh : AdjoinRoot.lift v (p.val (AdjoinRoot.root Q)) hr = p.val := by
    apply AdjoinRoot.ringHom_ext
    · exact (AdjoinRoot.lift_comp_of hr).trans p.property.symm
    · exact AdjoinRoot.lift_root hr
  change p.val (AdjoinRoot.mk Q P) = P.eval₂ v (p.val (AdjoinRoot.root Q))
  calc
    p.val (AdjoinRoot.mk Q P) =
        AdjoinRoot.lift v (p.val (AdjoinRoot.root Q)) hr (AdjoinRoot.mk Q P) :=
      congrArg (fun h : AdjoinRoot Q →+* ℂ => h (AdjoinRoot.mk Q P)) hh.symm
    _ = _ := AdjoinRoot.lift_mk hr P

/-- Every element of the ENTIRE original localized chart admits one
fixed polynomial expression valid at ALL its base-preserving complex
points, simultaneously over every base evaluation. The expression is
chosen in the actual quotient order, not just in its generic field. -/
theorem exists_expression (a : L) :
    ∃ P : Polynomial R, e (AdjoinRoot.mk Q P) = a ∧
      ∀ (v : R →+* ℂ) (f : BasePreservingAffinePoints318.Points g v),
        f.val a = P.eval₂ v (f.val (e (AdjoinRoot.root Q))) := by
  obtain ⟨P,hP⟩ := AdjoinRoot.mk_surjective (g := Q) (e.symm a)
  have hp : e (AdjoinRoot.mk Q P) = a := by rw [hP,e.apply_symm_apply]
  refine ⟨P,hp,?_⟩
  intro v f
  rw [←hp]
  exact evaluate_representative g Q e he P v f
end MonogenicOriginalCoordinates318
