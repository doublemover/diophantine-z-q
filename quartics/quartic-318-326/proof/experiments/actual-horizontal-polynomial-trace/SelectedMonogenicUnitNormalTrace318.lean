module
public import SelectedTraceDualNormalization318
public import Mathlib.RingTheory.AdjoinRoot
public section
noncomputable section

open Polynomial SelectedTraceDualNormalization318

namespace SelectedMonogenicUnitNormalTrace318

variable {R K F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Field F] [Algebra R K] [IsFractionRing R K]
variable [Algebra K F] [Algebra R F] [IsScalarTower R K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

/-- Applying the original derivative unit in the actual AdjoinRoot
order produces its literal inverse in R[x], not merely in F. -/
theorem normal_dual_of_derivative_unit {x : F}
    (hx : Algebra.adjoin K ({x}:Set F) = ⊤) (hint : IsIntegral R x)
    (p : R[X]) (hp : p.map (algebraMap R K) = minpoly K x)
    (hu : IsUnit (AdjoinRoot.mk p p.derivative)) :
    ∀ y ∈ complementary K (integralClosure R F), y∈integralClosure R F := by
  have hx0 : aeval x (p.map (algebraMap R K)) = 0 := by
    rw [hp]
    exact minpoly.aeval K x
  rw [aeval_map_algebraMap] at hx0
  let e : AdjoinRoot p →ₐ[R] F :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId R F) x hx0
  have he (g : R[X]) : e (AdjoinRoot.mk p g)=aeval x g :=
    AdjoinRoot.liftAlgHom_mk p (Algebra.ofId R F) x hx0 g
  let u : (AdjoinRoot p)ˣ := hu.unit
  have hu0 : (u : AdjoinRoot p) = AdjoinRoot.mk p p.derivative := hu.unit_spec
  let w : F := e (↑u⁻¹ : AdjoinRoot p)
  have hw : w ∈ Algebra.adjoin R ({x}:Set F) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    obtain ⟨g,hg⟩ := (AdjoinRoot.mk_surjective (g:=p)) (↑u⁻¹ : AdjoinRoot p)
    exact ⟨g,(he g).symm.trans (congrArg e hg)⟩
  have hd : e (u : AdjoinRoot p) = aeval x p.derivative :=
    (congrArg e hu0).trans (he p.derivative)
  have witness : aeval x p.derivative * w = ((1:ℕ):F) := calc
    aeval x p.derivative * w = e (u : AdjoinRoot p) * e (↑u⁻¹ : AdjoinRoot p) :=
      congrArg (fun a : F => a*w) hd.symm
    _ = e ((u : AdjoinRoot p) * (↑u⁻¹ : AdjoinRoot p)) := (map_mul e _ _).symm
    _ = ((1:ℕ):F) := by
      rw [Units.mul_inv,map_one,Nat.cast_one]
  intro y hy
  have h := (actual_normalization_clear hx hint p hp 1 hw witness y hy).2
  simpa only [Nat.cast_one,one_mul] using h

/-- The derivative unit from the literal original monogenic chart
persists under its actual coefficient map; it is not a hypothetical
local regularity statement. -/
theorem derivative_unit_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : A[X]) (hu : IsUnit (AdjoinRoot.mk p p.derivative)) :
    IsUnit (AdjoinRoot.mk (p.map f) (p.map f).derivative) := by
  have hmap (g : A[X]) :
      AdjoinRoot.map f p (p.map f) dvd_rfl (AdjoinRoot.mk p g) =
        AdjoinRoot.mk (p.map f) (g.map f) := by
    unfold AdjoinRoot.map
    rw [AdjoinRoot.lift_mk, ←Polynomial.eval₂_map,
      ←AdjoinRoot.algebraMap_eq, ←Polynomial.aeval_def, AdjoinRoot.aeval_eq]
  have h := hu.map (AdjoinRoot.map f p (p.map f) dvd_rfl)
  rwa [hmap, ←Polynomial.derivative_map] at h

end SelectedMonogenicUnitNormalTrace318

#print axioms SelectedMonogenicUnitNormalTrace318.normal_dual_of_derivative_unit
#print axioms SelectedMonogenicUnitNormalTrace318.derivative_unit_map
