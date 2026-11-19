module
public import DyadicUnitRatioCover318
public import FourRootOrder318
public import UnitRootScaling318
public section
noncomputable section
namespace DyadicFourRatioMarkedOrder318
open scoped TensorProduct
open DyadicUnitRatioCover318
variable {R : Type*} [CommRing R] (c : Fin 4 → R)
abbrev P01 := Cover (c 0) ⊗[R] Cover (c 1)
abbrev P23 := Cover (c 2) ⊗[R] Cover (c 3)
abbrev Joint := P01 c ⊗[R] P23 c

theorem finite_free : Module.Finite R (Joint c) ∧ Module.Free R (Joint c) := by
  letI (i : Fin 4) : Module.Finite R (Cover (c i)) := finite _
  letI (i : Fin 4) : Module.Free R (Cover (c i)) := free _
  exact ⟨inferInstance,inferInstance⟩

theorem rank_sixteen [Nontrivial R] : Module.finrank R (Joint c)=16 := by
  letI (i : Fin 4) : Module.Free R (Cover (c i)) := free _
  simp only [Joint,P01,P23,Module.finrank_tensorProduct,rank_two]

theorem faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Joint c) := by
  letI : Module.Free R (Joint c) := (finite_free c).2
  letI : Nontrivial (Joint c) := Module.nontrivial_of_finrank_pos (R:=R) (by rw [rank_sixteen]; decide)
  infer_instance

theorem etale (hu : ∀ i, IsUnit (1+4*c i)) : Algebra.Etale R (Joint c) := by
  letI (i : Fin 4) : Algebra.Etale R (Cover (c i)) := DyadicUnitRatioCover318.etale _ (hu i)
  letI : Algebra.Etale R (P01 c) := Algebra.Etale.comp R (Cover (c 0)) (P01 c)
  letI : Algebra.Etale R (P23 c) := Algebra.Etale.comp R (Cover (c 2)) (P23 c)
  exact Algebra.Etale.comp R (P01 c) (Joint c)

@[expose] def left : P01 c →ₐ[R] Joint c := Algebra.TensorProduct.includeLeft
@[expose] def right : P23 c →ₐ[R] Joint c := Algebra.TensorProduct.includeRight
@[expose] def factor : (i : Fin 4) → Cover (c i) →ₐ[R] Joint c :=
  Fin.cases ((left c).comp Algebra.TensorProduct.includeLeft)
    (Fin.cases ((left c).comp Algebra.TensorProduct.includeRight)
      (Fin.cases ((right c).comp Algebra.TensorProduct.includeLeft)
        (Fin.cases ((right c).comp Algebra.TensorProduct.includeRight) (fun i=>Fin.elim0 i))))

@[expose] def scale (i : Fin 4) : Joint c := factor c i (multiplier (c i))
theorem scale_square (i : Fin 4) : scale c i ^ 2 = algebraMap R (Joint c) (1+4*c i) := by
  rw [scale,←map_pow,multiplier_square,AlgHom.commutes]

theorem scale_unit (hu : ∀ i, IsUnit (1+4*c i)) (i : Fin 4) : IsUnit (scale c i) :=
  (multiplier_isUnit _ (hu i)).map (factor c i).toRingHom

/-- After the explicitly constructed common rank-sixteen cover, the two actual
marked four-quadratic orders are isomorphic, including at nonunit contacts.
The base-ring parameters are untouched. This need not identify raw orders
before a nonunit square scaling, and does not yet identify integral closures. -/
@[expose] def markedOrderEquiv (hu : ∀ i, IsUnit (1+4*c i)) (a b : Fin 4 → R)
    (hab : ∀ i, a i = b i * (1+4*c i)) :
    Joint c ⊗[R] FourRootOrder318.Order a ≃ₐ[Joint c] Joint c ⊗[R] FourRootOrder318.Order b := by
  let f := algebraMap R (Joint c)
  let e (i : Fin 4) := UnitRootScaling318.equiv (f (a i)) (f (b i)) (scale_unit c hu i).unit (by
    rw [(scale_unit c hu i).unit_spec,scale_square,hab i,map_mul])
  exact (FourRootOrder318.baseChange a (Joint c)).trans
    ((Algebra.TensorProduct.congr (Algebra.TensorProduct.congr (e 0) (e 1))
      (Algebra.TensorProduct.congr (e 2) (e 3))).trans (FourRootOrder318.baseChange b (Joint c)).symm)

end DyadicFourRatioMarkedOrder318
