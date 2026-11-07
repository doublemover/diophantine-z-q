module
public import EvenContactEtale318
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace FourUnitCover318
set_option maxHeartbeats 900000
open scoped TensorProduct
open EvenContactEtale318
variable {R:Type*} [CommRing R] (u:Fin 4→Rˣ)

abbrev Pair01:=RootRing (u 0)⊗[R]RootRing (u 1)
abbrev Pair23:=RootRing (u 2)⊗[R]RootRing (u 3)
abbrev Cover:=Pair01 u⊗[R]Pair23 u

@[expose] def generator : Fin 4→Cover u :=
  ![((root (u 0)⊗ₜ[R]1)⊗ₜ[R]1),((1⊗ₜ[R]root (u 1))⊗ₜ[R]1),
    (1⊗ₜ[R](root (u 2)⊗ₜ[R]1)),(1⊗ₜ[R](1⊗ₜ[R]root (u 3)))]

@[expose] def includeFactor (i:Fin 4) : RootRing (u i)→ₐ[R]Cover u := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (Algebra.TensorProduct.includeLeft : Pair01 u→ₐ[R]Cover u).comp
      (Algebra.TensorProduct.includeLeft : RootRing (u 0)→ₐ[R]Pair01 u)
  · refine Fin.cases ?_ (fun k=>?_) j
    · exact (Algebra.TensorProduct.includeLeft : Pair01 u→ₐ[R]Cover u).comp
        (Algebra.TensorProduct.includeRight : RootRing (u 1)→ₐ[R]Pair01 u)
    · refine Fin.cases ?_ (fun l=>?_) k
      · exact (Algebra.TensorProduct.includeRight : Pair23 u→ₐ[R]Cover u).comp
          (Algebra.TensorProduct.includeLeft : RootRing (u 2)→ₐ[R]Pair23 u)
      · refine Fin.cases ?_ (fun t=>Fin.elim0 t) l
        exact (Algebra.TensorProduct.includeRight : Pair23 u→ₐ[R]Cover u).comp
          (Algebra.TensorProduct.includeRight : RootRing (u 3)→ₐ[R]Pair23 u)

theorem generator_eq_include (i:Fin 4) : generator u i=includeFactor u i (root (u i)) := by
  fin_cases i <;> rfl

theorem generator_square (i:Fin 4) :
    generator u i^2=algebraMap R (Cover u) (u i:R) := by
  rw [generator_eq_include,←map_pow,root_square,AlgHom.commutes]

/-- Genuine finite/free etale rank-sixteen algebra; split factors are allowed. -/
theorem finite_free_etale (h2:IsUnit (2:R)) :
    Module.Finite R (Cover u) ∧ Module.Free R (Cover u) ∧ Algebra.Etale R (Cover u) := by
  letI (i:Fin 4):Module.Finite R (RootRing (u i)):=rootRing_finite _
  letI (i:Fin 4):Module.Free R (RootRing (u i)):=rootRing_free _
  letI (i:Fin 4):Algebra.Etale R (RootRing (u i)):=rootRing_etale _ h2
  letI:Algebra.Etale R (Pair01 u):=Algebra.Etale.comp R (RootRing (u 0)) (Pair01 u)
  letI:Algebra.Etale R (Pair23 u):=Algebra.Etale.comp R (RootRing (u 2)) (Pair23 u)
  letI:Algebra.Etale R (Cover u):=Algebra.Etale.comp R (Pair01 u) (Cover u)
  exact ⟨inferInstance,inferInstance,inferInstance⟩

theorem rank_sixteen [Nontrivial R] : Module.finrank R (Cover u)=16 := by
  letI (i:Fin 4):Module.Free R (RootRing (u i)):=rootRing_free _
  simp only [Cover,Pair01,Pair23,Module.finrank_tensorProduct,rootRing_rank_two]

/-- The tensor construction is actually a covering algebra, not an empty
finite etale algebra. -/
theorem faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Cover u) := by
  letI (i:Fin 4):Module.FaithfullyFlat R (RootRing (u i)):=rootRing_faithfullyFlat _
  letI:Module.FaithfullyFlat R (Pair01 u):=
    Module.FaithfullyFlat.trans R (RootRing (u 0)) (Pair01 u)
  letI:Module.FaithfullyFlat R (Pair23 u):=
    Module.FaithfullyFlat.trans R (RootRing (u 2)) (Pair23 u)
  exact Module.FaithfullyFlat.trans R (Pair01 u) (Cover u)

variable {T:Type*} [CommRing T] [Algebra R T]

@[expose] def liftFour (f:∀i:Fin 4,RootRing (u i)→ₐ[R]T) : Cover u→ₐ[R]T :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (f 0) (f 1) (fun _ _=>Commute.all _ _))
    (Algebra.TensorProduct.lift (f 2) (f 3) (fun _ _=>Commute.all _ _))
    (fun _ _=>Commute.all _ _)

theorem liftFour_generator (f:∀i:Fin 4,RootRing (u i)→ₐ[R]T) (i:Fin 4) :
    liftFour u f (generator u i)=f i (root (u i)) := by
  fin_cases i <;> simp [liftFour,generator,Algebra.TensorProduct.lift_tmul]

@[expose] def rootLift (y:Fin 4→T) (hy:∀i,y i^2=algebraMap R T (u i:R))
    (i:Fin 4) : RootRing (u i)→ₐ[R]T :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R T) (y i) (by
    change Polynomial.aeval (y i) (polynomial (u i))=0
    simp only [polynomial,map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
    exact sub_eq_zero.mpr (hy i))

theorem rootLift_root (y:Fin 4→T) (hy:∀i,y i^2=algebraMap R T (u i:R)) (i:Fin 4) :
    rootLift u y hy i (root (u i))=y i := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem roots_lift (y:Fin 4→T) (hy:∀i,y i^2=algebraMap R T (u i:R)) :
    ∃f:Cover u→ₐ[R]T,∀i,f (generator u i)=y i := by
  refine ⟨liftFour u (rootLift u y hy),?_⟩
  intro i
  rw [liftFour_generator,rootLift_root]

/-- The four actual generators determine every algebra map from the cover. -/
theorem hom_ext (f g:Cover u→ₐ[R]T)
    (h:∀i:Fin 4,f (generator u i)=g (generator u i)) : f=g := by
  apply Algebra.TensorProduct.ext
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 0
    · apply AdjoinRoot.algHom_ext
      exact h 1
  · apply Algebra.TensorProduct.ext
    · apply AdjoinRoot.algHom_ext
      exact h 2
    · apply AdjoinRoot.algHom_ext
      exact h 3

theorem roots_unique_lift (y:Fin 4→T) (hy:∀i,y i^2=algebraMap R T (u i:R)) :
    ∃!f:Cover u→ₐ[R]T,∀i,f (generator u i)=y i := by
  obtain ⟨f,hf⟩:=roots_lift u y hy
  exact ⟨f,hf,fun g hg=>hom_ext u g f (fun i=>(hg i).trans (hf i).symm)⟩

end FourUnitCover318
