module
public import OriginalSameJExactEtaleDiagonalFactor318
public import OriginalSameJDiagonalEquationFibre318
public import OriginalCyclicDivisorFieldFibreCartier318

@[expose] public section
noncomputable section

open Algebra Polynomial
open scoped TensorProduct

namespace OriginalSameJMovingDiagonalCentre318
open OriginalSameJDiagonalEquationFibre318 (coordinateDifference raw raw_reads quotient quotient_reads)
open OriginalSameJExactEtaleDiagonalFactor318 (diagonalRead reads_both_legs discarded)
open OriginalCyclicDivisorFieldFibreCartier318 (fibreRead q L into locRead localized_kernel)
universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Algebra k[X] A] [IsScalarTower k k[X] A]

abbrev movingRead : (A⊗[k]A) →ₐ[k] A :=
  diagonalRead (D:=k) (A:=A)

abbrev x := coordinateDifference (k:=k) (A:=A)

theorem same_whole (a : A⊗[k]A) :
    diagonalRead (D:=k[X]) (A:=A) (raw a) = movingRead a := by
  have h :
      ((diagonalRead (D:=k[X]) (A:=A)).restrictScalars k).comp
        ((raw (k:=k) (A:=A)).restrictScalars k) = movingRead (k:=k) (A:=A) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    change diagonalRead (D:=k[X]) (A:=A) (raw (a⊗ₜ[k]b)) = movingRead (a⊗ₜ[k]b)
    rw [raw_reads, reads_both_legs]
    exact (reads_both_legs a b).symm
  exact AlgHom.congr_fun h a

theorem vanishes : movingRead (x (k:=k) (A:=A)) = 0 := by
  change movingRead (coordinateDifference (k:=k) (A:=A)) = 0
  rw [coordinateDifference,map_sub,reads_both_legs,reads_both_legs,mul_one,one_mul,sub_self]

abbrev overDifference :=
  fibreRead (movingRead (k:=k) (A:=A)).toRingHom (x (k:=k) (A:=A)) (vanishes (k:=k) (A:=A))

theorem exactly_factors :
    (diagonalRead (D:=k[X]) (A:=A)).toRingHom.comp (quotient (k:=k) (A:=A)).toRingHom =
      overDifference (k:=k) (A:=A) := by
  apply RingHom.ext
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  calc
    _ = diagonalRead (D:=k[X]) (A:=A)
      (quotient (Ideal.Quotient.mk (Ideal.span (Set.singleton (x (k:=k) (A:=A)))) p)) := rfl
    _ = diagonalRead (D:=k[X]) (A:=A) (raw p) :=
      congrArg (diagonalRead (D:=k[X]) (A:=A)) (quotient_reads (k:=k) (A:=A) p)
    _ = movingRead p := same_whole p
    _ = _ := rfl

variable [Algebra.EssFiniteType k[X] A] [Algebra.FormallyUnramified k[X] A]

theorem actual_diagonal_selection :
    ∃ δ : (A⊗[k]A) ⧸ Ideal.span (Set.singleton (x (k:=k) (A:=A))),
      δ*δ=δ ∧ RingHom.ker (overDifference (k:=k) (A:=A)) =
        Ideal.span (Set.singleton δ) := by
  obtain ⟨d,hd,he⟩ := discarded (D:=k[X]) (A:=A)
  let q' := quotient (k:=k) (A:=A)
  refine ⟨q'.symm d, ?_, ?_⟩
  · exact ((map_mul q'.symm d d).symm.trans (congrArg q'.symm hd))
  · rw [← exactly_factors,← RingHom.comap_ker,← Ideal.map_symm q',he,Ideal.map_span,
      Set.image_singleton]
    rfl

/-- A true localized ambient neighbourhood of the moving diagonal,
not a chosen fibre point: the target evaluation remains the entire
multiplication map into the same A. -/
theorem on_actual_diagonal :
    ∃ (δ : (A⊗[k]A) ⧸ Ideal.span (Set.singleton (x (k:=k) (A:=A))))
      (he : RingHom.ker (overDifference (k:=k) (A:=A)) = Ideal.span (Set.singleton δ)),
      RingHom.ker (locRead (movingRead (k:=k) (A:=A)).toRingHom
        (x (k:=k) (A:=A)) (vanishes (k:=k) (A:=A)) δ he) =
        Ideal.span (Set.singleton (into (x (k:=k) (A:=A)) δ (x (k:=k) (A:=A)))) := by
  obtain ⟨δ,hδ,he⟩ := actual_diagonal_selection (k:=k) (A:=A)
  exact ⟨δ,he,localized_kernel _ _ _ _ he hδ⟩

end OriginalSameJMovingDiagonalCentre318

#print axioms OriginalSameJMovingDiagonalCentre318.same_whole
#print axioms OriginalSameJMovingDiagonalCentre318.exactly_factors
#print axioms OriginalSameJMovingDiagonalCentre318.actual_diagonal_selection
#print axioms OriginalSameJMovingDiagonalCentre318.on_actual_diagonal
