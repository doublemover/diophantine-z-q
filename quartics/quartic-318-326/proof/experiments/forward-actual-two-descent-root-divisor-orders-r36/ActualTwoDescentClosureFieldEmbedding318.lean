module
public import ActualTwoDescentRealCohomologicalImage318
public section
noncomputable section
namespace ActualTwoDescentClosureFieldEmbedding318
set_option maxHeartbeats 16000000

variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L]

def closureMap (f : F →+* L) : AlgebraicClosure F →+* AlgebraicClosure L := by
  letI : Algebra F L := f.toAlgebra
  letI g : AlgebraicClosure F →ₐ[F] AlgebraicClosure L := IsAlgClosed.lift
  exact g.toRingHom

lemma actual_closure_map_base (f : F →+* L) (a : F) :
    closureMap f (algebraMap F (AlgebraicClosure F) a)=algebraMap L (AlgebraicClosure L) (f a) := by
  letI : Algebra F L := f.toAlgebra
  letI g : AlgebraicClosure F →ₐ[F] AlgebraicClosure L := IsAlgClosed.lift
  change g (algebraMap F (AlgebraicClosure F) a)=algebraMap L (AlgebraicClosure L) (f a)
  rw [g.commutes]
  exact IsScalarTower.algebraMap_apply F L (AlgebraicClosure L) a

/-- The SAME closure embedding used by the actual continuous absolute-Galois restriction map. -/
lemma actual_closure_map_galois (f : F →+* L) (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure F) :
    closureMap f ((Field.absoluteGaloisGroup.map f σ) x)=σ (closureMap f x) := by
  letI : Algebra F L := f.toAlgebra
  letI g : AlgebraicClosure F →ₐ[F] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure F) (AlgebraicClosure L) := g.toAlgebra
  change algebraMap (AlgebraicClosure F) (AlgebraicClosure L)
    (((σ.restrictScalars F).restrictNormal (AlgebraicClosure F)) x)=
      σ (algebraMap (AlgebraicClosure F) (AlgebraicClosure L) x)
  exact (σ.restrictScalars F).restrictNormal_commutes (AlgebraicClosure F) x

end ActualTwoDescentClosureFieldEmbedding318
