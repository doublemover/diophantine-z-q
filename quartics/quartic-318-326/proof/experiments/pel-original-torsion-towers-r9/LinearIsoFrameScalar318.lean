module
public import FrameScalarAlgebra318
public section
noncomputable section
namespace LinearIsoFrameScalar318
universe u v w
variable {R : Type u} [CommRing R] {P : Type v} {Q : Type w}
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  (F : P ≃ₗ[R] Q) (e : R ≃ₗ[R] P) (d : R ≃ₗ[R] Q)

/-- The unit of an ACTUAL isomorphism between two framed lines. -/
@[expose] def scalar : Rˣ := FrameScalarAlgebra318.scalar d (e.trans F)
lemma value : (scalar F e d).val=d.symm (F (e 1)) := rfl
lemma relation (x : R) : d ((scalar F e d).val*x)=F (e x) :=
  FrameScalarAlgebra318.relation d (e.trans F) x

lemma transported (f : R ≃ₗ[R] P) :
    FrameScalarAlgebra318.scalar (e.trans F) (f.trans F)=FrameScalarAlgebra318.scalar e f := by
  apply FrameScalarAlgebra318.unique
  intro x
  exact congrArg F (FrameScalarAlgebra318.relation e f x)

/-- Full frame-change equation. It retains BOTH original transition
units; no flat character or translation invariance is assumed. -/
lemma transition (f : R ≃ₗ[R] P) (g : R ≃ₗ[R] Q) :
    scalar F e d*FrameScalarAlgebra318.scalar e f=
      FrameScalarAlgebra318.scalar d g*scalar F f g := by
  rw [scalar,scalar,←transported F e f]
  exact (FrameScalarAlgebra318.comp d (e.trans F) (f.trans F)).trans
    (FrameScalarAlgebra318.comp d g (f.trans F)).symm
end LinearIsoFrameScalar318
