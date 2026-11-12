module
public import PELOriginalFlatPeriodSquare318
public import PELOriginalMovingKernelConnection318
public section
noncomputable section
namespace PELOriginalFlatSymplecticTransport318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalFlatPeriodKernel318 PELOriginalComplexifiedOrder318
open PELOriginalUnitFlatTransport318 PELOriginalFlatPeriodSquare318
open PELOriginalPeriodKernelConnection318

lemma oriented_right (G M N : Mat) : oriented (M*G) (N*G)=G.det*oriented M N := by
  simp [oriented,Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_two,div_eq_mul_inv]
  ring
lemma unitMatrixC_det (u : PELJointNormOneAction318.normOneUnits) : (unitMatrixC u.val).det=1 := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) u.property
  simpa [unitMatrixC,Matrix.det_fin_two] using h

/-- The same constant full integral-lattice automorphism preserves the
ENTIRE original complex symplectic form. -/
theorem symplectic_transport (u : PELJointNormOneAction318.normOneUnits) (p q : Ambient) :
    symplectic (transport u.val p) (transport u.val q)=symplectic p q := by
  rw [←oriented_split,split_transport,split_transport,oriented_right,unitMatrixC_det,one_mul,
    oriented_split]

/-- Actual both-inverse linear equivalence of the two whole kernel
submodules, not merely equality of their dimensions or closed points. -/
@[expose] def kernelEquiv (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    LinearMap.ker (periodMap (parameter u τ)) ≃ₗ[ℂ] LinearMap.ker (periodMap τ) where
  toFun p := ⟨transport u.val p,(kernel_transport u τ hτ p).mpr p.property⟩
  invFun q := ⟨(transport u.val).symm q,(kernel_transport u τ hτ _).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using q.property)⟩
  left_inv := by intro p;apply Subtype.ext;exact (transport u.val).symm_apply_apply p
  right_inv := by intro p;apply Subtype.ext;exact (transport u.val).apply_symm_apply p
  map_add' := by intros;apply Subtype.ext;exact map_add _ _ _
  map_smul' := by intros;apply Subtype.ext;exact map_smul _ _ _

/-- Actual constant transport commutes with the ordinary flat derivative,
which is essential for descent of the second-fundamental tensor. -/
lemma hasDerivAt_transport (u : PELJointNormOneAction318.normOneUnits)
    (s : ℂ → Ambient) (s' : Ambient) (τ : ℂ) (hs : HasDerivAt s s' τ) :
    HasDerivAt (fun z => transport u.val (s z)) (transport u.val s') τ :=
  (transport u.val).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hs
end PELOriginalFlatSymplecticTransport318
