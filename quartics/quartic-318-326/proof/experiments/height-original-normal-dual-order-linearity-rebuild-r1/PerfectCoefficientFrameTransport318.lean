module
public import CoefficientPairingTrace318
public section
noncomputable section
namespace PerfectCoefficientFrameTransport318
open TensorCoefficientDuality318 CoefficientPairingTrace318
variable {F A B ι : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι] [DecidableEq ι]
  (G : Frame F A ι) (e : A ≃ₐ[F] B)

/-- Transport the actual perfect coefficient pairing through a literal
algebra equivalence, retaining its basis and coefficient functional. -/
@[expose] def frame : Frame F B ι where
  basis := G.basis.map e.toLinearEquiv
  switch := G.switch
  involutive := G.involutive
  coefficient := G.coefficient.comp e.symm.toLinearMap
  pairing i j := by
    change G.coefficient (e.symm (e (G.basis i)*e (G.basis j)))=_
    rw [←map_mul,e.symm_apply_apply]
    exact G.pairing i j

lemma basis (i : ι) : (frame G e).basis i=e (G.basis i) := rfl
lemma coefficient (x : A) : (frame G e).coefficient (e x)=G.coefficient x := by
  change G.coefficient (e.symm (e x))=_
  rw [e.symm_apply_apply]
lemma euler : CoefficientPairingTrace318.euler (frame G e)=e (CoefficientPairingTrace318.euler G) := by
  change (∑ i,e (G.basis i)*e (G.basis (G.switch i)))=e (∑ i,G.basis i*G.basis (G.switch i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_mul e _ _).symm
end PerfectCoefficientFrameTransport318
