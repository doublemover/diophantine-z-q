module
public import VaryingWholeIdealDescent318
public import VaryingLocalFreeIdealGluing318
public section
noncomputable section
namespace VaryingLocalFreeIdealRecovery318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : Ideal (S ⊗[R] A)) (C : VaryingLocalFreeIdealCover318.Data R A ι S I)
local notation "x" => VaryingLocalFreeIdealGluing318.point R A ι S I C
/-- The new glued classifier recovers EVERY input whole ideal, not just
ideals already known to come from parameter points. The complete
coefficient-cover descent above discharges the remaining direction. -/
lemma ideal_classify : VaryingParameterPointIdeal318.ideal R A ι S x=I := by
  apply VaryingWholeIdealDescent318.ideal_eq R A S _ I C.coefficients
  intro i
  have hx : VaryingParameterPoint318.map R A ι S (C.coefficients.ring i)
      (C.coefficients.coefficient i) x=
      VaryingParameterPoint318.ofIdeal R A ι (C.coefficients.ring i)
        (VaryingLocalFreeIdealCover318.localIdeal R A ι S I C i) := by
    apply Subtype.ext
    exact VaryingLocalFreeIdealGluing318.into_classify R A ι S I C i
  have hi := congrArg (VaryingParameterPointIdeal318.ideal R A ι (C.coefficients.ring i)) hx
  rw [VaryingPointIdealNaturality318.ideal_map,VaryingClassifiedIdealRecovery318.ideal_ofIdeal] at hi
  exact hi
lemma cover_independent (C' : VaryingLocalFreeIdealCover318.Data R A ι S I) :
    VaryingLocalFreeIdealGluing318.point R A ι S I C=VaryingLocalFreeIdealGluing318.point R A ι S I C' := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι S
  rw [ideal_classify,ideal_classify]
end VaryingLocalFreeIdealRecovery318
