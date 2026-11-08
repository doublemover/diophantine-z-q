module
public import ThreeArithmeticQuotient318
public section
noncomputable section
namespace ThreePrimitiveOrbit318
open ModularTorsionTransport318 ModularTorusTransport318 EllipticTorsion318
open PrimitiveTorsion318 MarkedPeriod318
open scoped MatrixGroups Matrix
set_option maxHeartbeats 0

/-- Explicit integral determinant-one matrices move every primitive
three-torsion period vector to the genuine standard vector (0,1). -/
theorem exists_matrix (x : ZMod 3 × ZMod 3) (hx : Primitive 3 x) :
    ∃g : SL(2,ℤ), residueMap g 3 x=standardLabel 3 := by
  obtain ⟨m,n⟩ := x
  fin_cases m <;> fin_cases n
  · exfalso
    exact (by unfold Primitive; decide : ¬Primitive 3 ((0:ZMod 3),0)) hx
  · refine ⟨1,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨-1,?_⟩
    norm_num [residueMap,standardLabel,Matrix.SpecialLinearGroup.coe_neg] <;> decide
  · refine ⟨⟨!![0,-1;1,0],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨⟨!![1,0;1,1],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨⟨!![-1,0;1,-1],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨⟨!![0,1;-1,0],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨⟨!![1,0;-1,1],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide
  · refine ⟨⟨!![-1,0;-1,-1],by norm_num [Matrix.det_fin_two]⟩,?_⟩
    norm_num [residueMap,standardLabel] <;> decide

/-- Every actual order-three elliptic point becomes the genuine standard
1/3-period point after an actual integral modular change of period. -/
theorem exists_point_transport (tau : UpperHalfPlane)
    (P : (ModularWeierstrass318.curve tau).toAffine.Point) (hP : addOrderOf P=3) :
    ∃g : SL(2,ℤ), pointAddEquiv g tau P=standardPoint 3 (g•tau) := by
  obtain ⟨x,hx⟩ := (primitiveEquiv tau 3).surjective ⟨P,hP⟩
  have he : torsionMap tau 3 x.val=P := congrArg Subtype.val hx
  obtain ⟨g,hg⟩ := exists_matrix x.val x.property
  refine ⟨g,?_⟩
  rw [←he,torsion_transport,hg]
  rfl

end ThreePrimitiveOrbit318
