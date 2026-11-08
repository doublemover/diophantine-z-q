module
public import FiniteAdditionGluing318
public import ChartNegation318
public section
noncomputable section
namespace FiniteAntiDiagonal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open RelativeChordAlgebra318 (PairRing leftPair rightPair)
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)
abbrev Curve:=ShortAffineJacobian318.Ring A B
local instance pairCommRing : CommRing (PairRing A B):=inferInstance
local instance pairAlgebra : Algebra R (PairRing A B):=inferInstance

/-- The actual anti-diagonal coordinate map, retaining arbitrary base rings. -/
@[expose] def pair : PairRing A B→ₐ[R]Curve A B:=
  Algebra.TensorProduct.lift (AlgHom.id R (Curve A B)) (ChartNegation318.affineNeg A B)
    (fun _ _=>Commute.all _ _)
@[simp] lemma pair_left (z:Curve A B) : pair A B (leftPair A B z)=z:=by
  simp only [pair,leftPair,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.lift_tmul,map_one,mul_one,AlgHom.id_apply]
@[simp] lemma pair_right (z:Curve A B) : pair A B (rightPair A B z)=
    ChartNegation318.affineNeg A B z:=by
  simp only [pair,rightPair,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul,map_one,one_mul,AlgHom.id_apply]

lemma gap_zero : pair A B (RelativeChordAlgebra318.gap A B)=0:=by
  simp [RelativeChordAlgebra318.gap]
lemma ordinateSum_zero : pair A B (TangentOpenAlgebra318.ordinateSum A B)=0:=by
  simp [TangentOpenAlgebra318.ordinateSum]
lemma denominator_zero (t:Bool) : pair A B (InfinityAdditionAlgebra318.denominator A B t)=0:=by
  cases t <;> simp [InfinityAdditionAlgebra318.denominator,
    InfinityAdditionAlgebra318.X1,InfinityAdditionAlgebra318.X2,
    InfinityAdditionAlgebra318.Y1,InfinityAdditionAlgebra318.Y2]

/-- These are precisely the pullbacks of the two existing infinity-output
addition chart denominators. -/
@[expose] def denominator (t:Bool) : Curve A B:=
  pair A B (InfinityAdditionAlgebra318.numeratorY A B t)
lemma denominator_formula (t:Bool) : denominator A B t=
    -(pair A B (InfinityAdditionAlgebra318.slopeNumerator A B t))^3:=by
  simp only [denominator,InfinityAdditionAlgebra318.numeratorY,
    InfinityAdditionAlgebra318.numeratorX,map_sub,map_mul,map_pow,map_add,
    denominator_zero,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
    mul_zero,zero_mul,sub_zero,zero_sub]
  ring

lemma denominator_false : denominator A B false=(2*ShortAffineJacobian318.y A B)^3:=by
  rw [denominator_formula]
  simp only [InfinityAdditionAlgebra318.slopeNumerator,Bool.false_eq_true,ite_false,
    InfinityAdditionAlgebra318.Y1,InfinityAdditionAlgebra318.Y2,map_sub,
    pair_left,pair_right,ChartNegation318.affineNeg_y]
  ring
lemma denominator_true : denominator A B true=
    -(3*ShortAffineJacobian318.x A B^2+algebraMap R (Curve A B) A)^3:=by
  rw [denominator_formula]
  simp only [InfinityAdditionAlgebra318.slopeNumerator,ite_true,
    InfinityAdditionAlgebra318.X1,InfinityAdditionAlgebra318.X2,map_add,map_mul,map_pow,
    pair_left,pair_right,ChartNegation318.affineNeg_x,
    InfinityAdditionAlgebra318.coeffMap,Algebra.ofId_apply,AlgHom.commutes]
  ring

lemma basic_cover (hD:IsUnit (-16*(4*A^3+27*B^2))) (p:PrimeSpectrum (Curve A B)) :
    p∈PrimeSpectrum.basicOpen (denominator A B false) ∨
      p∈PrimeSpectrum.basicOpen (denominator A B true):=by
  have h:=FinitePairCover318.basic_open_cover A B hD
    (PrimeSpectrum.comap (pair A B).toRingHom p)
  rcases h with h|h|h|h
  · change pair A B (RelativeChordAlgebra318.gap A B)∉p.asIdeal at h
    rw [gap_zero] at h
    exact False.elim (h p.asIdeal.zero_mem)
  · change pair A B (TangentOpenAlgebra318.ordinateSum A B)∉p.asIdeal at h
    rw [ordinateSum_zero] at h
    exact False.elim (h p.asIdeal.zero_mem)
  · exact Or.inl h
  · exact Or.inr h

lemma span_top (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Ideal.span (Set.range (denominator A B))=⊤:=by
  apply (PrimeSpectrum.iSup_basicOpen_eq_top_iff (f:=denominator A B)).mp
  apply top_unique
  intro p _
  rcases basic_cover A B hD p with h|h
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false,h⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true,h⟩
end FiniteAntiDiagonal318
