module
public import InfinityFiniteCompatibility318
public import TangentChordOverlap318
public section
noncomputable section
namespace InfinityAdditionFinite318
open InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma pair_pow (A B:R) (f:PairRing A B →ₐ[R] S) (a:PairRing A B) (n:ℕ) : f (a^n)=(f a)^n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      exact f.toRingHom.map_one
  | succ n ih => simp only [pow_succ,map_mul,ih]

/-- Exact homogeneous-coordinate certificate from an actual slope identity. -/
theorem mapped_coordinates (A B:R) (t:Bool) (f:PairRing A B →ₐ[R] S) (l:S)
    (hl:l*f (denominator A B t)=f (slopeNumerator A B t)) :
    (l^2-f (X1 A B)-f (X2 A B))*f (denominator A B t)^2=f (numeratorX A B t) ∧
    (l*(f (X1 A B)-(l^2-f (X1 A B)-f (X2 A B)))-f (Y1 A B))*f (denominator A B t)^3=
      f (numeratorY A B t) := by
  simp only [numeratorX,numeratorY,map_sub,pair_pow,map_mul,map_add,←hl]
  constructor <;> ring

@[expose] def chordLift (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B false (denominator A B false)))) :
    RelativeChordAlgebra318.ChordRing A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=φ.comp (pairMap A B false))
    (RelativeChordAlgebra318.gap A B) hd

@[simp] theorem chordLift_pair (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B false (denominator A B false)))) (a:PairRing A B) :
    chordLift A B φ hd (TangentChordOverlap318.chordPairMap A B a)=φ (pairMap A B false a) := by
  exact IsLocalization.Away.lift_eq (S:=RelativeChordAlgebra318.ChordRing A B) (g:=(φ.comp (pairMap A B false)).toRingHom) (RelativeChordAlgebra318.gap A B) hd a

@[simp] theorem chordLift_left (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B false (denominator A B false)))) (a:ShortAffineJacobian318.Ring A B) :
    chordLift A B φ hd (RelativeChordAlgebra318.left A B a)=
      φ (InfinityAdditionScheme318.leftInput A B false a) := chordLift_pair A B φ hd _
@[simp] theorem chordLift_right (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B false (denominator A B false)))) (a:ShortAffineJacobian318.Ring A B) :
    chordLift A B φ hd (RelativeChordAlgebra318.right A B a)=
      φ (InfinityAdditionScheme318.rightInput A B false a) := chordLift_pair A B φ hd _

open AlgebraicGeometry CategoryTheory in
/-- The chord infinity-output morphism agrees with the actual finite chord morphism
on their actual principal-open intersection, over arbitrary coefficient algebras. -/
theorem chord_agreement (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B false (denominator A B false)))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B false=
      Spec.map (CommRingCat.ofHom (chordLift A B φ hd).toRingHom) ≫
        RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B := by
  let f:=φ.comp (pairMap A B false)
  let g:=chordLift A B φ hd
  have hs:=congrArg g (RelativeChordAlgebra318.slope_identity A B)
  simp only [map_mul,map_sub,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
    RelativeChordAlgebra318.y1,RelativeChordAlgebra318.y2,g,chordLift_left,chordLift_right] at hs
  have hl : g (RelativeChordAlgebra318.slope A B)*f (denominator A B false)=f (slopeNumerator A B false) := by
    simpa only [f,AlgHom.comp_apply,denominator,slopeNumerator,Bool.false_eq_true,ite_false,
      map_sub,X1,X2,Y1,Y2,InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput] using hs
  obtain ⟨hx,hy⟩:=mapped_coordinates A B false f (g (RelativeChordAlgebra318.slope A B)) hl
  have hh:=InfinityFiniteCompatibility318.output_agreement A B false φ
    (g.comp (RelativeChordAlgebra318.chordMap A B)) hd
  have hx' : (g.comp (RelativeChordAlgebra318.chordMap A B)) (ShortAffineJacobian318.x A B)*
      φ (pairMap A B false (denominator A B false))^2=φ (pairMap A B false (numeratorX A B false)) := by
    simpa only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_x,RelativeChordAlgebra318.x3,
      map_sub,map_pow,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,g,chordLift_left,chordLift_right,
      InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput,AlgHom.comp_apply,f,X1,X2] using hx
  have hy' : (g.comp (RelativeChordAlgebra318.chordMap A B)) (ShortAffineJacobian318.y A B)*
      φ (pairMap A B false (denominator A B false))^3=φ (pairMap A B false (numeratorY A B false)) := by
    simpa only [AlgHom.comp_apply,RelativeChordAlgebra318.chordMap_y,RelativeChordAlgebra318.y3,
      RelativeChordAlgebra318.x3,map_sub,map_pow,map_mul,RelativeChordAlgebra318.x1,RelativeChordAlgebra318.x2,
      RelativeChordAlgebra318.y1,g,chordLift_left,chordLift_right,
      InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput,AlgHom.comp_apply,f,X1,X2,Y1] using hy
  specialize hh hx' hy'
  rw [hh]
  dsimp only [RelativeChordScheme318.addition,RelativeChordScheme318.chordOpen,ShortAffineScheme318.scheme]
  rw [←Category.assoc,←Spec.map_comp]
  rfl

@[expose] def tangentLift (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B true (denominator A B true)))) :
    TangentOpenAlgebra318.TangentRing A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=φ.comp (pairMap A B true))
    (TangentOpenAlgebra318.ordinateSum A B) hd

@[simp] theorem tangentLift_pair (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B true (denominator A B true)))) (a:PairRing A B) :
    tangentLift A B φ hd (TangentChordOverlap318.tangentPairMap A B a)=φ (pairMap A B true a) := by
  exact IsLocalization.Away.lift_eq (S:=TangentOpenAlgebra318.TangentRing A B) (g:=(φ.comp (pairMap A B true)).toRingHom) (TangentOpenAlgebra318.ordinateSum A B) hd a

@[simp] theorem tangentLift_left (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B true (denominator A B true)))) (a:ShortAffineJacobian318.Ring A B) :
    tangentLift A B φ hd (TangentOpenAlgebra318.left A B a)=
      φ (InfinityAdditionScheme318.leftInput A B true a) := tangentLift_pair A B φ hd _
@[simp] theorem tangentLift_right (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B true (denominator A B true)))) (a:ShortAffineJacobian318.Ring A B) :
    tangentLift A B φ hd (TangentOpenAlgebra318.right A B a)=
      φ (InfinityAdditionScheme318.rightInput A B true a) := tangentLift_pair A B φ hd _

open AlgebraicGeometry CategoryTheory in
/-- The complementary infinity-output morphism agrees with the actual finite tangent/secant morphism
on their actual principal-open intersection, over arbitrary coefficient algebras. -/
theorem tangent_agreement (A B:R) (φ:OutputRing A B true →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B true (denominator A B true)))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B true=
      Spec.map (CommRingCat.ofHom (tangentLift A B φ hd).toRingHom) ≫
        TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B := by
  let f:=φ.comp (pairMap A B true)
  let g:=tangentLift A B φ hd
  have hs:=congrArg g (TangentOpenAlgebra318.slope_sum A B)
  simp only [map_mul,map_sub,map_add,map_pow,AlgHom.commutes,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,
    TangentOpenAlgebra318.y1,TangentOpenAlgebra318.y2,g,tangentLift_left,tangentLift_right] at hs
  have hl : g (TangentOpenAlgebra318.slope A B)*f (denominator A B true)=f (slopeNumerator A B true) := by
    simpa only [f,AlgHom.comp_apply,denominator,slopeNumerator,ite_true,
      map_sub,map_add,map_mul,map_pow,pair_pow,coeffMap,Algebra.ofId_apply,AlgHom.commutes,X1,X2,Y1,Y2,InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput] using hs
  obtain ⟨hx,hy⟩:=mapped_coordinates A B true f (g (TangentOpenAlgebra318.slope A B)) hl
  have hh:=InfinityFiniteCompatibility318.output_agreement A B true φ
    (g.comp (TangentOpenAlgebra318.tangentMap A B)) hd
  have hx' : (g.comp (TangentOpenAlgebra318.tangentMap A B)) (ShortAffineJacobian318.x A B)*
      φ (pairMap A B true (denominator A B true))^2=φ (pairMap A B true (numeratorX A B true)) := by
    simpa only [AlgHom.comp_apply,TangentOpenAlgebra318.tangentMap_x,TangentOpenAlgebra318.x3,
      map_sub,map_pow,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,g,tangentLift_left,tangentLift_right,
      InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput,AlgHom.comp_apply,f,X1,X2] using hx
  have hy' : (g.comp (TangentOpenAlgebra318.tangentMap A B)) (ShortAffineJacobian318.y A B)*
      φ (pairMap A B true (denominator A B true))^3=φ (pairMap A B true (numeratorY A B true)) := by
    simpa only [AlgHom.comp_apply,TangentOpenAlgebra318.tangentMap_y,TangentOpenAlgebra318.y3,
      TangentOpenAlgebra318.x3,map_sub,map_pow,map_mul,TangentOpenAlgebra318.x1,TangentOpenAlgebra318.x2,
      TangentOpenAlgebra318.y1,g,tangentLift_left,tangentLift_right,
      InfinityAdditionScheme318.leftInput,InfinityAdditionScheme318.rightInput,AlgHom.comp_apply,f,X1,X2,Y1] using hy
  specialize hh hx' hy'
  rw [hh]
  dsimp only [TangentOpenScheme318.addition,TangentOpenScheme318.tangentOpen,ShortAffineScheme318.scheme]
  rw [←Category.assoc,←Spec.map_comp]
  rfl

end InfinityAdditionFinite318
