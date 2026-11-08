module
public import ThreeTorsionSplitData318
public import Mathlib.RingTheory.FiniteType
public section
noncomputable section
namespace ThreeTorsionSplitEval318
open Polynomial ThreeTorsionAlgebra318 ThreeTorsionSplitData318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] [Nontrivial R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2)))
abbrev Index := Fin 4×Bool

@[expose] def signedY (i:Index) : T A B hD := if i.2 then -(ys A B hD i.1) else ys A B hD i.1
lemma signedY_square (i:Index) : (signedY A B hD i)^2=(xs A B hD i.1)^3+
    algebraMap R (T A B hD) A*xs A B hD i.1+algebraMap R (T A B hD) B := by
  rcases i with ⟨i,b⟩
  cases b
  · exact ys_square A B hD i
  · change (-(ys A B hD i))^2=_
    exact (neg_sq (ys A B hD i)).trans (ys_square A B hD i)

@[expose] def evaluate (i:Index) : Ring A B hD→ₐ[R]T A B hD :=
  ThreeTorsionFunctor318.toHom A B hD ⟨(xs A B hD i.1,signedY A B hD i),
    xs_relation A B hD i.1,signedY_square A B hD i⟩
@[simp] theorem evaluate_x (i:Index) : evaluate A B hD i (x A B hD)=xs A B hD i.1 :=
  ThreeTorsionFunctor318.toHom_x _ _ _ _
@[simp] theorem evaluate_y (i:Index) : evaluate A B hD i (y A B hD)=signedY A B hD i :=
  ThreeTorsionFunctor318.toHom_y _ _ _ _

@[expose] def evaluation : T A B hD⊗[R]Ring A B hD→ₐ[T A B hD](Index→T A B hD) :=
  AlgHom.liftEquiv R (T A B hD) _ _ (AlgHom.pi (evaluate A B hD))
theorem evaluation_tmul (s:T A B hD) (b:Ring A B hD) (i:Index) :
    evaluation A B hD (s⊗ₜ[R]b) i=s*evaluate A B hD i b := rfl

@[expose] def includeX : T A B hD⊗[R]XRing A B→ₐ[T A B hD]T A B hD⊗[R]Ring A B hD :=
  Algebra.TensorProduct.map (AlgHom.id _ _)
    (AdjoinRoot.ofAlgHom R (EvenContactEtale318.polynomial (cubicUnit A B hD)))

lemma evaluate_of_mk (f:R[X]) (i:Index) :
    evaluate A B hD i (algebraMap (XRing A B) (Ring A B hD)
      (AdjoinRoot.mk (ShortThreeTorsion318.polynomial A B) f))=
        f.eval₂ (algebraMap R (T A B hD)) (xs A B hD i.1) := by
  simp only [evaluate,ThreeTorsionFunctor318.toHom,AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of,ThreeTorsionFunctor318.xHom,AdjoinRoot.liftAlgHom_mk]
  rfl

lemma evaluation_includeX (z:T A B hD⊗[R]XRing A B) (i:Index) :
    evaluation A B hD (includeX A B hD z) i=xSplitEquiv A B hD z i.1 := by
  induction z using TensorProduct.inductionOn with
  | tmul s b =>
    obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective b
    rw [xSplitEquiv_tmul]
    change evaluation A B hD (s⊗ₜ[R](algebraMap (XRing A B) (Ring A B hD)
      (AdjoinRoot.mk (ShortThreeTorsion318.polynomial A B) f))) i=_
    rw [evaluation_tmul,evaluate_of_mk]
  | add z w hz hw => simp only [map_add,Pi.add_apply,hz,hw]

lemma evaluation_surjective : Function.Surjective (evaluation A B hD) := by
  intro f
  have h2:IsUnit (2:T A B hD):=by
    simpa only [map_ofNat] using (two_unit A B hD).map (algebraMap R (T A B hD))
  let u: (T A B hD)ˣ := h2.unit
  let v (i:Fin 4):(T A B hD)ˣ := (ys_unit A B hD i).unit
  have hu:(u:T A B hD)=2:=h2.unit_spec
  have hv (i:Fin 4):(v i:T A B hD)=ys A B hD i:=(ys_unit A B hD i).unit_spec
  let a:Fin 4→T A B hD:=fun i=>(f (i,false)+f (i,true))*(↑u⁻¹:T A B hD)
  let b:Fin 4→T A B hD:=fun i=>(f (i,false)-f (i,true))*(↑u⁻¹:T A B hD)*(↑(v i)⁻¹:T A B hD)
  refine ⟨includeX A B hD ((xSplitEquiv A B hD).symm a)+
    includeX A B hD ((xSplitEquiv A B hD).symm b)*(1⊗ₜ[R]y A B hD),?_⟩
  funext i
  simp only [map_add,map_mul,Pi.add_apply,Pi.mul_apply,evaluation_includeX,
    AlgEquiv.apply_symm_apply,evaluation_tmul,evaluate_y,one_mul]
  rcases i with ⟨i,j⟩
  have hbr:b i*ys A B hD i=(f (i,false)-f (i,true))*(↑u⁻¹:T A B hD):=by
    rw [←hv]
    dsimp [b]
    rw [mul_assoc,Units.inv_mul,mul_one]
  have hi:(2:T A B hD)*(↑u⁻¹:T A B hD)=1:=by rw [←hu];exact Units.mul_inv u
  cases j
  · change a i+b i*ys A B hD i=f (i,false)
    rw [hbr]
    dsimp [a]
    linear_combination f (i,false)*hi
  · change a i+b i*(-(ys A B hD i))=f (i,true)
    have hn := mul_neg (b i) (ys A B hD i)
    rw [hn,hbr]
    dsimp [a]
    linear_combination f (i,true)*hi

lemma evaluation_bijective : Function.Bijective (evaluation A B hD) := by
  letI:=ThreeTorsionAlgebra318.free A B hD
  letI:=ThreeTorsionAlgebra318.finite A B hD
  apply OrzechProperty.bijective_of_surjective_of_finrank_le (evaluation A B hD).toLinearMap
    (evaluation_surjective A B hD)
  rw [Module.finrank_baseChange,ThreeTorsionAlgebra318.rank_eight]
  simp [Index]

/-- The constructed finite-etale faithfully-flat extension splits the actual
rank-eight algebra by evaluation at its four x-roots and both y signs. -/
@[expose] def splitEquiv : T A B hD⊗[R]Ring A B hD≃ₐ[T A B hD](Index→T A B hD) :=
  AlgEquiv.ofBijective (evaluation A B hD) (evaluation_bijective A B hD)

theorem splitEquiv_tmul (s:T A B hD) (b:Ring A B hD) (i:Index) :
    splitEquiv A B hD (s⊗ₜ[R]b) i=s*evaluate A B hD i b := rfl

end ThreeTorsionSplitEval318
