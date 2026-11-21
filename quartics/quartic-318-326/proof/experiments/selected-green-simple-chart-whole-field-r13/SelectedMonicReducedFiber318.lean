module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Algebra.Polynomial.Derivative
public section
noncomputable section
open Polynomial
open scoped TensorProduct

namespace SelectedMonicReducedFiber318

/-- A repeated root in a field gives a concrete nonzero nilpotent in the
actual root quotient. This uses no enumeration of the roots or Galois orbit. -/
theorem simple_at_root {F : Type*} [Field F] (P : F[X]) (hP : P.Monic)
    [IsReduced (AdjoinRoot P)] (a : F) (ha : P.IsRoot a) :
    P.derivative.eval a ≠ 0 := by
  intro hder
  obtain ⟨g,hg⟩ := dvd_iff_isRoot.mpr ha
  have hg0 : g ≠ 0 := by
    intro hz
    exact hP.ne_zero (by simp [hg,hz])
  have hga : g.IsRoot a := by
    rw [hg,derivative_mul,derivative_X_sub_C,one_mul,eval_add,eval_mul,eval_sub,
      eval_X,eval_C,sub_self,zero_mul,add_zero] at hder
    exact hder
  obtain ⟨h,hh⟩ := dvd_iff_isRoot.mpr hga
  have hn : (AdjoinRoot.mk P g)^2 = 0 := by
    rw [← map_pow,AdjoinRoot.mk_eq_zero]
    refine ⟨h,?_⟩
    calc
      g^2 = g*g := pow_two g
      _ = g*((X-C a)*h) := congrArg (g * ·) hh
      _ = ((X-C a)*g)*h := by ring
      _ = P*h := by rw [← hg]
  have hz : AdjoinRoot.mk P g = 0 := IsReduced.eq_zero _ ⟨2,hn⟩
  have hle := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp hz) hg0
  have hdeg : P.natDegree = 1 + g.natDegree := by
    rw [hg,natDegree_mul (X_sub_C_ne_zero _) hg0,natDegree_X_sub_C]
  omega

section BaseChange

variable {R C B : Type*} [CommRing R] [CommRing C] [CommRing B]
variable [Algebra R C] [Algebra R B]

/-- Base change of the actual polynomial root algebra. Stating this
comparison separately avoids definitional equality across tensor unitors. -/
def mappedRootEquiv (F : Type*) [CommRing F] [Algebra R F] (p : R[X]) :
    F ⊗[R] AdjoinRoot p ≃ₐ[F] AdjoinRoot (p.map (algebraMap R F)) := by
  let j : R →ₐ[R] F ⊗[R] R := Algebra.TensorProduct.includeRight
  let u : F ⊗[R] R ≃ₐ[F] F := Algebra.TensorProduct.rid R F F
  let q := p.map j.toRingHom
  let uRing : (F ⊗[R] R) →+* F := RingHomClass.toRingHom u
  have hf : uRing.comp j.toRingHom = algebraMap R F := by
    ext r
    change u (1 ⊗ₜ[R] r) = algebraMap R F r
    simp only [u,Algebra.TensorProduct.rid_tmul,Algebra.smul_def,mul_one]
  have hq : q.map uRing = p.map (algebraMap R F) := by
    change (p.map j.toRingHom).map uRing = _
    rw [Polynomial.map_map,hf]
  exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
    (AdjoinRoot.mapAlgEquiv u q _ (by
      change Associated (q.map uRing) (p.map (algebraMap R F))
      rw [hq] <;> exact Associated.refl _))

/-- A split R-linear inclusion into an actual étale R algebra becomes an
injection into a reduced algebra over any residue field. The base change
of a retract is legitimate even when that field is not flat over R. -/
theorem tensor_injective_of_retract (F : Type*) [CommRing F] [Algebra R F]
    (j : C →ₐ[R] B) (L : B →ₗ[R] C) (hL : L.comp j.toLinearMap = LinearMap.id) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id F F) j) := by
  let φ : F ⊗[R] C →ₐ[F] F ⊗[R] B := Algebra.TensorProduct.map (AlgHom.id F F) j
  have hφ : φ.toLinearMap = j.toLinearMap.baseChange F := by
    ext a b
    simp [φ,LinearMap.baseChange_tmul]
  have hsplit : (L.baseChange F).comp φ.toLinearMap = LinearMap.id := by
    rw [hφ,← LinearMap.baseChange_comp,hL,LinearMap.baseChange_id]
  exact Function.LeftInverse.injective (fun z => DFunLike.congr_fun hsplit z)

/-- The derivative of the actual monic root presentation is a unit if
the coordinate algebra is a split summand of an étale algebra, without
postulating that it is itself étale or that a geometric fiber is split. -/
theorem derivative_unit [Algebra.Etale R B] (j : C →ₐ[R] B) (L : B →ₗ[R] C)
    (hL : L.comp j.toLinearMap = LinearMap.id)
    (p : R[X]) (hp : p.Monic) (e : AdjoinRoot p ≃ₐ[R] C) :
    IsUnit (aeval (e (AdjoinRoot.root p)) p.derivative) := by
  let x := e (AdjoinRoot.root p)
  let d := aeval x p.derivative
  change IsUnit d
  by_contra hdu
  have hI : Ideal.span {d} ≠ ⊤ := by
    intro h
    exact hdu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal (Ideal.span {d}) hI
  letI : m.IsMaximal := hm
  let F := C ⧸ m
  letI : Field F := Ideal.Quotient.field m
  let g : C →ₐ[R] F := Ideal.Quotient.mkₐ R m
  let a := g x
  let P := p.map (algebraMap R F)
  have hd : g d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (hle (Ideal.subset_span (by simp)))
  have hroot : aeval x p = 0 := by
    change aeval (e (AdjoinRoot.root p)) p = 0
    rw [Polynomial.aeval_algHom_apply e,AdjoinRoot.aeval_eq,AdjoinRoot.mk_self,map_zero]
  have hmap (s : R[X]) : (s.map (algebraMap R F)).eval a = g (aeval x s) := by
    rw [Polynomial.eval_map]
    exact Polynomial.aeval_algHom_apply g x s
  have hPr : P.IsRoot a := by
    change (p.map (algebraMap R F)).eval a = 0
    rw [hmap,hroot,map_zero]
  have hPd : P.derivative.eval a = 0 := by
    change (p.map (algebraMap R F)).derivative.eval a = 0
    rw [Polynomial.derivative_map,hmap]
    exact hd
  let E : F ⊗[R] C ≃ₐ[F] AdjoinRoot P :=
    (Algebra.TensorProduct.congr (.refl : F ≃ₐ[F] F) e.symm).trans (mappedRootEquiv F p)
  let f : F ⊗[R] C →ₐ[F] F ⊗[R] B := Algebra.TensorProduct.map (AlgHom.id F F) j
  let l : AdjoinRoot P →ₐ[F] F ⊗[R] B := f.comp E.symm.toAlgHom
  letI : IsReduced (F ⊗[R] B) := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[R] B)
  have hinj : Function.Injective l :=
    (tensor_injective_of_retract F j L hL).comp E.symm.injective
  letI : IsReduced (AdjoinRoot P) := by
    constructor
    intro z hz
    obtain ⟨k,hk⟩ := hz
    apply hinj
    rw [map_zero]
    exact IsReduced.eq_zero _ ⟨k,by rw [← map_pow,hk,map_zero]⟩
  exact simple_at_root P (hp.map _) a hPr hPd

end BaseChange
end SelectedMonicReducedFiber318

#print axioms SelectedMonicReducedFiber318.simple_at_root
#print axioms SelectedMonicReducedFiber318.derivative_unit
