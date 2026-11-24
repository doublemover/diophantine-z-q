module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic
public section
noncomputable section
namespace OriginalQuadraticDualizing318
open Polynomial Module
variable {R:Type*} [CommRing R] [Nontrivial R]
@[expose] def eqn (f:R) : R[X] := X^2-C f
abbrev Cover (f:R) := AdjoinRoot (eqn f)
abbrev y (f:R) : Cover f := AdjoinRoot.root (eqn f)
omit [Nontrivial R] in
theorem monic (f:R) : (eqn f).Monic := monic_X_pow_sub_C _ (by decide)
theorem deg (f:R) : (eqn f).natDegree=2 := natDegree_X_pow_sub_C
omit [Nontrivial R] in
theorem y_sq (f:R) : (y f)^2=algebraMap R (Cover f) f := by
  have e:=AdjoinRoot.eval₂_root (eqn f)
  change Polynomial.eval₂ (AdjoinRoot.of (eqn f)) (y f) (X^2-C f)=0 at e
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C] at e
  exact sub_eq_zero.mp e
@[expose] def basis (f:R) : Basis (Fin 2) R (Cover f) :=
  (AdjoinRoot.powerBasis' (monic f)).basis.reindex (finCongr ((AdjoinRoot.powerBasis'_dim _).trans (deg f)))
theorem basis_at (f:R) (i:Fin 2) : basis f i=(y f)^(i:ℕ) := by
  rw [basis,Basis.reindex_apply,PowerBasis.basis_eq_pow]
  rfl
@[simp] theorem b0 (f:R) : basis f 0=1 := by rw [basis_at]; exact pow_zero _
@[simp] theorem b1 (f:R) : basis f 1=y f := by rw [basis_at]; exact pow_one _
@[expose] def lambda (f:R) : Cover f→ₗ[R]R := (basis f).coord 1
theorem decompose (f:R) (a:Cover f) : ((basis f).repr a 0)•(1:Cover f)+lambda f a•y f=a := by
  have e:=(basis f).sum_repr a
  simpa only [Fin.sum_univ_two,b0,b1,lambda,Basis.coord_apply] using e
@[simp] theorem lambda_one (f:R) : lambda f 1=0 := by
  change (basis f).repr 1 1=0
  rw [←b0 f,Basis.repr_self,Finsupp.single_eq_of_ne (by decide)]
@[simp] theorem lambda_y (f:R) : lambda f (y f)=1 := by
  change (basis f).repr (y f) 1=1
  rw [←b1 f,Basis.repr_self,Finsupp.single_eq_same]
@[simp] theorem lambda_base (f a:R) : lambda f (algebraMap R (Cover f) a)=0 := by
  rw [Algebra.algebraMap_eq_smul_one,map_smul,lambda_one,smul_zero]
@[simp] theorem lambda_y_y (f:R) : lambda f (y f*y f)=0 := by rw [←pow_two,y_sq,lambda_base]

/-- Monogenic different/codifferent duality at both ramified and ordinary
points: lambda is the functional of the adjunction differential dx/(2y).
Its values on (1,y) are (0,1); it is not field trace divided by degree. -/
@[expose] def toDual (f:R) (a:Cover f) : Cover f→ₗ[R]R where
  toFun b := lambda f (a*b)
  map_add' b c := by rw [mul_add,map_add]
  map_smul' r b := by rw [mul_smul_comm,map_smul]; rfl

theorem dual_on_y (f:R) (a:Cover f) : toDual f a (y f)=(basis f).repr a 0 := by
  rw [toDual,LinearMap.coe_mk,AddHom.coe_mk]
  conv_lhs => arg 2; arg 1; rw [←decompose f a]
  simp only [add_mul,smul_mul_assoc,one_mul,map_add,map_smul,lambda_y,lambda_y_y,
    smul_eq_mul,mul_one,mul_zero,add_zero]

@[expose] def fromDual (f:R) (l:Cover f→ₗ[R]R) : Cover f := l (y f)•(1:Cover f)+l 1•y f
theorem dual_perfect (f:R) : Function.Bijective (toDual f) := by
  have i (a:Cover f) : fromDual f (toDual f a)=a := by
    rw [fromDual,dual_on_y]
    change _+lambda f (a*1)•y f=a
    rw [mul_one,decompose]
  have j (l:Cover f→ₗ[R]R) : toDual f (fromDual f l)=l := by
    apply (basis f).ext
    intro v
    fin_cases v
    · change toDual f (fromDual f l) (basis f 0)=l (basis f 0)
      rw [b0]
      change lambda f ((l (y f)•1+l 1•y f)*1)=l 1
      simp
    · change toDual f (fromDual f l) (basis f 1)=l (basis f 1)
      rw [b1]
      change lambda f ((l (y f)•1+l 1•y f)*y f)=l (y f)
      simp [add_mul]
  exact ⟨Function.LeftInverse.injective i,Function.RightInverse.surjective j⟩

/-- The finite dualizing pushforward evaluates its Hom functional at 1.
The pullback of h dx, in the frame dx/(2y), has coefficient 2yh;
its counit is the UNNORMALIZED rank-two trace, not h. -/
theorem push_pull (f h:R) : toDual f (h•(2*y f)) 1 = Algebra.trace R (Cover f) (algebraMap R (Cover f) h) := by
  rw [Algebra.trace_algebraMap_of_basis (basis f),Fintype.card_fin]
  change lambda f ((h•(2*y f))*1)=2 • h
  rw [mul_one,map_smul,two_mul,map_add,lambda_y]
  simp [mul_add,two_mul]

end OriginalQuadraticDualizing318
#print axioms OriginalQuadraticDualizing318.dual_perfect
#print axioms OriginalQuadraticDualizing318.push_pull
