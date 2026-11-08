module
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace IntegralFieldNorm318
open scoped nonZeroDivisors
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (A B K L:Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [Module.Finite A B]
/-- The actual field norm of a regular integral coefficient lies in the
original normal base ring, not merely in an isomorphic copy of its field. -/
lemma exists_value (x:B):∃a:A,algebraMap A K a=Algebra.norm K (algebraMap B L x):=by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  apply Algebra.isIntegral_norm K
  exact (IsIntegral.of_finite A x).map (IsScalarTower.toAlgHom A B L)
@[expose] def value (x:B):A:=Classical.choose (exists_value A B K L x)
lemma value_embedding (x:B):algebraMap A K (value A B K L x)=
    Algebra.norm K (algebraMap B L x):=Classical.choose_spec (exists_value A B K L x)
/-- A genuine multiplicative norm on the entire regular coefficient ring.
No freeness or chosen basis of B over A is assumed. -/
@[expose] def norm:B→*A where
  toFun:=value A B K L
  map_one':=by
    apply IsFractionRing.injective A K
    rw [value_embedding,map_one,map_one,map_one]
  map_mul' x y:=by
    apply IsFractionRing.injective A K
    rw [value_embedding,map_mul,map_mul,map_mul,value_embedding,value_embedding]
lemma norm_embedding (x:B):algebraMap A K (norm A B K L x)=
    Algebra.norm K (algebraMap B L x):=value_embedding A B K L x
/-- Pullback followed by this regular norm is the actual generic-degree power. -/
lemma norm_algebraMap (a:A):norm A B K L (algebraMap A B a)=a^Module.finrank K L:=by
  apply IsFractionRing.injective A K
  rw [norm_embedding,←IsScalarTower.algebraMap_apply A B L,
    IsScalarTower.algebraMap_apply A K L,Algebra.norm_algebraMap,map_pow]
/-- Uniqueness makes this construction independent of every integral witness. -/
lemma unique (n:B→*A)
    (hn:∀x,algebraMap A K (n x)=Algebra.norm K (algebraMap B L x)):
    n=norm A B K L:=by
  ext x
  apply IsFractionRing.injective A K
  rw [hn,norm_embedding]
end IntegralFieldNorm318
