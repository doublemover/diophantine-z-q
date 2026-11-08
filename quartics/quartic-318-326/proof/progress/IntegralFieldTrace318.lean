module
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace IntegralFieldTrace318
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (A B K L:Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [Module.Finite A B] [FiniteDimensional K L]
/-- The actual generic field trace of an integral regular coefficient lies
in the original normal base ring. -/
lemma exists_value (x:B):∃a:A,algebraMap A K a=Algebra.trace K L (algebraMap B L x):=by
  apply IsIntegrallyClosed.algebraMap_eq_of_integral
  apply Algebra.isIntegral_trace
  exact (IsIntegral.of_finite A x).map (IsScalarTower.toAlgHom A B L)
@[expose] def value (x:B):A:=Classical.choose (exists_value A B K L x)
lemma value_embedding (x:B):algebraMap A K (value A B K L x)=
    Algebra.trace K L (algebraMap B L x):=Classical.choose_spec (exists_value A B K L x)
/-- A genuine A-linear regular trace, retaining the exact scalar towers. -/
@[expose] def trace:B→ₗ[A]A where
  toFun:=value A B K L
  map_add' x y:=by
    apply IsFractionRing.injective A K
    rw [value_embedding,map_add,map_add,map_add,value_embedding,value_embedding]
  map_smul' a x:=by
    apply IsFractionRing.injective A K
    rw [value_embedding]
    simp only [Algebra.smul_def,map_mul]
    rw [←IsScalarTower.algebraMap_apply A B L,IsScalarTower.algebraMap_apply A K L]
    simpa only [Algebra.smul_def,Algebra.algebraMap_self,RingHom.id_apply,value_embedding] using
      (Algebra.trace K L).map_smul (algebraMap A K a) (algebraMap B L x)
lemma trace_embedding (x:B):algebraMap A K (trace A B K L x)=
    Algebra.trace K L (algebraMap B L x):=value_embedding A B K L x
lemma trace_algebraMap (a:A):trace A B K L (algebraMap A B a)=Module.finrank K L • a:=by
  apply IsFractionRing.injective A K
  rw [trace_embedding,←IsScalarTower.algebraMap_apply A B L,
    IsScalarTower.algebraMap_apply A K L,Algebra.trace_algebraMap,map_nsmul]
lemma unique (n:B→ₗ[A]A)
    (hn:∀x,algebraMap A K (n x)=Algebra.trace K L (algebraMap B L x)):
    n=trace A B K L:=by
  ext x
  apply IsFractionRing.injective A K
  rw [hn,trace_embedding]
end IntegralFieldTrace318
