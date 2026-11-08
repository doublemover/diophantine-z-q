module
public import SourcePrimeValuationInertia318
public import Mathlib.NumberTheory.RamificationInertia.Galois
public section
noncomputable section
namespace SourceOrderGaloisAction318
open ContactKummerOrder318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
abbrev G:=SourceOrder c≃ₐ[R]SourceOrder c
local instance rawField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceAlgebra:Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction:IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
local instance baseAlgebra:Algebra R (L c):=
  ((algebraMap K (L c)).comp (algebraMap R K)).toAlgebra
local instance baseSMul:SMul R (L c):=(baseAlgebra c).toSMul
local instance baseModule:Module R (L c):=Algebra.toModule
local instance baseTower:IsScalarTower R K (L c):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=K) (A:=L c) (fun _=>rfl)
local instance sourceTower:IsScalarTower R (SourceOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=SourceOrder c) (A:=L c)
    (fun p=>(SourceFractionField318.embedding_on_polynomial c p).symm)
local instance sourceClosure:IsIntegralClosure (SourceOrder c) R (L c):=
  SourceClosureComparison318.source_isIntegralClosure c (SourceGlobalAffine318.source_integrallyClosed c)
local instance rawFinite:FiniteDimensional K (L c):=
  Module.finite_of_finrank_pos (by rw [KummerTensorField318.source_raw_degree c]; decide)
local instance actualGalois:IsGalois K (L c):=ActualKummerGalois318.source_raw_galois c
local instance sourceFinite:Module.Finite R (SourceOrder c):=(source_finite_free c).1
local instance sourceFree:Module.Free R (SourceOrder c):=(source_finite_free c).2

/-- The original polynomial-order automorphism group is finite, with its
literal action on the original order. -/
theorem group_finite:Finite (G c):=Finite.of_equiv (Fin 4→Bool) (SourceOrderAutomorphisms318.signEquiv c)

/-- Actual invariants of the entire source order are precisely Q[t]. -/
theorem invariant:Algebra.IsInvariant R (SourceOrder c) (G c):=
  Algebra.isInvariant_of_isGalois' R K (L c) (SourceOrder c)

/-- The actual full order automorphism action satisfies the ramification
theorem's Galois-group predicate; this does not mean the branched map is etale. -/
theorem galoisGroup:IsGaloisGroup (G c) R (SourceOrder c) where
  faithful:=inferInstance
  commutes:=inferInstance
  isInvariant:=invariant c

theorem finite_flat:Module.Finite R (SourceOrder c)∧Module.Flat R (SourceOrder c):=
  ⟨inferInstance,Module.Flat.of_free⟩
end SourceOrderGaloisAction318
