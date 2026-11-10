module
public import PELOriginalLevelFiberEquivariance318
public section
noncomputable section
namespace PELOriginalPrimeBaseInvolutions318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELNormOneBaseAction318 PELJointNormOneAction318 PELEffectiveNormOneAction318
open PELUnlevelledComplexBase318 PELRealRationalProportionality318 PELPrimeNormalizerRelations318
set_option maxHeartbeats 1700000

theorem mobius_real_smul (M : RealMatrices) (r : ℝ) (hr : r≠0) (τ : ℂ) :
    mobius (r • M) τ=mobius M τ := by
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr
  have hn : ((r • M) 0 0:ℂ)*τ+((r • M) 0 1:ℂ)=
      (r:ℂ)*((M 0 0:ℂ)*τ+(M 0 1:ℂ)) := by
    simp only [Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
    ring
  have hd : denominator (r • M) τ=(r:ℂ)*denominator M τ := by
    simp only [denominator,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
    ring
  change (((r • M) 0 0:ℂ)*τ+((r • M) 0 1:ℂ))/denominator (r • M) τ= _
  rw [hn,hd]
  exact mul_div_mul_left _ _ hrC

theorem scalar_related_action (g h : positiveNormalizer) (q : ℚ) (hq : q≠0)
    (he : (g.val:B)=q • (h.val:B)) (x : UnlevelledBase) : coarseAction g x=coarseAction h x := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  rw [coarseAction_square,coarseAction_square]
  congr 1
  apply Subtype.ext
  change mobius (representation (g.val:B)) τ=mobius (representation (h.val:B)) τ
  rw [he,representation_rat_smul]
  exact mobius_real_smul _ q (by exact_mod_cast hq) τ

/-- Original norm-one units are killed on the unlevelled BASE, not on the
original polarized family or on arbitrary level markings. -/
theorem norm_one_trivial (u : normOneUnits) (x : UnlevelledBase) :
    coarseAction (originalNormalizer u) x=x := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  rw [coarseAction_square,normalizer_action]
  exact covering.map_smul (effectiveMap u)

@[expose] def originalPrime (i : Fin 4) : positiveNormalizer :=
  ⟨PELPrimeNormalizerData318.rationalUnit i,PELPositiveOrderNormalizer318.prime_mem i⟩
@[expose] def primeAction (i : Fin 4) : UnlevelledBase → UnlevelledBase := coarseAction (originalPrime i)

/-- Each actual prime normalizer becomes a genuine involution only AFTER
forgetting original norm-one units. Its square on the fine base was not
silently declared trivial. -/
theorem prime_involutive (i : Fin 4) : Function.Involutive (primeAction i) := by
  intro x
  let u : normOneUnits := ⟨squareUnit i,(mem_normOneUnits _).mpr (squareUnit_norm i)⟩
  change coarseAction (originalPrime i) (coarseAction (originalPrime i) x)=x
  rw [←coarseAction_mul]
  have he : (((originalPrime i*originalPrime i).val):B)=
      (PELPrimeNormalizerData318.prime i:ℚ) • ((originalNormalizer u).val:B) := by
    change PELPrimeNormalizerData318.element i*PELPrimeNormalizerData318.element i= _
    simpa only [pow_two] using square_relation i
  rw [scalar_related_action _ _ _ (PELPrimeNormalizerData318.prime_ne_zero i) he]
  exact norm_one_trivial u x

/-- All four original prime involutions commute on the SAME coarse base,
using every actual integral norm-one commutator from the original order. -/
theorem prime_commute (i j : Fin 4) (x : UnlevelledBase) :
    primeAction i (primeAction j x)=primeAction j (primeAction i x) := by
  let u : normOneUnits := ⟨commutatorUnit i j,(mem_normOneUnits _).mpr (commutatorUnit_norm i j)⟩
  have he : originalPrime i*originalPrime j=originalNormalizer u*(originalPrime j*originalPrime i) := by
    apply Subtype.ext
    apply Units.ext
    exact commutator_relation i j
  change coarseAction (originalPrime i) (coarseAction (originalPrime j) x)=
    coarseAction (originalPrime j) (coarseAction (originalPrime i) x)
  rw [←coarseAction_mul,he,coarseAction_mul,norm_one_trivial,coarseAction_mul]

open scoped Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

theorem prime_holomorphic (i : Fin 4) : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (primeAction i) :=
  coarseAction_holomorphic (originalPrime i)
end PELOriginalPrimeBaseInvolutions318
