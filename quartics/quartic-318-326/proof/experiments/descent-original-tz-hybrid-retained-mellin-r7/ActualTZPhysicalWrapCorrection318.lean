module
public import ActualTZLiteralPhysicalWrapCarrier318
public import ActualTZActualCollisionAverage318
import all ActualTZPhysicalCorrectionBound318
import all ActualTZMultiLinearCRT318
import all ActualTZCollisionPrimePartition318
import all ActualTZLiteralPhysicalWrapCarrier318
public section
noncomputable section
namespace ActualTZPhysicalWrapCorrection318
open scoped BigOperators
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZLiteralPhysicalWrapCarrier318.Context
open ActualTZLiteralOffsetMajorants318 ActualTZPhysicalPairMarkerKey318
open ActualTZPhysicalCorrectionBound318 ActualTZPhysicalEulerSplit318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
open ActualTZJointPolynomialForms318 ActualTZRelabelPhysicalGrid318
attribute [local instance] Classical.propDecidable

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable {S : Terminal m a b} (X : Context S I)

theorem exact_hit (p : ℕ) (z : X.OldGrid) (r : X.Keys) :
    ActualTZPhysicalCorrectionBound318.hit (primorial X.y) p (X.wrapped z r) X.base ↔
      X.collision p z r := by
  exact (X.collision_iff p z r).symm

theorem fixed_key (D₀ : ℕ) (hy : 1≤X.y) (A T B : ℤ) (hB : 0≤B)
    (Bnd : Bounds S A T) (hT : T≤A) (hA : A≤B*(primorial X.y:ℤ)^D₀) :
    ∃ K : ℕ,0<K ∧ Real.log K≤
      (Fintype.card (Pair I):ℝ)*
        (Real.log (max (1:ℝ) (16*(cap m a:ℝ)*(B:ℝ)))+((D₀+1:ℕ):ℝ)*Real.log 4)*(X.y:ℝ) ∧
      ∀ p,¬p∣K→∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0 := by
  obtain ⟨K,hK,hlog,H⟩ := key_exists S X.y D₀ hy X.good
    (fun q : Pair I=>X.node q.val.1) (fun q : Pair I=>X.node q.val.2)
    (fun q h=>q.property (X.distinct h)) A T B hB Bnd hT hA
  refine ⟨K,hK,hlog,?_⟩
  intro p hp r q
  exact H p hp q X.n
    (ActualTZCanonicalWrapFibres318.decode X.C r q.val.1)
    (ActualTZCanonicalWrapFibres318.decode X.C r q.val.2)

/-- The actual canonical retained-cell arithmetic now feeds the
weighted Euler correction directly. K is fixed before primes and
wraps, with its quantitative size supplied by fixed_key. -/
theorem correction_average (P K : ℕ)
    (hK : ∀ p,¬p∣K→∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0)
    (σ : ℝ) (hσ : 0<σ) (s t : I→ℂ) (hs : ∀ i,σ≤(s i).re) (ht : ∀ i,σ≤(t i).re) :
    let G := goodConst (Fintype.card I)*(∑ p∈offWheel (primorial X.y) P,(1/(p:ℝ))^2)+
      badConst (Fintype.card I)*extra (primorial X.y) P K
    let A := (Fintype.card X.Keys:ℝ)*(Fintype.card (Pair I):ℝ)*
      ((2:ℝ)^(D m a j)*(D m a j:ℝ)*(2:ℝ))
    (∑ z : X.OldGrid,(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)*
        (∑ r : X.Keys,X.theta z r*
          ‖corrected (primorial X.y) P (X.wrapped z r) X.base s t-1‖))≤
      (Real.exp G-1)+Real.exp G*(∑ p∈regular X.y X.N K,
        prefixWeight (badConst (Fintype.card I)) p*(A*(1/(p:ℝ)+1/(X.M:ℝ)))) := by
  intro G A
  have hW (p : ℕ) (hp : p.Prime) (hy : p≤X.y) : p∣primorial X.y :=
    hp.dvd_primorial_iff.2 hy
  have hY (p : ℕ) (hp : p∈regular X.y X.N K) : p.Prime ∧ ¬p∣K := by
    have H := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesBelow H.1,H.2.2⟩
  have hM0 : 0<(X.M:ℝ) := by exact_mod_cast X.Mpos
  apply ActualTZActualCollisionAverage318.corrected_average
    (primorial X.y) P X.y X.N K X.wrapped (fun _ _=>X.base)
    (fun _=>(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)) X.theta
    σ hσ s t hs ht hW (fun _=>by positivity) (fun z r=>(X.theta_bounds z r).1)
    X.mass_total_le (fun _ _ _ i=>(X.base_unit i).2.2)
    (fun z r hz p _ hh=>X.kept_horizon p z r hz ((exact_hit X p z r).1 hh))
    (X.M:ℝ) A hM0
  intro p hp
  have h := hY p hp
  letI : Fact p.Prime := ⟨h.1⟩
  letI : NeZero p := ⟨h.1.ne_zero⟩
  have H := X.sparse (p:=p) (hK p h.2)
  simpa only [exact_hit X p] using H

end ActualTZPhysicalWrapCorrection318
