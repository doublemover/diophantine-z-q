module
public import ActualCasselsTateNativeContinuousBoundary318
public import ActualCasselsTateTopologicalCycleProjection318
public section
noncomputable section
namespace ActualCasselsTateNativeContinuousCycleClass318
open CategoryTheory TopRep ContRepresentation ActualCasselsTateNativeContinuousFaces318
open ActualCasselsTateNativeContinuousCoordinates318 ActualCasselsTateNativeContinuousBoundary318
open ActualCasselsTateTopologicalCycleProjection318
variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (X : TopRep k G)
variable (hact : Continuous (fun p : G × X => X.ρ p.1 p.2))
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
local notation "K" => homogeneousCochains X

private lemma diagonal_four (z : K.X 4) (s a b c d e : G) :
    z.val (s*a) (s*b) (s*c) (s*d) (s*e) = X.ρ s (z.val a b c d e) := by
  have h := congrArg (fun f : C(G,C(G,C(G,C(G,C(G,X))))) =>
    f (s*a) (s*b) (s*c) (s*d) (s*e)) (z.2 s)
  change X.ρ s (z.val (s⁻¹*(s*a)) (s⁻¹*(s*b)) (s⁻¹*(s*c)) (s⁻¹*(s*d)) (s⁻¹*(s*e))) = _ at h
  simpa only [inv_mul_cancel_left] using h.symm

private lemma eval_four_detects_zero (z : K.X 4)
    (hz : ∀ g h l m, evalFour X z g h l m = 0) : z = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext; intro a
  apply ContinuousMap.ext; intro b
  apply ContinuousMap.ext; intro c
  apply ContinuousMap.ext; intro d
  apply ContinuousMap.ext; intro e
  have ht := diagonal_four X z a 1 (a⁻¹*b) ((a⁻¹*b)*(b⁻¹*c))
    ((a⁻¹*b)*((b⁻¹*c)*(c⁻¹*d))) ((a⁻¹*b)*((b⁻¹*c)*((c⁻¹*d)*(d⁻¹*e))))
  have h2 : a*((a⁻¹*b)*(b⁻¹*c))=c := by group
  have h3 : a*((a⁻¹*b)*((b⁻¹*c)*(c⁻¹*d)))=d := by group
  have h4 : a*((a⁻¹*b)*((b⁻¹*c)*((c⁻¹*d)*(d⁻¹*e))))=e := by group
  have hval := hz (a⁻¹*b) (b⁻¹*c) (c⁻¹*d) (d⁻¹*e)
  simp only [evalFour] at hval
  change z.val a b c d e = 0
  simpa only [mul_one,mul_inv_cancel_left,h2,h3,h4,hval,map_zero] using ht

/-- A cocycle condition on ordinary continuous coordinates suffices to
build an element of the actual native categorical cycle object. -/
def closedThree (c : C(G × G × G,X)) : Prop := ∀ g h l m : G,
  X.ρ g (c (h,l,m)) - c (g*h,l,m) + c (g,h*l,m) - c (g,h,l*m) + c (g,h,l) = 0

private theorem fromThree_closed (c : C(G × G × G,X)) (hc : closedThree X c) :
    (K.d 3 4).hom (fromThreeMap X hact c) = 0 := by
  apply eval_four_detects_zero
  intro g h l m
  rw [eval_native_dThree]
  have he (a b d : G) : evalThree X (fromThreeMap X hact c) a b d = c (a,b,d) :=
    congrArg (fun f : C(G × G × G,X) => f (a,b,d)) (eval_fromThree X hact c)
  simp only [he]
  exact hc g h l m

private def shortCycle (S : ShortComplex (TopModuleCat k)) (w : S.X₂) (hw : S.g w = 0) :
    S.cycles := (concreteLeft S).cyclesIso.inv ⟨w,hw⟩

private theorem shortCycle_val (S : ShortComplex (TopModuleCat k)) (w : S.X₂) (hw : S.g w = 0) :
    S.iCycles (shortCycle S w hw) = w :=
  congrArg (fun f : (concreteLeft S).K ⟶ S.X₂ => f ⟨w,hw⟩)
    (concreteLeft S).cyclesIso_inv_comp_iCycles

private theorem scClosed (c : C(G × G × G,X)) (hc : closedThree X c) :
    (K.sc 3).g (fromThreeMap X hact c) = 0 := by
  change (K.d 3 ((ComplexShape.up ℕ).next 3)).hom _ = 0
  have hn : (ComplexShape.up ℕ).next 3 = 4 := (ComplexShape.up ℕ).next_eq' (by decide)
  rw [hn]
  exact fromThree_closed X hact c hc

def nativeThreeCycle (c : C(G × G × G,X)) (hc : closedThree X c) :
    ContinuousCohomology.cocycles X 3 :=
  shortCycle (K.sc 3) (fromThreeMap X hact c) (scClosed X hact c hc)

def nativeThreeClass (c : C(G × G × G,X)) (hc : closedThree X c) :
    continuousCohomology 3 X := (ContinuousCohomology.π X 3) (nativeThreeCycle X hact c hc)

/-- Exact zero-class test with the actual supplied representative on the
right, rather than some representative with the same abstract class. -/
theorem nativeThreeClass_zero_iff (c : C(G × G × G,X)) (hc : closedThree X c) :
    nativeThreeClass X hact c hc = 0 ↔ ∃ b : C(G × G,X), ∀ g h l : G,
      X.ρ g (b (h,l)) - b (g*h,l) + b (g,h*l) - b (g,h) = c (g,h,l) := by
  have hp := native_class_eq_zero_iff (K.sc 3) (nativeThreeCycle X hact c hc)
  have hv := shortCycle_val (K.sc 3) (fromThreeMap X hact c) (scClosed X hact c hc)
  change (K.sc 3).iCycles (nativeThreeCycle X hact c hc) = fromThreeMap X hact c at hv
  rw [hv] at hp
  change nativeThreeClass X hact c hc = 0 ↔
    ∃ z : K.X ((ComplexShape.up ℕ).prev 3), (K.d _ 3).hom z = fromThreeMap X hact c at hp
  have hi : (ComplexShape.up ℕ).prev 3 = 2 := (ComplexShape.up ℕ).prev_eq' (by decide)
  rw [hi] at hp
  have hb := native_boundary_iff X hact (fromThreeMap X hact c)
  rw [eval_fromThree] at hb
  exact hp.trans hb
end ActualCasselsTateNativeContinuousCycleClass318
