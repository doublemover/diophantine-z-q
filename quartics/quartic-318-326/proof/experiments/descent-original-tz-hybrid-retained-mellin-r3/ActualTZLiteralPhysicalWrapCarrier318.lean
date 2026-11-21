module
public import ActualTZGridMarginalJoin318
public import ActualTZRetainedHorizon318
public import ActualTZPhysicalShortZero318
public import ActualTZPhysicalPairMarkerKey318
import all ActualTZCanonicalWrapFibres318
import all ActualTZLiteralWrapClipping318
import all ActualTZExactZeroIntegerGrid318
import all ActualTZLiteralTerminalLift318
public section
noncomputable section
namespace ActualTZLiteralPhysicalWrapCarrier318
open scoped BigOperators
open ActualTZRelabelPhysicalGrid318 ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318
open ActualTZLiteralWrapClipping318 ActualTZCanonicalWrapFibres318 ActualTZRetainedHorizon318
attribute [local instance] Classical.propDecidable

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

structure Context (S : Terminal m a b) (I : Type*) where
  y : ℕ
  N : ℕ
  n : ℕ
  M : ℕ
  M₀ : ℕ
  C : ℕ
  npos : 0<n
  Mpos : 0<M
  fine_le : M≤M₀
  sample : primorial y*n≤N
  node : I→Site a b j
  distinct : Function.Injective node
  good : GoodTerminal S (primorial y)
  offsetCap : ∀ (z : ActualTZExactZeroIntegerGrid318.Grid (len m a j M M₀)) i,
    |MvPolynomial.eval (ActualTZExactZeroIntegerGrid318.point
      (len m a j M M₀) (start m a j M) z) (py (siteP S (node i)))|≤(C:ℤ)*(n:ℤ)

namespace Context

variable {S : Terminal m a b} (X : Context S I)

abbrev OldGrid := ActualTZExactZeroIntegerGrid318.Grid (len m a j X.M X.M₀)
abbrev Keys := Wrap I X.C
abbrev Pair (I : Type*) := {p : I×I // p.1≠p.2}

@[expose] def point (z : X.OldGrid) : Fin (D m a j)→ℤ :=
  ActualTZExactZeroIntegerGrid318.point (len m a j X.M X.M₀) (start m a j X.M) z

@[expose] def off (z : X.OldGrid) (i : I) : ℤ :=
  MvPolynomial.eval (X.point z) (py (siteP S (X.node i)))

def code (z : X.OldGrid) (x : Fin X.n) : X.Keys :=
  key X.n X.C X.npos (X.off z) (X.offsetCap z) x

def width (z : X.OldGrid) (r : X.Keys) : ℕ := (fibre (X.code z) r).card

def wrapped (z : X.OldGrid) (r : X.Keys) (i : I) : ℤ :=
  X.off z i-decode X.C r i*(X.n:ℤ)

@[expose] def base (i : I) : ℕ := siteB S (X.node i)

def pairPol (r : X.Keys) (q : Pair I) : MvPolynomial (Fin (D m a j)) ℤ :=
  py (physicalP S (primorial X.y) X.n (decode X.C r q.val.1) (decode X.C r q.val.2)
    (X.node q.val.1) (X.node q.val.2))

def evalPair (z : X.OldGrid) (r : X.Keys) (q : Pair I) : ℤ :=
  MvPolynomial.eval (X.point z) (X.pairPol r q)

def theta (z : X.OldGrid) (r : X.Keys) : ℝ :=
  kept X.n ((X.n:ℝ)^((3:ℝ)/4)) X.width (fun z r q=>X.evalPair z r q=0) z r

def collision (p : ℕ) (z : X.OldGrid) (r : X.Keys) : Prop :=
  ∃ q : Pair I,(p:ℤ)∣X.evalPair z r q

theorem width_total (z : X.OldGrid) : (∑ r : X.Keys,X.width z r)=X.n := fibres_cover (X.code z)

theorem width_le (z : X.OldGrid) (r : X.Keys) : X.width z r≤X.n := by
  unfold width fibre
  exact (Finset.card_filter_le _ _).trans_eq Fintype.card_fin

theorem theta_bounds (z : X.OldGrid) (r : X.Keys) : 0≤X.theta z r ∧ X.theta z r≤1 := by
  unfold theta kept
  split_ifs
  · norm_num
  · have hN : 0<(X.n:ℝ) := by exact_mod_cast X.npos
    exact ⟨by unfold wrapMass; positivity,(div_le_one hN).2 (by exact_mod_cast X.width_le z r)⟩

theorem base_unit (i : I) : 1≤X.base i ∧ X.base i≤primorial X.y ∧
    (primorial X.y).Coprime (X.base i) := by
  unfold base
  cases H : X.node i with
  | marked ω => exact ⟨X.good.unitMarked.1,X.good.unitMarked.2.1,X.good.unitMarked.2.2.symm⟩
  | linear w k ω => exact ⟨(X.good.unitLinear k).1,(X.good.unitLinear k).2.1,(X.good.unitLinear k).2.2.symm⟩
  | nonlinear w k ω => exact ⟨(X.good.unitNonlinear k).1,(X.good.unitNonlinear k).2.1,(X.good.unitNonlinear k).2.2.symm⟩

theorem degree_pair (r : X.Keys) (q : Pair I) : (X.pairPol r q).totalDegree≤2 :=
  (py_degree _).trans (physicalD S _ _ _ _ _ _)

theorem evalPair_physical (z : X.OldGrid) (r : X.Keys) (q : Pair I) (x : ℤ) :
    X.evalPair z r q=
      ((primorial X.y:ℤ)*(x+X.wrapped z r q.val.1)+(X.base q.val.1:ℤ))-
      ((primorial X.y:ℤ)*(x+X.wrapped z r q.val.2)+(X.base q.val.2:ℤ)) := by
  simp only [evalPair,pairPol,py_eval,physical_eval S (primorial X.y) X.n x,wrapped,off,base]
  ring

/-- Actual collision equivalence before any residue-class bounds.
The original shared-x signed difference is used at each pair. -/
theorem collision_iff (p : ℕ) (z : X.OldGrid) (r : X.Keys) :
    X.collision p z r ↔ ∃ i k,i≠k ∧ (p:ℤ)∣
      ((primorial X.y:ℤ)*X.wrapped z r i+(X.base i:ℤ))-
      ((primorial X.y:ℤ)*X.wrapped z r k+(X.base k:ℤ)) := by
  constructor
  · rintro ⟨⟨⟨i,k⟩,hik⟩,H⟩
    exact ⟨i,k,hik,by simpa only [X.evalPair_physical z r _ 0,zero_add] using H⟩
  · rintro ⟨i,k,hik,H⟩
    exact ⟨⟨(i,k),hik⟩,by simpa only [X.evalPair_physical z r _ 0,zero_add] using H⟩

private theorem kept_fibre (z : X.OldGrid) (r : X.Keys) (h : 0<X.theta z r) :
    ∃ x : Fin X.n,x∈fibre (X.code z) r ∧ ∀ q : Pair I,X.evalPair z r q≠0 := by
  have hGood : ¬((X.width z r:ℝ)<(X.n:ℝ)^((3:ℝ)/4) ∨
      ∃ q : Pair I,X.evalPair z r q=0) := by
    intro H
    simp only [theta,kept,if_pos H,lt_irrefl] at h
  have hWidth : 0<X.width z r := by
    by_contra hn
    have hZ : X.width z r=0 := by omega
    simp only [theta,kept,if_neg hGood,wrapMass,hZ,Nat.cast_zero,zero_div,lt_irrefl] at h
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hWidth
  exact ⟨x,hx,fun q hq=>hGood (Or.inr ⟨q,hq⟩)⟩

theorem kept_horizon (p : ℕ) (z : X.OldGrid) (r : X.Keys) (h : 0<X.theta z r)
    (hD : X.collision p z r) : p≤2*X.N := by
  obtain ⟨q,hq⟩ := hD
  obtain ⟨x,hx,hNe⟩ := kept_fibre X z r h
  have k : X.code z x=r := (Finset.mem_filter.mp hx).2
  have hRep (i : I) :
      residue X.n ((x.val:ℤ)+1+X.off z i)=(x.val:ℤ)+1+X.wrapped z r i := by
    have H := decode_key X.n X.C X.npos (X.off z) (X.offsetCap z) x i
    change decode X.C (X.code z x) i=_ at H
    rw [k] at H
    rw [residue_split,←H,wrapped]
    ring
  have he := X.evalPair_physical z r q ((x.val:ℤ)+1)
  rw [←hRep q.val.1,←hRep q.val.2] at he
  rw [he] at hq
  exact horizon _ _ _ _ (primorial_pos _) X.npos X.sample _ _ _ _
    ⟨by exact_mod_cast (X.base_unit q.val.1).1,by exact_mod_cast (X.base_unit q.val.1).2.1⟩
    ⟨by exact_mod_cast (X.base_unit q.val.2).1,by exact_mod_cast (X.base_unit q.val.2).2.1⟩
    (by rw [←he]; exact hNe q) hq

/-- Actual signed-grid marginal for the same wrap-clipped physical
hit. K survives every actual shifted pair, not just a symbolic
unwrapped or source position substitute. -/
theorem sparse [NeZero p] [Fact p.Prime]
    (hD : ∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0) :
    (∑ z : X.OldGrid,(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)*
      (∑ r : X.Keys,X.theta z r*(if X.collision p z r then 1 else 0)))≤
      (Fintype.card X.Keys:ℝ)*(Fintype.card (Pair I):ℝ)*
        ((2:ℝ)^(D m a j)*(D m a j:ℝ)*(2:ℝ))*(1/(p:ℝ)+1/(X.M:ℝ)) :=
  ActualTZGridMarginalJoin318.weighted_marginal (p:=p) (len m a j X.M X.M₀) (start m a j X.M)
    X.M 2 X.Mpos (len_ge X.M X.M₀ X.fine_le) X.pairPol hD X.degree_pair X.theta
    (fun z r=>(theta_bounds X z r).1) (fun z r=>(theta_bounds X z r).2) (collision X p)
    (fun _ _ h=>h)

theorem theta_le_original (z : X.OldGrid) (r : X.Keys) :
    X.theta z r≤wrapMass X.n X.width z r := by
  unfold theta kept
  split_ifs
  · unfold wrapMass
    positivity
  · exact le_rfl

theorem mass_total_le :
    (∑ z : X.OldGrid,(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)*
      (∑ r : X.Keys,X.theta z r))≤1 := by
  have hN : 0<(X.n:ℝ) := by exact_mod_cast X.npos
  have hFull (z : X.OldGrid) : (∑ r : X.Keys,wrapMass X.n X.width z r)=1 := by
    unfold wrapMass
    rw [←Finset.sum_div,←Nat.cast_sum,X.width_total,div_self hN.ne']
  have hM : (∑ _ : X.OldGrid,
      (ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ))=1 := by
    exact_mod_cast ActualTZExactZeroIntegerGrid318.uniform_one (len m a j X.M X.M₀)
      (fun i=>X.Mpos.trans_le (len_ge X.M X.M₀ X.fine_le i))
  calc
    _ ≤ ∑ z : X.OldGrid,(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)*
        (∑ r : X.Keys,wrapMass X.n X.width z r) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun r _=>X.theta_le_original z r
    _ = _ := by simp only [hFull,mul_one,hM]

theorem pair_ne (r : X.Keys) (q : Pair I) : X.pairPol r q≠0 := by
  obtain ⟨u,c,hc,H⟩ := py_marker S (primorial X.y) X.good (primorial_pos _)
    (X.node q.val.1) (X.node q.val.2) (fun h=>q.property (X.distinct h))
  intro h
  have hh := H X.n (decode X.C r q.val.1) (decode X.C r q.val.2)
  change (X.pairPol r q).coeff u=c at hh
  rw [h] at hh
  exact hc (by simpa using hh.symm)

theorem lost_mass_bound :
    (∑ z : X.OldGrid,(ActualTZExactZeroIntegerGrid318.uniform (len m a j X.M X.M₀):ℝ)*
      (∑ r : X.Keys,(wrapMass X.n X.width z r-X.theta z r)))≤
      (Fintype.card X.Keys:ℝ)*((X.n:ℝ)^(-(1:ℝ)/4)+
        (Fintype.card (Pair I):ℝ)*((D m a j:ℝ)*((2:ℝ)/(X.M:ℝ)))) :=
  ActualTZPhysicalShortZero318.lost_key_mass (len m a j X.M X.M₀) (start m a j X.M) X.M 2 X.n
    X.Mpos (len_ge X.M X.M₀ X.fine_le) X.npos X.width X.width_le X.pairPol X.pair_ne X.degree_pair

end Context
end ActualTZLiteralPhysicalWrapCarrier318
