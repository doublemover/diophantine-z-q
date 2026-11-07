module
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public section
namespace DiscreteCompletion318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def magnitude (p:ℝ) : WithTop ℤ → ℝ := WithTop.recTopCoe 0 (fun z => p^(-z))
@[simp] theorem magnitude_top (p:ℝ) : magnitude p ⊤=0 := rfl
@[simp] theorem magnitude_coe (p:ℝ) (z:ℤ) : magnitude p z=p^(-z) := rfl

theorem magnitude_nonneg (p:ℝ) (hp:0<p) (z:WithTop ℤ) : 0≤magnitude p z := by
  induction z using WithTop.recTopCoe with
  | top => simp
  | coe z => exact (zpow_pos hp _).le

theorem magnitude_zero_iff (p:ℝ) (hp:0<p) (z:WithTop ℤ) : magnitude p z=0 ↔ z=⊤ := by
  induction z using WithTop.recTopCoe with
  | top => simp
  | coe z => simp [magnitude,zpow_ne_zero _ hp.ne']

theorem magnitude_add (p:ℝ) (hp:0<p) (a b:WithTop ℤ) :
    magnitude p (a+b)=magnitude p a*magnitude p b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      rw [←WithTop.coe_add,magnitude_coe,magnitude_coe,magnitude_coe,neg_add,
        zpow_add₀ hp.ne']

theorem magnitude_antitone (p:ℝ) (hp:1≤p) : Antitone (magnitude p) := by
  intro a b hab
  induction b using WithTop.recTopCoe with
  | top => exact magnitude_nonneg p (lt_of_lt_of_le zero_lt_one hp) a
  | coe b =>
    induction a using WithTop.recTopCoe with
    | top => exact (not_le_of_gt (WithTop.coe_lt_top b) hab).elim
    | coe a => exact zpow_le_zpow_right₀ hp (neg_le_neg (WithTop.coe_le_coe.mp hab))

theorem magnitude_min (p:ℝ) (hp:1≤p) (a b:WithTop ℤ) :
    magnitude p (min a b)=max (magnitude p a) (magnitude p b) := by
  rcases le_total a b with h|h
  · rw [min_eq_left h,max_eq_left (magnitude_antitone p hp h)]
  · rw [min_eq_right h,max_eq_right (magnitude_antitone p hp h)]

variable {K:Type*} [Field K]
@[expose] def absolute (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) : AbsoluteValue K ℝ where
  toFun x:=magnitude p (v x)
  map_mul' x y:=by rw [v.map_mul,magnitude_add p (by linarith)]
  nonneg' x:=magnitude_nonneg p (by linarith) _
  eq_zero' x:=by
    rw [magnitude_zero_iff p (by linarith)]
    exact not_iff_not.mp v.ne_top_iff
  add_le' x y:=by
    calc
      magnitude p (v (x+y))≤magnitude p (min (v x) (v y)) := magnitude_antitone p hp.le (v.map_add x y)
      _=max (magnitude p (v x)) (magnitude p (v y)):=magnitude_min p hp.le _ _
      _≤magnitude p (v x)+magnitude p (v y):=
        max_le_add_of_nonneg (magnitude_nonneg p (by linarith) _) (magnitude_nonneg p (by linarith) _)

theorem absolute_nonarch (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) (x y:K) :
    absolute p hp v (x+y)≤max (absolute p hp v x) (absolute p hp v y) := by
  exact (magnitude_antitone p hp.le (v.map_add x y)).trans_eq (magnitude_min p hp.le _ _)

@[expose] abbrev Completion (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) := (absolute p hp v).Completion

@[expose] def embed (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) : K →+* Completion p hp v :=
  UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv (absolute p hp v)).symm.toRingHom

theorem embed_injective (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) :
    Function.Injective (embed p hp v) := (embed p hp v).injective

theorem embed_dense (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) :
    DenseRange (embed p hp v) := by
  have hr:Set.range (embed p hp v)=Set.range
      ((↑):WithAbs (absolute p hp v)→Completion p hp v) := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨WithAbs.toAbs _ x,hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨x.ofAbs,hx⟩
  intro x
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe x

theorem norm_embed (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) (x:K) :
    ‖embed p hp v x‖=magnitude p (v x) := by
  change ‖((WithAbs.toAbs (absolute p hp v) x):Completion p hp v)‖=_
  rw [UniformSpace.Completion.norm_coe,WithAbs.norm_eq_apply_ofAbs]
  rfl

theorem norm_embed_value (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ))
    (x:K) (z:ℤ) (hx:v x=z) : ‖embed p hp v x‖=p^(-z) := by rw [norm_embed,hx,magnitude_coe]

theorem norm_embed_le_iff (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) (x:K) (z:ℤ) :
    ‖embed p hp v x‖≤p^(-z) ↔ (z:WithTop ℤ)≤v x := by
  rw [norm_embed]
  induction v x using WithTop.recTopCoe with
  | top =>
    simp only [magnitude_top,le_top,iff_true]
    exact (zpow_pos (by linarith : 0<p) (-z)).le
  | coe a =>
    rw [magnitude_coe,zpow_le_zpow_iff_right₀ hp,WithTop.coe_le_coe]
    omega

theorem norm_embed_lt_one_iff (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) (x:K) :
    ‖embed p hp v x‖<1 ↔ (0:WithTop ℤ)<v x := by
  rw [norm_embed]
  induction v x using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    rw [magnitude_coe,show (1:ℝ)=p^(0:ℤ) by simp,zpow_lt_zpow_iff_right₀ hp]
    change -a<0 ↔ ((0:ℤ):WithTop ℤ)<(a:WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    omega

/-- A value-one uniformizer makes the completed norm nontrivial. -/
def nontriviallyNormed (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ))
    (pi:K) (hpi:v pi=1) : NontriviallyNormedField (Completion p hp v) :=
  NontriviallyNormedField.ofNormNeOne ⟨embed p hp v pi,
    (by
      intro hz
      have hz0:pi=0 := (embed p hp v).injective (by simpa only [map_zero] using hz)
      rw [hz0,v.map_zero] at hpi
      exact WithTop.top_ne_coe hpi),
    ne_of_lt ((norm_embed_lt_one_iff p hp v pi).mpr (by rw [hpi]; norm_num))⟩

instance completion_ultrametric (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) :
    IsUltrametricDist (Completion p hp v) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  induction x,y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_le <;> fun_prop
  | ih x y =>
    simp only [←UniformSpace.Completion.coe_add,UniformSpace.Completion.norm_coe,
      WithAbs.norm_eq_apply_ofAbs,WithAbs.ofAbs_add]
    exact absolute_nonarch p hp v x.ofAbs y.ofAbs

instance completion_charZero [CharZero K] (p:ℝ) (hp:1<p) (v:AddValuation K (WithTop ℤ)) :
    CharZero (Completion p hp v) where
  cast_injective m n h := by
    apply Nat.cast_injective (R:=K)
    apply (embed p hp v).injective
    simpa only [map_natCast] using h

end
end DiscreteCompletion318
#print axioms DiscreteCompletion318.absolute
#print axioms DiscreteCompletion318.norm_embed
#print axioms DiscreteCompletion318.completion_ultrametric
