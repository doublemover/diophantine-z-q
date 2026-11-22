module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Germ
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Algebra.Ring.Subring.Basic

public section
noncomputable section

open Filter
open scoped Topology

namespace SelectedActualLocalHolomorphicGerms318

/-- The ring of genuine holomorphic germs at the specified complex center.
Using the full neighborhood, rather than the punctured neighborhood,
retains an actual evaluation map at the center. -/
@[expose] def Hol (c : ℂ) : Subring (Germ (𝓝 c) ℂ) where
  carrier := {u | ∃ f : ℂ → ℂ, AnalyticAt ℂ f c ∧ Germ.ofFun f = u}
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f + g,hf.add hg,Germ.coe_add f g⟩
  neg_mem' := by
    rintro _ ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,Germ.coe_neg f⟩
  mul_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f * g,hf.mul hg,Germ.coe_mul f g⟩

def germ (c : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f c) : Hol c :=
  ⟨Germ.ofFun f, f,hf,rfl⟩

def value (c : ℂ) : Hol c →+* ℂ :=
  (Germ.valueRingHom (x := c)).comp (Hol c).subtype

theorem value_germ (c : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f c) :
    value c (germ c f hf) = f c := by
  exact Germ.value_ofFun f c

theorem germ_eq_iff {c : ℂ} {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f c)
    (hg : AnalyticAt ℂ g c) :
    germ c f hf = germ c g hg ↔ f =ᶠ[𝓝 c] g := by
  constructor
  · intro h
    exact Germ.coe_eq.mp (congrArg (fun u : Hol c => (u : Germ (𝓝 c) ℂ)) h)
  · exact fun h => Subtype.ext (Germ.coe_eq.mpr h)

/-- In particular no inverse is obtained by discarding the center. It
is the holomorphic inverse across the center where the value is nonzero. -/
theorem germ_isUnit {c : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f c) (h₀ : f c ≠ 0) :
    IsUnit (germ c f hf) := by
  let u := germ c f hf
  let v := germ c (fun w => (f w)⁻¹) (hf.fun_inv h₀)
  have h : u * v = 1 := by
    apply Subtype.ext
    change Germ.ofFun (fun w => f w * (f w)⁻¹) = Germ.ofFun (fun _ => (1 : ℂ))
    apply Germ.coe_eq.mpr
    exact (hf.continuousAt.eventually_ne h₀).mono fun w hw => mul_inv_cancel₀ hw
  exact ⟨Units.mkOfMulEqOne u v h,rfl⟩

section Localize

variable {T S : Type*} [CommRing T] [CommRing S] [Algebra T S]
variable {M : Submonoid T} [IsLocalization M S]

/-- A single pointwise family of characters, including at the center. -/
open scoped Classical in
def updatedEval (c : ℂ) (ψ : ℂ → T →+* ℂ) (χ : T →+* ℂ) (w : ℂ) : T →+* ℂ :=
  if w = c then χ else ψ w

theorem updatedEval_center (c : ℂ) (ψ : ℂ → T →+* ℂ) (χ : T →+* ℂ) (b : T) :
    updatedEval c ψ χ c b = χ b := by
  simp only [updatedEval, if_pos rfl]

theorem updatedEval_away (c : ℂ) (ψ : ℂ → T →+* ℂ) (χ : T →+* ℂ) (b : T)
    {w : ℂ} (hw : w ≠ c) : updatedEval c ψ χ w b = ψ w b := by
  simp only [updatedEval, if_neg hw]

theorem updatedEval_eq_update (c : ℂ) (ψ : ℂ → T →+* ℂ) (χ : T →+* ℂ) (b : T) :
    (fun w => updatedEval c ψ χ w b) = Function.update (fun w => ψ w b) c (χ b) := by
  funext w
  by_cases hw : w = c
  · subst w
    rw [updatedEval_center,Function.update_self]
  · rw [updatedEval_away c ψ χ b hw,Function.update_of_ne hw]

variable (c : ℂ) (ψ : ℂ → T →+* ℂ) (χ : T →+* ℂ)
variable (hψ : ∀ b : T, AnalyticAt ℂ (fun w => updatedEval c ψ χ w b) c)

def sectionGerm : T →+* Hol c where
  toFun b := germ c (fun w => updatedEval c ψ χ w b) (hψ b)
  map_zero' := by
    apply Subtype.ext
    change Germ.ofFun (fun w => updatedEval c ψ χ w 0) = Germ.ofFun (fun _ => (0 : ℂ))
    exact congrArg Germ.ofFun (funext (fun w => map_zero (updatedEval c ψ χ w)))
  map_one' := by
    apply Subtype.ext
    change Germ.ofFun (fun w => updatedEval c ψ χ w 1) = Germ.ofFun (fun _ => (1 : ℂ))
    exact congrArg Germ.ofFun (funext (fun w => map_one (updatedEval c ψ χ w)))
  map_add' x y := by
    apply Subtype.ext
    change Germ.ofFun (fun w => updatedEval c ψ χ w (x+y)) =
      Germ.ofFun (fun w => updatedEval c ψ χ w x + updatedEval c ψ χ w y)
    exact congrArg Germ.ofFun (funext (fun w => map_add (updatedEval c ψ χ w) x y))
  map_mul' x y := by
    apply Subtype.ext
    change Germ.ofFun (fun w => updatedEval c ψ χ w (x*y)) =
      Germ.ofFun (fun w => updatedEval c ψ χ w x * updatedEval c ψ χ w y)
    exact congrArg Germ.ofFun (funext (fun w => map_mul (updatedEval c ψ χ w) x y))

theorem sectionGerm_apply (b : T) :
    sectionGerm c ψ χ hψ b = germ c (fun w => updatedEval c ψ χ w b) (hψ b) := by
  rfl

theorem value_sectionGerm (b : T) : value c (sectionGerm c ψ χ hψ b) = χ b := by
  rw [sectionGerm_apply,value_germ,updatedEval_center]

variable (S) (M)
variable (hM : ∀ s : M, χ s ≠ 0)

def localGerm : S →+* Hol c :=
  IsLocalization.lift (M := M) (g := sectionGerm c ψ χ hψ) fun s =>
    germ_isUnit (hψ s) (by rwa [updatedEval_center])

theorem localGerm_section (b : T) :
    localGerm c ψ χ hψ S M hM (algebraMap T S b) = sectionGerm c ψ χ hψ b := by
  unfold localGerm
  exact IsLocalization.lift_eq _ b

/-- The exact induced center character on the localization. -/
def localCenter : S →+* ℂ :=
  IsLocalization.lift (M := M) (g := χ) (fun s => isUnit_iff_ne_zero.mpr (hM s))

theorem localCenter_section (b : T) :
    localCenter χ S M hM (algebraMap T S b) = χ b := by
  unfold localCenter
  exact IsLocalization.lift_eq _ b

/-- Center value of the holomorphic localization agrees with the literal
algebraic evaluation of the fractions, with no analytic comparison axiom. -/
theorem value_localGerm :
    (value c).comp (localGerm c ψ χ hψ S M hM) = localCenter χ S M hM := by
  apply IsLocalization.ringHom_ext (S := S) M
  apply RingHom.ext
  intro b
  change value c (localGerm c ψ χ hψ S M hM (algebraMap T S b)) =
    localCenter χ S M hM (algebraMap T S b)
  rw [localGerm_section,value_sectionGerm,localCenter_section]

/-- A nonzero numerator may vanish at the center but cannot vanish on the
germ. The input is proved separately for the actual marked chart. -/
theorem injective_localGerm
    (hpunct : ∀ b : T, b ≠ 0 → ∀ᶠ w in 𝓝[≠] c, ψ w b ≠ 0) :
    Function.Injective (localGerm c ψ χ hψ S M hM) := by
  have hG : Function.Injective (sectionGerm c ψ χ hψ) := by
    apply (injective_iff_map_eq_zero' _).2
    intro b hb
    by_contra hne
    have hz : (fun w => updatedEval c ψ χ w b) =ᶠ[𝓝 c] fun _ => (0 : ℂ) :=
      Germ.coe_eq.mp (congrArg (fun u : Hol c => (u : Germ (𝓝 c) ℂ)) hb)
    have hfalse : ∀ᶠ w in 𝓝[≠] c, False := by
      filter_upwards [hz.filter_mono nhdsWithin_le_nhds,hpunct b hne,
        self_mem_nhdsWithin] with w hw hbw hc
      have hn : w ≠ c := fun h => hc (by exact Set.mem_singleton_iff.mpr h)
      exact hbw ((updatedEval_away c ψ χ b hn).symm.trans hw)
    exact (Filter.NeBot.ne inferInstance) (Filter.eventually_false_iff_eq_bot.mp hfalse)
  have H (x y : T) : algebraMap T S x = algebraMap T S y ↔
      sectionGerm c ψ χ hψ x = sectionGerm c ψ χ hψ y := by
    constructor
    · intro h
      exact (localGerm_section c ψ χ hψ S M hM x).symm.trans
        ((congrArg (localGerm c ψ χ hψ S M hM) h).trans
          (localGerm_section c ψ χ hψ S M hM y))
    · exact fun h => congrArg (algebraMap T S) (hG h)
  unfold localGerm
  exact IsLocalization.lift_injective_iff.mpr H

end Localize

end SelectedActualLocalHolomorphicGerms318
