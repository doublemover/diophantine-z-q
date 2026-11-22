module

public import SelectedActualLocalHolomorphicGerms318
import all SelectedActualLocalHolomorphicGerms318
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Span

public section
noncomputable section

open Filter
open scoped Topology

namespace SelectedActualEllipticFixedGermCore318

open SelectedActualLocalHolomorphicGerms318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {c : ℂ}

private theorem analytic_representation (u : Hol c) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f c ∧ Germ.ofFun f = (u : Germ (𝓝 c) ℂ) :=
  u.property

private def rep (u : Hol c) : ℂ → ℂ := (analytic_representation u).choose

private theorem rep_analytic (u : Hol c) : AnalyticAt ℂ (rep u) c :=
  (analytic_representation u).choose_spec.1

private theorem rep_coe (u : Hol c) : Germ.ofFun (rep u) = (u : Germ (𝓝 c) ℂ) :=
  (analytic_representation u).choose_spec.2

private theorem rep_value (u : Hol c) : rep u c = value c u := by
  have h := congrArg (Germ.valueRingHom (x := c) : Germ (𝓝 c) ℂ →+* ℂ) (rep_coe u)
  exact h

private theorem rep_order_ne_top (u : Hol c) (hu : u ≠ 0) :
    analyticOrderAt (rep u) c ≠ ⊤ := by
  intro h
  apply hu
  apply Subtype.ext
  exact (rep_coe u).symm.trans (Germ.coe_eq.mpr (analyticOrderAt_eq_top.mp h))

private def orderNat (u : Hol c) : ℕ := analyticOrderNatAt (rep u) c

private theorem orderNat_pos (u : Hol c) (hu : u ≠ 0) (hv : value c u = 0) :
    0 < orderNat u := by
  apply Nat.pos_of_ne_zero
  intro h
  have he := Nat.cast_analyticOrderNatAt (rep_order_ne_top u hu)
  change analyticOrderNatAt (rep u) c = 0 at h
  rw [h,Nat.cast_zero] at he
  exact ((rep_analytic u).analyticOrderAt_eq_zero.mp he.symm) ((rep_value u).trans hv)

private theorem orderNat_mul (a b : Hol c) (h : a * b ≠ 0) :
    orderNat (a*b) = orderNat a + orderNat b := by
  have ha : a ≠ 0 := fun hz => h (by rw [hz,zero_mul])
  have hb : b ≠ 0 := fun hz => h (by rw [hz,mul_zero])
  have hEq : rep (a*b) =ᶠ[𝓝 c] rep a * rep b := by
    apply Germ.coe_eq.mp
    exact (rep_coe (a*b)).trans
      ((congrArg₂ (fun x y : Germ (𝓝 c) ℂ => x*y) (rep_coe a) (rep_coe b)).symm.trans
        (Germ.coe_mul (rep a) (rep b)).symm)
  have hN : analyticOrderNatAt (rep (a*b)) c = analyticOrderNatAt (rep a * rep b) c := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hEq]
  exact hN.trans (analyticOrderNatAt_mul (rep_analytic a) (rep_analytic b)
    (rep_order_ne_top a ha) (rep_order_ne_top b hb))

/-- The exact finite-residue descent underlying rotation invariance. Two
holomorphic readouts of the same local ring that agree on the literal
scalar section and the one uniformizer cannot differ. This compares
actual analytic germs, without assuming a completed local ring, an
analytic DVR or isometry of orders. -/
theorem germ_maps_eq_of_residue_and_uniformizer
    {L : Type*} [CommRing L] [IsLocalRing L]
    (scalar : ℂ →+* L) (ε : L →+* ℂ) (π : L)
    (hker : ∀ a, ε a = 0 ↔ a ∈ IsLocalRing.maximalIdeal L)
    (hscalar : ∀ z, ε (scalar z) = z)
    (hspan : IsLocalRing.maximalIdeal L = Ideal.span ({π} : Set L))
    (f g : L →+* Hol c)
    (hvalue : ∀ a, value c (f a) = ε a)
    (hfixedScalar : ∀ z, f (scalar z) = g (scalar z))
    (hfixedPi : f π = g π) :
    f = g := by
  classical
  let D : L → Hol c := fun a => f a - g a
  have hStep (a : L) : ∃ b : L, D a = f π * D b := by
    have hm : a - scalar (ε a) ∈ IsLocalRing.maximalIdeal L := (hker _).mp (by
      rw [map_sub,hscalar,sub_self])
    rw [hspan,Ideal.mem_span_singleton] at hm
    obtain ⟨b,hb⟩ := hm
    refine ⟨b,?_⟩
    calc
      D a = f (a - scalar (ε a)) - g (a - scalar (ε a)) := by
        change f a - g a = _
        rw [map_sub,map_sub,hfixedScalar]
        ring
      _ = f π * D b := by
        change f (a - scalar (ε a)) - g (a - scalar (ε a)) = f π * (f b - g b)
        rw [hb,map_mul,map_mul,← hfixedPi,mul_sub]
  have hπValue : value c (f π) = 0 := by
    rw [hvalue]
    apply (hker π).mpr
    rw [hspan]
    exact Ideal.mem_span_singleton_self π
  apply RingHom.ext
  intro a₀
  by_contra hbad
  let W : ℕ → Prop := fun n => ∃ a : L, D a ≠ 0 ∧ orderNat (D a) = n
  have hex : ∃ n, W n := ⟨orderNat (D a₀), a₀,sub_ne_zero.mpr hbad,rfl⟩
  obtain ⟨a,ha,haMin⟩ := Nat.find_spec hex
  obtain ⟨b,hb⟩ := hStep a
  have hprod : f π * D b ≠ 0 := fun h => ha (hb.trans h)
  have hbn : D b ≠ 0 := fun hz => hprod (by rw [hz,mul_zero])
  have hπn : f π ≠ 0 := fun hz => hprod (by rw [hz,zero_mul])
  have hπord : 0 < orderNat (f π) := orderNat_pos _ hπn hπValue
  have hle : Nat.find hex ≤ orderNat (D b) :=
    Nat.find_min' hex ⟨b,hbn,rfl⟩
  rw [← haMin,hb,orderNat_mul _ _ hprod] at hle
  omega


private theorem tendsTo_center {σ : ℂ → ℂ} (hσ : AnalyticAt ℂ σ c) (h : σ c = c) :
    Tendsto σ (𝓝 c) (𝓝 c) :=
by
  simpa only [h] using hσ.continuousAt.tendsto

private def plainPullback (σ : ℂ → ℂ) (hσ : Tendsto σ (𝓝 c) (𝓝 c)) :
    Germ (𝓝 c) ℂ →+* Germ (𝓝 c) ℂ where
  toFun u := u.compTendsto σ hσ
  map_zero' := by
    exact Germ.coe_compTendsto (fun _ => (0 : ℂ)) hσ
  map_one' := by
    exact Germ.coe_compTendsto (fun _ => (1 : ℂ)) hσ
  map_add' u v := by
    refine Germ.inductionOn₂ u v (fun f g => ?_)
    change (Germ.ofFun (f+g)).compTendsto σ hσ =
      (Germ.ofFun f).compTendsto σ hσ + (Germ.ofFun g).compTendsto σ hσ
    rw [Germ.coe_compTendsto (f+g) hσ,Germ.coe_compTendsto f hσ,Germ.coe_compTendsto g hσ]
    exact Germ.coe_add (f ∘ σ) (g ∘ σ)
  map_mul' u v := by
    refine Germ.inductionOn₂ u v (fun f g => ?_)
    change (Germ.ofFun (f*g)).compTendsto σ hσ =
      (Germ.ofFun f).compTendsto σ hσ * (Germ.ofFun g).compTendsto σ hσ
    rw [Germ.coe_compTendsto (f*g) hσ,Germ.coe_compTendsto f hσ,Germ.coe_compTendsto g hσ]
    exact Germ.coe_mul (f ∘ σ) (g ∘ σ)

theorem compose_at_center {σ f : ℂ → ℂ} (hσ : AnalyticAt ℂ σ c) (h : σ c = c)
    (hf : AnalyticAt ℂ f c) : AnalyticAt ℂ (f ∘ σ) c := by
  have h₀ : AnalyticAt ℂ f (σ c) := h.symm ▸ hf
  exact h₀.comp hσ

/-- Pullback on this exact holomorphic germ ring along one analytic
germ fixing the designated complex center. -/
def pullback (σ : ℂ → ℂ) (hσ : AnalyticAt ℂ σ c) (h : σ c = c) : Hol c →+* Hol c := by
  let h₀ := tendsTo_center hσ h
  let f : Hol c →+* Germ (𝓝 c) ℂ := (plainPullback σ h₀).comp (Hol c).subtype
  have hf (u : Hol c) : f u ∈ Hol c := by
    change ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      Germ.ofFun g = (u : Germ (𝓝 c) ℂ).compTendsto σ h₀
    exact ⟨rep u ∘ σ,compose_at_center hσ h (rep_analytic u),
      (Germ.coe_compTendsto (rep u) h₀).symm.trans
        (congrArg (fun v : Germ (𝓝 c) ℂ => v.compTendsto σ h₀) (rep_coe u))⟩
  exact {
    toFun := fun u => ⟨f u,hf u⟩
    map_zero' := Subtype.ext (map_zero f)
    map_one' := Subtype.ext (map_one f)
    map_add' u v := Subtype.ext (map_add f u v)
    map_mul' u v := Subtype.ext (map_mul f u v) }

theorem pullback_germ (σ : ℂ → ℂ) (hσ : AnalyticAt ℂ σ c) (h : σ c = c)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f c) :
    pullback σ hσ h (germ c f hf) = germ c (f ∘ σ) (compose_at_center hσ h hf) := by
  apply Subtype.ext
  change (Germ.ofFun f).compTendsto σ (tendsTo_center hσ h) = Germ.ofFun (f ∘ σ)
  exact Germ.coe_compTendsto f (tendsTo_center hσ h)

/-- A local rotation that fixes the holomorphic image of the single
algebraic uniformizer fixes the image of every actual section. The
literal constant β is enough; no continuity of f on the algebraic
local ring, finite extension of germs, or completion is assumed. -/
theorem fixed_of_uniformizer
    {L : Type*} [CommRing L] [IsLocalRing L]
    (scalar : ℂ →+* L) (ε : L →+* ℂ) (π : L)
    (hker : ∀ a, ε a = 0 ↔ a ∈ IsLocalRing.maximalIdeal L)
    (hspan : IsLocalRing.maximalIdeal L = Ideal.span ({π} : Set L))
    (Φ : L →+* Hol c)
    (hvalue : ∀ a, value c (Φ a) = ε a)
    (hScalar : ∀ z, Φ (scalar z) = germ c (fun _ => z) analyticAt_const)
    (σ : ℂ → ℂ) (hσ : AnalyticAt ℂ σ c) (h : σ c = c)
    (hfixedPi : pullback σ hσ h (Φ π) = Φ π) :
    ∀ a : L, pullback σ hσ h (Φ a) = Φ a := by
  have hSc (z : ℂ) : ε (scalar z) = z := by
    rw [← hvalue,hScalar,value_germ]
  let f : L →+* Hol c := (pullback σ hσ h).comp Φ
  have hConst (z : ℂ) : Φ (scalar z) = f (scalar z) := by
    change Φ (scalar z) = pullback σ hσ h (Φ (scalar z))
    rw [hScalar,pullback_germ]
    all_goals apply Subtype.ext <;> rfl
  have hef : Φ = f := germ_maps_eq_of_residue_and_uniformizer scalar ε π hker hSc hspan
    Φ f hvalue hConst hfixedPi.symm
  intro a
  exact (RingHom.congr_fun hef a).symm

end SelectedActualEllipticFixedGermCore318

#print axioms SelectedActualEllipticFixedGermCore318.germ_maps_eq_of_residue_and_uniformizer
#print axioms SelectedActualEllipticFixedGermCore318.fixed_of_uniformizer
