module
public import ActualCasselsTateTameRootInertiaRigidity318
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.Group.Action.Units
public section

/-! Semilinear comparison at a supplied common place. The old group acts
only on the selected extension, the new group only on the common overfield.
No lift of the old group to the common overfield is assumed. -/
namespace ActualCasselsTateTameRootPrimitiveTransport318
open Polynomial ActualCasselsTateTameRootInertiaRigidity318

section
variable {R A k : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field k]
variable (n : ℕ) (u : Rˣ)
local notation "p" => ((X : R[X]) ^ n - C (u : R))
local notation "S" => AdjoinRoot p
variable (P : Ideal S) [P.IsPrime]
local notation "T" => Localization.AtPrime P
local notation "j" => algebraMap S T
local notation "t" => AdjoinRoot.root p
variable [IsDomain T]
local notation "M" => FractionRing T
variable {N Γ G : Type*} [Field N] [Group Γ] [Group G]
  [MulSemiringAction Γ N] [MulSemiringAction G M]
variable (red : A →+* k) (hn : (n : k) ≠ 0) (π : Γ →* G)
  (i : T →+* A) (v : A →+* N) (φ : M →+* N)
  (hφ : ∀ x : T, φ (algebraMap T M x) = v (i x))
  (a : Γ → A →+* A) (b : G → T →+* T)
  (ha : ∀ γ x, red (a γ x) = red x)
  (hb : ∀ g, b g (j t) = j t)
  (hR : ∀ γ (r : R),
    a γ (i (j (AdjoinRoot.of p r))) = i (b (π γ) (j (AdjoinRoot.of p r))))
  (hN : ∀ γ x, γ • v x = v (a γ x))
  (hM : ∀ g (x : T), g • algebraMap T M x = algebraMap T M (b g x))

include hn hφ ha hb hR hN hM

/-- Coefficient equivariance on M is proved from old-base agreement and
the distinct reductions of the tame roots. Not a hypothesis about M. -/
theorem selected_field_equivariant (γ : Γ) (x : M) : γ • φ x = φ (π γ • x) := by
  have hT : (a γ).comp i = i.comp (b (π γ)) := by
    apply tame_local_homs_eq n u P red hn
    · exact RingHom.ext (hR γ)
    · change red (a γ (i (j t))) = red (i (b (π γ) (j t)))
      rw [ha, hb]
  have he : (((MulSemiringAction.toRingAut Γ N) γ).toRingHom).comp φ =
      φ.comp (((MulSemiringAction.toRingAut G M) (π γ)).toRingHom) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors T)
    apply RingHom.ext
    intro y
    change γ • φ (algebraMap T M y) = φ (π γ • algebraMap T M y)
    rw [hφ, hN, hM, hφ]
    exact congrArg v (RingHom.congr_fun hT y)
  exact RingHom.congr_fun he x

local instance : MulDistribMulAction G Mˣ := Units.mulDistribMulActionRight
local instance : MulDistribMulAction Γ Nˣ := Units.mulDistribMulActionRight
local notation "V" => Units.map φ.toMonoidHom

/-- Transport a literal primitive on the old inertia group to any common
group satisfying the displayed integer restriction and residual hypotheses.
The primitive and cocycle on the right use the very same coefficient map.
No statement about arbitrary decomposition-group elements follows. -/
theorem transport_primitive (c : G → G → Mˣ) (d : G → Mˣ)
    (hd : ∀ g h, (g • d h) / d (g*h) * d g = c g h)
    (γ δ : Γ) :
    (γ • V (d (π δ))) / V (d (π (γ*δ))) * V (d (π γ)) = V (c (π γ) (π δ)) := by
  have he : γ • V (d (π δ)) = V (π γ • d (π δ)) := by
    apply Units.ext
    exact selected_field_equivariant n u P red hn π i v φ hφ a b ha hb hR hN hM γ _
  rw [he, map_mul π]
  simpa only [map_mul, map_div] using congrArg V (hd (π γ) (π δ))
end
end ActualCasselsTateTameRootPrimitiveTransport318
