module
public import RationalContactPoint318
public import RationalFourRootSplitting318
public import FourRootPointTorsor318
public import FourRootOrderSignAction318
public import FiberCentralizer318
public section
noncomputable section
namespace RationalFourRootGalois318
open FourRootOrder318 FourRootOrderSigns318 RationalFourRootFiber318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

/-- The literal four root signs, with their actual exclusive-or group law. -/
@[expose] def Signs := Fin 4 → Bool
instance : CommGroup Signs where
  mul s t i := Bool.xor (s i) (t i)
  one _ := false
  inv s := s
  mul_assoc s t u := by funext i; exact Bool.xor_assoc _ _ _
  one_mul s := by funext i; exact Bool.false_xor _
  mul_one s := by funext i; exact Bool.xor_false _
  inv_mul_cancel s := by funext i; exact Bool.xor_self _
  mul_comm s t := by funext i; exact Bool.xor_comm _ _
instance : Fintype Signs := inferInstanceAs (Fintype (Fin 4 → Bool))
theorem signs_card : Nat.card Signs = 16 := by
  change Nat.card (Fin 4 → Bool) = 16
  norm_num [Nat.card_eq_fintype_card]

variable (a : Fin 4 → ℚ)
abbrev Points := Order a →ₐ[ℚ] PointField a
abbrev GaloisGroup := PointField a ≃ₐ[ℚ] PointField a

@[expose] def signPermutation (s : Signs) : Equiv.Perm (Points a) where
  toFun p := p.comp (signEquiv a s).toAlgHom
  invFun p := p.comp (signEquiv a s).toAlgHom
  left_inv p := by
    apply AlgHom.ext
    intro x
    change p (signEquiv a s (signEquiv a s x)) = p x
    exact congrArg p (AlgEquiv.congr_fun (signEquiv_trans_self a s) x)
  right_inv p := by
    apply AlgHom.ext
    intro x
    change p (signEquiv a s (signEquiv a s x)) = p x
    exact congrArg p (AlgEquiv.congr_fun (signEquiv_trans_self a s) x)

/-- Genuine deck permutations of the same rational four-root fiber. -/
@[expose] def signAction : Signs →* Equiv.Perm (Points a) where
  toFun := signPermutation a
  map_one' := by
    apply Equiv.ext
    intro p
    apply AlgHom.ext
    intro x
    change p (signEquiv a (fun _ => false) x) = p x
    rw [FourRootOrderSignAction318.identity]
    rfl
  map_mul' s t := by
    apply Equiv.ext
    intro p
    apply AlgHom.ext
    intro x
    change p (signEquiv a (fun i => Bool.xor (s i) (t i)) x) =
      p (signEquiv a t (signEquiv a s x))
    exact congrArg p (AlgEquiv.congr_fun
      (FourRootOrderSignAction318.composition a s t).symm x)

/-- Field automorphisms act on actual fiber points by postcomposition. -/
@[expose] def galoisPermutation (s : GaloisGroup a) : Equiv.Perm (Points a) where
  toFun p := s.toAlgHom.comp p
  invFun p := s.symm.toAlgHom.comp p
  left_inv p := by apply AlgHom.ext; intro x; exact s.symm_apply_apply (p x)
  right_inv p := by apply AlgHom.ext; intro x; exact s.apply_symm_apply (p x)

@[expose] def galoisAction : GaloisGroup a →* Equiv.Perm (Points a) where
  toFun := galoisPermutation a
  map_one' := by apply Equiv.ext; intro p; apply AlgHom.ext; intro x; rfl
  map_mul' s t := by apply Equiv.ext; intro p; apply AlgHom.ext; intro x; rfl

theorem actions_commute (s : GaloisGroup a) (g : Signs) (p : Points a) :
    galoisAction a s (signAction a g p) = signAction a g (galoisAction a s p) := rfl

/-- Faithfulness uses surjectivity of the actual quotient map, not an
assumed Galois representation or an unrelated faithful action. -/
theorem galoisAction_injective : Function.Injective (galoisAction a) := by
  intro s t h
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := point_surjective a y
  exact congrArg (fun e : Equiv.Perm (Points a) => e (point a) x) h

variable (ha : ∀ i, a i ≠ 0)

include ha in
theorem sign_orbit_bijective : Function.Bijective
    (fun g : Signs => signAction a g (point a)) := by
  have h : ∀ i, algebraMap ℚ (PointField a) (a i) ≠ 0 := by
    intro i
    simpa only [map_zero] using (algebraMap ℚ (PointField a)).injective.ne (ha i)
  exact ⟨FourRootPointTorsor318.orbit_injective a h (point a),
    FourRootPointTorsor318.orbit_surjective a (point a)⟩

include ha in
/-- The original field degree divides sixteen. This is the contact point
field, not a field carrying an additional quaternionic level-three marking. -/
theorem field_degree_dvd_sixteen : Module.finrank ℚ (PointField a) ∣ 16 := by
  have h := FiberCentralizer318.faithful_torsor_card_dvd
    (signAction a) (point a) (sign_orbit_bijective a ha)
    (galoisAction a) (actions_commute a) (galoisAction_injective a)
  rwa [signs_card, IsGalois.card_aut_eq_finrank ℚ (PointField a)] at h

/-- Literal five-form avoidance gives the same degree bound for the original
contact source point at its exact coordinate normalization. -/
theorem contact_field_degree_dvd_of_forms (c : Fin 4 → ℚˣ) (u v : ℤ)
    (hn : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) :
    Module.finrank ℚ (RationalContactPoint318.PointField c
      (32 * ((u : ℚ) / (v : ℚ)))) ∣ 16 :=
  field_degree_dvd_sixteen _ (RationalContactPoint318.parameters_ne_of_forms c u v hn)

end RationalFourRootGalois318
