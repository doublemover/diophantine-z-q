module
public import SelectedThreeBranchSignedDegree318
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public section
noncomputable section

open scoped MatrixGroups
open CongruenceSubgroup

namespace SelectedGammaOneEllipticAction318

variable (N : ℕ)
abbrev Vect := ZMod N × ZMod N

local notation "e₁" => ((1,0) : Vect N)
local notation "U₀" => (ModularGroup.S * ModularGroup.T)

/-- Actual reduction of the integral modular matrix on the rank-two
level module. A sign changes both entries simultaneously. -/
@[expose] def act (g : SL(2, ℤ)) (p : Vect N) : Vect N :=
  ((g 0 0 : ZMod N)*p.1+(g 0 1 : ZMod N)*p.2,
    (g 1 0 : ZMod N)*p.1+(g 1 1 : ZMod N)*p.2)

theorem act_mul (g h : SL(2, ℤ)) (p : Vect N) :
    act N (g*h) p = act N g (act N h p) := by
  apply Prod.ext
  · change ((g*h) 0 0:ZMod N)*p.1+((g*h) 0 1:ZMod N)*p.2 =
      (g 0 0:ZMod N)*((h 0 0:ZMod N)*p.1+(h 0 1:ZMod N)*p.2)+
      (g 0 1:ZMod N)*((h 1 0:ZMod N)*p.1+(h 1 1:ZMod N)*p.2)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    ring
  · change ((g*h) 1 0:ZMod N)*p.1+((g*h) 1 1:ZMod N)*p.2 =
      (g 1 0:ZMod N)*((h 0 0:ZMod N)*p.1+(h 0 1:ZMod N)*p.2)+
      (g 1 1:ZMod N)*((h 1 0:ZMod N)*p.1+(h 1 1:ZMod N)*p.2)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    ring

theorem act_one (p : Vect N) : act N 1 p = p := by
  apply Prod.ext <;> simp [act, Matrix.SpecialLinearGroup.coe_one]

theorem act_neg (g : SL(2, ℤ)) (p : Vect N) : act N (-g) p = -(act N g p) := by
  apply Prod.ext
  · change ((-g) 0 0:ZMod N)*p.1+((-g) 0 1:ZMod N)*p.2 =
      -((g 0 0:ZMod N)*p.1+(g 0 1:ZMod N)*p.2)
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    ring
  · change ((-g) 1 0:ZMod N)*p.1+((-g) 1 1:ZMod N)*p.2 =
      -((g 1 0:ZMod N)*p.1+(g 1 1:ZMod N)*p.2)
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    ring

@[expose] def actAdd (g : SL(2, ℤ)) : Vect N →+ Vect N where
  toFun := act N g
  map_zero' := by apply Prod.ext <;> simp [act]
  map_add' p q := by apply Prod.ext <;> simp [act] <;> ring

theorem act_neg_vector (g : SL(2, ℤ)) (p : Vect N) :
    act N g (-p) = -(act N g p) :=
  (actAdd N g).map_neg p

theorem act_inv_act (g : SL(2, ℤ)) (p : Vect N) :
    act N g⁻¹ (act N g p) = p := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_order (g : SL(2, ℤ)) (p : Vect N) : addOrderOf (act N g p) = addOrderOf p := by
  have hinj : Function.Injective (actAdd N g) :=
    (show Function.LeftInverse (act N g⁻¹) (actAdd N g) from act_inv_act N g).injective
  exact addOrderOf_injective (actAdd N g) hinj p

theorem first_order : addOrderOf e₁ = N := by
  let f : ZMod N →+ Vect N :=
    { toFun := fun a => (a,0)
      map_zero' := rfl
      map_add' := fun _ _ => by simp }
  have hinj : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  exact (addOrderOf_injective f hinj 1).trans (ZMod.addOrderOf_one N)

/-- Exact ordinary Γ₁ membership on the actual reduced base vector.
The lower right entry is forced by determinant one, rather than being
discarded as part of a sign convention. -/
theorem gamma_one_iff (g : SL(2, ℤ)) : g ∈ Gamma1 N ↔ act N g e₁ = e₁ := by
  rw [Gamma1_mem]
  constructor
  · rintro ⟨h00,_,h10⟩
    apply Prod.ext <;> simp [act,h00,h10]
  · intro h
    have h00 : (g 0 0:ZMod N) = 1 := by simpa [act] using congrArg Prod.fst h
    have h10 : (g 1 0:ZMod N) = 0 := by simpa [act] using congrArg Prod.snd h
    have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
      simpa only [Matrix.det_fin_two] using g.det_coe
    have hd := congrArg (fun x : ℤ => (x:ZMod N)) hdet
    push_cast at hd
    rw [h00,h10,one_mul,mul_zero,sub_zero] at hd
    exact ⟨h00,hd,h10⟩

theorem act_S (p : Vect N) :
    act N ModularGroup.S p = SelectedThreeBranchSignedDegree318.S p := by
  apply Prod.ext <;> simp [act, ModularGroup.coe_S, SelectedThreeBranchSignedDegree318.S]

theorem act_T (p : Vect N) : act N ModularGroup.T p = (p.1+p.2,p.2) := by
  apply Prod.ext <;> simp [act, ModularGroup.coe_T]

theorem act_U (p : Vect N) :
    act N U₀ p = SelectedThreeBranchSignedDegree318.U p := by
  rw [act_mul,act_T,act_S] <;> rfl

theorem U_neg (p : Vect N) :
    SelectedThreeBranchSignedDegree318.U (-p) = -SelectedThreeBranchSignedDegree318.U p := by
  apply Prod.ext
  · rfl
  · change -p.1 + -p.2 = -(p.1+p.2)
    ring

/-- No nonidentity effective element of either cyclic elliptic
stabilizer can fix a primitive signed level vector. The square of
U=ST is included, not left to a separate orbit assumption. -/
theorem no_elliptic_fix (hN : 3 < N) (p : Vect N) (hp : addOrderOf p = N) :
    ¬(act N ModularGroup.S p = p ∨ act N ModularGroup.S p = -p) ∧
    ¬(act N U₀ p = p ∨ act N U₀ p = -p) ∧
    ¬(act N (U₀^2) p = p ∨ act N (U₀^2) p = -p) := by
  obtain ⟨hS,hU⟩ := SelectedThreeBranchSignedDegree318.no_signed_elliptic_fixed p hp hN
  refine ⟨by simpa only [act_S] using hS, by simpa only [act_U] using hU, ?_⟩
  have hU2 : act N (U₀^2) p =
      SelectedThreeBranchSignedDegree318.U (SelectedThreeBranchSignedDegree318.U p) := by
    rw [pow_two, act_mul N U₀ U₀ p, act_U N (act N U₀ p), act_U N p]
  rw [hU2]
  rintro (h|h)
  · have hy := congrArg SelectedThreeBranchSignedDegree318.U h
    rw [SelectedThreeBranchSignedDegree318.U_cube] at hy
    exact hU (Or.inr hy.symm)
  · have hy := congrArg SelectedThreeBranchSignedDegree318.U h
    rw [SelectedThreeBranchSignedDegree318.U_cube,U_neg] at hy
    exact hU (Or.inl (neg_injective hy).symm)

/-- Passing back to a lift gα of the base elliptic point: source
membership up to sign yields fixing the actual signed vector g⁻¹e₁. -/
theorem signed_fix_of_conjugated (g h : SL(2, ℤ)) :
    (g*h*g⁻¹ ∈ Gamma1 N ∨ -(g*h*g⁻¹) ∈ Gamma1 N) →
    (act N h (act N g⁻¹ e₁) = act N g⁻¹ e₁ ∨
      act N h (act N g⁻¹ e₁) = -(act N g⁻¹ e₁)) := by
  rintro (hp|hn)
  · left
    have hh := (gamma_one_iff N (g*h*g⁻¹)).mp hp
    have hh' : act N g (act N h (act N g⁻¹ e₁)) = e₁ := by simpa only [act_mul] using hh
    simpa only [act_inv_act] using congrArg (act N g⁻¹) hh'
  · right
    have hh := (gamma_one_iff N (-(g*h*g⁻¹))).mp hn
    have hh' : -(act N g (act N h (act N g⁻¹ e₁))) = e₁ := by
      simpa only [act_neg,act_mul] using hh
    have hh'' : act N g (act N h (act N g⁻¹ e₁)) = -e₁ := by
      simpa only [neg_neg] using congrArg (fun p : Vect N => -p) hh'
    simpa only [act_inv_act,act_neg_vector] using congrArg (act N g⁻¹) hh''

/-- On the actual Γ₁ subgroup, all lifts of the two base elliptic
points have trivial effective stabilizer. Neither sheet labels nor
torsion-free source stabilizers are supplied as selected hypotheses. -/
theorem no_elliptic_conjugates (hN : 3 < N) (g : SL(2, ℤ)) :
    ¬(g*ModularGroup.S*g⁻¹ ∈ Gamma1 N ∨ -(g*ModularGroup.S*g⁻¹) ∈ Gamma1 N) ∧
    ¬(g*U₀*g⁻¹ ∈ Gamma1 N ∨ -(g*U₀*g⁻¹) ∈ Gamma1 N) ∧
    ¬(g*(U₀^2)*g⁻¹ ∈ Gamma1 N ∨ -(g*(U₀^2)*g⁻¹) ∈ Gamma1 N) := by
  have hp : addOrderOf (act N g⁻¹ e₁) = N := (act_order N g⁻¹ e₁).trans (first_order N)
  obtain ⟨hS,hU,hU2⟩ := no_elliptic_fix N hN (act N g⁻¹ e₁) hp
  exact ⟨fun h => hS (signed_fix_of_conjugated N g _ h),
    fun h => hU (signed_fix_of_conjugated N g _ h),
    fun h => hU2 (signed_fix_of_conjugated N g _ h)⟩

end SelectedGammaOneEllipticAction318

#print axioms SelectedGammaOneEllipticAction318.gamma_one_iff
#print axioms SelectedGammaOneEllipticAction318.no_elliptic_fix
#print axioms SelectedGammaOneEllipticAction318.no_elliptic_conjugates
