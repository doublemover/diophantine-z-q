module
public import OddTwistDilatationCoordinates318
public import IntegralValuativeRootCoordinates318
public section
noncomputable section
namespace OddInfinityIntegralCoordinates318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (pi : V) (hp : Irreducible pi) (u : Fin 4 → Vˣ) (a : Fin 4 → V)
  (ha : a 0=0) (w : V) (hw : w≠0) (hwn : ¬IsUnit w)
  (z : Fin 4 → V)
  (hz : ∀ i,(z i)^2=(u i : V)*pi*w*(1-a i*w))

include K hp ha hw hwn hz in
/-- A reciprocal integral point with all four odd twists has an integral
infinity coordinate and three UNIT signed ratios. No contact-separation
or odd-residue-characteristic hypothesis is needed for these coordinates. -/
theorem exists_coordinates :
    ∃ (Z : V) (r : Fin 3 → Vˣ),
      Z≠0 ∧ z 0=pi*Z ∧ w=pi*(↑(u 0)⁻¹ : V)*Z^2 ∧
      (∀ j : Fin 3,z j.succ=pi*Z*(r j : V)) ∧
      ∀ j : Fin 3,(r j : V)^2=
        (u j.succ : V)*(↑(u 0)⁻¹ : V)*(1-a j.succ*w) := by
  have hz0 : (z 0)^2=(u 0 : V)*pi*(w-0) := by
    simpa only [ha,zero_mul,sub_zero,mul_one] using hz 0
  obtain ⟨Z,hZ,hwZ⟩ := OddTwistDilatationCoordinates318.exists_coordinate pi hp (u 0) 0 w (z 0) hz0
  have hwZ' : w=pi*(↑(u 0)⁻¹ : V)*Z^2 := by simpa only [zero_add] using hwZ
  have hZ0 : Z≠0 := by
    intro h
    apply hw
    simpa only [h,zero_pow (by decide : (2 : ℕ)≠0),mul_zero] using hwZ'
  let q : Fin 3 → V := fun j => (u j.succ : V)*(↑(u 0)⁻¹ : V)*(1-a j.succ*w)
  have hq (j : Fin 3) : IsUnit (q j) := by
    have hnon : ¬IsUnit (a j.succ*w) := fun h => hwn (isUnit_of_mul_isUnit_right h)
    exact ((u j.succ).isUnit.mul ((u 0)⁻¹).isUnit).mul
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hnon)
  have hrel (j : Fin 3) : (z j.succ)^2=(pi*Z)^2*q j := by
    rw [hz j.succ]
    change _=(pi*Z)^2*((u j.succ : V)*(↑(u 0)⁻¹ : V)*(1-a j.succ*w))
    conv_lhs => arg 1; rw [hwZ']
    ring
  have hd : algebraMap V K (pi*Z)≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective V K).ne (mul_ne_zero hp.ne_zero hZ0)
  have he (j : Fin 3) :
      (algebraMap V K (z j.succ)/algebraMap V K (pi*Z))^2=algebraMap V K (q j) := by
    rw [div_pow,←map_pow,hrel,map_mul,map_pow]
    field_simp [hd]
  have hex (j : Fin 3) : ∃ r : V,
      algebraMap V K r=algebraMap V K (z j.succ)/algebraMap V K (pi*Z) ∧ r^2=q j :=
    IntegralValuativeRootCoordinates318.square_preimage V K _ _ (he j)
  choose r hr hr2 using hex
  have hru (j : Fin 3) : IsUnit (r j) :=
    (isUnit_pow_iff (by decide : (2 : ℕ)≠0)).mp ((hr2 j).symm ▸ hq j)
  refine ⟨Z,fun j => (hru j).unit,hZ0,hZ,hwZ',?_,?_⟩
  · intro j
    rw [(hru j).unit_spec]
    apply IsFractionRing.injective V K
    rw [map_mul,hr j]
    field_simp [hd]
  · intro j
    rw [(hru j).unit_spec,hr2 j]
    rfl
end OddInfinityIntegralCoordinates318
