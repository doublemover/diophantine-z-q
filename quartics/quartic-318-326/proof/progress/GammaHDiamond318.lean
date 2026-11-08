module
public import GammaHGroup318
public section
noncomputable section
open scoped MatrixGroups
open CongruenceSubgroup
namespace GammaHDiamond318
open GammaHGroup318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual unit residue occurs as the lower-right entry of an actual
integral determinant-one Gamma0 matrix. The lift is built by integer Bezout. -/
theorem diagonal_surjective (N:ℕ) [NeZero N] : Function.Surjective (diagonal N) := by
  intro u
  let d:ℕ := (u:ZMod N).val
  have hd : Nat.Coprime d N := (ZMod.isUnit_iff_coprime d N).mp (by simpa [d] using u.isUnit)
  have hb:=Nat.gcd_eq_gcd_ab d N
  rw [hd.gcd_eq_one] at hb
  let a:ℤ:=Nat.gcdA d N
  let b:ℤ:= -Nat.gcdB d N
  have hab : a*(d:ℤ)-b*(N:ℤ)=1 := by
    dsimp [a,b]
    norm_num only [Nat.cast_one] at hb
    nlinarith [hb]
  let g:SL(2,ℤ):=⟨!![a,b; (N:ℤ),(d:ℤ)],by simpa [Matrix.det_fin_two] using hab⟩
  have hg:g∈Gamma0 N := by
    apply Gamma0_mem.mpr
    change ((N:ℤ):ZMod N)=0
    simp
  refine ⟨⟨g,hg⟩,?_⟩
  apply Units.ext
  change ((d:ℤ):ZMod N)=(u:ZMod N)
  simp [d]

/-- All units of the chosen subgroup H occur in the actual diamond map. -/
theorem diamond_surjective (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    Function.Surjective (diamond N H) := by
  intro u
  obtain ⟨g,hg⟩ := diagonal_surjective N u.val
  have hm : g.val∈gammaH N H := ⟨g,by change diagonal N g∈H;rw [hg];exact u.property,rfl⟩
  refine ⟨⟨g.val,hm⟩,?_⟩
  apply Subtype.ext
  exact hg

/-- Exact kernel equality in the ambient Gamma_H group. -/
theorem diamond_ker (N:ℕ) (H:Subgroup (ZMod N)ˣ) :
    (diamond N H).ker=(Gamma1 N).comap (gammaH N H).subtype := by
  ext g
  exact diamond_kernel_iff N H g

/-- The actual congruence-group quotient by the actual Gamma1 kernel is H.
This is a group quotient; it is not yet the effective action on the curve,
where central minus one may act trivially. -/
@[expose] def diamondQuotientEquiv (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    gammaH N H ⧸ (diamond N H).ker ≃* H :=
  QuotientGroup.quotientKerEquivOfSurjective (diamond N H) (diamond_surjective N H)

end GammaHDiamond318
