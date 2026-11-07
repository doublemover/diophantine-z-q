module
public import TorusAddition318
public import Mathlib.Data.ZMod.Basic
public section
noncomputable section
open ModularWeierstrass318 PeriodEisenstein318 LatticeInvariants318 LatticeModelPoint318 TorusAddition318
namespace EllipticTorsion318
set_option maxHeartbeats 0

variable (tau : UpperHalfPlane) (N : ℕ) [NeZero N]

@[expose] def integerStep (l : (periods tau).lattice) : ℤ →+ (curve tau).toAffine.Point :=
  (pointHom tau).comp (AddMonoidHom.mk' (fun m : ℤ => (m : ℂ)/(N:ℂ)*(l:ℂ))
    (by intros; simp [add_div,add_mul]))

lemma integerStep_apply (l : (periods tau).lattice) (m : ℤ) :
    integerStep tau N l m=point tau ((m:ℂ)/(N:ℂ)*(l:ℂ)) := rfl

lemma integerStep_N (l : (periods tau).lattice) : integerStep tau N l N=0 := by
  rw [integerStep_apply]
  have hN : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [Int.cast_natCast,div_self hN,one_mul]
  exact point_of_mem tau l l.property

@[expose] def periodTorsion (l : (periods tau).lattice) : ZMod N →+ (curve tau).toAffine.Point :=
  ZMod.lift N ⟨integerStep tau N l,integerStep_N tau N l⟩

lemma periodTorsion_intCast (l : (periods tau).lattice) (m : ℤ) :
    periodTorsion tau N l (m:ZMod N)=point tau ((m:ℂ)/(N:ℂ)*(l:ℂ)) := by
  simp only [periodTorsion,ZMod.lift_coe,integerStep_apply]

@[expose] def firstPeriod : (periods tau).lattice := latticeMap tau ![1,0]
@[expose] def secondPeriod : (periods tau).lattice := latticeMap tau ![0,1]

lemma firstPeriod_val : ((firstPeriod tau : (periods tau).lattice):ℂ)=tau := by
  simp [firstPeriod,latticeMap]
lemma secondPeriod_val : ((secondPeriod tau : (periods tau).lattice):ℂ)=1 := by
  simp [secondPeriod,latticeMap]

/-- Actual N-torsion point with the two specified lattice coordinates. -/
@[expose] def torsionMap : ZMod N × ZMod N →+ (curve tau).toAffine.Point :=
  (periodTorsion tau N (firstPeriod tau)).coprod (periodTorsion tau N (secondPeriod tau))

lemma torsionMap_intCast (m n : ℤ) :
    torsionMap tau N ((m:ZMod N),(n:ZMod N))=
      point tau (((m:ℂ)*tau+n)/(N:ℂ)) := by
  change periodTorsion tau N (firstPeriod tau) (m:ZMod N)+
    periodTorsion tau N (secondPeriod tau) (n:ZMod N)=_
  rw [periodTorsion_intCast,periodTorsion_intCast,firstPeriod_val,secondPeriod_val,
    ← point_add]
  congr 1
  ring

lemma divided_period_mem_iff (m n : ℤ) :
    ((m:ℂ)*tau+n)/(N:ℂ) ∈ (periods tau).lattice ↔ (N:ℤ)∣m ∧ (N:ℤ)∣n := by
  have hN : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := PeriodPair.mem_lattice.mp h
    have he : (m:ℂ)*tau+n=((N:ℤ)*a:ℤ)*tau+((N:ℤ)*b:ℤ) := by
      simp only [periods] at hab
      have hh := (div_eq_iff hN).mp hab.symm
      push_cast
      linear_combination hh
    have hvec : latticeMap tau ![m,n]=latticeMap tau ![(N:ℤ)*a,(N:ℤ)*b] := by
      apply Subtype.ext
      simpa [latticeMap] using he
    have hu := latticeMap_injective tau hvec
    exact ⟨⟨a,by simpa using congrFun hu 0⟩,⟨b,by simpa using congrFun hu 1⟩⟩
  · rintro ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    apply PeriodPair.mem_lattice.mpr
    refine ⟨a,b,?_⟩
    simp only [periods]
    push_cast
    field_simp

lemma torsionMap_eq_zero_iff (x : ZMod N × ZMod N) : torsionMap tau N x=0 ↔ x=0 := by
  obtain ⟨m,hm⟩ := ZMod.intCast_surjective x.1
  obtain ⟨n,hn⟩ := ZMod.intCast_surjective x.2
  have hx : x=((m:ZMod N),(n:ZMod N)) := Prod.ext hm.symm hn.symm
  rw [hx,torsionMap_intCast,TorusPointInterface318.point_eq_zero_iff,divided_period_mem_iff]
  simp only [Prod.mk_eq_zero,ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma torsionMap_injective : Function.Injective (torsionMap tau N) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (torsionMap_eq_zero_iff tau N (x-y)).mp
  rw [map_sub,h,sub_self]

lemma torsionMap_killed (x : ZMod N × ZMod N) : N • torsionMap tau N x=0 := by
  rw [← map_nsmul]
  have hz : N • x=0 := by ext <;> simp [nsmul_eq_mul]
  rw [hz,map_zero]

/-- Every actual N-torsion point comes from the two actual period coordinates. -/
lemma torsionMap_surjective_kernel (P : (curve tau).toAffine.Point) (hP : N • P=0) :
    ∃ x : ZMod N × ZMod N, torsionMap tau N x=P := by
  obtain ⟨z,hz⟩ := TorusBijection318.point_surjective tau P
  have hzN : point tau ((N:ℂ)*z)=0 := by
    have hh := (pointHom tau).map_nsmul N z
    change point tau (N • z)=N • point tau z at hh
    simpa [nsmul_eq_mul,hz,hP] using hh
  have hl := (TorusPointInterface318.point_eq_zero_iff tau _).mp hzN
  obtain ⟨m,n,hmn⟩ := PeriodPair.mem_lattice.mp hl
  refine ⟨((m:ZMod N),(n:ZMod N)),?_⟩
  rw [torsionMap_intCast]
  have he : ((m:ℂ)*tau+n)/(N:ℂ)=z := by
    simp only [periods,mul_one] at hmn
    rw [hmn]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
  rw [he,hz]

@[expose] def torsionSubgroup : AddSubgroup (curve tau).toAffine.Point :=
  (nsmulAddMonoidHom N).ker

@[expose] def torsionMapToKernel : ZMod N × ZMod N →+ torsionSubgroup tau N :=
  (torsionMap tau N).codRestrict (torsionSubgroup tau N) (torsionMap_killed tau N)

/-- The actual N-torsion subgroup of the normalized elliptic curve is (Z/N)². -/
@[expose] def torsionEquiv : (ZMod N × ZMod N) ≃+ torsionSubgroup tau N :=
  AddEquiv.ofBijective (torsionMapToKernel tau N) ⟨by
    intro x y h
    exact torsionMap_injective tau N (congrArg Subtype.val h),by
    intro P
    obtain ⟨x,hx⟩ := torsionMap_surjective_kernel tau N P.val P.property
    exact ⟨x,Subtype.ext hx⟩⟩

lemma torsionEquiv_apply (x : ZMod N × ZMod N) :
    (torsionEquiv tau N x).val=torsionMap tau N x := rfl

lemma torsion_card : Nat.card (torsionSubgroup tau N)=N^2 := by
  rw [← Nat.card_congr (torsionEquiv tau N).toEquiv]
  simp [ZMod.card,pow_two]

end EllipticTorsion318
