module

public import OriginalOriginLocalizationKernel318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

@[expose] public section
noncomputable section

namespace OriginalOriginUniversalThickRead318

open OriginalOriginLocalizationKernel318

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
variable (a : B→ₐ[k] k)
local notation "P" => RingHom.ker a.toRingHom
local instance originPrime : P.IsPrime := RingHom.ker_isPrime a.toRingHom
local notation "M" => P.Cotangent
local notation "T" => TrivSqZeroExt k M
variable (j : B→ₐ[k] T)
variable (fst_j : ∀ x, (j x).fst=a x)
variable (snd_j : ∀ x : P, (j x.val).snd=P.toCotangent x)

include fst_j snd_j in
/-- The detector is the old full coordinate pair (a(b), dₐb)
on arbitrary affine elements, as read by R74's universal v=id.
Knowing both coordinates on the indicated rings is essential. -/
theorem thick_kernel : RingHom.ker j.toRingHom=P^2 := by
  ext x
  change j x=0 ↔ x∈P^2
  constructor
  · intro h
    have h0 : a x=0 := (fst_j x).symm.trans (congrArg TrivSqZeroExt.fst h)
    let x0 : P := ⟨x,h0⟩
    apply (P.toCotangent_eq_zero x0).1
    exact (snd_j x0).symm.trans (congrArg TrivSqZeroExt.snd h)
  · intro hx
    let x0 : P := ⟨x,Ideal.pow_le_self (by decide : (2:ℕ)≠0) hx⟩
    apply TrivSqZeroExt.ext
    · exact fst_j x |>.trans x0.property
    · exact (snd_j x0).trans ((P.toCotangent_eq_zero x0).2 hx)

include fst_j in
theorem thick_den (s : P.primeCompl) : IsUnit (j s.val) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst,fst_j,isUnit_iff_ne_zero]
  exact s.property

variable {L : Type*} [CommRing L] [Algebra B L] [IsLocalization.AtPrime L P]

def wholeJet : L→+*T := onLocalRing P j.toRingHom (thick_den a j fst_j)
def residueJet : L→+*k := (TrivSqZeroExt.fstHom k k M).toRingHom.comp (wholeJet a j fst_j)

theorem wholeJet_read (x : B) :
    wholeJet a j fst_j (algebraMap B L x)=j x :=
  onLocalRing_read P j.toRingHom (thick_den a j fst_j) x

theorem residueJet_read (x : B) :
    residueJet a j fst_j (algebraMap B L x)=a x := by
  change (wholeJet a j fst_j (algebraMap B L x)).fst=a x
  rw [wholeJet_read a j fst_j,fst_j]

variable [IsLocalRing L]

include snd_j in
theorem wholeJet_ker :
    RingHom.ker (wholeJet a j fst_j : L→+*T)=(IsLocalRing.maximalIdeal L)^2 :=
  onLocalRing_ker_power P j.toRingHom (thick_den a j fst_j) 2 (thick_kernel a j fst_j snd_j)

theorem residueJet_ker :
    RingHom.ker (residueJet a j fst_j : L→+*k)=IsLocalRing.maximalIdeal L := by
  have den : ∀ y : P.primeCompl, IsUnit (a.toRingHom y) :=
    fun y => isUnit_iff_ne_zero.2 y.property
  have same : (residueJet a j fst_j : L→+*k)=onLocalRing P a.toRingHom den := by
    apply onLocalRing_unique P a.toRingHom den
    exact RingHom.ext (residueJet_read a j fst_j)
  rw [same,onLocalRing_ker_power P a.toRingHom den 1 (pow_one P).symm,pow_one]

def multiplyNil (n : ℕ) : T→ₐ[k]T :=
  TrivSqZeroExt.map (n • (LinearMap.id : M→ₗ[k]M))

theorem multiplyNil_pure (n : ℕ) (t : T) (pure : t.fst=0) :
    multiplyNil a n t=n • t := by
  have e : t=TrivSqZeroExt.inr t.snd := by
    apply TrivSqZeroExt.ext
    · exact pure
    · rfl
  rw [e,multiplyNil,TrivSqZeroExt.map_inr]
  exact map_nsmul (TrivSqZeroExt.inrHom k M) t.snd n

variable (f : L→+*L) (n : ℕ)
variable (square_exact : (wholeJet a j fst_j).comp f =
    (multiplyNil a n).toRingHom.comp (wholeJet a j fst_j))

include square_exact in
/-- Exact universal square-zero Scheme-map comparison in the old
germ gives the actual residue and cotangent congruences consumed by R261. -/
theorem actual_germ_congruences (sharp : RingHom.ker (wholeJet a j fst_j : L→+*T)=
      (IsLocalRing.maximalIdeal L)^2) :
    (∀ x : L, f x-x∈IsLocalRing.maximalIdeal L) ∧
    (∀ x∈IsLocalRing.maximalIdeal L, f x-(n:L)*x∈(IsLocalRing.maximalIdeal L)^2) := by
  have eval (x : L) : wholeJet a j fst_j (f x)=multiplyNil a n (wholeJet a j fst_j x) :=
    RingHom.congr_fun square_exact x
  constructor
  · intro x
    rw [←residueJet_ker a j fst_j, RingHom.mem_ker]
    change (wholeJet a j fst_j (f x-x)).fst=0
    rw [map_sub,TrivSqZeroExt.fst_sub,eval,multiplyNil,TrivSqZeroExt.fst_map,sub_self]
  · intro x hx
    have z : (wholeJet a j fst_j x).fst=0 := by
      rw [←residueJet_ker a j fst_j] at hx
      exact RingHom.mem_ker.1 hx
    rw [←sharp,RingHom.mem_ker]
    change wholeJet a j fst_j (f x-(n:L)*x)=0
    rw [←nsmul_eq_mul,map_sub,map_nsmul,eval,multiplyNil_pure a n _ z,sub_self]

end OriginalOriginUniversalThickRead318
