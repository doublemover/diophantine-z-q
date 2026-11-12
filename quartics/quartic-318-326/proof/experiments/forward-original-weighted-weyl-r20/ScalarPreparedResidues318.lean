module
public import PreparedTwoThreeSource318
public import LucasWitness318
public section
noncomputable section
namespace ScalarPreparedResidues318
open ScalarTwoThreePreparation318 ScalarForwardWitness318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Adjustable shared local depths, fixed before every real and prime choice. -/
@[expose] def residue (A B : ℕ) : ℕ := 2^A*3^B
@[expose] def modulus (A B : ℕ) : ℕ := 6*residue A B
@[expose] def scalarLabel (A B d : ℕ) : ℤ := 1+(6^(A+B+15)*d:ℕ)

lemma residue_pos (A B : ℕ) : 0<residue A B := by unfold residue; positivity
lemma modulus_pos (A B : ℕ) : 0<modulus A B := by
  exact Nat.mul_pos (by norm_num) (residue_pos A B)

lemma residue_depths (A B : ℕ) :
    padicValNat 2 (residue A B)=A ∧ padicValNat 3 (residue A B)=B := by
  have h23 : padicValNat 2 3=0 := padicValNat_primes (by decide)
  have h32 : padicValNat 3 2=0 := padicValNat_primes (by decide)
  constructor <;> simp [residue,padicValNat.mul (by positivity : (2:ℕ)^A≠0)
    (by positivity : (3:ℕ)^B≠0),padicValNat.pow,padicValNat_self,h23,h32]

/-- Congruence to the actual prepared residue fixes both local depths exactly. -/
lemma common_depths (A B h : ℕ) (hA : 6≤A)
    (hc : Nat.ModEq (modulus A B) h (residue A B)) :
    h≠0 ∧ 64∣h ∧ Even (h:ℤ) ∧
      padicValInt 2 (h:ℤ)=A ∧ padicValInt 3 (h:ℤ)=B := by
  have hR := residue_pos A B
  have hmod : h%modulus A B=residue A B := by
    have hlt : residue A B<modulus A B := by unfold modulus; omega
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hlt] using hc
  let j := h/modulus A B
  have he : h=residue A B*(1+6*j) := by
    calc
      h = h%modulus A B+modulus A B*(h/modulus A B) := (Nat.mod_add_div _ _).symm
      _ = residue A B*(1+6*j) := by rw [hmod]; dsimp [modulus,j]; ring
  have hu : 1+6*j≠0 := by omega
  have hv2 : padicValNat 2 (1+6*j)=0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; omega)
  have hv3 : padicValNat 3 (1+6*j)=0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; omega)
  have hh : h≠0 := by rw [he]; exact mul_ne_zero (ne_of_gt hR) hu
  have v2 : padicValNat 2 h=A := by
    rw [he,padicValNat.mul (ne_of_gt hR) hu,hv2,add_zero]
    exact (residue_depths A B).1
  have v3 : padicValNat 3 h=B := by
    rw [he,padicValNat.mul (ne_of_gt hR) hu,hv3,add_zero]
    exact (residue_depths A B).2
  have h64 : 64∣h := by
    change (2:ℕ)^6∣h
    exact (padicValNat_dvd_iff_le hh).mpr (by omega)
  have heven : Even h := even_iff_two_dvd.mpr ((by norm_num : 2∣64).trans h64)
  exact ⟨hh,h64,by exact_mod_cast heven,by simpa using v2,by simpa using v3⟩

/-- The scalar label can be chosen arbitrarily far out by varying d. -/
lemma label_domains (A B d : ℕ) (hd : d≠0) :
    3≤scalarLabel A B d ∧ Odd (scalarLabel A B d) ∧ scalarLabel A B d%3=1 ∧
      Even (scalarLabel A B d-1) := by
  have he : 6^(A+B+15)*d=6*(6^(A+B+14)*d) := by
    rw [show A+B+15=(A+B+14)+1 by omega,pow_succ]
    ring
  have hp : 0<(6^(A+B+14)*d:ℕ) := by positivity
  have hc : scalarLabel A B d=1+6*((6^(A+B+14)*d:ℕ):ℤ) := by
    unfold scalarLabel
    rw [he]
    push_cast
    ring
  rw [hc]
  have hp' : (0:ℤ)<(6^(A+B+14)*d:ℕ) := by exact_mod_cast hp
  refine ⟨by omega,Int.odd_iff.mpr (by omega),by omega,?_⟩
  exact even_iff_two_dvd.mpr ⟨3*((6^(A+B+14)*d:ℕ):ℤ),by ring⟩

lemma label_depths (A B d : ℕ) (hd : d≠0) :
    A+B+15≤padicValInt 2 (scalarLabel A B d-1) ∧
    A+B+15≤padicValInt 3 (scalarLabel A B d-1) := by
  have h2 : padicValNat 2 6=1 := by
    rw [show (6:ℕ)=2*3 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,padicValNat_primes (by decide : 2≠3)]
    norm_num
  have h3 : padicValNat 3 6=1 := by
    rw [show (6:ℕ)=3*2 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,padicValNat_primes (by decide : 3≠2)]
    norm_num
  have he : scalarLabel A B d-1=((6^(A+B+15)*d:ℕ):ℤ) := by simp [scalarLabel]
  rw [he,padicValInt.of_nat,padicValInt.of_nat,
    padicValNat.mul (by positivity : (6:ℕ)^(A+B+15)≠0) hd,
    padicValNat.mul (by positivity : (6:ℕ)^(A+B+15)≠0) hd,
    padicValNat.pow,padicValNat.pow,h2,h3]
  omega

/-- Additional fixed divisibility and an arbitrary size lower bound can be
imposed before the labels and real region are chosen. -/
theorem label_arbitrarily_divisible (A B M N : ℕ) (hM : 0<M) :
    ∃ d : ℕ, d≠0 ∧ (M:ℤ)∣scalarLabel A B d-1 ∧ (N:ℤ)<scalarLabel A B d := by
  let d := M*(N+1)
  have hd : 0<d := Nat.mul_pos hM (by omega)
  have hcoefpos : (0:ℕ)<6^(A+B+15) := by positivity
  have hcoef : (1:ℕ)≤6^(A+B+15) := by omega
  have hNd : N<d := by dsimp [d]; nlinarith
  have hsize : N<1+6^(A+B+15)*d := by nlinarith
  refine ⟨d,ne_of_gt hd,?_,?_⟩
  · refine ⟨((6^(A+B+15)*(N+1):ℕ):ℤ),?_⟩
    dsimp [scalarLabel,d]
    push_cast
    ring
  · dsimp [scalarLabel]
    exact_mod_cast hsize

/-- Exact adjustable preparation, using the actual common and scalar leaves. -/
theorem actual_units (a : ℤ) (labels : Fin 4 → ℤ) (A B d h : ℕ)
    (hA : 6≤A) (hd : d≠0) (hl : labels 1=scalarLabel A B d)
    (hc : Nat.ModEq (modulus A B) h (residue A B)) :
    padicValRat 2 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 ∧
    padicValRat 3 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 := by
  obtain ⟨hh,_,heven,h2,h3⟩ := common_depths A B h hA hc
  obtain ⟨hs,_,_,hseven⟩ := label_domains A B d hd
  obtain ⟨s2,s3⟩ := label_depths A B d hd
  rw [←hl] at hs hseven s2 s3
  have hh' : (h:ℤ)≠0 := by exact_mod_cast hh
  exact ⟨unit_two a labels (h:ℤ) hh' (by omega) (by omega) (by omega),
    unit_three a labels (h:ℤ) hh' heven (by omega) (by omega) hseven (by omega)⟩

end ScalarPreparedResidues318
