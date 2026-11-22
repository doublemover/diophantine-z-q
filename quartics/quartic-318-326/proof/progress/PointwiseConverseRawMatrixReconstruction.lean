module
public import PointwiseConverseRawMatrixReceiver
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Basic

public section
noncomputable section

open Filter
open PointwiseConverseRawMatrixReceiver

namespace PointwiseConverseRawMatrixReconstruction

abbrev SeriesPacket (S : Shape) : Type :=
  (m : Fin S.slots) → Fin (S.rows m) → Fin (S.cols m) → PowerSeries (PadicInt 2)

/-- The exact diagonal finite cut: keep degrees < r, reduce each coefficient
modulo 2^r. In particular r = 0 is the empty packet with modulus 1. -/
def cut (S : Shape) (r : ℕ) (A : SeriesPacket S) : Packet S r :=
  fun m a b d => PadicInt.toZModPow r (PowerSeries.coeff d.val (A m a b))

private theorem coeff_reduce_toZModPow {r s : ℕ} (h : r ≤ s) (x : PadicInt 2) :
    residueReduce h (PadicInt.toZModPow s x) = PadicInt.toZModPow r x := by
  have hc : (residueReduce h).comp (PadicInt.toZModPow (p := 2) s) =
      PadicInt.toZModPow (p := 2) r :=
    PadicInt.zmod_cast_comp_toZModPow r s h
  exact congrArg (fun f : PadicInt 2 →+* ZMod (modulus r) => f x) hc

theorem reduce_cut (S : Shape) {r s : ℕ} (h : r ≤ s) (A : SeriesPacket S) :
    reduce S h (cut S s A) = cut S r A := by
  funext m a b d
  exact coeff_reduce_toZModPow h (PowerSeries.coeff d.val (A m a b))

/-- Adjacent compatibility gives compatibility for every reduction. -/
theorem reduce_compatible (S : Shape) (W : ∀ r, Packet S r)
    (hW : ∀ r, reduce S (Nat.le_succ r) (W (r + 1)) = W r)
    (r s : ℕ) : ∀ h : r ≤ s, reduce S h (W s) = W r := by
  induction s with
  | zero =>
      intro h
      have hr : r = 0 := Nat.eq_zero_of_le_zero h
      subst r
      exact reduce_refl S 0 (W 0)
  | succ s ih =>
      intro h
      by_cases he : r = s + 1
      · subst r
        exact reduce_refl S (s + 1) (W (s + 1))
      · have hk : r ≤ s := Nat.le_of_lt_succ (lt_of_le_of_ne h he)
        calc
          reduce S h (W (s + 1)) =
              reduce S hk (reduce S (Nat.le_succ s) (W (s + 1))) :=
            (reduce_comp S hk (Nat.le_succ s) (W (s + 1))).symm
          _ = reduce S hk (W s) := congrArg (reduce S hk) (hW s)
          _ = W r := ih hk

private def coeffResidue (S : Shape) (W : ∀ r, Packet S r)
    (m : Fin S.slots) (a : Fin (S.rows m)) (b : Fin (S.cols m))
    (d n : ℕ) : ZMod (modulus n) :=
  residueReduce (le_max_left n (d + 1))
    (W (max n (d + 1)) m a b
      ⟨d, lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_right n (d + 1))⟩)

/-- Work at a single cut that sees both the desired coefficient and the
desired modulus. A farther cut gives the same residue. -/
private theorem coeffResidue_from (S : Shape) (W : ∀ r, Packet S r)
    (hW : ∀ r, reduce S (Nat.le_succ r) (W (r + 1)) = W r)
    (m : Fin S.slots) (a : Fin (S.rows m)) (b : Fin (S.cols m))
    (d n s : ℕ) (hn : n ≤ s) (hd : d < s) :
    coeffResidue S W m a b d n = residueReduce hn (W s m a b ⟨d, hd⟩) := by
  have hk : max n (d + 1) ≤ s := max_le hn (Nat.succ_le_of_lt hd)
  have hstage := reduce_compatible S W hW (max n (d + 1)) s hk
  have hc :
      (residueReduce (le_max_left n (d + 1))).comp (residueReduce hk) =
        residueReduce hn :=
    ZMod.castHom_comp (modulus_dvd (le_max_left n (d + 1))) (modulus_dvd hk)
  unfold coeffResidue
  rw [← hstage]
  exact congrArg (fun f : ZMod (modulus s) →+* ZMod (modulus n) =>
    f (W s m a b ⟨d, hd⟩)) hc

private theorem coeffResidue_step (S : Shape) (W : ∀ r, Packet S r)
    (hW : ∀ r, reduce S (Nat.le_succ r) (W (r + 1)) = W r)
    (m : Fin S.slots) (a : Fin (S.rows m)) (b : Fin (S.cols m))
    (d n : ℕ) :
    residueReduce (Nat.le_succ n) (coeffResidue S W m a b d (n + 1)) =
      coeffResidue S W m a b d n := by
  let s := max (n + 1) (d + 1)
  have hnext : n + 1 ≤ s := le_max_left _ _
  have hn : n ≤ s := (Nat.le_succ n).trans hnext
  have hd : d < s := lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_right _ _)
  rw [coeffResidue_from S W hW m a b d (n + 1) s hnext hd,
    coeffResidue_from S W hW m a b d n s hn hd]
  have hc : (residueReduce (Nat.le_succ n)).comp (residueReduce hnext) =
      residueReduce hn :=
    ZMod.castHom_comp (modulus_dvd (Nat.le_succ n)) (modulus_dvd hnext)
  exact congrArg (fun f : ZMod (modulus s) →+* ZMod (modulus n) =>
    f (W s m a b ⟨d, hd⟩)) hc

private def integerLift (v : ∀ n, ZMod (modulus n)) (n : ℕ) : ℤ :=
  ZMod.cast (v n)

private theorem integerLift_spec (v : ∀ n, ZMod (modulus n)) (n : ℕ) :
    (integerLift v n : ZMod (modulus n)) = v n :=
  ZMod.intCast_zmod_cast _

private theorem integerLift_step (v : ∀ n, ZMod (modulus n))
    (hv : ∀ n, residueReduce (Nat.le_succ n) (v (n + 1)) = v n) (n : ℕ) :
    (2 : ℤ) ^ n ∣ integerLift v (n + 1) - integerLift v n := by
  let f := residueReduce (Nat.le_succ n)
  have hh : (integerLift v n : ZMod (modulus n)) = integerLift v (n + 1) := by
    calc
      _ = v n := integerLift_spec v n
      _ = f (v (n + 1)) := (hv n).symm
      _ = f (integerLift v (n + 1) : ZMod (modulus (n + 1))) :=
        congrArg (fun z => f z) (integerLift_spec v (n + 1)).symm
      _ = _ := map_intCast f _
  have hk := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (modulus n)).mp hh
  simpa only [modulus, Nat.cast_pow, Nat.cast_ofNat] using hk

private def liftResidues (v : ∀ n, ZMod (modulus n))
    (hv : ∀ n, residueReduce (Nat.le_succ n) (v (n + 1)) = v n) : PadicInt 2 :=
  PadicInt.ofIntSeq (integerLift v)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (integerLift v) 2 (integerLift_step v hv))

private theorem liftResidues_spec (v : ∀ n, ZMod (modulus n))
    (hv : ∀ n, residueReduce (Nat.le_succ n) (v (n + 1)) = v n) (n : ℕ) :
    PadicInt.toZModPow n (liftResidues v hv) = v n :=
  (PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
    (integerLift v) 2 (integerLift_step v hv) n).trans (integerLift_spec v n)

/-- Reconstruct one power series per matrix entry from the actual compatible
finite matrices, not merely from pointwise existence of limits. -/
def reconstruct (S : Shape) (W : ∀ r, Packet S r)
    (hW : ∀ r, reduce S (Nat.le_succ r) (W (r + 1)) = W r) : SeriesPacket S :=
  fun m a b => PowerSeries.mk (fun d =>
    liftResidues (coeffResidue S W m a b d) (coeffResidue_step S W hW m a b d))

/-- Every finite cut is recovered, not just a tail or an eventual equality. -/
theorem reconstruct_cut (S : Shape) (W : ∀ r, Packet S r)
    (hW : ∀ r, reduce S (Nat.le_succ r) (W (r + 1)) = W r) (r : ℕ) :
    cut S r (reconstruct S W hW) = W r := by
  funext m a b d
  simp only [cut, reconstruct, PowerSeries.coeff_mk, liftResidues_spec]
  rw [coeffResidue_from S W hW m a b d.val r r (le_refl r) d.isLt]
  have hc : residueReduce (le_refl r) = RingHom.id (ZMod (modulus r)) :=
    Subsingleton.elim _ _
  exact congrArg (fun f : ZMod (modulus r) →+* ZMod (modulus r) =>
    f (W r m a b d)) hc

/-- Agreement on every diagonal cut separates the reconstructed series. -/
theorem cut_injective (S : Shape) (A B : SeriesPacket S)
    (h : ∀ r, cut S r A = cut S r B) : A = B := by
  funext m a b
  apply PowerSeries.ext
  intro d
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  let s := max n (d + 1)
  have hn : n ≤ s := le_max_left _ _
  have hd : d < s := lt_of_lt_of_le (Nat.lt_succ_self d) (le_max_right _ _)
  have hh : PadicInt.toZModPow s (PowerSeries.coeff d (A m a b)) =
      PadicInt.toZModPow s (PowerSeries.coeff d (B m a b)) :=
    congrFun (congrFun (congrFun (congrFun (h s) m) a) b) (⟨d, hd⟩ : Fin s)
  rw [← coeff_reduce_toZModPow hn, ← coeff_reduce_toZModPow hn, hh]

/-- Source-only consumer: one cofinal ultrafilter gives one whole matrix
packet over ℤ₂[[t]], with the stated finite cuts. -/
theorem existsUnique_stabilized_series (S : Shape) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (stage : (i : ℕ) → Packet S i) :
    ∃! A : SeriesPacket S, ∀ r, ∀ᶠ i in (U : Filter ℕ), row S stage r i = cut S r A := by
  obtain ⟨W, hW, hUnique⟩ := existsUnique_compatible_packets S U hU stage
  refine ⟨reconstruct S W hW.2, ?_, ?_⟩
  · intro r
    rw [reconstruct_cut]
    exact hW.1 r
  · intro B hB
    have he : (fun r => cut S r B) = W :=
      hUnique _ ⟨hB, fun r => reduce_cut S (Nat.le_succ r) B⟩
    apply cut_injective S
    intro r
    rw [reconstruct_cut]
    exact congrFun he r

end PointwiseConverseRawMatrixReconstruction
