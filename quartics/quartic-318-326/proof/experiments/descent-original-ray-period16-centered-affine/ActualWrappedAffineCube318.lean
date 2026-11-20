module
public import ActualRayPeriod16Interface318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualWrappedAffineCube318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayCubePeriod16318
open ActualRayPeriod16Interface318

abbrev V (a : ℕ) := Fin a → Bool
abbrev Z (n a J : ℕ) := Fin n × ((Fin a → Fin J) × (Fin a → Fin J))
abbrev Wrap (a : ℕ) := V a → Fin (2*a+1)

@[expose] def base {n a J : ℕ} (z : Z n a J) : ℤ := (z.1.val:ℤ)+1
@[expose] def diff {n a J : ℕ} (z : Z n a J) (j : Fin a) : ℤ :=
  ((z.2.1 j).val:ℤ)-((z.2.2 j).val:ℤ)
@[expose] def input {n a J : ℕ} (q : ℕ) (z : Z n a J) (ω : V a) : ℤ :=
  base z+(q:ℤ)*∑ j : Fin a, if ω j then diff z j else 0

@[expose] def signedWrap {n a J : ℕ} (q : ℕ) (z : Z n a J) (ω : V a) : ℤ :=
  (input q z ω-1)/(n:ℤ)

theorem signedWrap_bounds {n a q J : ℕ} (hn : 0<n) (hqJ : q*J≤n)
    (z : Z n a J) (ω : V a) :
    -(a:ℤ)≤signedWrap q z ω ∧ signedWrap q z ω≤(a:ℤ) := by
  have hn' : (0:ℤ)<(n:ℤ) := by exact_mod_cast hn
  have hq : (0:ℤ)≤(q:ℤ) := by positivity
  have hqJ' : (q:ℤ)*(J:ℤ)≤(n:ℤ) := by exact_mod_cast hqJ
  let s : ℤ := ∑ j : Fin a, if ω j then diff z j else 0
  have hj (j : Fin a) : -(J:ℤ) ≤ (if ω j then diff z j else 0) ∧
      (if ω j then diff z j else 0) ≤ (J:ℤ) := by
    have h₁ : ((z.2.1 j).val:ℤ)<(J:ℤ) := by exact_mod_cast (z.2.1 j).isLt
    have h₂ : ((z.2.2 j).val:ℤ)<(J:ℤ) := by exact_mod_cast (z.2.2 j).isLt
    split <;> simp only [diff] <;> omega
  have hs₁ : (a:ℤ)*(-(J:ℤ))≤s := by
    simpa only [s,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin a))) (fun j _ => (hj j).1))
  have hs₂ : s≤(a:ℤ)*(J:ℤ) := by
    simpa only [s,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin a))) (fun j _ => (hj j).2))
  have h₁ := mul_le_mul_of_nonneg_left hs₁ hq
  have h₂ := mul_le_mul_of_nonneg_left hs₂ hq
  have h₃ := mul_le_mul_of_nonneg_left hqJ' (show (0:ℤ)≤(a:ℤ) by positivity)
  have hlow : -((a:ℤ)*(n:ℤ))≤(q:ℤ)*s := by
    calc
      _ ≤ -((a:ℤ)*((q:ℤ)*(J:ℤ))) := neg_le_neg h₃
      _ = (q:ℤ)*((a:ℤ)*(-(J:ℤ))) := by ring
      _ ≤ _ := h₁
  have hhigh : (q:ℤ)*s≤(a:ℤ)*(n:ℤ) := by
    calc
      _ ≤ (q:ℤ)*((a:ℤ)*(J:ℤ)) := h₂
      _ = (a:ℤ)*((q:ℤ)*(J:ℤ)) := by ring
      _ ≤ _ := h₃
  have hx : (z.1.val:ℤ)<(n:ℤ) := by exact_mod_cast z.1.isLt
  constructor
  · refine (Int.le_ediv_iff_mul_le hn').2 ?_
    change -(a:ℤ)*(n:ℤ)≤base z+(q:ℤ)*s-1
    rw [neg_mul]
    unfold base
    omega
  · apply (Int.le_iff_lt_add_one).2
    refine (Int.ediv_lt_iff_lt_mul hn').2 ?_
    change base z+(q:ℤ)*s-1<((a:ℤ)+1)*(n:ℤ)
    rw [add_mul,one_mul]
    unfold base
    omega

def code {n a q J : ℕ} (hn : 0<n) (hqJ : q*J≤n) (z : Z n a J) : Wrap a :=
  fun ω => ⟨(signedWrap q z ω+(a:ℤ)).toNat, by
    have hb := signedWrap_bounds hn hqJ z ω
    omega⟩

@[expose] def decode {a : ℕ} (w : Wrap a) (ω : V a) : ℤ := (w ω).val-(a:ℤ)

theorem decode_code {n a q J : ℕ} (hn : 0<n) (hqJ : q*J≤n)
    (z : Z n a J) (ω : V a) : decode (code hn hqJ z) ω=signedWrap q z ω := by
  have hb := (signedWrap_bounds hn hqJ z ω).1
  change (((signedWrap q z ω+(a:ℤ)).toNat:ℕ):ℤ)-(a:ℤ)=_
  rw [Int.toNat_of_nonneg (by omega)]
  omega

theorem wrap_card (a : ℕ) : Fintype.card (Wrap a)=(2*a+1)^(2^a) := by
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]

@[expose] def raw (r : Row) (i : ℕ) (z : ℤ) : ℤ :=
  (r.W:ℤ)*rep r.n z+residue r i

theorem raw_on_wrap {r : Row} {i a q J : ℕ} (z : Z r.n a J)
    (ω : V a) (m : ℤ) (hm : signedWrap q z ω=m) :
    raw r i (input q z ω)=
      vertex r.n q r.W (residue r i) m (base z) (diff z) ω := by
  have he := Int.mul_ediv_add_emod (input q z ω-1) (r.n:ℤ)
  change (r.n:ℤ)*signedWrap q z ω+(input q z ω-1)%(r.n:ℤ)=input q z ω-1 at he
  have he' : rep r.n (input q z ω)=input q z ω-m*(r.n:ℤ) := by
    rw [hm,mul_comm (r.n:ℤ) m] at he
    unfold rep
    linarith only [he]
  rw [raw,he'] <;> rfl

/-- The actual finite FT cell; inactive points vanish in the centered
sum before the hybrid expansion, and no a priori fictitious μ is used. -/
def active {a q J : ℕ} (r : Row) (i : ℕ) : Finset (Z r.n a J) :=
  Finset.univ.filter fun z => ∀ ω : V a, (raw r i (input q z ω))%32=17

def cell {r : Row} {i a q J : ℕ} (hn : 0<r.n) (hqJ : q*J≤r.n) (w : Wrap a) :
    Finset (Z r.n a J) := (active (a:=a) (q:=q) (J:=J) r i).filter
      fun z => code hn hqJ z=w

theorem cell_raw {r : Row} {i a q J : ℕ} {hn : 0<r.n} {hqJ : q*J≤r.n}
    {w : Wrap a} {z : Z r.n a J} (hz : z∈cell (i:=i) hn hqJ w) (ω : V a) :
    raw r i (input q z ω)=vertex r.n q r.W (residue r i) (decode w ω)
      (base z) (diff z) ω := by
  apply raw_on_wrap
  rw [← (Finset.mem_filter.mp hz).2]
  exact (decode_code hn hqJ z ω).symm

theorem cell_one_residue {r : Row} {i a q J V₀ : ℕ} {hn : 0<r.n} {hqJ : q*J≤r.n}
    (hW : r.W=2*V₀) (hV : V₀.Coprime 2) {w : Wrap a} {z z₀ : Z r.n a J}
    (hz : z∈cell (i:=i) hn hqJ w) (hz₀ : z₀∈cell (i:=i) hn hqJ w) :
    base z ≡ base z₀ [ZMOD 16] ∧
      ∀ j, diff z j ≡ diff z₀ j [ZMOD (axisPeriod q:ℤ)] := by
  let zero : V a := fun _ => false
  let one (j : Fin a) : V a := fun k => decide (k=j)
  have ha {x : Z r.n a J} (hx : x∈cell (i:=i) hn hqJ w) (ω : V a) :
      vertex r.n q (2*V₀) (residue r i) (decode w ω) (base x) (diff x) ω
        ≡ (17:ℤ) [ZMOD 32] := by
    have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2 ω
    rw [cell_raw hx ω,hW] at h
    change _ % 32 = 17 % 32
    simpa only [show (17:ℤ)%32=17 by decide] using h
  have hzero {x : Z r.n a J} (hx : x∈cell (i:=i) hn hqJ w) :
      ((2*V₀:ℕ):ℤ)*(base x-decode w zero*(r.n:ℤ))+residue r i
        ≡ (17:ℤ) [ZMOD 32] := by
    simpa only [vertex,zero,Bool.false_eq_true,if_false,Finset.sum_const_zero,mul_zero,add_zero]
      using ha hx zero
  have hone {x : Z r.n a J} (hx : x∈cell (i:=i) hn hqJ w) (j : Fin a) :
      ((2*V₀:ℕ):ℤ)*(base x+(q:ℤ)*diff x j-decode w (one j)*(r.n:ℤ))+residue r i
        ≡ (17:ℤ) [ZMOD 32] := by
    have hs : (∑ k : Fin a, if one j k then diff x k else 0)=diff x j := by
      classical
      rw [Finset.sum_eq_single j]
      · simp [one]
      · intro k _ hkj
        simp [one,hkj]
      · simp
    simpa only [vertex,hs] using ha hx (one j)
  exact surviving_cell_unique V₀ q r.n hV (residue r i) (decode w zero)
    (base z) (base z₀) (fun j => decode w (one j)) (diff z) (diff z₀)
    (hzero hz) (hzero hz₀) (hone hz) (hone hz₀)

theorem cell_same_mean {r : Row} {i a q J V₀ F : ℕ} {hn : 0<r.n} {hqJ : q*J≤r.n}
    (hW : r.W=2*V₀) (hV : V₀.Coprime 2) (hF : F∣r.W*16) (μ : ℤ→ℝ)
    (hμ : ∀ p,r.mu p=μ (p%(F:ℤ))) {w : Wrap a} {z z₀ : Z r.n a J}
    (hz : z∈cell (i:=i) hn hqJ w) (hz₀ : z₀∈cell (i:=i) hn hqJ w) (ω : V a) :
    r.mu (raw r i (input q z ω))=r.mu (raw r i (input q z₀ ω)) := by
  obtain ⟨hx,ht⟩ := cell_one_residue hW hV hz hz₀
  simpa only [hμ,cell_raw hz ω,cell_raw hz₀ ω] using
    vertex_same_mean hF μ (residue r i) (decode w ω) (base z) (base z₀)
      (diff z) (diff z₀) ω hx ht

/-- Given one active point, the entire FT cell is *exactly* its
one lattice class intersected with the usual convex wrapping strips.
The ancestral variables h,h' have not been removed from the carrier. -/
theorem cell_iff_strips_lattice {r : Row} {i a q J V₀ : ℕ}
    {hn : 0<r.n} {hqJ : q*J≤r.n} (hW : r.W=2*V₀) (hV : V₀.Coprime 2)
    {w : Wrap a} {z z₀ : Z r.n a J} (hz₀ : z₀∈cell (i:=i) hn hqJ w) :
    z∈cell (i:=i) hn hqJ w ↔
      (base z≡base z₀ [ZMOD 16]) ∧
      (∀ j,diff z j≡diff z₀ j [ZMOD (axisPeriod q:ℤ)]) ∧
      (∀ ω : V a,1≤input q z ω-decode w ω*(r.n:ℤ) ∧
        input q z ω-decode w ω*(r.n:ℤ)≤(r.n:ℤ)) := by
  have hn' : (0:ℤ)<(r.n:ℤ) := by exact_mod_cast hn
  have hstrip (ω : V a) : signedWrap q z ω=decode w ω ↔
      1≤input q z ω-decode w ω*(r.n:ℤ) ∧
        input q z ω-decode w ω*(r.n:ℤ)≤(r.n:ℤ) := by
    rw [signedWrap,Int.ediv_eq_iff_of_pos hn']
    omega
  constructor
  · intro hz
    obtain ⟨hx,ht⟩ := cell_one_residue hW hV hz hz₀
    exact ⟨hx,ht,fun ω => (hstrip ω).1
      ((decode_code hn hqJ z ω).symm.trans
        (congrArg (fun u => decode u ω) (Finset.mem_filter.mp hz).2))⟩
  · rintro ⟨hx,ht,hs⟩
    have hw : ∀ ω, signedWrap q z ω=decode w ω := fun ω => (hstrip ω).2 (hs ω)
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun ω => ?_⟩
      have hd : 32∣r.W*16 := by
        refine ⟨V₀,?_⟩
        rw [hW]
        ring
      have hh := vertex_same_conductor hd (residue r i) (decode w ω)
        (base z) (base z₀) (diff z) (diff z₀) ω hx ht
      rw [←raw_on_wrap z ω _ (hw ω),←cell_raw hz₀ ω] at hh
      exact hh.trans ((Finset.mem_filter.mp (Finset.mem_filter.mp hz₀).1).2 ω)
    · funext ω
      apply Fin.ext
      have hh := (decode_code hn hqJ z ω).trans (hw ω)
      unfold decode at hh
      have hv : ((code hn hqJ z ω).val:ℤ)=((w ω).val:ℤ) := by omega
      exact_mod_cast hv

end ActualWrappedAffineCube318
