module
public import LiteralSliceBoxCount318
public section
noncomputable section
namespace LiteralAdjacentNormSlice318
open QuadricCRTAssembly318 LiteralQuarticSlice318
open TernaryQuadraticLineCover318
set_option maxHeartbeats 1000000

@[expose] def K {F : Type*} [CommRing F] (κ t : F) (v : Vector F) : F :=
  (κ*v.2.2^2-v.1*v.2.1+t^2+2*t)^2+t^2*(v.1+v.2.1)^2
@[expose] def P {F : Type*} [CommRing F] (κ t : F) (v : Vector F) : F := κ*v.2.2^2+2*t
@[expose] def P' {F : Type*} [CommRing F] (κ t : F) (v : Vector F) : F :=
  κ*(t+2)*v.2.2^2-2*v.1*v.2.1
@[expose] def D {F : Type*} [CommRing F] (t : F) (v : Vector F) : F :=
  (t^2+v.1^2)*(t^2+v.2.1^2)
@[expose] def G (v : Coordinates ℤ) : ℤ := (v.1.1+1)^2+v.1.2^2
@[expose] def H (v : Coordinates ℤ) : ℤ := (v.2.1.1+1)^2+v.2.1.2^2

/-- Exact connection to the earlier actual Gaussian adjacent norms. -/
theorem G_original_norm (v : Coordinates ℤ) :
    G v=(GaussianNeighborNorms318.plus v.1.1 v.1.2:ℤ) := by
  rw [GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm_cast]
  rfl

theorem H_original_norm (v : Coordinates ℤ) :
    H v=(GaussianNeighborNorms318.plus v.2.1.1 v.2.1.2:ℤ) := by
  rw [GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm_cast]
  rfl

/-- Both literal source charts give the SAME scaled adjacent norm K. -/
theorem K_original (κ t : ℤ) (side : Bool) (v : Slice κ t side) :
    K κ t (project v.1.1)=4*t^2*G v.1.1 := by
  have hs := v.2
  have hR : LiteralTernaryReduction318.R κ (project v.1.1)=t*(2*v.1.1.1.1-t) := by
    rw [←factorization κ v.1]
    cases side with
    | false =>
      change x1 v.1.1=t at hs
      rw [←hs]
      dsimp [x0,x1]
      ring
    | true =>
      change x0 v.1.1=t at hs
      rw [←hs]
      dsimp [x0,x1]
      ring
  change (LiteralTernaryReduction318.R κ (project v.1.1)+t^2+2*t)^2+
    t^2*((project v.1.1).1+(project v.1.1).2.1)^2=4*t^2*G v.1.1
  rw [hR]
  dsimp [project,G]
  ring

theorem P_original (κ t : ℤ) (v : Slice κ t false) :
    P κ t (project v.1.1)=G v.1.1-H v.1.1 := by
  have hQ := v.1.2
  have hs := v.2
  change x1 v.1.1=t at hs
  dsimp [equation] at hQ
  dsimp [x1] at hs
  dsimp [P,project,G,H]
  linear_combination -hQ-2*hs

theorem P'_original (κ t : ℤ) (v : Slice κ t true) :
    P' κ t (project v.1.1)=t*(G v.1.1-H v.1.1) := by
  have hQ := v.1.2
  have hs := v.2
  change x0 v.1.1=t at hs
  rw [←hs]
  dsimp [equation] at hQ
  dsimp [P',project,x0,G,H]
  linear_combination -(v.1.1.1.1+v.1.1.2.1.1+2)*hQ

/-- Literal polynomial identity, not a replacement congruence assumed by
an arithmetic or geometric sieve consumer. -/
theorem K_difference {F : Type*} [CommRing F] (κ t : F) (v : Vector F) :
    K κ t v-D t v=P κ t v*(P κ t v+2*t^2-2*v.1*v.2.1) := by
  dsimp [K,D,P]
  ring

lemma prime_cancel (p : ℕ) [Fact p.Prime] (a n : ℤ) (ha : ¬(p:ℤ)∣a) :
    (p:ℤ)∣a*n ↔ (p:ℤ)∣n := by
  have ha' : (a:ZMod p)≠0 := by
    intro hh
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hh)
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_mul,mul_eq_zero,ha',false_or]

lemma scale_nonzero (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (t : ℤ) (ht : ¬(p:ℤ)∣t) :
    ¬(p:ℤ)∣4*t^2 := by
  have ht' : (t:ZMod p)≠0 := by
    intro hh
    exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp hh)
  intro hh
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (4*t^2) p).mpr hh
  have h2 := GoodReductionResidue318.two_residue_ne p hp2
  have hn : (4:ZMod p)≠0 := by
    have he : (4:ZMod p)=2*2 := by norm_num
    rw [he]
    exact mul_ne_zero h2 h2
  exact (mul_ne_zero hn (pow_ne_zero 2 ht')) (by simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow] using hz)

lemma pair_cancel (p : ℕ) [Fact p.Prime] (a b g h f k : ℤ)
    (ha : ¬(p:ℤ)∣a) (hb : ¬(p:ℤ)∣b) (hf : f=a*(g-h)) (hk : k=b*g) :
    ((p:ℤ)∣g ∧ (p:ℤ)∣h) ↔ ((p:ℤ)∣f ∧ (p:ℤ)∣k) := by
  rw [hf,hk,prime_cancel p a (g-h) ha,prime_cancel p b g hb]
  constructor
  · rintro ⟨hg,hh⟩
    exact ⟨dvd_sub hg hh,hg⟩
  · rintro ⟨hd,hg⟩
    exact ⟨hg,by simpa only [sub_sub_cancel] using dvd_sub hg hd⟩

/-- Exact source congruences in the first chart, with the forbidden primes
2t excluded explicitly before any cancellation. -/
theorem first_chart_iff (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ t : ℤ) (ht : ¬(p:ℤ)∣t) (v : Slice κ t false) :
    ((p:ℤ)∣G v.1.1 ∧ (p:ℤ)∣H v.1.1) ↔
      ((p:ℤ)∣P κ t (project v.1.1) ∧ (p:ℤ)∣K κ t (project v.1.1)) := by
  apply pair_cancel p 1 (4*t^2) _ _ _ _
  · intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 p).mpr hd
    simpa using hh
  · exact scale_nonzero p hp2 t ht
  · simpa only [one_mul] using P_original κ t v
  · exact K_original κ t false v

/-- Exact source congruences in the other chart; no missing factor t. -/
theorem second_chart_iff (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ t : ℤ) (ht : ¬(p:ℤ)∣t) (v : Slice κ t true) :
    ((p:ℤ)∣G v.1.1 ∧ (p:ℤ)∣H v.1.1) ↔
      ((p:ℤ)∣P' κ t (project v.1.1) ∧ (p:ℤ)∣K κ t (project v.1.1)) :=
  pair_cancel p t (4*t^2) _ _ _ _ ht (scale_nonzero p hp2 t ht)
    (P'_original κ t v) (K_original κ t true v)

end LiteralAdjacentNormSlice318
