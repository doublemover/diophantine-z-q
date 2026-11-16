module
public import ActualOrderPrimeTrace318
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public section
noncomputable section
namespace SelectedRayEmbeddings318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
set_option maxHeartbeats 1000000

/-- The original rational ray already produces a genuine Qp root of2.
Quadratic reciprocity supplies a residue root; Hensel lifts it with unit
2*u derivative. No Gaussian orientation is chosen by this existence proof. -/
theorem square_root (p : ℕ) [Fact p.Prime] (hmod : p%8=1) :
    ∃ rho : ℚ_[p], rho^2=2 := by
  have hp2 : p≠2 := by intro he; subst p; norm_num at hmod
  have hp3 : 3≤p := by have he := (Fact.out : p.Prime).two_le; omega
  obtain ⟨z,hz⟩ := (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hmod)
  have hzsq : z^2=(2:ZMod p) := by simpa only [pow_two] using hz.symm
  have htwo : (2:ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp he
    have hb := Nat.le_of_dvd (by norm_num : 0<2) hd
    omega
  have hz0 : z≠0 := by intro he; rw [he,zero_pow (by decide : (2:ℕ)≠0)] at hzsq; exact htwo hzsq.symm
  have hnpos : 0<z.val := ZMod.val_pos.mpr hz0
  have hnlt : z.val<p := ZMod.val_lt z
  have hd : (p:ℤ)∣(z.val:ℤ)^2-2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast,
      ZMod.natCast_zmod_val,sub_eq_zero] using hzsq
  have hnear : ‖(z.val:ℤ_[p])^2-2‖<1 := by
    have he := (PadicInt.norm_intCast_lt_one_iff (p:=p)).mpr hd
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast] using he
  have hnunit : ‖(z.val:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt hnlt) (Nat.le_of_dvd hnpos h)))
  have h2unit : ‖(2:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.mpr
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
      (by omega : ¬p≤2) (Nat.le_of_dvd (by norm_num : 0<2) h)))
  have hsquare : IsSquare (2:ℤ_[p]) := ScalarLocalSquares318.square_of_near_square p (z.val:ℤ_[p]) 2 (by
    simpa only [norm_mul,h2unit,hnunit,mul_one,one_pow] using hnear)
  obtain ⟨rho,hr⟩ := hsquare
  refine ⟨(rho:ℚ_[p]),?_⟩
  have he : rho^2=(2:ℤ_[p]) := by simpa only [pow_two] using hr.symm
  exact_mod_cast he

lemma ray_mod_eight (z : ℤ) (hz : 0<z) (hray : (408:ℤ)∣z-1) : z.natAbs%8=1 := by
  obtain ⟨k,hk⟩ := hray
  have hpz : (z.natAbs:ℤ)=z := by rw [Int.natCast_natAbs,abs_of_pos hz]
  have he : (z.natAbs:ℤ)%8=1 := by omega
  exact_mod_cast he

variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hp : Values C u w)

@[expose] def roots (hray : ∀ k∈coefficients C, (408:ℤ)∣value u w k-1) : Roots C u w hp :=
  fun i =>
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
    let hroot := square_root p (ray_mod_eight _ (row_pos C u w hp i.1 i.2)
      (hray _ (coefficient_mem C i)))
    ⟨hroot.choose,hroot.choose_spec⟩

/-- All choices of primary embedding remain available. The opposite is
always its negative, never an independently chosen local embedding. -/
@[expose] def oriented (r : Roots C u w hp) (s : Fin 3 × Fin 5 → Bool) : Roots C u w hp :=
  fun i =>
    let p := (row C u w i.1 i.2).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
    if s i then ⟨-(r i).val,by simpa only [neg_sq] using (r i).property⟩ else r i

/-- The sign parametrization covers every possible actual root assignment;
using the constructed ray roots does not silently constrain CM orientation. -/
theorem all_orientations (r t : Roots C u w hp) :
    ∃ s : Fin 3 × Fin 5 → Bool, oriented C u w hp r s=t := by
  classical
  let s : Fin 3 × Fin 5 → Bool := fun i => decide ((t i).val≠(r i).val)
  refine ⟨s,?_⟩
  funext i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  apply Subtype.ext
  have he : (t i).val=(r i).val ∨ (t i).val= -(r i).val :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((t i).property.trans (r i).property.symm)
  by_cases ht : (t i).val=(r i).val
  · simpa [oriented,s,ht]
  · simpa [oriented,s,ht] using (he.resolve_left ht).symm

/-- Both actual positive lcm moduli are now produced from the original ray,
with arbitrary retained orientation signs and no root-existence premise. -/
theorem actual_orders (hray : ∀ k∈coefficients C, (408:ℤ)∣value u w k-1)
    (s : Fin 3 × Fin 5 → Bool) :
    let r := oriented C u w hp (roots C u w hp hray) s
    0<minus C u w hp r ∧ 0<plus C u w hp r ∧
      SelectedTraceFromOrders318.Orders C u w hp (minus C u w hp r) (plus C u w hp r) := by
  dsimp only
  exact ⟨(positive C u w hp _).1,(positive C u w hp _).2,orders C u w hp _⟩

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Same original three-pole preparation, now with no local-root input:
the rational ray constructs every root, while the orientation bits retain
all possible primary choices. Actual simultaneous CRT feasibility and
prime-pattern existence remain separate arithmetic obligations. -/
theorem ray_preparation_family (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h₀ L : ℕ) (N₂ N₃ N₁₇ : ℤ)
    (h₂ : SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3)
    (h₃ : SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1)
    (h₁₇ : SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2) :
    ∃ Q : ℕ, 0<Q ∧ ∀ u w : ℤ, ∀ hp : Values C u w,
      (Q:ℤ)∣w → ∀ hray : (∀ k∈coefficients C, (408:ℤ)∣value u w k-1),
      (∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs) →
      ∀ s : Fin 3 × Fin 5 → Bool,
      let r := oriented C u w hp (roots C u w hp hray) s
      ∀ h : ℕ,
      Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*minus C u w hp r) h 0 →
      Nat.ModEq (plus C u w hp r) h 1 → Nat.ModEq L h h₀ →
      (h:ℤ)≠0 → (h:ℤ)≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) →
      (∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ)
        (parameter C u w) (190+51*j.val) ∧
        ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) (parameter C u w) (190+51*j.val)<17) →
      ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) (parameter C u w) := by
  obtain ⟨Q,hQ,hfamily⟩ := ActualOrderPrimeTrace318.preparation_family C a hn hbeta hlucas
    h₀ L N₂ N₃ N₁₇ h₂ h₃ h₁₇
  refine ⟨Q,hQ,?_⟩
  intro u w hp hw hray hlarge s
  exact hfamily u w hp hw hray hlarge (oriented C u w hp (roots C u w hp hray) s)

end SelectedRayEmbeddings318
