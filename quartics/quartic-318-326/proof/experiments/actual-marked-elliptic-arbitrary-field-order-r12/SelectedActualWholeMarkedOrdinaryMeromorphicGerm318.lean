module

public import SelectedActualLiteralComplexCompactStalkDVR318
public import SelectedActualComplexWholeRootField318
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.RingTheory.Localization.Algebra

public section
noncomputable section

open Polynomial Filter Set UpperHalfPlane
open scoped Polynomial Topology nonZeroDivisors
open SelectedComplexOrdinaryBase318
open SelectedActualComplexOrdinaryScalar318
open SelectedActualComplexWholeRootField318
open SelectedComplexOrdinaryOneField318
open SelectedActualLiteralComplexCompactStalkDVR318

namespace SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev pC := p.map (toComplex N)

abbrev OrdinaryRoot := AdjoinRoot (pC N p)

abbrev fullRootSet := Set.range (periodMap N) =
  SelectedComplexConnectedNoSplit318.roots (pC N p)

private theorem actual_period_root_eq (hRoots : fullRootSet N p) (t : Period) :
    (pC N p).eval₂ (evaluation (periodMap N t).1) (periodMap N t).2 = 0 := by
  have hr : periodMap N t ∈ SelectedComplexConnectedNoSplit318.roots (pC N p) := by
    change Set.range (periodMap N) = SelectedComplexConnectedNoSplit318.roots (pC N p) at hRoots
    rw [← hRoots]
    exact Set.mem_range_self t
  change (pC N p).eval₂ (evaluation (periodMap N t).1) (periodMap N t).2 = 0 at hr
  exact hr

/-- Evaluate the same complex monic chart at a literal original marked
period, using the original full root relation. -/
def atPeriod (hRoots : fullRootSet N p) (t : Period) :
    OrdinaryRoot N p →+* ℂ :=
  AdjoinRoot.lift (evaluation (periodMap N t).1) (periodMap N t).2
    (actual_period_root_eq N p hRoots t)

theorem atPeriod_base (hRoots : fullRootSet N p) (t : Period) (r : Base) :
    atPeriod N p hRoots t (AdjoinRoot.of (pC N p) r) =
      evaluation (periodMap N t).1 r := by
  unfold atPeriod
  exact AdjoinRoot.lift_of (actual_period_root_eq N p hRoots t)

theorem atPeriod_root (hRoots : fullRootSet N p) (t : Period) :
    atPeriod N p hRoots t (AdjoinRoot.root (pC N p)) =
      SelectedMarkedPeriodCoordinate318.arithmeticX N t.val := by
  unfold atPeriod
  change _ = (periodMap N t).2
  exact AdjoinRoot.lift_root (actual_period_root_eq N p hRoots t)

def atDisk (hRoots : fullRootSet N p) (t : Period) (z : ℂ) :
    OrdinaryRoot N p →+* ℂ := by
  classical
  exact if hz : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex z)
    then atPeriod N p hRoots ⟨UpperHalfPlane.ofComplex z,hz⟩
    else atPeriod N p hRoots t

private theorem atDisk_of_admissible (hRoots : fullRootSet N p) (t : Period) (z : ℂ)
    (hz : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex z)) :
    atDisk N p hRoots t z = atPeriod N p hRoots ⟨UpperHalfPlane.ofComplex z,hz⟩ := by
  unfold atDisk
  exact dif_pos hz

private theorem base_poly_ev (hRoots : fullRootSet N p) (t : Period) (a : ℂ[X]) :
    (fun z : ℂ => atDisk N p hRoots t z
      (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base a))) =ᶠ[𝓝 (t.val : ℂ)]
      fun z => a.eval (OpenJLocalComparison318.j z) := by
  filter_upwards [OpenJLocalComparison318.admissible_eventually t.val t.property] with z hz
  rw [atDisk_of_admissible N p hRoots t z hz,atPeriod_base]
  exact evaluation_polynomial _ a

private theorem poly_analytic (t : Period) (a : ℂ[X]) :
    AnalyticAt ℂ (fun z => a.eval (OpenJLocalComparison318.j z)) (t.val : ℂ) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => a.eval w)
      (OpenJLocalComparison318.j (t.val : ℂ)) :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) a) _ (Set.mem_univ _)
  exact ha.comp (OpenJLocalComparison318.j_analyticAt t.val)

private theorem base_eq_fraction (hRoots : fullRootSet N p) (t : Period)
    (r : Base) (a d : ℂ[X]) (hd : d ∈ Submonoid.powers denominator)
    (he : r * algebraMap ℂ[X] Base d = algebraMap ℂ[X] Base a) :
    (fun z : ℂ => atDisk N p hRoots t z (AdjoinRoot.of (pC N p) r)) =ᶠ[𝓝 (t.val : ℂ)]
      fun z => a.eval (OpenJLocalComparison318.j z) /
        d.eval (OpenJLocalComparison318.j z) := by
  filter_upwards [base_poly_ev N p hRoots t a,base_poly_ev N p hRoots t d]
    with z ha hzd
  let ev : Base →+* ℂ := (atDisk N p hRoots t z).comp (AdjoinRoot.of (pC N p))
  have hd' : ev (algebraMap ℂ[X] Base d) ≠ 0 :=
    ((IsLocalization.map_units Base (⟨d,hd⟩ : Submonoid.powers denominator)).map ev).ne_zero
  have hde : ev (algebraMap ℂ[X] Base d) =
      d.eval (OpenJLocalComparison318.j z) := hzd
  have hne : d.eval (OpenJLocalComparison318.j z) ≠ 0 := fun h => hd' (hde.trans h)
  have hmul := congrArg ev he
  rw [map_mul,hde] at hmul
  exact (eq_div_iff hne).2 (hmul.trans ha)

private theorem base_analytic (hRoots : fullRootSet N p) (t : Period) (r : Base) :
    AnalyticAt ℂ (fun z => atDisk N p hRoots t z (AdjoinRoot.of (pC N p) r)) (t.val : ℂ) := by
  obtain ⟨⟨a,d⟩,he⟩ := IsLocalization.surj (Submonoid.powers denominator) r
  have hD := base_poly_ev N p hRoots t (d : ℂ[X])
  have hdn : d.val.eval (OpenJLocalComparison318.j (t.val : ℂ)) ≠ 0 := by
    have hD₀ := hD.eq_of_nhds
    rw [← hD₀]
    exact (((IsLocalization.map_units Base d).map (AdjoinRoot.of (pC N p))).map
      (atDisk N p hRoots t (t.val : ℂ))).ne_zero
  exact ((poly_analytic t a).fun_div (poly_analytic t d.val) hdn).congr
    (base_eq_fraction N p hRoots t r a d.val d.property he).symm

private theorem root_analytic (hN : 1 < N) (hRoots : fullRootSet N p) (t : Period) :
    AnalyticAt ℂ (fun z => atDisk N p hRoots t z (AdjoinRoot.root (pC N p))) (t.val : ℂ) := by
  apply (SelectedMarkedPeriodCoordinate318.arithmeticX_analyticAt N hN t.val t.property).congr
  filter_upwards [OpenJLocalComparison318.admissible_eventually t.val t.property] with z hz
  rw [atDisk_of_admissible N p hRoots t z hz,atPeriod_root]

/-- Arbitrary complex, not just rational, chart elements have the
actual ordinary analytic evaluation. Only the original j and marked x
are differentiated, including the old localization denominator. -/
theorem ordinary_ring_analytic (hN : 1 < N) (hRoots : fullRootSet N p) (t : Period)
    (r : OrdinaryRoot N p) :
    AnalyticAt ℂ (fun z => atDisk N p hRoots t z r) (t.val : ℂ) := by
  refine AdjoinRoot.induction_on (pC N p) r fun f => ?_
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have h : (fun z => atDisk N p hRoots t z (AdjoinRoot.mk (pC N p) (f + g))) =
        (fun z => atDisk N p hRoots t z (AdjoinRoot.mk (pC N p) f) +
          atDisk N p hRoots t z (AdjoinRoot.mk (pC N p) g)) := by
      funext z
      simp only [map_add]
    rw [h]
    exact hf.fun_add hg
  | monomial n c =>
    have h : (fun z => atDisk N p hRoots t z (AdjoinRoot.mk (pC N p) (monomial n c))) =
        (fun z => atDisk N p hRoots t z (AdjoinRoot.of (pC N p) c) *
          (atDisk N p hRoots t z (AdjoinRoot.root (pC N p))) ^ n) := by
      funext z
      simp only [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
        AdjoinRoot.mk_C,AdjoinRoot.mk_X] <;> rfl
    rw [h]
    exact (base_analytic N p hRoots t c).fun_mul ((root_analytic N p hN hRoots t).fun_pow n)

/-- The ordinary marked root in the same whole generic quotient before
the checked coefficient change to the installed C(J)-root field. -/
def intoGeneric : OrdinaryRoot N p →+* AdjoinRoot (P N p) :=
  AdjoinRoot.map (algebraMap Base Generic) (pC N p) (P N p) (dvd_refl _)

private theorem intoGeneric_mk (r : Base[X]) :
    intoGeneric N p (AdjoinRoot.mk (pC N p) r) =
      AdjoinRoot.mk (P N p) (r.map (algebraMap Base Generic)) := by
  have h : (intoGeneric N p).comp (AdjoinRoot.mk (pC N p)) =
      (AdjoinRoot.mk (P N p)).comp (Polynomial.mapRingHom (algebraMap Base Generic)) := by
    apply Polynomial.ringHom_ext
    · intro c
      change AdjoinRoot.map (algebraMap Base Generic) (pC N p) (P N p)
          (dvd_refl _) (AdjoinRoot.of (pC N p) c) =
        AdjoinRoot.mk (P N p) ((Polynomial.C c).map (algebraMap Base Generic))
      rw [AdjoinRoot.map_of, Polynomial.map_C] <;> rfl
    · change AdjoinRoot.map (algebraMap Base Generic) (pC N p) (P N p)
          (dvd_refl _) (AdjoinRoot.root (pC N p)) =
        AdjoinRoot.mk (P N p) (Polynomial.X.map (algebraMap Base Generic))
      rw [AdjoinRoot.map_root, Polynomial.map_X] <;> rfl
  exact RingHom.congr_fun h r

/-- The actual installed whole field, not an injection of an arbitrarily
chosen ordinary ring into a field. -/
def intoWhole : OrdinaryRoot N p →+* K N p :=
  (wholeRootEquiv N p).toRingHom.comp (intoGeneric N p)

theorem intoWhole_injective (hp : p.Monic) : Function.Injective (intoWhole N p) := by
  letI : IsDomain Base := coefficient_domain
  have hι : Function.Injective (algebraMap Base Generic) := IsFractionRing.injective Base Generic
  have hg : Function.Injective (intoGeneric N p) := by
    apply (injective_iff_map_eq_zero' _).2
    intro u
    constructor
    · intro hu
      obtain ⟨r,rfl⟩ := AdjoinRoot.mk_surjective u
      rw [intoGeneric_mk, AdjoinRoot.mk_eq_zero] at hu
      exact AdjoinRoot.mk_eq_zero.mpr
        ((Polynomial.map_dvd_map (algebraMap Base Generic) hι (hp.map (toComplex N))).mp hu)
    · intro hu
      rw [hu,map_zero]
  exact (wholeRootEquiv N p).injective.comp hg

private theorem clear_in_generic (u : AdjoinRoot (P N p)) :
    ∃ (b : Base), b ≠ 0 ∧ ∃ r : OrdinaryRoot N p,
      u * intoGeneric N p (AdjoinRoot.of (pC N p) b) = intoGeneric N p r := by
  letI : IsDomain Base := coefficient_domain
  letI : Algebra Base[X] Generic[X] := Polynomial.algebra Base Generic
  let S : Submonoid Base[X] := (nonZeroDivisors Base).map Polynomial.C
  letI : IsLocalization S Generic[X] := Polynomial.isLocalization (nonZeroDivisors Base) Generic
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective u
  obtain ⟨⟨r,d⟩,hd⟩ := IsLocalization.surj S g
  obtain ⟨b,hb,hbd⟩ := d.property
  have hC : algebraMap Base[X] Generic[X] d.val = Polynomial.C (algebraMap Base Generic b) := by
    change d.val.map (algebraMap Base Generic) = _
    rw [← hbd, Polynomial.map_C]
  have hr : g * Polynomial.C (algebraMap Base Generic b) = r.map (algebraMap Base Generic) := by
    rw [← hC]
    exact hd
  refine ⟨b,mem_nonZeroDivisors_iff_ne_zero.mp hb,AdjoinRoot.mk (pC N p) r,?_⟩
  rw [intoGeneric_mk]
  have hOf : intoGeneric N p (AdjoinRoot.of (pC N p) b) =
      AdjoinRoot.of (P N p) (algebraMap Base Generic b) := by
    unfold intoGeneric
    exact AdjoinRoot.map_of _ _ _ _ _
  rw [hOf]
  exact (map_mul (AdjoinRoot.mk (P N p)) _ _).symm.trans
    (congrArg (AdjoinRoot.mk (P N p)) hr)

theorem clear_in_whole (h : K N p) :
    ∃ (b : Base), b ≠ 0 ∧ ∃ r : OrdinaryRoot N p,
      h * intoWhole N p (AdjoinRoot.of (pC N p) b) = intoWhole N p r := by
  let W := wholeRootEquiv N p
  obtain ⟨b,hb,r,hr⟩ := clear_in_generic N p (W.symm h)
  refine ⟨b,hb,r,?_⟩
  have hW := congrArg (fun u : AdjoinRoot (P N p) => W u) hr
  change W (W.symm h * intoGeneric N p (AdjoinRoot.of (pC N p) b)) =
    W (intoGeneric N p r) at hW
  rw [map_mul, W.apply_symm_apply] at hW
  exact hW

private theorem nonzero_poly_germ (t : Period)
    (hder : deriv OpenJLocalComparison318.j (t.val : ℂ) ≠ 0)
    (a : ℂ[X]) (ha : a ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (t.val : ℂ), a.eval (OpenJLocalComparison318.j z) ≠ 0 := by
  let T : Set ℂ := {w | a.eval w = 0}
  letI : Finite T := (Polynomial.finite_setOfPred_isRoot ha).to_subtype
  have h₂ (v : T) : ∀ᶠ z in 𝓝[≠] (t.val : ℂ), OpenJLocalComparison318.j z ≠ v.val := by
    have hv : AnalyticAt ℂ (fun z => OpenJLocalComparison318.j z - v.val) (t.val : ℂ) :=
      (OpenJLocalComparison318.j_analyticAt t.val).fun_sub analyticAt_const
    have hh := hv.eventually_eq_zero_or_eventually_ne_zero
    refine (hh.resolve_left ?_).mono fun z hz he => hz (sub_eq_zero.mpr he)
    intro hz
    have he : OpenJLocalComparison318.j =ᶠ[𝓝 (t.val : ℂ)] fun _ => v.val :=
      hz.mono fun z h => sub_eq_zero.mp h
    apply hder
    rw [he.deriv_eq,deriv_const]
  have hAll : ∀ᶠ z in 𝓝[≠] (t.val : ℂ), ∀ v : T,
      OpenJLocalComparison318.j z ≠ v.val := Filter.eventually_all.mpr h₂
  exact hAll.mono fun z h hz => h ⟨OpenJLocalComparison318.j z,hz⟩ rfl

private theorem base_nonzero_germ (hRoots : fullRootSet N p) (t : Period)
    (hder : deriv OpenJLocalComparison318.j (t.val : ℂ) ≠ 0)
    (b : Base) (hb : b ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (t.val : ℂ), atDisk N p hRoots t z (AdjoinRoot.of (pC N p) b) ≠ 0 := by
  letI : IsDomain Base := coefficient_domain
  obtain ⟨⟨a,d⟩,he⟩ := IsLocalization.surj (Submonoid.powers denominator) b
  have ha : a ≠ 0 := by
    intro haz
    rw [haz,map_zero] at he
    exact hb ((mul_eq_zero.mp he).resolve_right (IsLocalization.map_units Base d).ne_zero)
  have hFilter : 𝓝[≠] (t.val : ℂ) ≤ 𝓝 (t.val : ℂ) := nhdsWithin_le_nhds
  have hF := (base_eq_fraction N p hRoots t b a d.val d.property he).filter_mono hFilter
  have hd := poly_analytic t d.val
  have hD := base_poly_ev N p hRoots t (d : ℂ[X])
  have hdn : d.val.eval (OpenJLocalComparison318.j (t.val : ℂ)) ≠ 0 := by
    rw [← hD.eq_of_nhds]
    exact (((IsLocalization.map_units Base d).map (AdjoinRoot.of (pC N p))).map
      (atDisk N p hRoots t (t.val : ℂ))).ne_zero
  have hDe := (hd.continuousAt.eventually_ne hdn).filter_mono hFilter
  filter_upwards [hF,nonzero_poly_germ t hder a ha,hDe] with z e hA hD
  rw [e]
  exact div_ne_zero hA hD

/-- Every element of the actual installed whole marked field has a
meromorphic representative on one genuine noncritical ordinary period
disk. The denominator is eventually nonzero punctured, so this is not
a statement about a totalized zero-over-zero expression. -/
theorem whole_field_meromorphic_at (hN : 1 < N) (hRoots : fullRootSet N p)
    (t : Period) (hder : deriv OpenJLocalComparison318.j (t.val : ℂ) ≠ 0) (h : K N p) :
    ∃ (b : Base) (r : OrdinaryRoot N p),
      b ≠ 0 ∧ h * intoWhole N p (AdjoinRoot.of (pC N p) b) = intoWhole N p r ∧
      (∀ᶠ z in 𝓝[≠] (t.val : ℂ), atDisk N p hRoots t z (AdjoinRoot.of (pC N p) b) ≠ 0) ∧
      MeromorphicAt (fun z => atDisk N p hRoots t z r /
        atDisk N p hRoots t z (AdjoinRoot.of (pC N p) b)) (t.val : ℂ) := by
  obtain ⟨b,hb,r,hr⟩ := clear_in_whole N p h
  exact ⟨b,r,hb,hr,base_nonzero_germ N p hRoots t hder b hb,
    (ordinary_ring_analytic N p hN hRoots t r).meromorphicAt.fun_div
      (base_analytic N p hRoots t b).meromorphicAt⟩

/-- The above representative is canonical as a punctured germ of the
actual field element. Equality is checked in the same whole field and
reflected into the old monic ordinary ring before analytic evaluation. -/
theorem whole_field_same_germ (hp : p.Monic) (hRoots : fullRootSet N p)
    (t : Period) (hder : deriv OpenJLocalComparison318.j (t.val : ℂ) ≠ 0)
    (h : K N p) (b d : Base) (r s : OrdinaryRoot N p) (hb : b ≠ 0) (hd : d ≠ 0)
    (hr : h * intoWhole N p (AdjoinRoot.of (pC N p) b) = intoWhole N p r)
    (hs : h * intoWhole N p (AdjoinRoot.of (pC N p) d) = intoWhole N p s) :
    (fun z => atDisk N p hRoots t z r / atDisk N p hRoots t z (AdjoinRoot.of (pC N p) b)) =ᶠ[
      𝓝[≠] (t.val : ℂ)]
      (fun z => atDisk N p hRoots t z s / atDisk N p hRoots t z (AdjoinRoot.of (pC N p) d)) := by
  have he : r * AdjoinRoot.of (pC N p) d = s * AdjoinRoot.of (pC N p) b := by
    apply intoWhole_injective N p hp
    rw [map_mul,map_mul,← hr,← hs,mul_assoc,mul_assoc]
    exact congrArg (fun a : K N p => h * a) (mul_comm _ _)
  filter_upwards [base_nonzero_germ N p hRoots t hder b hb,
    base_nonzero_germ N p hRoots t hder d hd] with z hbz hdz
  apply (div_eq_div_iff hbz hdz).2
  have hez := congrArg (fun u : OrdinaryRoot N p => atDisk N p hRoots t z u) he
  simpa only [map_mul] using hez

/-- The literal chart uniformizer candidate J−J(t), not a newly
chosen local coordinate, has analytic meromorphic order one. -/
theorem ordinary_parameter_order_one (hRoots : fullRootSet N p) (t : Period)
    (hder : deriv OpenJLocalComparison318.j (t.val : ℂ) ≠ 0) :
    meromorphicOrderAt (fun z => atDisk N p hRoots t z
      (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base
        (Polynomial.X - Polynomial.C (OpenJLocalComparison318.j (t.val : ℂ)))))) (t.val : ℂ) = 1 := by
  let j₀ := OpenJLocalComparison318.j (t.val : ℂ)
  have he : (fun z => atDisk N p hRoots t z (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base
      (Polynomial.X - Polynomial.C j₀)))) =ᶠ[𝓝 (t.val : ℂ)]
      fun z => OpenJLocalComparison318.j z - j₀ := by
    filter_upwards [base_poly_ev N p hRoots t (Polynomial.X - Polynomial.C j₀)] with z hz
    exact hz.trans <|
      (Polynomial.eval_sub _ _ _).trans (congrArg₂ (· - ·) Polynomial.eval_X Polynomial.eval_C)
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  have hj := OpenJLocalComparison318.j_analyticAt t.val
  have hs : AnalyticAt ℂ (fun z => OpenJLocalComparison318.j z - j₀) (t.val : ℂ) :=
    hj.fun_sub analyticAt_const
  have ho : analyticOrderAt (fun z => OpenJLocalComparison318.j z - j₀) (t.val : ℂ) = 1 :=
    hj.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hder
  rw [hs.meromorphicOrderAt_eq,ho] <;> rfl

end SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

#print axioms SelectedActualWholeMarkedOrdinaryMeromorphicGerm318.ordinary_ring_analytic
#print axioms SelectedActualWholeMarkedOrdinaryMeromorphicGerm318.intoWhole_injective
#print axioms SelectedActualWholeMarkedOrdinaryMeromorphicGerm318.whole_field_meromorphic_at
#print axioms SelectedActualWholeMarkedOrdinaryMeromorphicGerm318.whole_field_same_germ
#print axioms SelectedActualWholeMarkedOrdinaryMeromorphicGerm318.ordinary_parameter_order_one
