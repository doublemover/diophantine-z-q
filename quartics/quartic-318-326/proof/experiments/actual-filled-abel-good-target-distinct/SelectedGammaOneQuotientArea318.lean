module
public import GammaOneAtlas318
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Compactness.Lindelof
public section
noncomputable section

namespace SelectedGammaOneQuotientArea318
open Matrix UpperHalfPlane Function Set MeasureTheory
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 DerivativeCocycle318
open scoped Pointwise MeasureTheory MatrixGroups

private theorem quotient_smul (N : ℕ) (g : image N) (x : UpperHalfPlane) :
    quotientMap N (g • x) = quotientMap N x :=
  Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g,rfl⟩)

private theorem measurable_quotient (N : ℕ) : Measurable (quotientMap N) :=
  measurable_quotient_mk' (s := MulAction.orbitRel (image N) UpperHalfPlane)

private theorem first_sheet_representatives {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (q : X → Y) (hq : Measurable q)
    (U : ℕ → Set X) (hUm : ∀ n, MeasurableSet (U n)) (hUi : ∀ n, InjOn q (U n))
    (hWm : ∀ n, MeasurableSet (q '' U n)) (hWc : ∀ a : Y, ∃ n, a ∈ q '' U n) :
    ∃ A : Set X, MeasurableSet A ∧ (∀ a : Y, ∃ x ∈ A, q x = a) ∧
      InjOn q A ∧ U 0 ⊆ A := by
  classical
  let W (n : ℕ) := q '' U n
  let P (n : ℕ) := ⋃ m : {m : ℕ // m < n}, W m.val
  let V (n : ℕ) := U n ∩ q ⁻¹' (W n \ P n)
  have hVm (n : ℕ) : MeasurableSet (V n) :=
    (hUm n).inter
      (((hWm n).diff (MeasurableSet.iUnion fun (m : {m : ℕ // m < n}) => hWm m.val)).preimage
        hq)
  let A := ⋃ n, V n
  have hAm : MeasurableSet A := MeasurableSet.iUnion hVm
  have hBA (x : X) (hx : x ∈ U 0) : x ∈ A := by
    refine mem_iUnion_of_mem 0 ⟨hx,⟨⟨x,hx,rfl⟩,?_⟩⟩
    intro h
    obtain ⟨m,_⟩ := mem_iUnion.mp h
    exact (Nat.not_lt_zero _) m.property
  have hAs (a : Y) : ∃ x ∈ A, q x = a := by
    let n := Nat.find (hWc a)
    obtain ⟨x,hx,hxa⟩ := Nat.find_spec (hWc a)
    have hnot : a ∉ P n := by
      intro h
      obtain ⟨m,hm⟩ := mem_iUnion.mp h
      have hge : n ≤ m.val := Nat.find_min' _ hm
      exact (Nat.not_lt_of_ge hge) m.property
    refine ⟨x,mem_iUnion_of_mem n ⟨hx,?_⟩,hxa⟩
    change q x ∈ W n \ P n
    rw [hxa]
    exact ⟨Nat.find_spec (hWc a),hnot⟩
  have hAi : InjOn q A := by
    intro x hx y hy hxy
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hy
    have hxW : q x ∈ W n := hn.2.1
    have hyW : q y ∈ W m := hm.2.1
    have hxP : q x ∉ P n := hn.2.2
    have hyP : q y ∉ P m := hm.2.2
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · exfalso
      apply hyP
      rw [← hxy]
      exact mem_iUnion_of_mem ⟨n,hnm⟩ hxW
    · subst m
      exact hUi n hn.1 hm.1 hxy
    · exfalso
      apply hxP
      rw [hxy]
      exact mem_iUnion_of_mem ⟨m,hmn⟩ hyW
  exact ⟨A,hAm,hAs,hAi,hBA⟩

private theorem actual_orbit_domain (N : ℕ) (hN : 5 ≤ N) {A : Set UpperHalfPlane}
    (hAm : MeasurableSet A) (hAs : ∀ a : Base (image N), ∃ x ∈ A, quotientMap N x = a)
    (hAi : InjOn (quotientMap N) A) : IsFundamentalDomain (image N) A volume := by
  apply IsFundamentalDomain.mk' hAm.nullMeasurableSet
  intro x
  obtain ⟨y,hy,hyx⟩ := hAs (quotientMap N x)
  have horb := @Quotient.exact UpperHalfPlane (MulAction.orbitRel (image N) UpperHalfPlane) y x hyx
  obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp horb
  have hxy : g • x = y := hg
  have hgA : g • x ∈ A :=
    Eq.mpr (congrArg (fun w : UpperHalfPlane => w ∈ A) hxy) hy
  refine ⟨g,hgA,?_⟩
  intro h hh
  have he : h • x = g • x := hAi hh hgA
    ((quotient_smul N h x).trans (quotient_smul N g x).symm)
  have hfix : (g⁻¹*h) • x = x := by rw [mul_smul,he,inv_smul_smul]
  have h1 : ((g⁻¹*h : image N) : G) = 1 :=
    image_fixed_eq_one N hN _ (g⁻¹*h).property x hfix
  have h1' : g⁻¹ * h = 1 := Subtype.ext h1
  have hc := congrArg (fun u : image N => g*u) h1'
  simpa [← mul_assoc] using hc

/-- A Borel fundamental domain for the actual fine-level action, which
contains the given injective open sheet. The tiling is exact (not merely ae):
order a countable set of local sheets with B first and choose the first
open sheet hitting each orbit. No Dirichlet geometry or finite volume
assumption is used. -/
theorem adapted_domain (N : ℕ) (hN : 5 ≤ N) (B : Set UpperHalfPlane)
    (hB : IsOpen B) (hBI : InjOn (quotientMap N) B) :
    ∃ A : Set UpperHalfPlane, IsFundamentalDomain (image N) A volume ∧ B ⊆ A := by
  classical
  let q : UpperHalfPlane → Base (image N) := quotientMap N
  let qp := GammaOneAtlas318.quotient_localHomeomorph N hN
  let C (x : UpperHalfPlane) : Set UpperHalfPlane := (qp.localInverseAt x).target
  have hCo (x : UpperHalfPlane) : IsOpen (C x) := (qp.localInverseAt x).open_target
  have hCc : (univ : Set UpperHalfPlane) ⊆ ⋃ x, C x := fun x _ =>
    mem_iUnion_of_mem x qp.self_mem_localInverseAt_target
  obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover C hCo hCc
  let U : ℕ → Set UpperHalfPlane
    | 0 => B
    | (n+1) => C (f n)
  have hUo (n : ℕ) : IsOpen (U n) := by
    cases n with
    | zero => exact hB
    | succ n => exact hCo (f n)
  have hUi (n : ℕ) : InjOn q (U n) := by
    cases n with
    | zero => exact hBI
    | succ n => exact qp.injOn_localInverseAt_target
  have hWm (n : ℕ) : MeasurableSet (q '' U n) := by
    have ho : IsOpen (q '' U n) := qp.isOpenMap _ (hUo n)
    exact measurableSet_quotient.mpr (qp.continuous.isOpen_preimage _ ho).measurableSet
  have hWc (a : Base (image N)) : ∃ n, a ∈ q '' U n := by
    obtain ⟨x,rfl⟩ := GammaOneAtlas318.quotient_surjective N a
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hf (Set.mem_univ x))
    exact ⟨n+1,x,hn,rfl⟩
  obtain ⟨A,hAm,hAs,hAi,hBA⟩ := first_sheet_representatives q (measurable_quotient N)
    U (fun n => (hUo n).measurableSet) hUi hWm hWc
  exact ⟨A,actual_orbit_domain N hN hAm hAs hAi,hBA⟩

private theorem countableImage (N : ℕ) : Countable (image N) := by
  have hmat : Injective (fun g : SL(2,ℤ) => (fun i j : Fin 2 => g i j)) := by
    intro g h e
    exact Matrix.SpecialLinearGroup.ext g h (fun i j => congrFun (congrFun e i) j)
  letI : Countable (SL(2,ℤ)) := hmat.countable
  let fn (g : CongruenceSubgroup.Gamma1 N) : image N :=
    ⟨positiveMatrix N g,⟨g,rfl⟩⟩
  have hfn : Function.Surjective fn := by
    rintro ⟨g,hg⟩
    obtain ⟨γ,hγ⟩ := hg
    exact ⟨γ,Subtype.ext hγ⟩
  exact hfn.countable

private theorem invariantImage (N : ℕ) :
    SMulInvariantMeasure (image N) UpperHalfPlane volume :=
  ⟨fun g s _ => by
    change volume (((((g : G) : GL (Fin 2) ℝ)) • ·) ⁻¹' s) = volume s
    exact measure_preimage_smul volume ((g : G) : GL (Fin 2) ℝ) s⟩

private theorem measurableImage (N : ℕ) : MeasurableConstSMul (image N) UpperHalfPlane :=
  ⟨fun g => by
    change Measurable (fun x : UpperHalfPlane => ((g : G) : GL (Fin 2) ℝ) • x)
    exact (continuous_const_smul ((g : G) : GL (Fin 2) ℝ)).measurable⟩

private theorem exists_domain (N : ℕ) (hN : 5 ≤ N) :
    ∃ A : Set UpperHalfPlane, IsFundamentalDomain (image N) A volume := by
  obtain ⟨A,hA,_⟩ := adapted_domain N hN ∅ isOpen_empty (injOn_empty (quotientMap N))
  exact ⟨A,hA⟩

/-- The canonical actual quotient hyperbolic area. It is not the pushforward
of all upper half-plane area, which would count every orbit infinitely. -/
def area (N : ℕ) (hN : 5 ≤ N) : Measure (Base (image N)) :=
  (volume.restrict (exists_domain N hN).choose).map (quotientMap N)

theorem area_from_domain (N : ℕ) (hN : 5 ≤ N) {A : Set UpperHalfPlane}
    (hA : IsFundamentalDomain (image N) A volume) :
    area N hN = (volume.restrict A).map (quotientMap N) := by
  letI := countableImage N
  letI := invariantImage N
  letI := measurableImage N
  exact ((exists_domain N hN).choose_spec).quotientMeasure_eq volume hA

/-- The measure pushed forward from an injective open period sheet is
dominated by the very same quotient area, independently of the chosen
fundamental domain. This is the one-chart restriction used at j=1. -/
theorem sheet_area_le (N : ℕ) (hN : 5 ≤ N) (B : Set UpperHalfPlane)
    (hB : IsOpen B) (hBI : InjOn (quotientMap N) B) :
    (volume.restrict B).map (quotientMap N) ≤ area N hN := by
  obtain ⟨A,hA,hBA⟩ := adapted_domain N hN B hB hBI
  rw [area_from_domain N hN hA]
  exact Measure.map_mono (Measure.restrict_mono hBA le_rfl) (measurable_quotient N)

/-- A set of finite genuine hyperbolic area meeting every fine-level
orbit bounds the quotient area. There is no disjointness premise
on that cover: the actual fundamental domain supplies it in measure. -/
theorem area_univ_le_of_cover (N : ℕ) (hN : 5 ≤ N) (B : Set UpperHalfPlane)
    (hit : ∀ z : UpperHalfPlane, ∃ g : image N, z ∈ g • B) :
    area N hN Set.univ ≤ volume B := by
  letI := countableImage N
  letI := invariantImage N
  letI := measurableImage N
  obtain ⟨A,hA⟩ := exists_domain N hN
  have he : area N hN Set.univ = volume A := by
    rw [area_from_domain N hN hA,Measure.map_apply (measurable_quotient N) MeasurableSet.univ,
      Set.preimage_univ,Measure.restrict_apply_univ]
  rw [he]
  have hsub : A ⊆ ⋃ g : image N, (g • B) ∩ A := by
    intro z hz
    obtain ⟨g,hg⟩ := hit z
    exact Set.mem_iUnion_of_mem g ⟨hg,hz⟩
  calc
    volume A ≤ volume (⋃ g : image N, (g • B) ∩ A) := measure_mono hsub
    _ ≤ ∑' g : image N, volume ((g • B) ∩ A) := measure_iUnion_le _
    _ = volume B := (hA.measure_eq_tsum B).symm

end SelectedGammaOneQuotientArea318
#print axioms SelectedGammaOneQuotientArea318.adapted_domain
#print axioms SelectedGammaOneQuotientArea318.sheet_area_le

#print axioms SelectedGammaOneQuotientArea318.area_univ_le_of_cover
