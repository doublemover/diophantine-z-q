module
public import OriginalR47RelativeOffCentre318
public import OriginalR47RelativeTraitCentrePayment318
public import OriginalR47ArithmeticFixedPoint318
public import OriginalR47ArithmeticCentreFG318
public import OriginalR47ChosenRoundTrait318
public section
noncomputable section

namespace OriginalR47RelativeArithmeticRound318
open AlgebraicGeometry CategoryTheory Set
open OriginalR47TraitRoundKernel318 (restricted forgetMap toTrait)
open OriginalR47InitialArithmeticAtlas318 (fixedPrime fixedPoint fixedPoint_old eq_fixedPoint)
open OriginalR47RelativeNodeDatum318
open OriginalR47IsolatedCentreCover318
open OriginalR47GlobalCentreRees318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

variable {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
local notation "S" => Spec (CommRingCat.of R)
local notation "η" => genericPoint S

abbrev OnTrait {X : Scheme} (s : X ⟶ S) (x : X) :=
  TerminalAt (toTrait (fixedPrime s x) s) (fixedPoint s x)

abbrev ThickOnTrait {X : Scheme} (s : X ⟶ S) (x : X) (d : ℕ) :=
  ActiveAt (toTrait (fixedPrime s x) s) (fixedPoint s x) d

theorem terminal_fixed {X : Scheme} (s : X ⟶ S) (x : X) (p : Ideal R) [p.IsPrime]
    (h : fixedPrime s x = p) (t : restricted p s) (ht : forgetMap p s t = x)
    (C : TerminalAt (toTrait p s) t) : OnTrait s x := by
  subst p
  rwa [eq_fixedPoint s x t ht] at C

theorem active_fixed {X : Scheme} (s : X ⟶ S) (x : X) (p : Ideal R) [p.IsPrime]
    (h : fixedPrime s x = p) (t : restricted p s) (ht : forgetMap p s t = x)
    (d : ℕ) (C : Nonempty (ActiveAt (toTrait p s) t d)) : Nonempty (ThickOnTrait s x d) := by
  subst p
  rwa [eq_fixedPoint s x t ht] at C

variable {X : Scheme} (s : X ⟶ S) [LocallyOfFiniteType s]
variable (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z)
local notation "Y" => source Z hZ hC pick
local notation "r" => proj Z hZ hC pick

/-- The same actual global Rees round now retains the full relative atlas
as the induction payload. The terminal read is only needed at arithmetic
points. Its off-centre part uses the true complementary open, and the new
finite set consists only of the actual surviving thick centres.
Because the literal active offset drops by exactly two, a strict
bound 2*(N+1) on old offsets yields a strict bound 2*N on the new. -/
theorem one (N : ℕ) (depth : Z → ℕ) (lt : ∀ z, depth z < 2*(N+1))
    (localSite : ∀ z, ThickOnTrait s z.val (depth z))
    (oldTerminal : ∀ x, x ∉ Z → s x ≠ η → OnTrait s x)
    (oldVertical : ∀ z ∈ Z, s z ≠ η) :
    IsProper r ∧
      (∀ x, _root_.IsConnected (r ⁻¹' ({x} : Set X))) ∧
      ∃ (Z' : Set Y) (d' : Z' → ℕ),
        Z'.Finite ∧ (∀ y ∈ Z', IsClosed ({y} : Set Y)) ∧
        (∀ y ∈ Z', (r ≫ s) y ≠ η) ∧ (∀ y, d' y < 2*N) ∧
        (∀ y, Nonempty (ThickOnTrait (r ≫ s) y.val (d' y))) ∧
        ∀ y, y ∉ Z' → (r ≫ s) y ≠ η → OnTrait (r ≫ s) y := by
  classical
  have hFG : ∀ z : Z, (marked pick z).asIdeal.FG :=
    OriginalR47ArithmeticCentreFG318.fg s pick
  let T (z : Z) (o : Option (Y × ℕ)) : Prop :=
    match o with
    | none => ∀ y : Y, r y = z.val → OnTrait (r ≫ s) y
    | some uv =>
      uv.2 + 2 = depth z ∧ r uv.1 = z.val ∧ IsClosed ({uv.1} : Set Y) ∧
      Nonempty (ThickOnTrait (r ≫ s) uv.1 uv.2) ∧
      ∀ y : Y, r y = z.val → y ≠ uv.1 → OnTrait (r ≫ s) y
  have hx (z : Z) : _root_.IsConnected (r ⁻¹' ({z.val} : Set X)) ∧
      ∃ o : Option (Y × ℕ), T z o := by
    let A := OriginalR47GlobalCentreRees318.A pick z
    let j := affineArrow pick z
    let P := (marked pick z).asIdeal
    let p := fixedPrime s z.val
    let : Algebra R A := OriginalR47ChosenRoundTrait318.oldScalar s pick z
    let : P.IsMaximal := marked_max Z hC pick z
    let : p.IsPrime := (s z.val).isPrime
    have hroot : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ s :=
      OriginalR47ChosenRoundTrait318.old_scalar_read s pick z
    obtain ⟨_,_,i',Hi',_⟩ := OriginalR47ChosenRoundTrait318.attached s Z hZ hC pick z
    have hp : P.comap (algebraMap R A) = p :=
      OriginalR47ArithmeticCentreFG318.prime_read s pick z
    let t := fixedPoint s z.val
    have ht : forgetMap p s t = j ⟨P,inferInstance⟩ :=
      (fixedPoint_old s z.val).trans (marked_read pick z).symm
    have hm : j (⟨P,inferInstance⟩ : PrimeSpectrum A) = z.val := marked_read pick z
    have hc : IsClosed ({j (⟨P,inferInstance⟩ : PrimeSpectrum A)} : Set X) :=
      hm.symm ▸ hC z.val z.property
    obtain ⟨hconn,h⟩ :=
      OriginalR47RelativeTraitCentrePayment318.pay_attached p s r j hroot P hp t ht hc
        (localSite z) (hFG z) i' Hi'
    rw [hm] at hconn h
    have same (y : Y) (hy : r y = z.val) : fixedPrime (r ≫ s) y = p := by
      change ((r ≫ s) y).asIdeal = (s z.val).asIdeal
      rw [Scheme.Hom.comp_apply,hy]
    refine ⟨hconn,?_⟩
    rcases h with h | ⟨u,d,t',hd,hr,hclosed,hproj,hs,he⟩
    · refine ⟨none,fun y hy => ?_⟩
      obtain ⟨q,hq,C⟩ := h y hy
      exact terminal_fixed (r ≫ s) y p (same y hy) q hq C
    · refine ⟨some (u,d),hd,hr,hclosed,
        active_fixed (r ≫ s) u p (same u hr) t' hproj d hs,fun y hy hne => ?_⟩
      obtain ⟨q,hq,C⟩ := he y hy hne
      exact terminal_fixed (r ≫ s) y p (same y hy) q hq C
  choose O hO using fun z => (hx z).2
  let Z' : Set Y := Option.some ⁻¹' Set.range (fun z : Z => (O z).map Prod.fst)
  have hmem (y : Y) (hy : y ∈ Z') : ∃ z : Z, ∃ d, O z = some (y,d) := by
    obtain ⟨z,hz⟩ := hy
    change (O z).map Prod.fst = some y at hz
    cases he : O z with
    | none => simp only [he,Option.map_none,reduceCtorEq] at hz
    | some row =>
      have hrow : row.1 = y := by
        rw [he] at hz
        exact Option.some.inj hz
      exact ⟨z,row.2,he.trans (congrArg some (Prod.ext hrow rfl))⟩
  have hmem' (z : Z) (y : Y) (d : ℕ) (he : O z = some (y,d)) : y ∈ Z' := by
    exact ⟨z,by rw [he]; rfl⟩
  have hdata (y : Z') :
      ∃ d : ℕ, d < 2*N ∧ IsClosed ({y.val} : Set Y) ∧
        (r ≫ s) y.val ≠ η ∧ Nonempty (ThickOnTrait (r ≫ s) y.val d) := by
    obtain ⟨z,d,he⟩ := hmem y.val y.property
    have hh := hO z
    rw [he] at hh
    change d + 2 = depth z ∧ r y.val = z.val ∧ _ at hh
    obtain ⟨h₀,h₁,h₂,h₃,_⟩ := hh
    have hbound : d < 2*N := by
      have L := lt z
      omega
    have hvertical : (r ≫ s) y.val ≠ η := by
      rw [Scheme.Hom.comp_apply,h₁]
      exact oldVertical z.val z.property
    exact ⟨d,hbound,h₂,hvertical,h₃⟩
  choose d' hd hcl hv hsite using hdata
  have hf : Z'.Finite := by
    let : Finite Z := hZ
    exact (Set.finite_range (fun z : Z => (O z).map Prod.fst)).preimage
      (Option.some_injective Y).injOn
  refine ⟨proper Z hZ hC pick hFG,?_,Z',d',hf,?_,?_,hd,hsite,?_⟩
  · intro x
    by_cases h : x ∈ Z
    · exact (hx ⟨x,h⟩).1
    · exact OriginalR47ActualRoundConnected318.outside Z hZ hC pick x h
  · intro y hy
    exact hcl ⟨y,hy⟩
  · intro y hy
    exact hv ⟨y,hy⟩
  · intro y hy hv
    by_cases h : r y ∈ Z
    · let z : Z := ⟨r y,h⟩
      have hh := hO z
      cases he : O z with
      | none => exact (show ∀ y : Y, r y = z.val → OnTrait (r ≫ s) y from he ▸ hh) y rfl
      | some row =>
        rw [he] at hh
        change _ ∧ _ ∧ _ ∧ _ ∧ (∀ y : Y, r y = z.val → y ≠ row.1 → OnTrait (r ≫ s) y) at hh
        exact hh.2.2.2.2 y rfl (fun en =>
          hy (en ▸ hmem' z row.1 row.2 (show O z = some (row.1,row.2) from he)))
    · let p := fixedPrime s (r y)
      let : p.IsPrime := (s (r y)).isPrime
      let xₚ := fixedPoint s (r y)
      have oldVert : s (r y) ≠ η := by simpa only [Scheme.Hom.comp_apply] using hv
      obtain ⟨yₚ,hyₚ,C⟩ :=
        OriginalR47RelativeOffCentre318.terminal_off p s Z hZ hC pick y h xₚ
          (fixedPoint_old s (r y)) (oldTerminal (r y) h oldVert)
      have eq : fixedPrime (r ≫ s) y = p := by
        change ((r ≫ s) y).asIdeal = (s (r y)).asIdeal
        rw [Scheme.Hom.comp_apply]
      exact terminal_fixed (r ≫ s) y p eq yₚ hyₚ C

end OriginalR47RelativeArithmeticRound318

#print axioms OriginalR47RelativeArithmeticRound318.terminal_fixed
#print axioms OriginalR47RelativeArithmeticRound318.one
