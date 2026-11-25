module
public import OriginalR47RelativeArithmeticRound318
public import OriginalR47ArithmeticGenericRound318
public section
noncomputable section

namespace OriginalR47RelativeArithmeticTermination318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47IsolatedCentreCover318
open OriginalR47GlobalCentreRees318
open OriginalR47RelativeArithmeticRound318 (OnTrait ThickOnTrait)
open OriginalR47ActualArithmeticTermination318 (GenericRead generic_round)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
local notation "S" => Spec (CommRingCat.of R)

/-- Strong induction on the actual R47 thickness offset. Each proper
arrow is the preceding glued Rees round, never a newly assumed regular
model. The original arithmetic base map is carried by composition.
Every actual point fibre is connected, including nonsplit centres,
and every vertical point has the retained ordinary relative witness
from the actual chart, not just an assertion of absolute regularity.

The actual old stable family and its pointed relative atlas remain
upstream. The terminal relative atlas is produced by these Rees rounds. -/
theorem resolve_of_bound (N : ℕ) :
    ∀ {X : Scheme} (s : X ⟶ S) [LocallyOfFiniteType s]
      (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
      (depth : Z → ℕ) (_ : ∀ z, depth z < N)
      (_ : ∀ z, Nonempty (ThickOnTrait s z.val (depth z)))
      (_ : ∀ x, x ∉ Z → s x ≠ genericPoint S → OnTrait s x)
      (_ : ∀ x ∈ Z, s x ≠ genericPoint S),
      ∃ (Y : Scheme) (r : Y ⟶ X), IsProper r ∧
        (∀ y : Y, (r ≫ s) y ≠ genericPoint S → OnTrait (r ≫ s) y) ∧
        (∀ x : X, _root_.IsConnected (r ⁻¹' ({x} : Set X))) ∧
        GenericRead s r := by
  induction N with
  | zero =>
    intro X s sFinite Z hZ hC depth hdepth hsite hreg hvert
    refine ⟨X,𝟙 X,inferInstance,?_,(fun x => ?_),?_⟩
    · rw [Category.id_comp]
      intro x hx
      exact hreg x (fun h => Nat.not_lt_zero _ (hdepth ⟨x,h⟩)) hx
    · change _root_.IsConnected ({x} : Set X)
      exact isConnected_singleton
    · intro T g hg
      exact ⟨g,IsPullback.of_id_snd⟩
  | succ n ih =>
    intro X s sFinite Z hZ hC depth hdepth hsite hreg hvert
    classical
    let pick : ∀ z : Z, Centre Z z := fun z =>
      Classical.choice (centre_exists Z hZ hC z)
    let Y := source Z hZ hC pick
    let r := proj Z hZ hC pick
    obtain ⟨hproper,hconn,Z',d',hf,hc,hvert',hlt,hsite',hreg'⟩ :=
      OriginalR47RelativeArithmeticRound318.one s Z hZ hC pick n depth hdepth
        (fun z => Classical.choice (hsite z)) hreg hvert
    let : IsProper r := hproper
    let : LocallyOfFiniteType (r ≫ s) := inferInstance
    obtain ⟨Y',r',hpr',hr',hc',hGeneric⟩ :=
      ih (r ≫ s) Z' hf hc d' hlt hsite' hreg' hvert'
    let : IsProper r' := hpr'
    refine ⟨Y',r' ≫ r,inferInstance,?_,
      (fun x => OriginalUpperReesFibreTransfer318.comp_connected r r' hc' hconn x),?_⟩
    · rw [Category.assoc]
      exact hr'
    · intro T g hg
      obtain ⟨k,H⟩ := generic_round s Z hZ hC pick hvert g hg
      have hk (t : T) : (r ≫ s) (k t) = genericPoint S := by
        have h := congrArg (fun l : T ⟶ X => l t) H.w
        rw [Category.id_comp,Scheme.Hom.comp_apply] at h
        rw [Scheme.Hom.comp_apply,h]
        exact hg t
      obtain ⟨k',H'⟩ := hGeneric k hk
      exact ⟨k',by simpa only [Category.id_comp] using H'.paste_vert H⟩

/-- The actual finite old centre family supplies a natural-number
budget. This final read does not require a separately entered depth
bound. -/
theorem resolve {X : Scheme} (s : X ⟶ S) [LocallyOfFiniteType s]
    (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (depth : Z → ℕ) (hsite : ∀ z, Nonempty (ThickOnTrait s z.val (depth z)))
    (hreg : ∀ x, x ∉ Z → s x ≠ genericPoint S → OnTrait s x)
    (hvert : ∀ x ∈ Z, s x ≠ genericPoint S) :
    ∃ (Y : Scheme) (r : Y ⟶ X), IsProper r ∧
      (∀ y : Y, (r ≫ s) y ≠ genericPoint S → OnTrait (r ≫ s) y) ∧
      (∀ x : X, _root_.IsConnected (r ⁻¹' ({x} : Set X))) ∧
      GenericRead s r := by
  classical
  let : Finite Z := hZ
  let : Fintype Z := Fintype.ofFinite Z
  let N : ℕ := (Finset.univ.sup depth) + 1
  have hN (z : Z) : depth z < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f:=depth) (Finset.mem_univ z))
  exact resolve_of_bound N s Z hZ hC depth hN hsite hreg hvert

end OriginalR47RelativeArithmeticTermination318

#print axioms OriginalR47RelativeArithmeticTermination318.resolve_of_bound
#print axioms OriginalR47RelativeArithmeticTermination318.resolve
