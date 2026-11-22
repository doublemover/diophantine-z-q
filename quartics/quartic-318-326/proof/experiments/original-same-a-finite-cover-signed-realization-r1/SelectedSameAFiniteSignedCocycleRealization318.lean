module

public import SelectedSameAInjectiveOpenExtension318
public import SelectedSameASignedLiftCocycle318
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic

/-!
Attach each original open to the finite family already solved.
Extend the actual section from the union of its existing overlaps
by injectivity. Then the true quotient sections glue globally and
give back the original right-minus-left coefficient.
-/
public section
noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAFiniteSignedCocycleRealization318

open SelectedSameAActualLiftDifference318 (Sh local_inclusion_injective)
open SelectedSameASignedLiftCocycle318 (res res_res res_natural coeff coeff_beta)

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable {ι : Type u} (U : ι → Opens X)

/-- Degree-one cocycle on the actual opens. The triple equation is on
the literal full triple overlap, not extra choices on subopens. -/
structure Cocycles (F : Sh X) where
  edge : ∀ i j, F.obj.obj (op (U i ⊓ U j))
  diag : ∀ i, edge i i = 0
  triple : ∀ i j k,
    res X F inf_le_left (edge i j) +
      res X F (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (edge j k) =
        res X F (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (edge i k)

variable {F : Sh X} (c : Cocycles X U F)

private theorem res_self (V : Opens X) (t : F.obj.obj (op V)) :
    res X F (le_rfl : V ≤ V) t = t := by
  change F.obj.map (𝟙 (op V)) t = t
  rw [F.obj.map_id] <;> rfl

private theorem triple_on {W : Opens X} (i j k : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    res X F (le_inf hi hj) (c.edge i j) +
      res X F (le_inf hj hk) (c.edge j k) =
        res X F (le_inf hi hk) (c.edge i k) := by
  have h := congrArg (fun t : F.obj.obj (op ((U i ⊓ U j) ⊓ U k)) =>
    res X F (le_inf (le_inf hi hj) hk) t) (c.triple i j k)
  rw [map_add, res_res X, res_res X, res_res X] at h
  exact h

private theorem antisymm (i j : ι) :
    c.edge i j =
      -res X F (le_inf (inf_le_right : U i ⊓ U j ≤ U j) inf_le_left) (c.edge j i) := by
  have h := triple_on X U c i j i inf_le_left inf_le_right inf_le_left
  have hSame : res X F (le_inf (inf_le_left : U i ⊓ U j ≤ U i) inf_le_right)
      (c.edge i j) = c.edge i j := res_self X (U i ⊓ U j) (c.edge i j)
  rw [hSame, c.diag, map_zero] at h
  calc
    _ = (c.edge i j + res X F (le_inf (inf_le_right : U i ⊓ U j ≤ U j) inf_le_left)
      (c.edge j i)) - res X F (le_inf (inf_le_right : U i ⊓ U j ≤ U j) inf_le_left)
      (c.edge j i) := by abel
    _ = _ := by rw [h, zero_sub]

/-- A finite actual family has zero Čech H¹ in the injective sheaf:
construct the cochain one new genuine overlap-union at a time. No
condition on H² of the original structure sheaf is used. -/
theorem finite_right_minus_left [Injective F] (T : Finset ι) :
    ∃ t : ∀ i, F.obj.obj (op (U i)), ∀ i ∈ T, ∀ j ∈ T,
      res X F inf_le_right (t j) - res X F inf_le_left (t i) = c.edge i j := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a s ha IH =>
    obtain ⟨t, ht⟩ := IH
    let V (i : {i : ι // i ∈ s}) : Opens X := U i.1 ⊓ U a
    let W : Opens X := ⨆ i, V i
    have hW : W ≤ U a := iSup_le (fun _ => inf_le_right)
    let pieces (i : {i : ι // i ∈ s}) : F.obj.obj (op (V i)) :=
      res X F inf_le_left (t i.1) + c.edge i.1 a
    have hCompat : TopCat.Presheaf.IsCompatible F.obj V pieces := by
      intro i j
      let Z := V i ⊓ V j
      have hi : Z ≤ U i.1 := inf_le_left.trans inf_le_left
      have hj : Z ≤ U j.1 := inf_le_right.trans inf_le_left
      have hA : Z ≤ U a := inf_le_left.trans inf_le_right
      have hOld := congrArg (fun z : F.obj.obj (op (U i.1 ⊓ U j.1)) =>
        res X F (le_inf hi hj) z) (ht i.1 i.2 j.1 j.2)
      rw [map_sub, res_res X, res_res X] at hOld
      have eOld : res X F hj (t j.1) - res X F hi (t i.1) =
          res X F (le_inf hi hj) (c.edge i.1 j.1) := hOld
      have eTriple := triple_on X U c i.1 j.1 a hi hj hA
      change res X F inf_le_left (pieces i) = res X F inf_le_right (pieces j)
      unfold pieces
      rw [map_add, map_add, res_res X, res_res X]
      apply sub_eq_zero.mp
      change (res X F hi (t i.1) + res X F (le_inf hi hA) (c.edge i.1 a)) -
        (res X F hj (t j.1) + res X F (le_inf hj hA) (c.edge j.1 a)) = 0
      calc
        _ = res X F (le_inf hi hA) (c.edge i.1 a) -
          ((res X F hj (t j.1) - res X F hi (t i.1)) +
            res X F (le_inf hj hA) (c.edge j.1 a)) := by abel
        _ = 0 := by rw [eOld, eTriple, sub_self]
    obtain ⟨g, hg, _⟩ := TopCat.Sheaf.existsUnique_gluing' F V W
      (fun i => homOfLE (le_iSup V i)) le_rfl pieces hCompat
    obtain ⟨ta, hta⟩ :=
      SelectedSameAInjectiveOpenExtension318.restriction_surjective X F (homOfLE hW) g
    have hta' : res X F hW ta = g := hta
    have edgeToNew (i : ι) (hi : i ∈ s) :
        res X F inf_le_right ta - res X F inf_le_left (t i) = c.edge i a := by
      let l : {i : ι // i ∈ s} := ⟨i, hi⟩
      let h := le_iSup V l
      have hRest : res X F h g = pieces l := hg l
      have hAll : res X F (inf_le_right : U i ⊓ U a ≤ U a) ta = pieces l :=
        (res_res X F h hW ta).symm.trans ((congrArg (res X F h) hta').trans hRest)
      rw [hAll]
      change (res X F inf_le_left (t i) + c.edge i a) -
        res X F inf_le_left (t i) = c.edge i a
      abel
    let update (i : ι) : F.obj.obj (op (U i)) :=
      if hi : i = a then hi.symm ▸ ta else t i
    have update_a : update a = ta := by simp [update]
    have update_old (i : ι) (hi : i ∈ s) : update i = t i := by
      have hn : i ≠ a := fun he => ha (he ▸ hi)
      simp [update, hn]
    refine ⟨update, ?_⟩
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with ri | hi
    · subst i
      rcases Finset.mem_insert.mp hj with rj | hj
      · subst j
        rw [c.diag]
        exact sub_self _
      · rw [update_a, update_old j hj]
        have swap : U a ⊓ U j ≤ U j ⊓ U a := le_inf inf_le_right inf_le_left
        have he := congrArg (fun z : F.obj.obj (op (U j ⊓ U a)) => res X F swap z)
          (edgeToNew j hj)
        rw [map_sub, res_res X, res_res X] at he
        have h' : res X F inf_le_left ta - res X F inf_le_right (t j) =
            res X F swap (c.edge j a) := he
        rw [antisymm X U c a j, ← h']
        abel
    · rcases Finset.mem_insert.mp hj with rj | hj
      · subst j
        rw [update_old i hi, update_a]
        exact edgeToNew i hi
      · rw [update_old i hi, update_old j hj]
        exact ht i hi j hj

/-- Push the old additive coefficients through the actual inclusion,
preserving the literal cocycle restrictions before any local lifts. -/
def mapCocycle {G : Sh X} (f : F ⟶ G) : Cocycles X U G where
  edge i j := f.hom.app (op (U i ⊓ U j)) (c.edge i j)
  diag i := by rw [c.diag, map_zero]
  triple i j k := by
    rw [← res_natural X, ← res_natural X, ← res_natural X, ← map_add, c.triple]

/-- Every genuine finite-cover cocycle is the actual right-minus-left
readout of local lifts of **one** global section in the quotient of
the very same injective row. Plug in the checked under-injective row
of the original additive structure sheaf. No class comparison or
cocycle equality is assumed. -/
theorem realizes_signed_coefficients [Fintype ι]
    (S : ShortComplex (Sh X)) (hS : S.ShortExact) [Injective S.X₂]
    (cover : (⊤ : Opens X) ≤ ⨆ i, U i) (c₀ : Cocycles X U S.X₁) :
    ∃ (z : S.X₃.obj.obj (op (⊤ : Opens X))) (t : ∀ i, S.X₂.obj.obj (op (U i)))
      (ht : ∀ i, S.g.hom.app (op (U i)) (t i) = res X S.X₃ le_top z),
      ∀ i j, coeff X S hS U z t ht i j = c₀.edge i j := by
  classical
  obtain ⟨t, ht⟩ := finite_right_minus_left X U (mapCocycle X U c₀ S.f) Finset.univ
  have eqOn (i j : ι) :
      res X S.X₂ inf_le_right (t j) - res X S.X₂ inf_le_left (t i) =
        S.f.hom.app (op (U i ⊓ U j)) (c₀.edge i j) :=
    ht i (Finset.mem_univ i) j (Finset.mem_univ j)
  let y (i : ι) : S.X₃.obj.obj (op (U i)) := S.g.hom.app (op (U i)) (t i)
  have hCompat : TopCat.Presheaf.IsCompatible S.X₃.obj U y := by
    intro i j
    have e := congrArg (fun a : S.X₂.obj.obj (op (U i ⊓ U j)) =>
      S.g.hom.app (op (U i ⊓ U j)) a) (eqOn i j)
    have ez := congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom.app (op (U i ⊓ U j)) (c₀.edge i j)) S.zero
    have e0 : S.g.hom.app (op (U i ⊓ U j))
        (S.f.hom.app (op (U i ⊓ U j)) (c₀.edge i j)) = 0 := ez
    rw [map_sub, res_natural X, res_natural X, e0] at e
    change res X S.X₃ inf_le_left (y i) = res X S.X₃ inf_le_right (y j)
    exact (sub_eq_zero.mp e).symm
  obtain ⟨z, hz, _⟩ := TopCat.Sheaf.existsUnique_gluing' S.X₃ U ⊤
    (fun _ => homOfLE le_top) cover y hCompat
  have hzt (i : ι) : S.g.hom.app (op (U i)) (t i) = res X S.X₃ le_top z := (hz i).symm
  refine ⟨z, t, hzt, ?_⟩
  intro i j
  apply local_inclusion_injective X S hS (U i ⊓ U j)
  exact (coeff_beta X S hS U z t hzt i j).trans (eqOn i j)

end SelectedSameAFiniteSignedCocycleRealization318
