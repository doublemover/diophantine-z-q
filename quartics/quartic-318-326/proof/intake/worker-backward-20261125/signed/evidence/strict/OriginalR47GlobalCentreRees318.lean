module
public import OriginalR47IsolatedCentreCover318
public import Mathlib.AlgebraicGeometry.RelativeGluing
public section
noncomputable section

namespace OriginalR47GlobalCentreRees318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47IsolatedCentreCover318 OriginalAffineReesBlowup318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

universe u
variable {X : Scheme.{u}} (Z : Set X) (hZ : Z.Finite)
variable (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z)

local notation "J" => Idx Z hZ hC pick
local notation "cover" => oldCover Z hZ hC pick

/-- The vertical arrows of the very same old open cover, before forming
its one relative colimit. -/
@[expose] def vertical :
    pieceFunctor Z hZ hC pick ⟶ (cover).functorOfLocallyDirected where
  app i := over Z hZ hC pick i
  naturality i j h := by
    change step Z hZ hC pick (i:=i) (j:=j) h ≫ over Z hZ hC pick j =
      over Z hZ hC pick i ≫ oldStep Z hZ hC pick h
    exact (step_cartesian Z hZ hC pick h).w

/-- The actual Rees pieces are equifibered over the directed old open
cover, so the one glued scheme carries the same old arrows. -/
@[expose] def datum : Scheme.Cover.RelativeGluingData cover where
  functor := pieceFunctor Z hZ hC pick
  natTrans := vertical Z hZ hC pick
  equifibered := fun {i j} h => by
    change IsPullback (step Z hZ hC pick (i:=i) (j:=j) h) (over Z hZ hC pick i)
      (over Z hZ hC pick j) (oldStep Z hZ hC pick h)
    exact step_cartesian Z hZ hC pick h

abbrev source := (datum Z hZ hC pick).glued
abbrev proj : source Z hZ hC pick ⟶ X := (datum Z hZ hC pick).toBase

/-- Historical Chart-style output: the chosen old affine's whole
preimage is its true closed-point Rees Proj with both structural maps. -/
theorem chart (z : Z) :
    ∃ k : blowup (marked pick z).asIdeal ⟶ source Z hZ hC pick,
      IsPullback k (projection (marked pick z).asIdeal)
        (proj Z hZ hC pick) (affineArrow pick z) := by
  let DD := datum Z hZ hC pick
  let i : J := .hit z
  let e := (pick z).affine.isoSpec
  let pr := projection (marked pick z).asIdeal
  let k : blowup (marked pick z).asIdeal ⟶ source Z hZ hC pick := colimit.ι DD.functor i
  have H : IsPullback k (pr ≫ e.inv) (proj Z hZ hC pick) (pick z).U.ι :=
    (DD.isPullback_natTrans_ι_toBase i).flip
  refine ⟨k,H.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · exact (Category.comp_id k).trans (Category.id_comp k).symm
  · change (pr ≫ e.inv) ≫ e.hom = (𝟙 _) ≫ pr
    rw [Category.assoc,e.inv_hom_id]
    exact (Category.comp_id pr).trans (Category.id_comp pr).symm
  · exact (Category.comp_id (proj Z hZ hC pick)).trans
      (Category.id_comp (proj Z hZ hC pick)).symm
  · change (pick z).U.ι ≫ 𝟙 X = e.hom ≫ (e.inv ≫ (pick z).U.ι)
    rw [Category.comp_id,e.hom_inv_id_assoc]

/-- No modification on the entire centre-free open: the exact
projection restricts to the identity, not just an abstract equivalent
generic chart. -/
theorem unchanged :
    ∃ k : (off Z hZ hC).toScheme ⟶ source Z hZ hC pick,
      IsPullback k (𝟙 _) (proj Z hZ hC pick) (off Z hZ hC).ι := by
  let G := datum Z hZ hC pick
  let i : J := .outside (off Z hZ hC) le_rfl
  let k : (off Z hZ hC).toScheme ⟶ source Z hZ hC pick := colimit.ι G.functor i
  have H : IsPullback k (𝟙 _) (proj Z hZ hC pick) (off Z hZ hC).ι :=
    (G.isPullback_natTrans_ι_toBase i).flip
  exact ⟨k,H⟩

/-- The projection is proper from the genuine local properness
of the prescribed Rees Projs and the unchanged outside opens. -/
theorem proper (finiteIdeal : ∀ z : Z, (marked pick z).asIdeal.FG) :
    IsProper (proj Z hZ hC pick) := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@IsProper) cover
  intro i
  let DD := datum Z hZ hC pick
  have H := (DD.isPullback_natTrans_ι_toBase i).flip
  change IsProper (pullback.snd DD.toBase ((cover).f i))
  rw [← H.isoPullback_inv_snd]
  let : IsProper (DD.natTrans.app i) := by
    change IsProper (over Z hZ hC pick i)
    cases i with
    | outside V hV => exact inferInstanceAs (IsProper (𝟙 V.toScheme))
    | hit z =>
      let : IsProper (projection (marked pick z).asIdeal) :=
        OriginalAffineReesBlowup318.proper _ (finiteIdeal z)
      exact inferInstanceAs
        (IsProper (projection (marked pick z).asIdeal ≫ (pick z).affine.isoSpec.inv))
  infer_instance

end OriginalR47GlobalCentreRees318

#print axioms OriginalR47GlobalCentreRees318.datum
#print axioms OriginalR47GlobalCentreRees318.chart
#print axioms OriginalR47GlobalCentreRees318.unchanged
#print axioms OriginalR47GlobalCentreRees318.proper
