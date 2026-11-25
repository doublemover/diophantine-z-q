module
public import OriginalR47RelativeCentreCharts318
public import OriginalR47ActualPointedWindowBase318
public import OriginalR47ChosenRoundTrait318
public import OriginalR47TraitRoundActualFibre318
public import OriginalR47ActualRoundConnected318
public import OriginalR47LocalizedPointedMorphisms318
public section
noncomputable section

namespace OriginalR47RelativeTraitCentrePayment318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318
open OriginalR47TraitAffineCentre318 (B chart carriedIdeal carried_maximal carried_on_trait)
open OriginalR47RelativeNodeDatum318
open OriginalR47PointedReesAlignment318 (asSpec extended)
open OriginalAffineReesBlowup318 (blowup projection)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
variable (p : Ideal R) [p.IsPrime]
variable {X Y : Scheme} (s : X ⟶ base (R:=R)) (r : Y ⟶ X)
variable (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
variable (root : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ s)
variable (P : Ideal A) [P.IsMaximal]
variable (hbase : P.comap (algebraMap R A) = p)
local notation "x" => j (⟨P,inferInstance⟩ : PrimeSpectrum A)
local notation "F" => restricted p s
local notation "F'" => restricted p (r ≫ s)
local notation "E" => restrictedRoundIso p s r

/-- Every step uses the same literal trait for the old and new charts.
The actual localization arrow is not required to have finite type:
the local atlas is transferred by the canonical whole isomorphism E. -/
theorem pay_attached (t : F) (ht : forgetMap p s t = x) (hc : IsClosed ({x} : Set X))
    {d : ℕ} (T : ActiveAt (toTrait p s) t d)
    (hfg : P.FG)
    (i' : blowup (carriedIdeal p P) ⟶ Yp p s r)
    (H' : IsPullback i' (projection (carriedIdeal p P)) (a p s r) (chart p s j root)) :
    _root_.IsConnected (r ⁻¹' ({x} : Set X)) ∧
      ((∀ y : Y, r y = x → ∃ u : F', forgetMap p (r ≫ s) u = y ∧
          TerminalAt (toTrait p (r ≫ s)) u) ∨
        ∃ (y' : Y) (d' : ℕ) (t' : F'),
          d' + 2 = d ∧ r y' = x ∧ IsClosed ({y'} : Set Y) ∧
          forgetMap p (r ≫ s) t' = y' ∧ Nonempty (ActiveAt (toTrait p (r ≫ s)) t' d') ∧
          ∀ y : Y, r y = x → y ≠ y' → ∃ u : F', forgetMap p (r ≫ s) u = y ∧
            TerminalAt (toTrait p (r ≫ s)) u) := by
  let p' := carriedIdeal p P
  let : p'.IsMaximal := carried_maximal p P hbase
  let j' := chart p s j root
  let : IsOpenImmersion j' := inferInstance
  have hfg' : p'.FG := hfg.map (algebraMap A (B p (A:=A)))
  have hmark : j' (⟨p',inferInstance⟩ : PrimeSpectrum (B p (A:=A))) = t :=
    carried_on_trait p s j root P hbase t ht
  let C := activeSite T
  obtain ⟨M⟩ := OriginalR47ActualPointedRound318.of_dvr_site C.q d p' C.into C.split
    j' C.u C.q_irred (C.read.trans hmark.symm) C.literal
  let : Algebra (B p (A:=A)) M.V.B := M.V.old.hom.toAlgebra
  let : Algebra (OriginalThickCentralReesChart318.O C.q d) M.V.B := M.V.split.hom.toAlgebra
  let L := M.alignment
  have straight := OriginalR47ActualPointedWindowBase318.window_triangle C.q d p'
    C.into C.split j' C.u M (toTrait p s) (Spec.map (CommRingCat.ofHom T.params.φ)) T.W.over
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ :=
    OriginalR47LocalizedPointedMorphisms318.inherited C.q d p' C.into C.split j' C.u M
  let : Flat (asSpec (extended (A:=B p (A:=A)) L.W.g)) := h₁
  let : FormallyUnramified (asSpec (extended (A:=B p (A:=A)) L.W.g)) := h₂
  let : LocallyOfFiniteType (asSpec (extended (A:=B p (A:=A)) L.W.g)) := h₃
  let : Flat (asSpec (extended (A:=OriginalThickCentralReesChart318.O C.q d) L.W.g)) := h₄
  let : FormallyUnramified (asSpec (extended (A:=OriginalThickCentralReesChart318.O C.q d) L.W.g)) := h₅
  let : LocallyOfFiniteType (asSpec (extended (A:=OriginalThickCentralReesChart318.O C.q d) L.W.g)) := h₆
  have hconn : _root_.IsConnected ((a p s r) ⁻¹' ({t} : Set F)) := by
    rw [← hmark]
    exact OriginalR47ActualRoundConnected318.global_centre C.q C.q_irred d p' L
      (a p s r) j' i' H'
  have hC : IsClosed ({j' (⟨p',inferInstance⟩ : PrimeSpectrum (B p (A:=A)))} : Set F) := by
    rw [hmark]
    have he : ({t} : Set F) = (forgetMap p s) ⁻¹' ({x} : Set X) := by
      ext z
      change z = t ↔ forgetMap p s z = x
      rw [← ht]
      let : IsPreimmersion (forgetMap p s) := forgetMap_preimmersion p s
      exact (forgetMap p s).isEmbedding.injective.eq_iff.symm
    rw [he]
    exact hc.preimage (forgetMap p s).continuous
  have points (y : Y) (hy : r y = x) :
      ∃ u : Yp p s r, b p s r u = y ∧ a p s r u = t :=
    OriginalR47TraitRoundActualFibre318.full_fibre p s r t y (hy.trans ht.symm)
  have Eold (u : Yp p s r) : forgetMap p (r ≫ s) (E.hom u) = b p s r u := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : Yp p s r ⟶ Y => f u) (restrictedRoundIso_old p s r)
  have transport (u : Yp p s r)
      (h : TerminalAt (a p s r ≫ toTrait p s) u) :
      TerminalAt (toTrait p (r ≫ s)) (E.hom u) :=
    terminal_push_open h E.hom (restrictedRoundIso_trait p s r)
  refine ⟨?_,?_⟩
  · rw [← ht]
    exact OriginalUpperReesFibreTransfer318.descend_connected_point (pullback_round p s r) t hconn
  rcases OriginalR47RelativeCentreCharts318.one T.params d p' L (a p s r) (toTrait p s)
    j' i' H' straight hfg' hC with clear | ⟨u',d',hd,hu,hclose,⟨Act⟩,ordinary⟩
  · left
    intro y hy
    obtain ⟨u,huy,hut⟩ := points y hy
    exact ⟨E.hom u,(Eold u).trans huy,transport u (clear u (hut.trans hmark.symm))⟩
  · right
    let y' := b p s r u'
    have hy' : r y' = x := by
      have eq := congrArg (fun f : Yp p s r ⟶ X => f u') (pullback_round p s r).w
      simpa only [y',Scheme.Hom.comp_apply,hu,hmark,ht] using eq
    have hCl' : IsClosed ({y'} : Set Y) :=
      OriginalR47TraitRoundActualFibre318.child_closed p s r u' hclose (hy'.symm ▸ hc)
    refine ⟨y',d',E.hom u',hd,hy',hCl',Eold u',
      ⟨active_push_iso Act E (restrictedRoundIso_trait p s r)⟩,?_⟩
    intro y hy neq
    obtain ⟨u,huy,hut⟩ := points y hy
    have hne : u ≠ u' := fun h => neq (huy.symm.trans (congrArg (b p s r) h))
    exact ⟨E.hom u,(Eold u).trans huy,transport u (ordinary u (hut.trans hmark.symm) hne)⟩

end OriginalR47RelativeTraitCentrePayment318

#print axioms OriginalR47RelativeTraitCentrePayment318.pay_attached
