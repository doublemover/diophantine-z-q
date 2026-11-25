module

public import OriginalRetainedAffineOpenEuclideanRead318
public import OriginalRetainedActualCenteredRead318

@[expose] public section
noncomputable section

namespace OriginalRetainedActualCenteredBand318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedEuclideanAtlas318
open OriginalRetainedAffineMapContinuity318 OriginalRetainedAffineOpenEuclideanRead318
open OriginalRetainedComplexAffineEquation318 OriginalRetainedActualCenteredRead318
open OriginalActualRegularMapAtComplexChart318
open scoped Topology

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y E : Scheme} (a : A ⟶ Y) (P33 : E ⟶ Y) (σ : T ⟶ E)
local notation "X" => retainedCarrier a P33 σ
local notation "F" => fiber a (σ≫P33)
local notation "P" => (Over.mk (𝟙 T) ⟶ F)
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 σ embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 σ embedding C

variable {m : ℕ} (p : Fin m → Polynomials m) (g : coordinateQuotient p)
variable {B : Type} [CommRing B] [Algebra ℂ B] [Algebra (coordinateQuotient p) B]
variable [IsLocalization.Away g B]
variable (sc : (scalar p : ℂ →+* B)=algebraMap ℂ B)
variable (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
variable (jBase : j≫F.hom=Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
local notation "U" => oldOpen a P33 σ j
local notation "read_j" => readActual a P33 σ j jBase

variable (r ρ : ℝ)
local notation "D" => {x : Fin 2 → ℂ // ‖x‖<r}

def band : Set U := {z | ‖free p (read_j z)‖<r ∧ ‖aux p (read_j z)‖<ρ}

theorem band_open : IsOpen (band a P33 σ p j jBase r ρ) := by
  have x : Continuous (fun z : U => free p (read_j z)) := by
    apply continuous_pi
    intro i
    exact readActual_continuous a P33 σ embedding C j jBase (slot p (.inl i))
  have y : Continuous (fun z : U => aux p (read_j z)) := by
    apply continuous_pi
    intro i
    exact readActual_continuous a P33 σ embedding C j jBase (slot p (.inr i))
  exact (isOpen_lt x.norm continuous_const).inter (isOpen_lt y.norm continuous_const)

def openBand : Set P := Subtype.val '' band a P33 σ p j jBase r ρ

theorem openBand_open : IsOpen (openBand a P33 σ p j jBase r ρ) :=
  (oldOpen_isOpen a P33 σ embedding C j).isOpenMap_subtype_val _
    (band_open a P33 σ embedding C p j jBase r ρ)

abbrev oldPart (q : openBand a P33 σ p j jBase r ρ) : U :=
  ⟨q.val, by
    obtain ⟨z,_,hz⟩ := q.property
    exact hz ▸ z.property⟩

theorem oldPart_band (q : openBand a P33 σ p j jBase r ρ) :
    oldPart a P33 σ p j jBase r ρ q∈band a P33 σ p j jBase r ρ := by
  obtain ⟨z,hz,he⟩ := q.property
  rwa [show oldPart a P33 σ p j jBase r ρ q=z from Subtype.ext he.symm]

variable (y : D → Fin m → ℂ)
variable (h : ∀ x, ∀ i, eval x.val (y x) (p i)=0)
variable (den : ∀ x, evalQ p (h x) g≠0)
variable (interior : ∀ x, ‖y x‖<ρ)
variable (unique : ∀ x : D, ∀ w : Fin m → ℂ, ‖w‖<ρ →
    (∀ i, eval x.val w (p i)=0) → w=y x)
variable (cy : Continuous y)

local notation "ev" => (fun x : D => asAlgHom p g sc (h x) (den x))
local notation "mkP" => mapped a P33 σ j jBase ev

def oldPoint (x : D) : U :=
  ⟨mkP x, by
    rintro _ ⟨z,rfl⟩
    exact ⟨point (ev x).toRingHom z,rfl⟩⟩

theorem oldPoint_read (x : D) : read_j (oldPoint a P33 σ p g sc j jBase r y h den x)=ev x := by
  let u := oldPoint a P33 σ p g sc j jBase r y h den x
  have hl : point (ev x).toRingHom≫j=u.val.left := rfl
  apply AlgHom.ext
  intro b
  have rr := readActual_on_lift a P33 σ j jBase u (point (ev x).toRingHom) hl
  rw [point,Spec.preimage_map] at rr
  exact RingHom.congr_fun rr b

theorem oldPoint_free (x : D) : free p (read_j (oldPoint a P33 σ p g sc j jBase r y h den x))=x.val := by
  rw [oldPoint_read a P33 σ p g sc j jBase r y h den x]
  funext i
  exact slot_read p g (h x) (den x) (.inl i)

theorem oldPoint_aux (x : D) : aux p (read_j (oldPoint a P33 σ p g sc j jBase r y h den x))=y x := by
  rw [oldPoint_read a P33 σ p g sc j jBase r y h den x]
  funext i
  exact slot_read p g (h x) (den x) (.inr i)

include interior unique cy in
/-- The actual old centered R125 branch is a homeomorphism onto one
true open of the original arithmetic-selected complex marked surface,
for the very same projective Euclidean topology used by multiplication.
Its forward point is the old localization read, not a new exponential. -/
def localHomeo : D ≃ₜ openBand a P33 σ p j jBase r ρ := by
  let into (x : D) : openBand a P33 σ p j jBase r ρ :=
    ⟨mkP x,⟨oldPoint a P33 σ p g sc j jBase r y h den x,by
      refine ⟨?_,?_⟩
      · rw [oldPoint_free a P33 σ p g sc j jBase r y h den x]
        exact x.property
      · rw [oldPoint_aux a P33 σ p g sc j jBase r y h den x]
        exact interior x,rfl⟩⟩
  let get (z : openBand a P33 σ p j jBase r ρ) : D :=
    ⟨free p (read_j (oldPart a P33 σ p j jBase r ρ z)),
      (oldPart_band a P33 σ p j jBase r ρ z).1⟩
  refine {toFun:=into, invFun:=get, left_inv:=?_, right_inv:=?,
    continuous_toFun:=?, continuous_invFun:=?}
  · intro x
    apply Subtype.ext
    exact oldPoint_free a P33 σ p g sc j jBase r y h den x
  · intro z
    apply Subtype.ext
    apply Over.OverMorphism.ext
    let q := read_j (oldPart a P33 σ p j jBase r ρ z)
    have eq : aux p q=y (get z) :=
      unique (get z) (aux p q) (oldPart_band a P33 σ p j jBase r ρ z).2
        (read_equations p sc q)
    have ev_eq : (ev (get z)).toRingHom=q.toRingHom := by
      apply maps_unique p g
      · rw [sc]
        apply RingHom.ext
        intro c
        exact ((ev (get z)).commutes c).trans (q.commutes c).symm
      · rintro (i|i)
        · exact slot_read p g (h (get z)) (den (get z)) (.inl i)
        · exact (slot_read p g (h (get z)) (den (get z)) (.inr i)).trans
            (congrFun eq i).symm
    change point (ev (get z)).toRingHom≫j=z.val.left
    rw [ev_eq]
    exact readActual_returns a P33 σ j jBase (oldPart a P33 σ p j jBase r ρ z)
  · apply Topology.IsInducing.subtypeVal.continuous_iff.2
    exact mapped_continuous a P33 σ embedding C j jBase ev
      (all_branch_evaluations_continuous p g sc Subtype.val y continuous_subtype_val cy h den)
  · apply Topology.IsInducing.subtypeVal.continuous_iff.2
    apply continuous_pi
    intro i
    have ct : Continuous (oldPart a P33 σ p j jBase r ρ) :=
      Topology.IsInducing.subtypeVal.continuous_iff.2 continuous_subtype_val
    exact (readActual_continuous a P33 σ embedding C j jBase (slot p (.inl i))).comp ct

include interior unique cy in
theorem homeo_reads_same_original (x : D) :
    ((localHomeo a P33 σ embedding C p g sc j jBase r ρ y h den interior unique cy) x).val =
      markedPoint p g a P33 σ j (by rw [sc]; exact jBase) (h x) (den x) := by
  apply Over.OverMorphism.ext
  rfl

end OriginalRetainedActualCenteredBand318
