module
public import PointwiseConverseRawMatrixReconstruction
public import PointwiseConverseOuterDefect

public section
noncomputable section

open Filter
open PointwiseConverseInnerStabilization
open PointwiseConverseRawMatrixReceiver
open PointwiseConverseRawMatrixReconstruction
open PointwiseConverseOuterDefect

namespace PointwiseConverseMatchedInnerOuter

universe u v

/-- Arithmetic-facing ABI at one fixed outer instance. The two packets
already use the same retained finite basis, oriented coefficient model and
one cofinal inner ultrafilter. This structure is an input, not a producer
of finite Artin quotients or Frobenius representatives. -/
structure RawMatch (S : Shape) where
  inner : Ultrafilter ℕ
  cofinal : (inner : Filter ℕ) ≤ atTop
  left : (i : ℕ) → Packet S i
  right : (i : ℕ) → Packet S i
  fullMatch : ∀ᶠ i in (inner : Filter ℕ), left i = right i

def seriesAt (S : Shape) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (stage : (i : ℕ) → Packet S i) : SeriesPacket S :=
  Classical.choose (existsUnique_stabilized_series S U hU stage).exists

theorem seriesAt_spec (S : Shape) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (stage : (i : ℕ) → Packet S i) (r : ℕ) :
    ∀ᶠ i in (U : Filter ℕ), row S stage r i = cut S r (seriesAt S U hU stage) :=
  (Classical.choose_spec (existsUnique_stabilized_series S U hU stage).exists) r

def leftSeries {S : Shape} (M : RawMatch S) : SeriesPacket S :=
  seriesAt S M.inner M.cofinal M.left

def rightSeries {S : Shape} (M : RawMatch S) : SeriesPacket S :=
  seriesAt S M.inner M.cofinal M.right

theorem matched_series_eq {S : Shape} (M : RawMatch S) : leftSeries M = rightSeries M := by
  apply cut_injective S
  intro r
  calc
    cut S r (leftSeries M) = stabilizedValue M.inner (row S M.left r) :=
      (stabilizedValue_eq_of_eventually M.inner (row S M.left r)
        (seriesAt_spec S M.inner M.cofinal M.left r)).symm
    _ = stabilizedValue M.inner (row S M.right r) :=
      stabilized_rows_eq S M.inner M.left M.right M.fullMatch r
    _ = cut S r (rightSeries M) :=
      stabilizedValue_eq_of_eventually M.inner (row S M.right r)
        (seriesAt_spec S M.inner M.cofinal M.right r)

abbrev IntegralPacket (S : Shape) (R : Type v) : Type v :=
  (m : Fin S.slots) → Fin (S.rows m) → Fin (S.cols m) → R

/-- Apply only a hom on the full reconstructed series ring. No map out of a
truncated t-ring appears here. The actual localization/completion map is
supplied by arithmetic in the intended application. -/
def mapFullSeriesPacket (S : Shape) {R : Type v} [CommRing R]
    (σ : PowerSeries (PadicInt 2) →+* R) (A : SeriesPacket S) : IntegralPacket S R :=
  fun m a b => σ (A m a b)

theorem matched_specialization_eq {S : Shape} (M : RawMatch S) {R : Type v} [CommRing R]
    (σ : PowerSeries (PadicInt 2) →+* R) :
    mapFullSeriesPacket S σ (leftSeries M) = mapFullSeriesPacket S σ (rightSeries M) :=
  congrArg (mapFullSeriesPacket S σ) (matched_series_eq M)

/-- Narrow conditional interface for the §5.7 inner/outer seam.
Each j has one retained inner clock shared by its left/right evaluations.
An actual integral coordinate extraction and one fixed clearing identity
are inputs. The right-hand cleared relation then uses the exact same
coefficient matrix, and the defect dies only in the outer quotient. -/
theorem matched_integral_outer_identity {ι : Type u} (F : Filter ι) (R : ι → Type v)
    [∀ j, CommRing (R j)] [∀ j, IsDomain (R j)]
    (two_ne_zero : ∀ j, (2 : R j) ≠ 0)
    (S : ι → Shape) (M : ∀ j, RawMatch (S j))
    (σ : ∀ j, PowerSeries (PadicInt 2) →+* R j)
    (d e c : ℕ) (x : ∀ j, Fin d → R j) (A B : ∀ j, Fin e → R j)
    (L : ∀ j, IntegralPacket (S j) (R j) → ((Fin d → R j) →ₗ[R j] (Fin e → R j)))
    (hx : VectorVanishes F R d x)
    (hclear : ∀ᶠ j in F, ((2 : R j) ^ c) • (A j - B j) =
      L j (mapFullSeriesPacket (S j) (σ j) (leftSeries (M j))) (x j)) :
    (∀ j, leftSeries (M j) = rightSeries (M j)) ∧
      (∀ j, mapFullSeriesPacket (S j) (σ j) (leftSeries (M j)) =
        mapFullSeriesPacket (S j) (σ j) (rightSeries (M j))) ∧
      (∀ k : Fin e,
        outerReduction F R (fun j => A j k) = outerReduction F R (fun j => B j k)) := by
  have hs : ∀ j, mapFullSeriesPacket (S j) (σ j) (leftSeries (M j)) =
      mapFullSeriesPacket (S j) (σ j) (rightSeries (M j)) :=
    fun j => matched_specialization_eq (M j) (σ j)
  refine ⟨fun j => matched_series_eq (M j), hs, ?_⟩
  have hright : ∀ᶠ j in F, ((2 : R j) ^ c) • (A j - B j) =
      L j (mapFullSeriesPacket (S j) (σ j) (rightSeries (M j))) (x j) :=
    hclear.mono (fun j hj => by rw [← hs j]; exact hj)
  exact cleared_identity_in_outer F R two_ne_zero d e c x A B
    (fun j => L j (mapFullSeriesPacket (S j) (σ j) (rightSeries (M j)))) hx hright

end PointwiseConverseMatchedInnerOuter
