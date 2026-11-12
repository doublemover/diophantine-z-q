module
public import RelativeAmbientCharts318
public section
noncomputable section
namespace CartesianSourceOpenCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C B S : Scheme.{u}} (q : C ⟶ S) (b : B ⟶ S) (U : B.OpenCover)
  (D : U.I₀ → Scheme.{u}) (a : ∀ i,D i ⟶ C) (d : ∀ i,D i ⟶ U.X i)
  (H : ∀ i,IsPullback (a i) (d i) q (U.f i≫b))
abbrev into (i : U.I₀) : D i ⟶ pullback q b :=
  RelativeAmbientCharts318.lift q b (U.f i) (a i) (d i) (H i)
/-- A genuine full cover by the specified Cartesian source models.
No replacement by reduced points or assumed covering is used. -/
def cover : (pullback q b).OpenCover where
  I₀ := U.I₀
  X := D
  f := into q b U D a d H
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i,z,hz⟩ := RelativeAmbientCharts318.covers q b U D a d H x
      exact ⟨i,z,hz⟩
    · intro i
      dsimp [into]
      infer_instance
@[reassoc] lemma source (i : U.I₀) : into q b U D a d H i≫pullback.fst q b=a i :=
  RelativeAmbientCharts318.lift_original q b (U.f i) (a i) (d i) (H i)
@[reassoc] lemma base (i : U.I₀) : into q b U D a d H i≫pullback.snd q b=d i≫U.f i :=
  RelativeAmbientCharts318.lift_projection q b (U.f i) (a i) (d i) (H i)
lemma cartesian (i : U.I₀) : IsPullback (into q b U D a d H i) (d i)
    (pullback.snd q b) (U.f i) :=
  RelativeAmbientCharts318.square q b (U.f i) (a i) (d i) (H i)
end CartesianSourceOpenCover318
