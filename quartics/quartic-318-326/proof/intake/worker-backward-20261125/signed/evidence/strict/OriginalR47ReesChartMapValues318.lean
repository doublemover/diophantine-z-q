module
public import OriginalR47ReesLiteralFractions318
public import OriginalR47ReesCoefficientMap318
public section
noncomputable section

namespace OriginalR47ReesChartMapValues318

open Polynomial HomogeneousLocalization Graded
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalAffineReesChartLocal318 OriginalR47ReesLiteralFractions318
open OriginalR47ReesCoefficientMap318 (mapGraded generator_read homogeneous_read)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : Type*} [CommRing A] [CommRing B]
variable (I : Ideal A) (f : A →+* B) (a : A) (ha : a ∈ I)

abbrev newChart := chart (I.map f) (f a) (Ideal.mem_map_of_mem f ha)
abbrev newHa : f a ∈ I.map f := Ideal.mem_map_of_mem f ha
abbrev chartHom : chart I a ha →+* newChart I f a ha :=
  OriginalR47ReesCoefficientMap318.chartMap I f a ha

def mappedNum (n : ℕ) (r : ↥(I^n)) : ↥((I.map f)^n) :=
  ⟨f r.val, by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f r.property⟩

/-- The canonical map of genuine Proj charts preserves every numerator
and power of the *same* selected degree-one generator. -/
theorem chart_ratio (n : ℕ) (r : ↥(I^n)) :
    chartHom I f a ha (ratio I a ha n r) =
      ratio (I.map f) (f a) (newHa I f a ha) n (mappedNum I f n r) := by
  apply HomogeneousLocalization.val_injective _
  simp only [chartHom, OriginalR47ReesCoefficientMap318.chartMap, ratio,
    HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  congr 1
  · exact homogeneous_read I f n r.val r.property
  · apply Subtype.ext
    change mapGraded I f ((generator I a ha)^n) =
      (generator (I.map f) (f a) (newHa I f a ha))^n
    exact ((mapGraded I f).map_pow (generator I a ha) n).trans
      (congrArg (fun z : Rees (I.map f) => z^n) (generator_read I f a ha))

theorem scalar_ratio {T : Type*} [CommRing T] (J : Ideal T) (b : T) (hb : b ∈ J) (r : T) :
    chartScalars J b hb r = ratio J b hb 0 ⟨r, by simp⟩ := by
  apply chartEval_injective J b hb
  rw [chartEval_scalar, chartEval_ratio]
  have he : (⟨b^0, 0, rfl⟩ : Submonoid.powers b) = 1 := Subtype.ext (pow_zero b)
  rw [he, IsLocalization.mk'_one]

/-- The named scalar map in the tensor pushout, on the actual chart. -/
theorem chart_scalar (r : A) :
    chartHom I f a ha (chartScalars I a ha r) =
      chartScalars (I.map f) (f a) (newHa I f a ha) (f r) := by
  rw [scalar_ratio I a ha r, chart_ratio]
  exact (scalar_ratio (I.map f) (f a) (newHa I f a ha) (f r)).symm

theorem ambient_powers :
    Submonoid.powers a ≤ (Submonoid.powers (f a)).comap f := by
  rintro _ ⟨n,rfl⟩
  exact ⟨n,(f.map_pow a n).symm⟩

/-- Ambient coefficient extension through the localization of the
actual coefficient ring at the chart's chosen denominator. -/
def ambient : Localization.Away a →+* Localization.Away (f a) :=
  IsLocalization.map _ f (ambient_powers f a)

theorem ambient_ratio (n : ℕ) (r : A) :
    ambient f a (IsLocalization.mk' (Localization.Away a) r
        (⟨a^n,n,rfl⟩ : Submonoid.powers a)) =
      IsLocalization.mk' (Localization.Away (f a)) (f r)
        (⟨(f a)^n,n,rfl⟩ : Submonoid.powers (f a)) := by
  rw [ambient, IsLocalization.map_mk']
  have hd : (⟨f (a^n),ambient_powers f a (show a^n ∈ Submonoid.powers a from ⟨n,rfl⟩)⟩ :
      Submonoid.powers (f a)) = ⟨(f a)^n,n,rfl⟩ := Subtype.ext (f.map_pow a n)
  exact congrArg (IsLocalization.mk' (Localization.Away (f a)) (f r)) hd

/-- Exact factorization in the ambient actual localization, before
applying flatness. No auxiliary fraction field or domain assumption. -/
theorem chart_ambient (z : chart I a ha) :
    chartEval (I.map f) (f a) (newHa I f a ha) (chartHom I f a ha z) =
      ambient f a (chartEval I a ha z) := by
  obtain ⟨n,r,hr⟩ := exists_ratio I a ha z
  rw [← hr, chart_ratio, chartEval_ratio, chartEval_ratio, ambient_ratio]
  rfl

end OriginalR47ReesChartMapValues318

#print axioms OriginalR47ReesChartMapValues318.chart_ratio
#print axioms OriginalR47ReesChartMapValues318.chart_scalar
#print axioms OriginalR47ReesChartMapValues318.chart_ambient
