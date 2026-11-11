module
public import OriginalPointFinitePlaceRoots318
public import LiteralContactMetricCharts318
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace OriginalArchimedeanMarkedPoint318
open NumberField OriginalPointFinitePlaceRoots318 FourRootNormalizedPointCharts318
open LiteralMetricExtension318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)

lemma contacts_cast (i : Fin 4) : (LinearContactSquareclass318.contacts i : ℂ)=contacts i := by
  fin_cases i <;> norm_num [LinearContactSquareclass318.contacts,contacts]
include hn in
lemma coordinate_ne (i : Fin 4) : (t:ℂ)≠contacts i := by
  intro h
  have ht : t=LinearContactSquareclass318.contacts i := by
    exact Rat.cast_injective (h.trans (contacts_cast i).symm)
  exact hn i (by rw [RationalContactPoint318.parameters_eq,ht,sub_self,mul_zero])

/-- Only the constant twist square roots are chosen. The point roots retain
exactly the signs of the original quotient-field point under the place. -/
@[expose] def twistRoot (i : Fin 4) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq ((c i:ℚ):ℂ) (by decide : 0<2))
lemma twistRoot_square (i : Fin 4) : twistRoot c i^2=((c i:ℚ):ℂ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((c i:ℚ):ℂ) (by decide : 0<2))
lemma twistRoot_ne (i : Fin 4) : twistRoot c i≠0 := by
  intro h
  have hc : ((c i:ℚ):ℂ)≠0 := Rat.cast_ne_zero.mpr (Units.ne_zero _)
  exact hc (by rw [←twistRoot_square c i,h];norm_num)

variable (w : InfinitePlace (K c t))
@[expose] def markedRoot (i : Fin 4) : ℂ := w.embedding (roots c t i)
lemma markedRoot_square (i : Fin 4) : markedRoot c t w i^2=
    ((c i:ℚ):ℂ)*((t:ℂ)-contacts i) := by
  have h := congrArg w.embedding (roots_square c t i)
  simpa only [map_pow,map_ratCast,Rat.cast_mul,Rat.cast_sub,contacts_cast,markedRoot] using h
include hn in
lemma markedRoot_ne (i : Fin 4) : markedRoot c t w i≠0 := by
  intro h
  have hh := markedRoot_square c t w i
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact (mul_ne_zero (Rat.cast_ne_zero.mpr (Units.ne_zero _))
    (sub_ne_zero.mpr (coordinate_ne c t hn i))) hh.symm

@[expose] def point : FinitePoints contacts :=
  ⟨((t:ℂ),fun i => markedRoot c t w i/twistRoot c i),by
    intro i
    dsimp only
    rw [div_pow,markedRoot_square,twistRoot_square]
    field_simp [Rat.cast_ne_zero.mpr (Units.ne_zero (c i))]⟩
@[expose] def completedPoint : Completed contacts := .inl (point c t w)
lemma point_root (i : Fin 4) : (point c t w).val.2 i*twistRoot c i=markedRoot c t w i :=
  div_mul_cancel₀ _ (twistRoot_ne c i)
include hn in
lemma regular : LiteralContactMetricCharts318.Regular (completedPoint c t w) :=
  coordinate_ne c t hn
lemma markedRoot_norm (i : Fin 4) : ‖markedRoot c t w i‖=w (roots c t i) :=
  InfinitePlace.norm_embedding_eq w _
end OriginalArchimedeanMarkedPoint318
