module
public import MonicRootProjectionOpen318
public import LocalizedPrimitiveRootChart318
public import OpenComplexPolynomialIndependence318
public section
noncomputable section
namespace LocalizedMonicRootDensity318
open Set Polynomial
variable {ι : Type*} [Fintype ι]

/-- A nonzero complex polynomial has genuinely Euclidean-dense
nonvanishing locus, by the proved analytic polynomial identity principle. -/
lemma polynomial_nonzero_dense (d : MvPolynomial ι ℂ) (hd : d ≠ 0) :
    Dense {v : ι → ℂ | MvPolynomial.eval v d ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  apply hd
  apply OpenComplexPolynomialIndependence318.eq_zero_of_open d U hU hne
  intro v hv
  by_contra hn
  exact h ⟨v,hv,hn⟩

abbrev BaseOpen (d : MvPolynomial ι ℂ) := {v : ι → ℂ // MvPolynomial.eval v d ≠ 0}
@[expose] def family (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))
    (v : BaseOpen d) : Polynomial ℂ :=
  Q.map (ComplexPolynomialOpenPoints318.evaluation d v.val v.property)

lemma baseOpen_isOpen (d : MvPolynomial ι ℂ) :
    IsOpen {v : ι → ℂ | MvPolynomial.eval v d ≠ 0} := by
  have hc : Continuous (fun v : ι → ℂ => MvPolynomial.eval v d) :=
    continuous_iff_continuousAt.mpr (fun v =>
      ((AnalyticOnNhd.eval_mvPolynomial d) v (mem_univ v)).continuousAt)
  exact isOpen_ne_fun hc continuous_const

lemma family_eval_continuous (d : MvPolynomial ι ℂ)
    (Q : Polynomial (Localization.Away d)) (z : ℂ) :
    Continuous (fun v : BaseOpen d => (family d Q v).eval z) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hc := (LocalizedPrimitiveRootChart318.equation_analytic d Q v.val v.property z).continuousAt
  have ht : Continuous (fun w : BaseOpen d => (w.val,z)) :=
    continuous_subtype_val.prodMk continuous_const
  have he := hc.comp ht.continuousAt
  apply he.congr
  exact Filter.Eventually.of_forall (fun w =>
    LocalizedPrimitiveRootChart318.equation_on_open d Q w.val w.property z)

/-- The entire root locus over the SAME original localization has a
proved OPEN projection, even where the specialized derivative vanishes.
No separability assumption or discriminant inversion is used. -/
theorem projection_open (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))
    (hm : Q.Monic) :
    IsOpenMap (fun q : MonicRootProjectionOpen318.Roots (family d Q) => q.val.1) :=
  MonicRootProjectionOpen318.projection_open (family d Q) Q.natDegree
    (fun v => hm.map _) (fun v => hm.natDegree_map _)
    (family_eval_continuous d Q)

/-- Removing ANY nonzero base polynomial from this full monic root
locus leaves a genuinely Euclidean-dense set. This includes multiple and
ramified roots over its zero divisor. It is a density producer on the
specified monic model, not yet on an arbitrary nonmonogenic chart. -/
theorem dense_nonvanishing (d : MvPolynomial ι ℂ)
    (Q : Polynomial (Localization.Away d)) (hm : Q.Monic)
    (a : MvPolynomial ι ℂ) (ha : a ≠ 0) :
    Dense {q : MonicRootProjectionOpen318.Roots (family d Q) |
      MvPolynomial.eval q.val.1.val a ≠ 0} := by
  have hb : Dense {v : BaseOpen d | MvPolynomial.eval v.val a ≠ 0} :=
    (polynomial_nonzero_dense a ha).preimage
      (baseOpen_isOpen d).isOpenEmbedding_subtypeVal.isOpenMap
  exact hb.preimage (projection_open d Q hm)
end LocalizedMonicRootDensity318
