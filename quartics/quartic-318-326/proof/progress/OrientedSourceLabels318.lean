module
public import ActualGlobalGenerator318
public import RawRootDifference318
public import TorsionSafeIndex318
public section
namespace OrientedSourceLabels318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 RawOddAnchorPoints318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Actual unconditional square-abscissa generation, composed from the
 separately proved arithmetic, finite search, height and rank packets. -/
theorem square_generation : RawGroupAnchor318.SquarePointGeneration :=
  GlobalSaturation318.square_point_generation ActualCanonicalHeight318.canonical_data
    PrimitiveQuadraticMahler318.polynomial_height_coverage ActualGlobalRank318.odd_rank_one_data
    GlobalDualSquare318.dual_square_abscissa

/-- Either reciprocal endpoint, and either ordinate sign, is assigned its
 actual global integer label. There is no local formal-branch assumption. -/
theorem reciprocal_label (u v:K) (hv:v≠0) (hc:v^2=1-CompressedOrientation318.D*u^4) :
    ∃n:ℤ,n • P=transport curve_eq (PrimaryFormal318.point u v hv hc) := by
  by_cases hu:u=0
  · refine ⟨0,?_⟩
    simp only [PrimaryFormal318.point,dite_eq_left hu,zero_zsmul,map_zero]
  have hD:CompressedOrientation318.D=D := by
    ext <;> norm_num [CompressedOrientation318.D,D,i,pair,pow_succ]
  have hj:(v/u^2)^2=(u⁻¹)^4-D := by
    rw [hD] at hc
    field_simp [hu]
    linear_combination hc
  obtain ⟨n,hn⟩:=square_generation (u⁻¹) (v/u^2) hj
  refine ⟨n,?_⟩
  rw [PrimaryFormal318.point,dite_eq_right hu,transport_some]
  have hx:(u⁻¹)^2=1/u^2 := by simp [one_div,inv_pow]
  have hy:u⁻¹*(v/u^2)=v/u^3 := by field_simp [hu]
  simpa only [hx,hy] using hn

/-- Actual U and V labels, not arbitrary signs of their difference roots. -/
theorem source_UV_labels (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    ∃(uLabel vLabel:Fin 4→ℤ),
      (∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j)) ∧
      (∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j)) := by
  have hu:∀j:Fin 4,∃n:ℤ,n • P=transport curve_eq (RawRootDifference318.U S w source j) := by
    intro j
    exact reciprocal_label _ _ _ _
  have hv:∀j:Fin 4,∃n:ℤ,n • P=transport curve_eq (RawRootDifference318.V S w source j) := by
    intro j
    exact reciprocal_label _ _ _ _
  choose uLabel hu using hu
  choose vLabel hv using hv
  exact ⟨uLabel,vLabel,hu,hv⟩

theorem root_binding (w:Assignment) (j:Fin 4) :
    RawRootDifference318.root w j=RawAnchorNorm318.root w j := by fin_cases j <;> rfl

/-- The oriented differences themselves satisfy the root-label predicate
 used by the raw odd anchor and scalar Kummer orientation. -/
theorem difference_root_labels (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (uLabel vLabel:Fin 4→ℤ)
    (hu:∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U S w source j))
    (hv:∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V S w source j)) :
    RootLabels w (fun j=>uLabel j-vLabel j) := by
  intro j
  obtain ⟨y,h,he⟩:=RawRootDifference318.source_differences S w source j
  have hh:=congrArg (transport curve_eq) he
  rw [map_sub,transport_some,←hu,←hv] at hh
  have hid:(uLabel j-vLabel j) • P=uLabel j • P-vLabel j • P := by exact sub_smul _ _ _
  rw [←hid] at hh
  have hy:E.Nonsingular ((RawAnchorNorm318.root w j)^2) y := by simpa only [root_binding,←curve_eq] using h
  refine ⟨y,hy,?_⟩
  simpa only [root_binding] using hh

/-- One consistent global choice for both log-ratio families and the exact
 root/scalar labels. Oddness and the enormous scalar bound hold for these
 oriented labels, rather than labels with an unrelated ordinate sign. -/
theorem source_oriented_labels (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    ∃(uLabel vLabel:Fin 4→ℤ)(c n:ℤ)(tau:E.Point),
      (∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U ((3:ℚ)^65536) w source j)) ∧
      (∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V ((3:ℚ)^65536) w source j)) ∧
      RootLabels w (fun j=>uLabel j-vLabel j) ∧ ScalarLabel w c ∧
      (∀j,Odd (uLabel j-vLabel j)) ∧
      (c=(uLabel 1-vLabel 1)-1 ∨ c= -(uLabel 1-vLabel 1)-1) ∧
      (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) ∧
      n≠0 ∧ (tau=0 ∨ tau=T 0) ∧
      transport curve_eq (CompressedTranslation318.H ((3:ℚ)^65536) w source)=n • P+tau ∧
      transport curve_eq (CompressedTranslation318.V ((3:ℚ)^65536) w source)=(n-1) • P+tau := by
  obtain ⟨ul,vl,hu,hv⟩:=source_UV_labels _ w source
  have hroots:=difference_root_labels _ w source ul vl hu hv
  obtain ⟨hodd,c,hc,hor,hdiv,hbound⟩:=RawScalarOrientation318.source_anchor_from_root_labels w source _ hroots
  obtain ⟨n,tau,ht,hH,hV⟩:=RawCompressedLabels318.source_HV_labels _ w source
    GlobalFirstDescent318.first_descent_classes square_generation
  have hn:=RawCompressedLabels318.source_H_label_ne_zero _ w source n tau ht hH
  exact ⟨ul,vl,c,n,tau,hu,hv,hroots,hc,hodd,hor,hdiv,hbound,hn,ht,hH,hV⟩

end
end OrientedSourceLabels318
#print axioms OrientedSourceLabels318.square_generation
#print axioms OrientedSourceLabels318.source_oriented_labels
