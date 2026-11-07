module
public import CompressedGeneratorBridge318
public import GlobalNormCoset318
public section
namespace RawCompressedLabels318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalNormClasses318 GlobalNormCoset318
open CompressedGeneratorBridge318 CircuitReplay Raw318FinalReplay WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The literal norm-square row supplies the actual norm-square point
predicate after transporting to the same group as all source root labels. -/
theorem source_H_norm_square (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    NormSquare (transport curve_eq (CompressedTranslation318.H S w source)) := by
  rw [CompressedTranslation318.H,transport_some]
  change IsSquare (AnchorNorm318.norm (CompressedPoint318.xH w))
  rw [CompressedPoint318.xH,one_div,AnchorNorm318.norm_inv]
  have hn := CompressedGlobal318.source_norm_square S w source
  change AnchorNorm318.norm (CompressedOrientation318.fH w)=(w 37)^2 at hn
  rw [hn]
  exact ⟨(w 37)⁻¹,by simp [pow_two]⟩

/-- Actual source labels for H and V with one common 2-torsion offset.
The signed translation H−V=P is preserved exactly. The only hypotheses
beyond the literal source are the two stated global descent assertions. -/
theorem source_HV_labels (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (classes:FirstDescentClasses) (hg:RawGroupAnchor318.SquarePointGeneration) :
    ∃(n:ℤ)(τ:E.Point),(τ=0 ∨ τ=T 0) ∧
      transport curve_eq (CompressedTranslation318.H S w source)=n • P+τ ∧
      transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+τ := by
  obtain ⟨n,hn⟩ := norm_square_coset classes hg
    (transport curve_eq (CompressedTranslation318.H S w source)) (source_H_norm_square S w source)
  have ht := CompressedGeneratorBridge318.source_translation S w source
  have hv : transport curve_eq (CompressedTranslation318.V S w source)=
      transport curve_eq (CompressedTranslation318.H S w source)-P := by
    have he := sub_eq_iff_eq_add.mp ht
    rw [he]; abel
  rcases hn with hh|hh
  · refine ⟨n,0,Or.inl rfl,by simpa using hh,?_⟩
    rw [hv,hh,sub_zsmul,one_zsmul,add_zero,sub_eq_add_neg]
  · refine ⟨n,T 0,Or.inr rfl,hh,?_⟩
    rw [hv,hh,sub_zsmul,one_zsmul]; abel

/-- The compressed source H is never either of the two allowed pure torsion
points: its finite ordinate is globally nonzero. -/
theorem source_H_not_pure_torsion (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    transport curve_eq (CompressedTranslation318.H S w source)≠0 ∧
    transport curve_eq (CompressedTranslation318.H S w source)≠T 0 := by
  rw [CompressedTranslation318.H,transport_some]
  constructor
  · exact Point.some_ne_zero _
  · intro he
    rw [T,Point.some.injEq] at he
    exact (CompressedGlobal318.source_global_H S w source).2.1 he.2

theorem source_H_label_ne_zero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (n:ℤ) (τ:E.Point) (ht:τ=0 ∨ τ=T 0)
    (he:transport curve_eq (CompressedTranslation318.H S w source)=n • P+τ) : n≠0 := by
  intro hn
  rw [hn,zero_zsmul,zero_add] at he
  have hh := source_H_not_pure_torsion S w source
  rcases ht with ht|ht
  · exact hh.1 (he.trans ht)
  · exact hh.2 (he.trans ht)

end
end RawCompressedLabels318
