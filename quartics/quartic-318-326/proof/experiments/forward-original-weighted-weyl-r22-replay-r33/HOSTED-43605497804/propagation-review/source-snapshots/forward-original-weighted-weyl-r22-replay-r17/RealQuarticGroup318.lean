module
public import RealQuarticAssociativity318
public section
noncomputable section
namespace RealQuarticGroup318
open ReciprocalGroup318 RealQuarticSumU318 RealQuarticSumAnalytic318 RealQuarticAssociativity318
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The full ordinary real quartic oval, not just a normalized chart branch. -/
abbrev Oval (D : ℝ) := {p : ℝ × ℝ // p.2^2=1-D*p.1^4}

@[expose] def zero (D : ℝ) : Oval D := ⟨(0,1),by norm_num⟩
@[expose] def neg {D : ℝ} (p : Oval D) : Oval D := ⟨(-p.val.1,p.val.2),by
  change p.val.2^2=1-D*(-p.val.1)^4
  convert p.property using 1
  ring⟩
@[expose] def add {D : ℝ} (hD : 0<D) (p q : Oval D) : Oval D :=
  ⟨(sumU D p.val.1 p.val.2 q.val.1 q.val.2,
     sumV D p.val.1 p.val.2 q.val.1 q.val.2),
    sum_curve D _ _ _ _ p.property q.property (denominator_ne hD _ _)⟩

lemma add_comm {D : ℝ} (hD : 0<D) (p q : Oval D) : add hD p q=add hD q p := by
  apply Subtype.ext
  apply Prod.ext
  · exact sumU_comm _ _ _ _ _
  · dsimp [add,sumV]
    congr 1 <;> ring

lemma zero_add {D : ℝ} (hD : 0<D) (p : Oval D) : add hD (zero D) p=p := by
  apply Subtype.ext
  simp [add,zero,sumU,sumV]

lemma add_zero {D : ℝ} (hD : 0<D) (p : Oval D) : add hD p (zero D)=p := by
  rw [add_comm,zero_add]

lemma neg_add {D : ℝ} (hD : 0<D) (p : Oval D) : add hD (neg p) p=zero D := by
  apply Subtype.ext
  apply Prod.ext
  · simp [add,neg,zero,sumU]
  · change sumV D (-p.val.1) p.val.2 p.val.1 p.val.2=1
    have hq := denominator_ne hD (-p.val.1) p.val.1
    unfold sumV
    field_simp [hq]
    linear_combination (1-D*p.val.1^4)*p.property

lemma add_assoc {D : ℝ} (hD : 0<D) (p q r : Oval D) :
    add hD (add hD p q) r=add hD p (add hD q r) := by
  apply Subtype.ext
  apply Prod.ext
  · exact sumU_associative hD _ _ _ _ _ _ p.property q.property r.property
  · exact sumV_associative hD _ _ _ _ _ _ p.property q.property r.property

/-- The rational quartic formulas define an actual commutative group on the
whole real oval. In particular, no tangent, inverse or zero-ordinate branches
are excluded by a division hypothesis. -/
@[expose, instance_reducible] def group (D : ℝ) (hD : 0<D) : AddCommGroup (Oval D) := by
  letI : Add (Oval D) := ⟨add hD⟩
  letI : Zero (Oval D) := ⟨zero D⟩
  letI : Neg (Oval D) := ⟨neg⟩
  exact {
  add := add hD
  zero := zero D
  neg := neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := add_assoc hD
  zero_add := zero_add hD
  add_zero := add_zero hD
  neg_add_cancel := neg_add hD
  add_comm := add_comm hD }

end RealQuarticGroup318
