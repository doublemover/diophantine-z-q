module
public import NormalizingRadicals318
public import ShortCurveBaseChange318
public section
noncomputable section

/-! Actual normalized elliptic points and the selective radical involution.
The conclusions concern the algebraic group, not its real topology. -/
namespace NormalizedPointSigns318
open NormalizingRadicals318
open ConcreteG8Domain (K)
open ReciprocalDouble318 ShortCurveBaseChange318
-- Capture each primitive from a generic Field before specializing the
-- nested quadratic tower. Direct quadratic-ring instances otherwise cause
-- the constructor to expand concrete fourth powers while comparing spines.
abbrev fieldZero {F : Type*} [Field F] : Zero F := inferInstance
abbrev fieldOne {F : Type*} [Field F] : One F := inferInstance
abbrev fieldAdd {F : Type*} [Field F] : Add F := inferInstance
abbrev fieldMul {F : Type*} [Field F] : Mul F := inferInstance
abbrev fieldSub {F : Type*} [Field F] : Sub F := inferInstance
abbrev fieldNeg {F : Type*} [Field F] : Neg F := inferInstance
abbrev fieldNatPow {F : Type*} [Field F] : Pow F ℕ := inferInstance

local instance : Zero Both := @fieldZero Both NormalizingRadicals318.bothField
local instance : One Both := @fieldOne Both NormalizingRadicals318.bothField
local instance : Add Both := @fieldAdd Both NormalizingRadicals318.bothField
local instance : Mul Both := @fieldMul Both NormalizingRadicals318.bothField
local instance : Sub Both := @fieldSub Both NormalizingRadicals318.bothField
local instance : Neg Both := @fieldNeg Both NormalizingRadicals318.bothField
local instance : Pow Both ℕ := @fieldNatPow Both NormalizingRadicals318.bothField

-- Align reciprocal-point operations with the exact field instance.
local instance : CommRing Both := NormalizingRadicals318.bothField.toCommRing
local instance : DecidableEq Both := Classical.decEq Both
set_option maxHeartbeats 1000000
-- Let typed proof boundaries unfold the same imported algebraic structures.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option diagnostics true

/-- All construction proofs are elaborated with an abstract target field.
Specializing this whole term avoids comparing a separately elaborated
concrete tower fourth power at the reciprocal-point constructor boundary. -/
section GenericTarget
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

lemma target_curve (φ : K →+* L) (d u v : K) (r : L)
    (hr : r^2=φ d) (hc : v^2=1-d^2*u^4) :
    (φ v)^2=1-(1:L)*(r*φ u)^4 := by
  have he := congrArg φ hc
  simp only [map_pow,map_sub,map_one,map_mul] at he
  rw [show (r*φ u)^4=(r^2)^2*(φ u)^4 by ring,hr]
  simpa only [one_mul] using he

@[expose] def targetPoint (φ : K →+* L) (d : K) (r : L) (hr : r^2=φ d)
    (u v : K) (hv : v≠0) (hc : v^2=1-d^2*u^4) : (E (1:L)).Point :=
  point 1 (r*φ u) (φ v)
    (fun h => hv (φ.injective (h.trans φ.map_zero.symm)))
    (target_curve φ d u v r hr hc)

@[expose] def targetFlip (σ : L →+* L) : (E (1:L)).Point →+ (E (1:L)).Point :=
  (transport (congrArg E σ.map_one)).toAddMonoidHom.comp (pointMap σ 1)

private lemma target_transport (D D' u v : L) (h : D=D')
    (hv : v≠0) (hc : v^2=1-D*u^4) :
    transport (congrArg E h) (point D u v hv hc)=point D' u v hv (h ▸ hc) := by
  subst D'
  rfl

lemma targetFlip_reciprocal (σ : L →+* L) (u v : L) (hv : v≠0)
    (hc : v^2=1-(1:L)*u^4) :
    targetFlip σ (point 1 u v hv hc)=
      point 1 (σ u) (σ v)
        (fun h => hv (σ.injective (h.trans σ.map_zero.symm)))
        (by simpa only [map_pow,map_sub,map_one,map_mul] using congrArg σ hc) := by
  change transport (congrArg E σ.map_one) (pointMap σ 1 (point 1 u v hv hc))=_
  rw [pointMap_reciprocal,target_transport]

lemma targetFlip_fixed (φ : K →+* L) (d : K) (r : L) (hr : r^2=φ d)
    (σ : L →+* L) (hbase : ∀ x, σ (φ x)=φ x) (hroot : σ r=r)
    (u v : K) (hv : v≠0) (hc : v^2=1-d^2*u^4) :
    targetFlip σ (targetPoint φ d r hr u v hv hc)=targetPoint φ d r hr u v hv hc := by
  unfold targetPoint
  rw [targetFlip_reciprocal]
  simp only [map_mul,hroot,hbase]

lemma targetFlip_negative (φ : K →+* L) (d : K) (r : L) (hr : r^2=φ d)
    (σ : L →+* L) (hbase : ∀ x, σ (φ x)=φ x) (hroot : σ r= -r)
    (u v : K) (hv : v≠0) (hc : v^2=1-d^2*u^4) :
    targetFlip σ (targetPoint φ d r hr u v hv hc)= -targetPoint φ d r hr u v hv hc := by
  unfold targetPoint
  rw [targetFlip_reciprocal]
  simp only [map_mul,hroot,hbase,neg_mul]
  exact point_negative 1 _ _ _ _

end GenericTarget

#check targetPoint
#check targetFlip_reciprocal
#check targetFlip_fixed
#check targetFlip_negative

/-- Keep the two scalar maps literal; no implicit scalar-tower identification. -/
@[expose] abbrev base : K →+* Both :=
  (algebraMap First Both).comp (algebraMap K First)


#check base

lemma flip_base (x : K) : flipSecond (base x)=base x :=
  flipSecond_base x

#check flip_base


/-- The normalization uses r*u, not u/r. The induced reciprocal coordinates
are x/r^2 and y/r^3. -/
lemma normalized_curve (d u v : K) (r : Both)
    (hr : r^2=base d) (hc : v^2=1-d^2*u^4) :
    (base v)^2=1-(1:Both)*(r*base u)^4 := by
  have he := congrArg base hc
  simp only [map_pow,map_sub,map_one,map_mul] at he
  rw [show (r*base u)^4=(r^2)^2*(base u)^4 by ring,hr]
  simpa only [one_mul] using he


#check normalized_curve

/-- Expand the composite base map before comparing the imported radical law. -/
lemma first_square : firstRoot^2=base delta := by
  simpa only [base,RingHom.comp_apply] using firstRoot_square

#check first_square

lemma second_square : secondRoot^2=base deltaBar := by
  simpa only [base,RingHom.comp_apply] using secondRoot_square

#check second_square

lemma first_curve (u v : K) (hc : v^2=1-ConcreteG8Domain.D*u^4) :
    (base v)^2=1-(1:Both)*(firstRoot*base u)^4 := by
  exact normalized_curve delta u v firstRoot first_square
    (by simpa only [delta_square] using hc)

#check first_curve

lemma second_curve (u v : K) (hc : v^2=1-deltaBar^2*u^4) :
    (base v)^2=1-(1:Both)*(secondRoot*base u)^4 := by
  exact normalized_curve deltaBar u v secondRoot second_square hc

#check second_curve

@[expose] def firstPoint (u v : K) (hv : v≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) : (E (1:Both)).Point :=
  targetPoint base delta firstRoot first_square u v hv
    (by simpa only [delta_square] using hc)

#check firstPoint

@[expose] def secondPoint (u v : K) (hv : v≠0)
    (hc : v^2=1-deltaBar^2*u^4) : (E (1:Both)).Point :=
  targetPoint base deltaBar secondRoot second_square u v hv hc

#check secondPoint

/-- The same involution, now specialized from its abstract-field construction. -/
@[expose] def flipPoint : (E (1:Both)).Point →+ (E (1:Both)).Point :=
  targetFlip flipSecond.toRingHom

#check flipPoint

lemma flipPoint_first (u v : K) (hv : v≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) :
    flipPoint (firstPoint u v hv hc)=firstPoint u v hv hc :=
  targetFlip_fixed base delta firstRoot first_square flipSecond.toRingHom
    flip_base flipSecond_firstRoot u v hv (by simpa only [delta_square] using hc)

#check flipPoint_first

lemma flipPoint_second (u v : K) (hv : v≠0)
    (hc : v^2=1-deltaBar^2*u^4) :
    flipPoint (secondPoint u v hv hc)= -secondPoint u v hv hc :=
  targetFlip_negative base deltaBar secondRoot second_square flipSecond.toRingHom
    flip_base flipSecond_secondRoot u v hv hc

#check flipPoint_second

/-- A selective sign map excludes integer relations once nontorsion of the
two particular normalized points has actually been supplied. -/
theorem relation_coefficients_zero {G : Type*} [AddCommGroup G]
    (σ : G →+ G) (P Q : G) (hP : σ P=P) (hQ : σ Q= -Q)
    (hPinf : ∀ n : ℤ, n • P=0 → n=0)
    (hQinf : ∀ n : ℤ, n • Q=0 → n=0)
    (m n : ℤ) (hrel : m • P+n • Q=0) : m=0 ∧ n=0 := by
  have hrel' : m • P+ -(n • Q)=0 := by
    simpa only [map_add,map_zsmul,hP,hQ,zsmul_neg,map_zero] using congrArg σ hrel
  have hnneg : n • Q= -(n • Q) := add_left_cancel (hrel.trans hrel'.symm)
  have hdouble : (2*n) • Q=0 := by
    rw [mul_zsmul,two_zsmul]
    calc
      n • Q+n • Q = -(n • Q)+n • Q := congrArg (fun x : G => x+n • Q) hnneg
      _ = 0 := neg_add_cancel _
  have hn : n=0 := by
    have he := hQinf (2*n) hdouble
    omega
  refine ⟨hPinf m ?_,hn⟩
  simpa only [hn,zero_zsmul,add_zero] using hrel

#check relation_coefficients_zero


/-- This consumer keeps both nontorsion premises visible. It does not replace
them with coordinate nonvanishing and does not assert real orbit density. -/
theorem normalized_relation_coefficients_zero
    (u v u' v' : K) (hv : v≠0) (hv' : v'≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) (hc' : v'^2=1-deltaBar^2*u'^4)
    (hfirst : ∀ n : ℤ, n • firstPoint u v hv hc=0 → n=0)
    (hsecond : ∀ n : ℤ, n • secondPoint u' v' hv' hc'=0 → n=0)
    (m n : ℤ)
    (hrel : m • firstPoint u v hv hc+n • secondPoint u' v' hv' hc'=0) :
    m=0 ∧ n=0 :=
  relation_coefficients_zero flipPoint _ _ (flipPoint_first u v hv hc)
    (flipPoint_second u' v' hv' hc') hfirst hsecond m n hrel

#check normalized_relation_coefficients_zero


end NormalizedPointSigns318
