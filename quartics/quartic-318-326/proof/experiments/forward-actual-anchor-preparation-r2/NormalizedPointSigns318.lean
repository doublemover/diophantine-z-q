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
  point 1 (firstRoot*base u) (base v)
    (fun h => hv (base.injective (h.trans base.map_zero.symm)))
    (first_curve u v hc)

#check firstPoint

@[expose] def secondPoint (u v : K) (hv : v≠0)
    (hc : v^2=1-deltaBar^2*u^4) : (E (1:Both)).Point :=
  point 1 (secondRoot*base u) (base v)
    (fun h => hv (base.injective (h.trans base.map_zero.symm)))
    (second_curve u v hc)

#check secondPoint

private lemma transport_point {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (D D' u v : F) (h : D=D') (hv : v≠0) (hc : v^2=1-D*u^4) :
    transport (congrArg E h) (point D u v hv hc)=
      point D' u v hv (h ▸ hc) := by
  subst D'
  rfl

#check transport_point


/-- The involution acts on the actual Mathlib elliptic group by field base
change followed by the explicit equality of the coefficient 1 with its image. -/
@[expose] def flipPoint : (E (1:Both)).Point →+ (E (1:Both)).Point :=
  (transport (congrArg E flipSecond.toRingHom.map_one)).toAddMonoidHom.comp
    (pointMap flipSecond.toRingHom 1)


#check flipPoint

lemma flip_curve (u v : Both) (hc : v^2=1-(1:Both)*u^4) :
    (flipSecond v)^2=1-(1:Both)*(flipSecond u)^4 := by
  simpa only [map_pow,map_sub,map_one,map_mul] using congrArg flipSecond hc

#check flip_curve

lemma flipPoint_reciprocal (u v : Both) (hv : v≠0)
    (hc : v^2=1-(1:Both)*u^4) :
    flipPoint (point 1 u v hv hc)=
      point 1 (flipSecond u) (flipSecond v)
        (fun h => hv (flipSecond.injective (h.trans flipSecond.map_zero.symm)))
        (flip_curve u v hc) := by
  change transport (congrArg E flipSecond.toRingHom.map_one)
    (pointMap flipSecond.toRingHom 1 (point 1 u v hv hc)) = _
  rw [pointMap_reciprocal,transport_point]


#check flipPoint_reciprocal

lemma flipPoint_first (u v : K) (hv : v≠0)
    (hc : v^2=1-ConcreteG8Domain.D*u^4) :
    flipPoint (firstPoint u v hv hc)=firstPoint u v hv hc := by
  unfold firstPoint
  rw [flipPoint_reciprocal]
  simp only [map_mul,flipSecond_firstRoot,flip_base]


#check flipPoint_first

lemma flipPoint_second (u v : K) (hv : v≠0)
    (hc : v^2=1-deltaBar^2*u^4) :
    flipPoint (secondPoint u v hv hc)= -secondPoint u v hv hc := by
  unfold secondPoint
  rw [flipPoint_reciprocal]
  simp only [map_mul,flipSecond_secondRoot,flip_base,neg_mul]
  exact point_negative 1 _ _ _ _

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
