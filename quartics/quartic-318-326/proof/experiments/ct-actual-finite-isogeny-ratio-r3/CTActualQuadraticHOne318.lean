module
public import CTActualAllQuadraticPhases318
public import CTActualPhaseSquareclass318
public import Mathlib.Data.ZMod.Basic
import all ActualTwoDescentSquareClassQuotient318
import all CTActualQuadraticRootSigns318
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
public section
noncomputable section

namespace CTActualQuadraticHOne318

open CTActualQuadraticRootSigns318 CTFieldPrimitiveRestriction318
open CTActualPhaseSquareclass318 CTActualAllQuadraticPhases318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentClosureFieldEmbedding318

abbrev Bit := ZMod 2

@[expose] def bit (b : Bool) : Bit := if b then 1 else 0
private def flag (i : Bit) : Bool := decide (i = 1)

private theorem bit_xor (b d : Bool) : bit (xor b d)=bit b+bit d := by
  cases b <;> cases d <;> decide

private theorem bit_inj : Function.Injective bit := by
  intro b d h
  cases b <;> cases d
  · rfl
  · exact False.elim ((by decide : bit false≠bit true) h)
  · exact False.elim ((by decide : bit true≠bit false) h)
  · rfl

private theorem bit_flag (i : Bit) : bit (flag i)=i := by
  fin_cases i <;> decide

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "ι" => (algebraMap K A)
local instance : DecidableEq A := Classical.decEq _

/-- In degree one for the trivial rational order-two kernel, the
continuous inhomogeneous cycles are locally constant additive characters. -/
def cycles : AddSubgroup (Gal K → Bit) where
  carrier := {z | IsLocallyConstant z ∧ ∀ g h, z (g*h)=z g+z h}
  zero_mem' := ⟨IsLocallyConstant.const 0,fun _ _ => by simp⟩
  add_mem' := by
    intro u v hu hv
    change (IsLocallyConstant u ∧ ∀ g h, u (g*h)=u g+u h) at hu
    change (IsLocallyConstant v ∧ ∀ g h, v (g*h)=v g+v h) at hv
    refine ⟨(hu.1.prodMk hv.1).comp (fun p => p.1+p.2),?_⟩
    intro g h
    change u (g*h)+v (g*h)=(u g+v g)+(u h+v h)
    rw [hu.2,hv.2]
    abel
  neg_mem' := by
    intro u hu
    change (IsLocallyConstant u ∧ ∀ g h, u (g*h)=u g+u h) at hu
    refine ⟨hu.1.comp Neg.neg,?_⟩
    intro g h
    change -(u (g*h))= -u g + -u h
    rw [hu.2,neg_add]

/-- This model of the continuous H¹ of the trivial order-two kernel
has literal representatives: its actual degree-zero boundary is 0. -/
abbrev QuadraticHOne := cycles K

theorem trivial_d0 (u : Bit) (g : Gal K) :
    (fun _ : Gal K => AddMonoidHom.id Bit) g u-u=0 := sub_self u

private theorem eval_lc (z : QuadraticHOne K) : IsLocallyConstant z.val := z.property.1

private theorem eval_mul (z : QuadraticHOne K) (g h : Gal K) :
    z.val (g*h)=z.val g+z.val h := z.property.2 g h

/-- Build the continuous class using a chosen root, retaining an exact
pointwise identity irrespective of the choice of root. -/
def rootCycle (a : Kˣ) (r : Aˣ) (hr : (r:A)^2=ι (a:K)) : QuadraticHOne K :=
  ⟨fun g => bit (phase K r g),
    (phase_lc K r).comp bit,
    fun g h => by rw [phase_mul K r a hr,bit_xor]⟩

theorem rootCycle_apply (a : Kˣ) (r : Aˣ) (hr : (r:A)^2=ι (a:K)) (g : Gal K) :
    (rootCycle K a r hr).val g=bit (phase K r g) := rfl

theorem rootCycle_eq_iff (a b : Kˣ) (r s : Aˣ)
    (hr : (r:A)^2=ι (a:K)) (hs : (s:A)^2=ι (b:K)) :
    rootCycle K a r hr=rootCycle K b s hs ↔
    classOf (a:K) a.ne_zero=classOf (b:K) b.ne_zero := by
  rw [← phase_eq_iff_squareclass_eq K a b r s hr hs]
  constructor
  · intro he g
    apply bit_inj
    exact congrArg (fun z : QuadraticHOne K => z.val g) he
  · intro he
    apply Subtype.ext
    funext g
    rw [rootCycle_apply,rootCycle_apply,he]

private def pickedRoot (a : Kˣ) : Aˣ := Classical.choose (exists_unit_root K a)

private theorem pickedRoot_eq (a : Kˣ) : (pickedRoot K a:A)^2=ι (a:K) :=
  Classical.choose_spec (exists_unit_root K a)

theorem mul_root (a b : Kˣ) (r s : Aˣ)
    (hr : (r:A)^2=ι (a:K)) (hs : (s:A)^2=ι (b:K)) :
    ((r*s:Aˣ):A)^2=ι ((a*b:Kˣ):K) := by
  rw [Units.val_mul,mul_pow,hr,hs,Units.val_mul,map_mul]

private theorem sign_inj (r : Aˣ) : Function.Injective (fun b => fieldSign K b (r:A)) := by
  have hn : -(r:A)≠(r:A) := by
    intro he
    have hz : (2:A)*(r:A)=0 := calc
      _=(r:A)+(r:A) := two_mul _
      _= -(r:A)+(r:A) := congrArg (fun x : A => x+(r:A)) he.symm
      _=0 := neg_add_cancel _
    exact mul_ne_zero (by norm_num) r.ne_zero hz
  intro b d he
  cases b <;> cases d
  · rfl
  · exact False.elim (hn he.symm)
  · exact False.elim (hn he)
  · rfl

theorem rootCycle_mul (a b : Kˣ) (r s : Aˣ)
    (hr : (r:A)^2=ι (a:K)) (hs : (s:A)^2=ι (b:K)) :
    rootCycle K (a*b) (r*s) (mul_root K a b r s hr hs) =
      rootCycle K a r hr+rootCycle K b s hs := by
  apply Subtype.ext
  funext g
  have h := act_on_square_root K (r*s) (a*b) (mul_root K a b r s hr hs) g
  rw [Units.val_mul,map_mul,act_on_square_root K r a hr g,act_on_square_root K s b hs g] at h
  have hSign : phase K (r*s) g=xor (phase K r g) (phase K s g) := by
    apply sign_inj K (r*s)
    rw [← h]
    cases e : phase K r g <;> cases f : phase K s g <;>
      simp [e,f,fieldSign,xor,Units.val_mul]
  change bit (phase K (r*s) g)=bit (phase K r g)+bit (phase K s g)
  rw [hSign,bit_xor]

private def unitCycle : Kˣ →* Multiplicative (QuadraticHOne K) where
  toFun a := Multiplicative.ofAdd (rootCycle K a (pickedRoot K a) (pickedRoot_eq K a))
  map_one' := by
    change rootCycle K 1 (pickedRoot K 1) (pickedRoot_eq K 1) = 0
    have h1 : ((1:Aˣ):A)^2=ι ((1:Kˣ):K) := by simp
    have h := (rootCycle_eq_iff K 1 1 (pickedRoot K 1) 1 (pickedRoot_eq K 1) h1).mpr rfl
    rw [h]
    apply Subtype.ext
    funext g
    change bit (phase K 1 g)=0
    simp [phase,act,bit]
  map_mul' a b := by
    change rootCycle K (a*b) (pickedRoot K (a*b)) (pickedRoot_eq K (a*b)) = _
    have h := (rootCycle_eq_iff K (a*b) (a*b) (pickedRoot K (a*b))
      (pickedRoot K a*pickedRoot K b) (pickedRoot_eq K (a*b))
      (mul_root K a b (pickedRoot K a) (pickedRoot K b) (pickedRoot_eq K a) (pickedRoot_eq K b))).mpr rfl
    rw [h,rootCycle_mul] <;> rfl

private theorem unitCycle_mk0 (a : Kˣ) : Units.mk0 (a:K) a.ne_zero=a := by
  apply Units.ext
  rfl

private def classHom : SquareClass K →* Multiplicative (QuadraticHOne K) :=
  QuotientGroup.lift (powMonoidHom (α:=Kˣ) 2).range (unitCycle K) (by
    rintro _ ⟨u,rfl⟩
    change (unitCycle K (u^2)).toAdd=0
    rw [map_pow]
    apply Subtype.ext
    funext g
    change (2:ℕ) • ((unitCycle K u).toAdd.val g)=0
    rw [two_nsmul]
    generalize he : (unitCycle K u).toAdd.val g = t
    fin_cases t <;> decide)

private theorem classHom_on_unit (a : Kˣ) :
    (classHom K (classOf (a:K) a.ne_zero)).toAdd=
      rootCycle K a (pickedRoot K a) (pickedRoot_eq K a) := by
  change (classHom K (QuotientGroup.mk (Units.mk0 (a:K) a.ne_zero))).toAdd=_
  rw [unitCycle_mk0]
  rfl

private theorem classHom_bijective : Function.Bijective (classHom K) := by
  constructor
  · intro q t h
    revert h
    refine QuotientGroup.induction_on q (fun a => ?_)
    refine QuotientGroup.induction_on t (fun b => ?_)
    intro he
    have ha : classOf (a:K) a.ne_zero=QuotientGroup.mk a := by
      change QuotientGroup.mk (Units.mk0 (a:K) a.ne_zero)=_
      rw [unitCycle_mk0]
    have hb : classOf (b:K) b.ne_zero=QuotientGroup.mk b := by
      change QuotientGroup.mk (Units.mk0 (b:K) b.ne_zero)=_
      rw [unitCycle_mk0]
    rw [←ha,←hb] at he ⊢
    have hC := congrArg Multiplicative.toAdd he
    rw [classHom_on_unit,classHom_on_unit] at hC
    exact (rootCycle_eq_iff K a b _ _ _ _).mp hC
  · intro z
    let χ : Gal K → Bool := fun g => flag (z.toAdd.val g)
    have hχ : IsLocallyConstant χ := (eval_lc K z.toAdd).comp flag
    have hMul (g h : Gal K) : χ (g*h)=xor (χ g) (χ h) := by
      apply bit_inj
      simp only [χ,bit_xor,bit_flag,eval_mul]
    obtain ⟨a,r,hr,he⟩ := character_is_actual_phase K χ hχ hMul
    refine ⟨classOf (a:K) a.ne_zero,?_⟩
    apply Multiplicative.toAdd.injective
    rw [classHom_on_unit]
    have h := (rootCycle_eq_iff K a a (pickedRoot K a) r (pickedRoot_eq K a) hr).mpr rfl
    rw [h]
    apply Subtype.ext
    funext g
    rw [rootCycle_apply,he]
    exact bit_flag (z.toAdd.val g)

/-- Literal squareclass ↔ continuous H¹ for the trivial order-two
kernel, as a group equivalence. No finite Selmer comparison is used. -/
def scalarKummer : SquareClass K ≃* Multiplicative (QuadraticHOne K) :=
  MulEquiv.ofBijective (classHom K) (classHom_bijective K)

theorem scalarKummer_on_root (a : Kˣ) (r : Aˣ) (hr : (r:A)^2=ι (a:K)) :
    (scalarKummer K (classOf (a:K) a.ne_zero)).toAdd=rootCycle K a r hr := by
  change (classHom K (classOf (a:K) a.ne_zero)).toAdd=_
  rw [classHom_on_unit]
  exact (rootCycle_eq_iff K a a (pickedRoot K a) r (pickedRoot_eq K a) hr).mpr rfl

variable {L : Type} [Field L] [CharZero L]

def restrict (f : K →+* L) : QuadraticHOne K →+ QuadraticHOne L where
  toFun z := ⟨fun g => z.val (Field.absoluteGaloisGroup.map f g),
    (eval_lc K z).comp_continuous (Field.absoluteGaloisGroup.map f).continuous,
    fun g h => by rw [map_mul,eval_mul]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem restrict_eval (f : K →+* L) (z : QuadraticHOne K) (g : Gal L) :
    (restrict K f z).val g=z.val (Field.absoluteGaloisGroup.map f g) := rfl

theorem scalarKummer_restrict_on_unit (f : K →+* L) (a : Kˣ) :
    restrict K f (scalarKummer K (classOf (a:K) a.ne_zero)).toAdd =
      (scalarKummer L (classOf (f (a:K)) (map_ne_zero f a.ne_zero))).toAdd := by
  let r := pickedRoot K a
  let r' := Units.map (closureMap f).toMonoidHom r
  let a' := Units.mk0 (f (a:K)) (map_ne_zero f a.ne_zero)
  have hr' : (r':AlgebraicClosure L)^2=algebraMap L (AlgebraicClosure L) (a':L) := by
    change (closureMap f (r:A))^2=algebraMap L (AlgebraicClosure L) (f (a:K))
    rw [← map_pow,pickedRoot_eq K a,actual_closure_map_base]
  have ha' := scalarKummer_on_root L a' r' hr'
  change restrict K f (scalarKummer K (classOf (a:K) a.ne_zero)).toAdd =
    (scalarKummer L (classOf (a':L) a'.ne_zero)).toAdd
  rw [ha',scalarKummer_on_root K a r (pickedRoot_eq K a)]
  apply Subtype.ext
  funext g
  rw [restrict_eval,rootCycle_apply,rootCycle_apply,actual_phase_restriction]

/-- Literal field localization on the existing squareclass quotient.
This factors the actual unit map, not an arithmetic placeholder. -/
def scalarMap (f : K →+* L) : SquareClass K →* SquareClass L :=
  QuotientGroup.lift (powMonoidHom (α:=Kˣ) 2).range
    ((QuotientGroup.mk' (powMonoidHom (α:=Lˣ) 2).range).comp (Units.map f.toMonoidHom)) (by
      rintro _ ⟨u,rfl⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨Units.map f.toMonoidHom u,?_⟩
      exact (map_pow (Units.map f.toMonoidHom) u 2).symm)

theorem scalarMap_on_unit (f : K →+* L) (a : Kˣ) :
    scalarMap K f (classOf (a:K) a.ne_zero)=
      classOf (f (a:K)) (map_ne_zero f a.ne_zero) := by
  have hu : Units.map f.toMonoidHom (Units.mk0 (a:K) a.ne_zero) =
      Units.mk0 (f (a:K)) (map_ne_zero f a.ne_zero) := by
    apply Units.ext
    rfl
  change QuotientGroup.mk (Units.map f.toMonoidHom (Units.mk0 (a:K) a.ne_zero)) =
    QuotientGroup.mk (Units.mk0 (f (a:K)) (map_ne_zero f a.ne_zero))
  rw [hu]

/-- The continuous degree-one square commutes on all classes. The
restriction in its bottom edge is the original absolute map. -/
theorem scalarKummer_restrict (f : K →+* L) (c : SquareClass K) :
    restrict K f (scalarKummer K c).toAdd=
      (scalarKummer L (scalarMap K f c)).toAdd := by
  refine QuotientGroup.induction_on c (fun a => ?_)
  have ha : classOf (a:K) a.ne_zero=QuotientGroup.mk a := by
    change QuotientGroup.mk (Units.mk0 (a:K) a.ne_zero)=_
    rw [unitCycle_mk0]
  rw [←ha,scalarMap_on_unit]
  exact scalarKummer_restrict_on_unit K f a

end CTActualQuadraticHOne318

#print axioms CTActualQuadraticHOne318.scalarKummer
#print axioms CTActualQuadraticHOne318.scalarKummer_on_root
#print axioms CTActualQuadraticHOne318.scalarKummer_restrict
