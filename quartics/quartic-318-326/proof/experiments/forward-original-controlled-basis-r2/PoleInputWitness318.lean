module
public import ContactChainWitness318
public import AnchorNorm318
public section
noncomputable section
namespace PoleInputWitness318
open CircuitReplay Raw318FinalReplay
open ContactWeightWitness318 (contact weight)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def realChain (w : Assignment) (t : ℚ) : ℚ :=
  ContactChainWitness318.value187 (ContactWeightWitness318.fill w t)
@[expose] def imagChain (w : Assignment) (t : ℚ) : ℚ :=
  ContactChainWitness318.value188 (ContactWeightWitness318.fill w t)
@[expose] def traceQuotient (w : Assignment) (t : ℚ) : ℚ :=
  ((realChain w t)^2-2*(imagChain w t)^2)/(2*realChain w t)
@[expose] def squareFactor (w : Assignment) (t : ℚ) : ℚ := traceQuotient w t/(t-1)^3
@[expose] def poleInput (w : Assignment) (t : ℚ) : ℚ :=
  (traceQuotient w t)^2*contact t/(t-1)^6

/-- The exact pole input has the original five-factor contact squareclass. -/
theorem pole_squareclass (w : Assignment) (t : ℚ) :
    poleInput w t=contact t*(squareFactor w t)^2 := by
  unfold poleInput squareFactor
  rw [div_pow]
  ring

lemma traceQuotient_ne (w : Assignment) (t : ℚ) (hr : realChain w t≠0) :
    traceQuotient w t≠0 := by
  have hp : ConcreteG8Domain.pair (realChain w t) (imagChain w t)≠0 := by
    intro he
    apply hr
    simpa [ConcreteG8Domain.pair] using congrArg QuadraticAlgebra.re he
  have hn : (realChain w t)^2-2*(imagChain w t)^2≠0 := by
    simpa [AnchorNorm318.norm,ConcreteG8Domain.pair] using AnchorNorm318.norm_ne_zero hp
  exact div_ne_zero hn (mul_ne_zero (by norm_num) hr)

lemma squareFactor_ne (w : Assignment) (t : ℚ) (hr : realChain w t≠0) (ht : t≠1) :
    squareFactor w t≠0 := div_ne_zero (traceQuotient_ne w t hr)
      (pow_ne_zero 3 (sub_ne_zero.mpr ht))

/-- Positivity of the actual pole input is exactly positivity of the original
contact polynomial, once its true quotient domain has been established. -/
theorem pole_positive_iff (w : Assignment) (t : ℚ) (hr : realChain w t≠0) (ht : t≠1) :
    0<poleInput w t ↔ 0<contact t := by
  rw [pole_squareclass]
  have hs := sq_pos_of_ne_zero (squareFactor_ne w t hr ht)
  exact mul_pos_iff_of_pos_right hs

/-- All prime valuations differ by an even contribution. This is the exact
local squareclass join needed by the remaining prime-pattern/pole theorem. -/
theorem pole_valuation (v : AddValuation ℚ (WithTop ℤ)) (w : Assignment) (t : ℚ) :
    v (poleInput w t)=v (contact t)+2 • v (squareFactor w t) := by
  rw [pole_squareclass,v.map_mul,v.map_pow]

@[expose] def fill (w : Assignment) (t : ℚ) : Assignment := fun i =>
  if i=189 then traceQuotient w t else
  if i=190 then poleInput w t else
  ContactChainWitness318.fill (ContactWeightWitness318.fill w t) i

lemma fill_input (w : Assignment) (t : ℚ) : fill w t 0=w 0 := rfl

/-- The actual final chain quotient row is filled on its exact trace domain. -/
theorem row150 (S : ℚ) (w : Assignment) (t : ℚ) (hr : realChain w t≠0) :
    r150 S (fill w t)=0 := by
  have ha : fill w t 187=realChain w t := rfl
  have hb : fill w t 188=imagChain w t := rfl
  have hc : fill w t 189=traceQuotient w t := rfl
  rw [r150,ha,hb,hc]
  unfold traceQuotient
  field_simp [hr]
  ring

/-- The next row uses the original signed e*delta CSE quantity, whose value
is q0*delta^4, with no new normalization of the pole input. -/
theorem row151 (S : ℚ) (w : Assignment) (t : ℚ) (ht : t≠1) (hF : contact t≠0) :
    r151 S (fill w t)=0 := by
  have h151 : fill w t 151=weight t := rfl
  have h152 : fill w t 152= -weight t*((t-1)^3+1) := rfl
  have h153 : fill w t 153= -t*weight t*(t-1)^3 := rfl
  have h189 : fill w t 189=traceQuotient w t := rfl
  have h190 : fill w t 190=poleInput w t := rfl
  rw [r151,h151,h152,h153,h189,h190]
  unfold poleInput weight
  field_simp [sub_ne_zero.mpr ht,hF]
  ring

end PoleInputWitness318
