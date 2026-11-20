module
public import ActualGaussianResidueOrbit318
public import ActualGaussianDegreeFromFrobenius318
public import ActualGaussianRayConjugateLift318
public section
noncomputable section
namespace ActualGaussianReciprocityBridge318

open ActualGaussianDegreeOneGenerator318 ActualGaussianResidueOrbit318 ActualGaussianDegreeFromFrobenius318
open ActualGaussianRayConjugateLift318

@[expose] def switchGaussian (bar : Bool) (z : GaussianInt) : GaussianInt :=
  if bar then star z else z

theorem coords_switch (bar : Bool) (z : GaussianInt) :
    coords (switchGaussian bar z)=switch bar (coords z) := by cases bar <;> rfl

theorem unit_turn (e : GaussianIntˣ) (z : GaussianInt) :
    ∃ q : Quarter,coords ((e:GaussianInt)*z)=rotate q (coords z) := by
  rcases unit_axes e with h|h|h|h
  · have ha : (e:GaussianInt).re=1 := congrArg Prod.fst h
    have hb : (e:GaussianInt).im=0 := congrArg Prod.snd h
    refine ⟨.one,?_⟩
    simp [coords,rotate,Zsqrtd.re_mul,Zsqrtd.im_mul,ha,hb]
  · have ha : (e:GaussianInt).re=0 := congrArg Prod.fst h
    have hb : (e:GaussianInt).im=1 := congrArg Prod.snd h
    refine ⟨.i,?_⟩
    simp [coords,rotate,Zsqrtd.re_mul,Zsqrtd.im_mul,ha,hb]
  · have ha : (e:GaussianInt).re= -1 := congrArg Prod.fst h
    have hb : (e:GaussianInt).im=0 := congrArg Prod.snd h
    refine ⟨.negOne,?_⟩
    simp [coords,rotate,Zsqrtd.re_mul,Zsqrtd.im_mul,ha,hb]
  · have ha : (e:GaussianInt).re=0 := congrArg Prod.fst h
    have hb : (e:GaussianInt).im= -1 := congrArg Prod.snd h
    refine ⟨.negI,?_⟩
    simp [coords,rotate,Zsqrtd.re_mul,Zsqrtd.im_mul,ha,hb]

theorem generator_coprime {p M : ℕ} (D : DegreeOne p) (hp : p.Prime) (hc : p.Coprime M) :
    (generator D).norm.natAbs.Coprime M := by
  simpa only [generator_norm D hp,Int.natAbs_natCast] using hc

/-- Input convention: the residue class of a principal generator of
the ACTUAL Gaussian prime ideal equals the chosen branch in the
literal quotient of residue units, with the arithmetic Artin direction.
This record contains no generator norm, quotient-unit multiplier,
coordinatewise congruence, or final RayWitness. -/
structure ReciprocityPacket {s : ℕ} (P : Policy s) (p : ℕ) (hp : p.Prime) where
  degreeOne : DegreeOne p
  coprime : p.Coprime (P.base*P.fresh)
  reference : GaussianInt
  referenceGood : Reference P (coords reference)
  conjugateBranch : Bool
  targetUnit : (Residue (P.base*P.fresh))ˣ
  target_value : (targetUnit:Residue (P.base*P.fresh))=
    red (P.base*P.fresh) (switchGaussian conjugateBranch reference)
  equality : rayClass (P.base*P.fresh)
      (residueUnit (P.base*P.fresh) (generator degreeOne)
        (generator_coprime degreeOne hp coprime)) =
    rayClass (P.base*P.fresh) targetUnit

/-- Deterministic finite algebra AFTER the stated concrete reciprocity
identity. The class field extension and the reciprocity identity are
not constructed or inferred from lower prime-log mass here. -/
theorem toArtinDatum {s p : ℕ} {P : Policy s} {hp : p.Prime}
    (D : ReciprocityPacket P p hp) : Nonempty (ArtinDatum P p) := by
  let z := generator D.degreeOne
  obtain ⟨e,he⟩ := class_equality_actual_coords (P.base*P.fresh)
    (residueUnit_val (P.base*P.fresh) z (generator_coprime D.degreeOne hp D.coprime))
    D.target_value D.equality
  obtain ⟨q,hq⟩ := unit_turn e z
  refine ⟨{
    raw := coords z
    ref := coords D.reference
    unit := q
    bar := D.conjugateBranch
    rawNorm := ?_
    refGood := D.referenceGood
    congr := ?_ }⟩
  · change (coords z).1^2+(coords z).2^2=(p:ℤ)
    rw [←norm_coords]
    exact generator_norm D.degreeOne hp
  · rw [←hq,←coords_switch]
    exact he

/-- Direct boundary for a selected arithmetic Frobenius:
identity of the restriction yields the integral p-th-power residue
equality, while reciprocity yields precisely the actual quotient
class identity below. No degree-one, norm or unit lift is assumed. -/
theorem artin_of_restricted_power {s p : ℕ} (P : Policy s) (hp : p.Prime)
    (I : Ideal GaussianInt) (hI : I.IsPrime) (hpI : (p:GaussianInt)∈I)
    (hFix : ∀ z : GaussianInt,(Ideal.Quotient.mk I z)^p=Ideal.Quotient.mk I z)
    (hc : p.Coprime (P.base*P.fresh)) (r : GaussianInt)
    (hr : Reference P (coords r)) (bar : Bool) (t : (Residue (P.base*P.fresh))ˣ)
    (hT : (t:Residue (P.base*P.fresh))=red (P.base*P.fresh) (switchGaussian bar r))
    (hClass :
      let D := ofRationalPower hp I hI hpI (quotient_power_of_integer_congruence I hFix)
      rayClass (P.base*P.fresh) (residueUnit (P.base*P.fresh) (generator D)
        (generator_coprime D hp hc))=rayClass (P.base*P.fresh) t) :
    Nonempty (ArtinDatum P p) :=
  toArtinDatum
    { degreeOne := ofRationalPower hp I hI hpI (quotient_power_of_integer_congruence I hFix)
      coprime := hc, reference := r, referenceGood := hr, conjugateBranch := bar
      targetUnit := t, target_value := hT, equality := hClass }

end ActualGaussianReciprocityBridge318
