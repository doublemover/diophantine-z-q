module
public import GoodReductionResidue318
public section
noncomputable section
namespace GoodReductionLifting318
open Polynomial GoodReductionResidue318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- Every point of the actual smooth residue curve lifts to an integral
point of the same p-adic model. Both coordinate charts are retained. -/
theorem lift_residue (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1)
    (z : ResidueCurve p D) : ∃ P : IntegralCurve p D, reduce p D P=z := by
  let x : ℤ_[p] := (z.1.1.val:ℤ_[p])
  let y : ℤ_[p] := (z.1.2.val:ℤ_[p])
  have hx : PadicInt.toZMod x=z.1.1 := by simp only [x,map_natCast,ZMod.natCast_zmod_val]
  have hy : PadicInt.toZMod y=z.1.2 := by simp only [y,map_natCast,ZMod.natCast_zmod_val]
  have hs := smooth_residue (PadicInt.toZMod D) z.1.1 z.1.2
    (two_residue_ne p hp) ((residue_unit p D).mpr hD) z.2
  rcases hs with hyunit|hxunit
  · let F : Polynomial ℤ_[p] := X^2-C (x^3-D*x)
    have hzero : PadicInt.toZMod (F.aeval y)=0 := by
      simpa [F,hx,hy] using (sub_eq_zero.mpr z.2)
    have hder : PadicInt.toZMod (F.derivative.aeval y)≠0 := by
      simpa [F,hy] using hyunit
    obtain ⟨b,hb,hres⟩ := hensel_same_residue p F y hzero hder
    have hc : b^2=x^3-D*x := sub_eq_zero.mp (by simpa [F] using hb)
    refine ⟨⟨(x,b),hc⟩,?_⟩
    apply Subtype.ext
    exact Prod.ext hx (hres.trans hy)
  · let F : Polynomial ℤ_[p] := X^3-C D*X-C (y^2)
    have hzero : PadicInt.toZMod (F.aeval x)=0 := by
      simpa [F,hx,hy] using (sub_eq_zero.mpr z.2.symm)
    have hder : PadicInt.toZMod (F.derivative.aeval x)≠0 := by
      simpa [F,hx,mul_comm] using hxunit
    obtain ⟨b,hb,hres⟩ := hensel_same_residue p F x hzero hder
    have hc : y^2=b^3-D*b := (sub_eq_zero.mp (by simpa [F] using hb)).symm
    refine ⟨⟨(b,y),hc⟩,?_⟩
    apply Subtype.ext
    exact Prod.ext (hres.trans hx) hy

lemma coefficient_ne (D : ℤ_[p]) (hD : ‖D‖=1) : (D:ℚ_[p])≠0 := by
  intro he
  have hh : ‖D‖=0 := by rw [PadicInt.norm_def,he,norm_zero]
  linarith

lemma nonsingular (D : ℤ_[p]) (hD : ‖D‖=1) (P : IntegralCurve p D) :
    (E (D:ℚ_[p])).Nonsingular (P.1.1:ℚ_[p]) (P.1.2:ℚ_[p]) :=
  CompactLocalPointCoding318.curve_nonsingular (D:ℚ_[p]) (coefficient_ne p D hD)
    ⟨((P.1.1:ℚ_[p]),(P.1.2:ℚ_[p])),P.1.1.2,P.1.2.2,by exact_mod_cast P.2⟩

@[expose] def point (D : ℤ_[p]) (hD : ‖D‖=1) (P : IntegralCurve p D) :
    (E (D:ℚ_[p])).Point :=
  Point.some (P.1.1:ℚ_[p]) (P.1.2:ℚ_[p]) (nonsingular p D hD P)

@[expose] def subgroup (D : ℤ_[p]) : AddSubgroup (E (D:ℚ_[p])).Point :=
  AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue ℚ_[p])
    (ActualSplitOrbitEntry318.nonarchimedean p) (D:ℚ_[p]) D.2

/-- Equal actual residue coordinates imply equality in the original formal
quotient, by the unit derivative chart of this good-reduction model. -/
theorem same_residue_coset (hp : p≠2) (D : ℤ_[p]) (hD : ‖D‖=1)
    (P Q : IntegralCurve p D) (he : reduce p D P=reduce p D Q) :
    QuotientAddGroup.mk' (subgroup p D) (point p D hD P)=
      QuotientAddGroup.mk' (subgroup p D) (point p D hD Q) := by
  have hx : ‖Q.1.1-P.1.1‖<1 := (residue_equal p _ _).mp
    (congrArg (fun z : ResidueCurve p D => z.1.1) he.symm)
  have hy : ‖Q.1.2-P.1.2‖<1 := (residue_equal p _ _).mp
    (congrArg (fun z : ResidueCurve p D => z.1.2) he.symm)
  have hu := derivative_unit p hp D P.1.1 P.1.2 hD P.2
  have hc : point p D hD P-point p D hD Q∈subgroup p D := by
    apply LocalPointDifference318.close_points
      (NormedField.toAbsoluteValue ℚ_[p]) (ActualSplitOrbitEntry318.nonarchimedean p)
      (D:ℚ_[p]) (P.1.1:ℚ_[p]) (P.1.2:ℚ_[p]) (Q.1.1:ℚ_[p]) (Q.1.2:ℚ_[p])
      D.2 (nonsingular p D hD P) (nonsingular p D hD Q) P.1.1.2 Q.1.1.2
    rcases hu with hu|hu
    · left
      have hd : ‖2*(P.1.2:ℚ_[p])‖=1 := by exact_mod_cast hu
      simpa only [hd,←PadicInt.coe_sub,←PadicInt.norm_def] using And.intro hx hy
    · right
      have hd : ‖3*(P.1.1:ℚ_[p])^2-(D:ℚ_[p])‖=1 := by exact_mod_cast hu
      simpa only [hd,←PadicInt.coe_sub,←PadicInt.norm_def] using And.intro hx hy
  have hz := (QuotientAddGroup.eq_zero_iff (subgroup p D)).mpr hc
  simpa only [map_sub,sub_eq_zero] using hz

end GoodReductionLifting318
