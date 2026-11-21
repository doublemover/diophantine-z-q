module
public import ActualGaussianDegreeOneGenerator318
public section
noncomputable section
namespace ActualGaussianResidueOrbit318

@[expose] def coords (z : GaussianInt) : ℤ×ℤ := (z.re,z.im)

theorem norm_coords (z : GaussianInt) : z.norm=(coords z).1^2+(coords z).2^2 := by
  rw [Zsqrtd.norm_def]
  change z.re*z.re-(-1:ℤ)*z.im*z.im=z.re^2+z.im^2
  ring

@[expose] def modIdeal (M : ℕ) : Ideal GaussianInt :=
  Ideal.span ({(M:GaussianInt)} : Set GaussianInt)

abbrev Residue (M : ℕ) := GaussianInt ⧸ modIdeal M

@[expose] def red (M : ℕ) : GaussianInt→+*Residue M := Ideal.Quotient.mk (modIdeal M)

@[expose] def unitReduction (M : ℕ) : GaussianIntˣ→*(Residue M)ˣ :=
  Units.map (red M).toMonoidHom

abbrev RayClass (M : ℕ) := (Residue M)ˣ ⧸ (unitReduction M).range

@[expose] def rayClass (M : ℕ) (x : (Residue M)ˣ) : RayClass M :=
  QuotientGroup.mk x

theorem gaussian_modulus_zero (M : ℕ) : (M:Residue M)=0 := by
  rw [←(red M).map_natCast M]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (M:GaussianInt))

/-- The Gaussian residue is a unit from integer norm coprimality.
This is a genuine unit of the actual ideal quotient. -/
theorem unit_of_norm_coprime (M : ℕ) (z : GaussianInt)
    (h : z.norm.natAbs.Coprime M) : IsUnit (red M z) := by
  have hh : IsCoprime z.norm (M:ℤ) := by
    rw [←GaussianInt.abs_natCast_norm z]
    exact h.isCoprime
  obtain ⟨a,b,hBez⟩ := hh
  have H := congrArg (fun u : ℤ => (u:Residue M)) hBez
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,gaussian_modulus_zero,
    mul_zero,add_zero] at H
  have hNorm : (z.norm:Residue M)=red M z*red M (star z) := by
    simpa only [map_intCast,map_mul] using congrArg (red M) (Zsqrtd.norm_eq_mul_conj z)
  rw [hNorm] at H
  have hu : red M z*((a:Residue M)*red M (star z))=1 := by
    calc
      _ = (a:Residue M)*(red M z*red M (star z)) := by ring
      _ = _ := H
  exact ⟨Units.mkOfMulEqOne _ _ hu,rfl⟩

def residueUnit (M : ℕ) (z : GaussianInt) (h : z.norm.natAbs.Coprime M) : (Residue M)ˣ :=
  (unit_of_norm_coprime M z h).unit

theorem residueUnit_val (M : ℕ) (z : GaussianInt) (h : z.norm.natAbs.Coprime M) :
    (residueUnit M z h:Residue M)=red M z :=
  (unit_of_norm_coprime M z h).unit_spec

/-- Equality is in ((Z[i]/M)ˣ)/im(Z[i]ˣ), not Galois equality
in a placeholder type. It yields ONE actual unit multiplying the source
to the target, in that direction. -/
theorem class_equality_has_unit (M : ℕ) {v t : (Residue M)ˣ}
    (h : rayClass M v=rayClass M t) :
    ∃ e : GaussianIntˣ,unitReduction M e*v=t := by
  have hh : t/v∈(unitReduction M).range :=
    QuotientGroup.eq_iff_div_mem.mp h.symm
  obtain ⟨e,he⟩ := MonoidHom.mem_range.mp hh
  exact ⟨e,by rw [he]; group⟩

theorem full_coordinate_congruence {M : ℕ} {z t : GaussianInt} (h : red M z=red M t) :
    z.re≡t.re [ZMOD (M:ℤ)] ∧ z.im≡t.im [ZMOD (M:ℤ)] := by
  have hh : z-t∈modIdeal M := (Ideal.Quotient.eq (I:=modIdeal M)).mp h
  have hd : (M:GaussianInt)∣z-t := Ideal.mem_span_singleton.mp hh
  obtain ⟨e,he⟩ := hd
  have hr := congrArg (fun x : GaussianInt => x.re) he
  have hi := congrArg (fun x : GaussianInt => x.im) he
  simp only [Zsqrtd.re_sub,Zsqrtd.re_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
    mul_zero,zero_mul,add_zero] at hr
  simp only [Zsqrtd.im_sub,Zsqrtd.im_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast,
    zero_mul,add_zero] at hi
  constructor
  · apply Int.modEq_iff_dvd.mpr
    exact ⟨-e.re,by linear_combination -hr⟩
  · apply Int.modEq_iff_dvd.mpr
    exact ⟨-e.im,by linear_combination -hi⟩

theorem class_equality_actual_coords (M : ℕ) {z t : GaussianInt}
    {v w : (Residue M)ˣ} (hv : (v:Residue M)=red M z) (hw : (w:Residue M)=red M t)
    (h : rayClass M v=rayClass M w) :
    ∃ e : GaussianIntˣ,
      ((e:GaussianInt)*z).re≡t.re [ZMOD (M:ℤ)] ∧
      ((e:GaussianInt)*z).im≡t.im [ZMOD (M:ℤ)] := by
  obtain ⟨e,he⟩ := class_equality_has_unit M h
  have hu := congrArg (fun c : (Residue M)ˣ => (c:Residue M)) he
  change red M (e:GaussianInt)*(v:Residue M)=(w:Residue M) at hu
  rw [hv,hw,←map_mul] at hu
  exact ⟨e,full_coordinate_congruence hu⟩

private theorem three_of_natAbs_le_one (x : ℤ) (h : x.natAbs≤1) :
    x = -1 ∨ x=0 ∨ x=1 := by
  have h' : (x.natAbs:ℤ)≤1 := by exact_mod_cast h
  by_cases hx : 0≤x
  · rw [Int.natAbs_of_nonneg hx] at h'
    omega
  · rw [Int.ofNat_natAbs_of_nonpos (by omega : x≤0)] at h'
    omega

/-- Global Gaussian units are exactly the four rotations; no new
local unit representatives are introduced at individual primes. -/
theorem unit_axes (e : GaussianIntˣ) :
    coords (e:GaussianInt)=(1,0) ∨ coords (e:GaussianInt)=(0,1) ∨
    coords (e:GaussianInt)=(-1,0) ∨ coords (e:GaussianInt)=(0,-1) := by
  let z : GaussianInt := e
  have hu : z.norm.natAbs=1 := Zsqrtd.norm_eq_one_iff.mpr e.isUnit
  have hN := (GaussianInt.natAbs_norm_eq z).symm.trans hu
  have ha : z.re.natAbs≤1 := (Nat.le_mul_self _).trans (by omega)
  have hb : z.im.natAbs≤1 := (Nat.le_mul_self _).trans (by omega)
  have hone := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1:ℤ)≤0) z).mpr e.isUnit
  rw [norm_coords] at hone
  change z.re^2+z.im^2=1 at hone
  change coords z=(1,0) ∨ coords z=(0,1) ∨ coords z=(-1,0) ∨ coords z=(0,-1)
  rcases three_of_natAbs_le_one z.re ha with hr|hr|hr <;>
    rcases three_of_natAbs_le_one z.im hb with hi|hi|hi <;>
    norm_num [coords,hr,hi] at hone ⊢

end ActualGaussianResidueOrbit318
