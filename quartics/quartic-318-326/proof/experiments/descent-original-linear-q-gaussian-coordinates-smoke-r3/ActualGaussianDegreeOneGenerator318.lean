module
public import Mathlib
public section
noncomputable section
namespace ActualGaussianDegreeOneGenerator318

/-- Actual degree-one Gaussian prime over p, with its residue-ring
isomorphism, not a Gaussian norm or representation hypothesis. The
quotient map is the actual ideal quotient of Mathlib.GaussianInt. -/
structure DegreeOne (p : ℕ) where
  ideal : Ideal GaussianInt
  isPrime : ideal.IsPrime
  residue : (GaussianInt ⧸ ideal) ≃+* ZMod p

/-- The standard residue-size equality for absolute residue degree
one is enough; no choice of an arbitrary representation of p is used. -/
def ofCard {p : ℕ} (P : Ideal GaussianInt) (hP : P.IsPrime) (hp : p.Prime)
    (h : Nat.card (GaussianInt ⧸ P)=p) : DegreeOne p := by
  letI : Finite (GaussianInt ⧸ P) := Nat.finite_of_card_ne_zero (by rw [h]; exact hp.ne_zero)
  letI : Fintype (GaussianInt ⧸ P) := Fintype.ofFinite _
  have h' : Fintype.card (GaussianInt ⧸ P)=p := by
    simpa only [Nat.card_eq_fintype_card] using h
  exact ⟨P,hP,(ZMod.ringEquivOfPrime (GaussianInt ⧸ P) hp h').symm⟩

@[expose] def gi : GaussianInt := Zsqrtd.sqrtd

@[expose] def generator {p : ℕ} (D : DegreeOne p) : GaussianInt :=
  Submodule.IsPrincipal.generator D.ideal

theorem generator_span {p : ℕ} (D : DegreeOne p) :
    Ideal.span ({generator D} : Set GaussianInt)=D.ideal :=
  Ideal.span_singleton_generator D.ideal

theorem integer_mem_iff {p : ℕ} (D : DegreeOne p) (a : ℤ) :
    (a:GaussianInt)∈D.ideal ↔ (p:ℤ)∣a := by
  calc
    _ ↔ Ideal.Quotient.mk D.ideal (a:GaussianInt)=0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I:=D.ideal)).symm
    _ ↔ D.residue (Ideal.Quotient.mk D.ideal (a:GaussianInt))=D.residue 0 :=
      D.residue.injective.eq_iff.symm
    _ ↔ (a:ZMod p)=0 := by simp only [map_intCast,map_zero]
    _ ↔ _ := ZMod.intCast_zmod_eq_zero_iff_dvd a p

theorem contraction {p : ℕ} (D : DegreeOne p) :
    D.ideal.comap (Int.castRingHom GaussianInt)=Ideal.span ({(p:ℤ)}:Set ℤ) := by
  ext a
  rw [Ideal.mem_comap,Ideal.mem_span_singleton]
  exact integer_mem_iff D a

theorem modulus_not_mem {p M : ℕ} (D : DegreeOne p) (hp : p.Prime) (hc : p.Coprime M) :
    (M:GaussianInt)∉D.ideal := by
  intro h
  have H : (((M:ℤ):GaussianInt))∈D.ideal := by simpa only [Int.cast_natCast] using h
  have hpM : p∣M := by exact_mod_cast (integer_mem_iff D (M:ℤ)).mp H
  exact hp.coprime_iff_not_dvd.mp hc hpM

theorem rational_mem {p : ℕ} (D : DegreeOne p) : (p:GaussianInt)∈D.ideal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply D.residue.injective
  simpa only [map_natCast,map_zero] using ZMod.natCast_self p

theorem residue_i_mem {p : ℕ} (D : DegreeOne p) (hp : p.Prime) :
    ∃ a : ℕ, gi-(a:GaussianInt)∈D.ideal := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let r : ZMod p := D.residue (Ideal.Quotient.mk D.ideal gi)
  refine ⟨r.val,?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply D.residue.injective
  simp only [map_sub,map_natCast,map_zero]
  change r-(r.val:ZMod p)=0
  rw [ZMod.natCast_zmod_val,sub_self]

theorem rational_not_dvd_i_minus {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ¬(p:GaussianInt)∣gi-(a:GaussianInt) := by
  rintro ⟨b,hb⟩
  have hi := congrArg (fun t : GaussianInt => t.im) hb
  have hs : (1:ℤ)=(p:ℤ)*b.im := by
    simpa only [gi,Zsqrtd.im_sub,Zsqrtd.im_natCast,Zsqrtd.im_sqrtd,sub_zero,
      Zsqrtd.im_mul,Zsqrtd.re_natCast,zero_mul,add_zero] using hi
  have hI : (p:ℤ)∣(1:ℤ) := ⟨b.im,hs⟩
  have hN : p∣(1:ℕ) := by exact_mod_cast hI
  exact hp.ne_one (Nat.dvd_one.mp hN)

theorem generator_not_unit {p : ℕ} (D : DegreeOne p) : ¬IsUnit (generator D) := by
  intro hu
  have hD : generator D∣(1:GaussianInt) := isUnit_iff_dvd_one.mp hu
  have hmem : (1:GaussianInt)∈D.ideal := by
    rw [←generator_span D]
    exact Ideal.mem_span_singleton.mpr hD
  exact D.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)

/-- Principal generator of the actual degree-one ideal has norm p,
not p². The residue field being F_p is used essentially: the image
of i acquires a rational representative, so the ideal cannot be (p). -/
theorem generator_norm {p : ℕ} (D : DegreeOne p) (hp : p.Prime) :
    (generator D).norm=(p:ℤ) := by
  have hD := rational_mem D
  rw [←generator_span D] at hD
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hD
  have hbnu : ¬IsUnit b := by
    rintro ⟨e,rfl⟩
    have hg : (p:GaussianInt)∣generator D := by
      refine ⟨((e⁻¹ : GaussianIntˣ):GaussianInt),?_⟩
      rw [hb]
      simp [mul_assoc]
    obtain ⟨a,ha⟩ := residue_i_mem D hp
    rw [←generator_span D] at ha
    exact rational_not_dvd_i_minus hp a (hg.trans (Ideal.mem_span_singleton.mp ha))
  have hProd : (generator D).norm.natAbs*b.norm.natAbs=p^2 := by
    calc
      _ = ((generator D)*b).norm.natAbs := by rw [Zsqrtd.norm_mul,Int.natAbs_mul]
      _ = ((p:GaussianInt).norm).natAbs := by rw [←hb]
      _ = _ := by simp only [Zsqrtd.norm_natCast,Int.natAbs_mul,Int.natAbs_natCast,pow_two]
  have hn : (generator D).norm.natAbs=p :=
    ((hp.mul_eq_prime_sq_iff
      (mt Zsqrtd.norm_eq_one_iff.mp (generator_not_unit D))
      (mt Zsqrtd.norm_eq_one_iff.mp hbnu)).mp hProd).1
  simpa only [hn] using (GaussianInt.abs_natCast_norm (generator D)).symm

end ActualGaussianDegreeOneGenerator318
