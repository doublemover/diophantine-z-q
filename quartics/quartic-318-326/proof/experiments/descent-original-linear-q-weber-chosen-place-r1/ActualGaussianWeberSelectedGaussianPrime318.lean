module
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic
public section
noncomputable section

namespace ActualGaussianWeberSelectedGaussianPrime318

open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

@[expose] def literal (a b : ℤ) : GaussianInt := ⟨a,b⟩

@[expose] def gaussianI : GaussianInt := literal 0 1

theorem norm_literal (a b : ℤ) : (literal a b).norm=a^2+b^2 := by
  simp only [literal,Zsqrtd.norm]
  ring

theorem gaussianI_sq : gaussianI^2=(-1:GaussianInt) := by
  rw [pow_two]
  change (Zsqrtd.sqrtd:GaussianInt)*Zsqrtd.sqrtd=(((-1:ℤ)):GaussianInt)
  exact Zsqrtd.dmuld

variable {p : ℕ} [Fact p.Prime]

/-- The original norm-p pair selects the right reduction of i:
a+b·i₀=0. The opposite sign is not an independent choice. -/
@[expose] def rootOf (a b : ℤ) : ZMod p := -(a:ZMod p)/(b:ZMod p)

theorem pair_sq_zero (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    (a:ZMod p)^2+(b:ZMod p)^2=0 := by
  have e := congrArg (fun x : ℤ => (x:ZMod p)) hn
  simpa only [Int.cast_add,Int.cast_pow,Int.cast_natCast,CharP.cast_eq_zero] using e

theorem imag_not_zero_mod (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) : (b:ZMod p)≠0 := by
  intro hb
  have ha : (a:ZMod p)=0 := by
    have e := pair_sq_zero a b hn
    rw [hb,zero_pow (by decide : (2:ℕ)≠0),add_zero] at e
    by_contra h
    exact pow_ne_zero 2 h e
  obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha
  obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : (p:ℤ)*((p:ℤ)*(u^2+v^2))=(p:ℤ)*1 := by
    calc
      _ = ((p:ℤ)*u)^2+((p:ℤ)*v)^2 := by ring
      _ = a^2+b^2 := by rw [←hu,←hv]
      _ = _ := by rw [hn,mul_one]
  have hd : (p:ℤ)∣(1:ℤ) := ⟨u^2+v^2,(mul_left_cancel₀ hp0 e).symm⟩
  have hd' : p∣(1:ℕ) := by exact_mod_cast hd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hd')

theorem rootOf_sq (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) : (rootOf (p:=p) a b)^2= -1 := by
  unfold rootOf
  rw [div_pow,neg_sq]
  apply (div_eq_iff (pow_ne_zero 2 (imag_not_zero_mod a b hn))).2
  linear_combination pair_sq_zero a b hn

theorem rootOf_selected (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    (a:ZMod p)+(b:ZMod p)*rootOf (p:=p) a b=0 := by
  unfold rootOf
  rw [mul_comm (b:ZMod p),div_mul_cancel₀ _ (imag_not_zero_mod a b hn),add_neg_cancel]

/-- The actual Gaussian reduction with the selected square root, not
an unspecified degree-one residue-field isomorphism. -/
@[expose] def reduce (j : ZMod p) (hj : j^2= -1) : GaussianInt→+*ZMod p :=
  Zsqrtd.lift ⟨j,by simpa only [pow_two,Int.cast_neg,Int.cast_one] using hj⟩

theorem reduce_literal (j : ZMod p) (hj : j^2= -1) (a b : ℤ) :
    reduce j hj (literal a b)=(a:ZMod p)+(b:ZMod p)*j := rfl

theorem reduce_i (j : ZMod p) (hj : j^2= -1) : reduce j hj gaussianI=j := by
  rw [gaussianI,reduce_literal]
  simp only [Int.cast_zero,Int.cast_one,one_mul,zero_add]

theorem reduce_surjective (j : ZMod p) (hj : j^2= -1) :
    Function.Surjective (reduce j hj) := by
  intro z
  exact ⟨(z.val:GaussianInt),by rw [map_natCast,ZMod.natCast_zmod_val]⟩

@[expose] def selectedIdeal (j : ZMod p) (hj : j^2= -1) : Ideal GaussianInt :=
  RingHom.ker (reduce j hj)

theorem selected_ne_bot (j : ZMod p) (hj : j^2= -1) : selectedIdeal j hj≠⊥ := by
  intro he
  have hp0 : (p:GaussianInt)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp : (p:GaussianInt)∈selectedIdeal j hj := by
    change reduce j hj (p:GaussianInt)=0
    rw [map_natCast]
    exact CharP.cast_eq_zero (ZMod p) p
  rw [he,Ideal.mem_bot] at hp
  exact hp0 hp

instance selectedIdeal_isPrime (j : ZMod p) (hj : j^2= -1) :
    (selectedIdeal j hj).IsPrime := RingHom.ker_isPrime (reduce j hj)

instance selectedIdeal_isMaximal (j : ZMod p) (hj : j^2= -1) :
    (selectedIdeal j hj).IsMaximal :=
  (selectedIdeal_isPrime j hj).isMaximal (selected_ne_bot j hj)

@[expose] def selectedPrime (j : ZMod p) (hj : j^2= -1) : HeightOneSpectrum GaussianInt where
  asIdeal := selectedIdeal j hj
  isPrime := RingHom.ker_isPrime (reduce j hj)
  ne_bot := selected_ne_bot j hj

private theorem norm_prime_irreducible (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    Irreducible (literal a b) := by
  let g := literal a b
  have hp := (Fact.out : p.Prime)
  have hN : g.norm=(p:ℤ) := (norm_literal a b).trans hn
  have hp' : g.norm.natAbs=p := by rw [hN] <;> rfl
  constructor
  · intro h
    have hu := (Zsqrtd.isUnit_iff_norm_isUnit g).mp h
    have he : g.norm.natAbs=1 := Int.isUnit_iff_natAbs_eq.mp hu
    exact hp.ne_one (hp'.symm.trans he)
  · intro u v h
    have hf : u.norm.natAbs*v.norm.natAbs=p := by
      rw [←Int.natAbs_mul,←Zsqrtd.norm_mul,←h]
      exact hp'
    have hd : u.norm.natAbs ∣ p := ⟨v.norm.natAbs,hf.symm⟩
    rcases (Nat.dvd_prime hp).mp hd with he | he
    · exact Or.inl ((Zsqrtd.isUnit_iff_norm_isUnit u).mpr (Int.isUnit_iff_natAbs_eq.mpr he))
    · have hv : v.norm.natAbs=1 := by
        rw [he] at hf
        apply mul_left_cancel₀ hp.ne_zero
        simpa only [mul_one] using hf
      exact Or.inr ((Zsqrtd.isUnit_iff_norm_isUnit v).mpr (Int.isUnit_iff_natAbs_eq.mpr hv))

/-- The evaluated kernel is exactly the original prime generated by
a+bi, with the chosen sign of i. Norm p makes the generator prime;
annihilation by the selected evaluation distinguishes conjugates. -/
theorem selected_is_principal (j : ZMod p) (hj : j^2= -1)
    (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) (hSel : (a:ZMod p)+(b:ZMod p)*j=0) :
    selectedIdeal j hj=Ideal.span {literal a b} := by
  let g := literal a b
  have hgp : Prime g := (norm_prime_irreducible a b hn).prime
  have hs : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).mpr hgp
  have hne : (Ideal.span {g})≠⊥ := by
    intro h
    have hg : g∈Ideal.span ({g}:Set GaussianInt) := Ideal.subset_span (by simp)
    rw [h,Ideal.mem_bot] at hg
    exact hgp.ne_zero hg
  have hmax := hs.isMaximal hne
  have hIncl : Ideal.span ({g}:Set GaussianInt)≤selectedIdeal j hj := by
    apply Ideal.span_le.mpr
    intro z hz
    have he : z=g := Set.mem_singleton_iff.mp hz
    rw [he]
    change reduce j hj (literal a b)=0
    rw [reduce_literal]
    exact hSel
  exact (hmax.eq_of_le (RingHom.ker_ne_top _) hIncl).symm

theorem original_pair_selected_ideal (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    selectedIdeal (rootOf (p:=p) a b) (rootOf_sq a b hn)=Ideal.span {literal a b} :=
  selected_is_principal (rootOf (p:=p) a b) (rootOf_sq a b hn) a b hn (rootOf_selected a b hn)

@[expose] def quotientEquiv (j : ZMod p) (hj : j^2= -1) :
    (GaussianInt ⧸ selectedIdeal j hj) ≃+* ZMod p :=
  (reduce j hj).quotientKerEquivOfSurjective (reduce_surjective j hj)

theorem quotientEquiv_mk (j : ZMod p) (hj : j^2= -1) (z : GaussianInt) :
    quotientEquiv j hj (Ideal.Quotient.mk _ z)=reduce j hj z :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (reduce_surjective j hj) z

abbrev Base := FractionRing GaussianInt
abbrev BasePlace (j : ZMod p) (hj : j^2= -1) :=
  valuationSubringAtPrime Base (selectedPrime j hj)

@[expose] def complexEmbedding : Base→+*ℂ :=
  IsFractionRing.lift GaussianInt.toComplex_injective

theorem complexEmbedding_i :
    complexEmbedding (algebraMap GaussianInt Base gaussianI)=Complex.I := by
  rw [complexEmbedding,IsFractionRing.lift_algebraMap]
  change (((⟨0,1⟩:GaussianInt):ℂ))=Complex.I
  rw [GaussianInt.toComplex_def'] <;> simp

@[expose] def integralI (j : ZMod p) (hj : j^2= -1) : BasePlace j hj :=
  algebraMap GaussianInt (BasePlace j hj) gaussianI

theorem integralI_sq (j : ZMod p) (hj : j^2= -1) :
    (integralI j hj)^2=(-1:BasePlace j hj) := by
  have h := congrArg (algebraMap GaussianInt (BasePlace j hj)) gaussianI_sq
  simpa only [integralI,map_pow,map_neg,map_one] using h

/-- Exact degree-one residue map on the actual localized Gaussian
fraction field. The underlying quotient is the selected prime. -/
@[expose] def residueEquiv (j : ZMod p) (hj : j^2= -1) :
    ResidueField (BasePlace j hj) ≃+* ZMod p :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (selectedIdeal j hj) (BasePlace j hj)).toRingEquiv.symm.trans
    (quotientEquiv j hj)

theorem residueEquiv_integral (j : ZMod p) (hj : j^2= -1) (z : GaussianInt) :
    residueEquiv j hj (residue (BasePlace j hj) (algebraMap GaussianInt (BasePlace j hj) z))=
      reduce j hj z := by
  let E := IsLocalization.AtPrime.equivQuotMaximalIdeal (selectedIdeal j hj) (BasePlace j hj)
  have e : E (Ideal.Quotient.mk (selectedIdeal j hj) z)=
      residue (BasePlace j hj) (algebraMap GaussianInt (BasePlace j hj) z) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk (selectedIdeal j hj) (BasePlace j hj) z
  change quotientEquiv j hj (E.symm (residue _ (algebraMap GaussianInt (BasePlace j hj) z)))=_
  rw [←e,AlgEquiv.symm_apply_apply,quotientEquiv_mk]

theorem residueEquiv_i (j : ZMod p) (hj : j^2= -1) :
    residueEquiv j hj (residue (BasePlace j hj) (integralI j hj))=j :=
  (residueEquiv_integral j hj gaussianI).trans (reduce_i j hj)

theorem complexEmbedding_integralI (j : ZMod p) (hj : j^2= -1) :
    complexEmbedding ((BasePlace j hj).subtype (integralI j hj))=Complex.I := by
  change complexEmbedding (algebraMap (BasePlace j hj) Base
    (algebraMap GaussianInt (BasePlace j hj) gaussianI))=_
  rw [←IsScalarTower.algebraMap_apply GaussianInt (BasePlace j hj) Base]
  exact complexEmbedding_i

theorem selected_zero_in_residue (j : ZMod p) (hj : j^2= -1)
    (a b : ℤ) (hSel : (a:ZMod p)+(b:ZMod p)*j=0) :
    (a:ResidueField (BasePlace j hj))+
      (b:ResidueField (BasePlace j hj))*residue (BasePlace j hj) (integralI j hj)=0 := by
  apply (residueEquiv j hj).injective
  simpa only [map_add,map_mul,map_intCast,map_zero,residueEquiv_i] using hSel

end ActualGaussianWeberSelectedGaussianPrime318
