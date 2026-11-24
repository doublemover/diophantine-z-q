module
public import OriginalCanonicalVerticalStalk318
public import OriginalCharacterHorizontal318
import all SelectedActualSameAFiniteDlogRows318
import all OriginalCharacterHorizontal318
import all OriginalIntegerAffineExtend318
import all OriginalIntegralFrameLocalize318
public section
noncomputable section

namespace OriginalWholeAffineSections318
open OriginalIntegerAffineExtend318 OriginalCanonicalVerticalStalk318 OriginalIntegralFrameLocalize318
open SelectedActualSameAFiniteDlogRows318 SelectedSameADyadicVerticalD2_318
open scoped nonZeroDivisors

section general
variable {K : Type*} [Field K] (G : Subring K)

theorem from_all_maximals (x : K) (h : ∀ q : Ideal G,q.IsMaximal → HasStalkValue G q x) :
    x∈G := by
  let I : Ideal G :=
    { carrier := {a : G | (a:K)*x∈G}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change ((a:K)+(b:K))*x∈G
        rw [add_mul]
        exact G.add_mem ha hb
      smul_mem' := by
        intro a b hb
        change ((a:K)*(b:K))*x∈G
        rw [mul_assoc]
        exact G.mul_mem a.property hb }
  by_contra hn
  have ht : I≠⊤ := by
    intro e
    have hh : (1:G)∈I := by rw [e]; trivial
    exact hn (by change (1:K)*x∈G at hh; simpa using hh)
  obtain ⟨q,hq,hI⟩ := Ideal.exists_le_maximal I ht
  obtain ⟨s,hs,a,he⟩ := h q hq
  exact hs (hI (by change (s:K)*x∈G; rw [he]; exact a.property))

theorem bottom_stalk_value [IsFractionRing G K] (x : K) : HasStalkValue G ⊥ x := by
  obtain ⟨a,b,hb,he⟩ := IsFractionRing.div_surjective G x
  have nb : b≠0 := nonZeroDivisors.ne_zero hb
  have nk : (b:K)≠0 := fun e => nb (Subtype.ext e)
  refine ⟨b,fun h => nb (Ideal.mem_bot.mp h),a,?_⟩
  change (a:K)/(b:K)=x at he
  rw [←he]; field_simp [nk]

private theorem inverse_mem (V : Subring K) (u : V) (hu : IsUnit u) : (u:K)⁻¹∈V := by
  obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp hu
  have he : (u:K)*(b:K)=1 := congrArg V.subtype hb
  rw [inv_eq_of_mul_eq_one_right he]
  exact b.property

private theorem finite_or_infty (V : Subring K) [IsFractionRing V K] [ValuationRing V]
    (t : K) : t∈V ∨ t⁻¹∈V := by
  let v := ValuationRing.valuation V K
  rcases Valuation.val_le_one_or_val_inv_le_one v t with h|h
  · obtain ⟨a,ha⟩ := (ValuationRing.mem_integer_iff V K t).mp h
    exact Or.inl (ha ▸ a.property)
  · obtain ⟨a,ha⟩ := (ValuationRing.mem_integer_iff V K t⁻¹).mp h
    exact Or.inr (ha ▸ a.property)

private theorem infinity_unit (V : Subring K) [IsLocalRing V] (t : K) (hn : t∉V)
    (hs : t⁻¹∈V) : (OriginalCharacterHorizontal318.G t⁻¹)⁻¹∈V ∧
      OriginalCharacterHorizontal318.G t⁻¹ ≠ 0 := by
  let s : V := ⟨t⁻¹,hs⟩
  let m := IsLocalRing.maximalIdeal V
  have nu : ¬IsUnit s := by
    intro h
    have hh := inverse_mem V s h
    change (t⁻¹)⁻¹∈V at hh
    exact hn (by simpa using hh)
  have sm : s∈m := nu
  let H : V := -32*(1-76832*s)*(1+343*s)-76832*(1+343*s)+343
  let g := OriginalCharacterHorizontal318.G s
  have eg : g=1+s*H := by dsimp [g,H,OriginalCharacterHorizontal318.G]; ring
  have gu : IsUnit g := by
    by_contra notg
    have gm : g∈m := notg
    have om := m.sub_mem gm (m.mul_mem_right H sm)
    rw [eg,add_sub_cancel_right] at om
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).mpr om)
  have gread : (g:K)=OriginalCharacterHorizontal318.G t⁻¹ := by
    change V.subtype ((1-32*s)*(1-76832*s)*(1+343*s))=_
    simp only [map_mul,map_sub,map_add,map_ofNat,map_one]
    rfl
  rw [←gread]
  exact ⟨inverse_mem V g gu,(gu.map V.subtype).ne_zero⟩
end general

section original
variable {K : Type*} [Field K] [CharZero K]

private theorem killsQ (D : Derivation ℤ K K) (q : ℚ) : D (algebraMap ℚ K q)=0 := by
  have he : algebraMap ℚ K q=algebraMap ℤ K q.num/algebraMap ℤ K (q.den:ℤ) := by
    conv_lhs => rw [←q.num_div_den]
    rw [map_div₀,map_intCast,map_natCast]
    norm_num
  rw [he,D.leibniz_div,D.map_algebraMap,D.map_algebraMap]
  simp

def asQ (D : Derivation ℤ K K) : Derivation ℚ K K where
  toLinearMap :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun q x => by
        rw [RingHom.id_apply,Algebra.smul_def,Algebra.smul_def]
        rw [D.leibniz,killsQ,smul_zero,add_zero,smul_eq_mul] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

/-- Entire characteristic-zero generic fibre from its actual structural functions.
At any nonzero maximal the canonical DVR contains t or its inverse; when
t is not integral there the reciprocal denominator is automatically a unit. -/
theorem generic_pair (G : Subalgebra ℚ K) [IsFractionRing G K] [IsDedekindDomain G]
    (D : Derivation ℚ K K) (hD : ∀ z∈G,D z∈G) (t : K)
    (r : Fin 4 → K) (c : Fin 4 → ℚˣ) (hn : ∀ i,contact t i≠0)
    (he : ∀ i,r i^2=algebraMap ℚ K (c i:ℚ)*contact t i) :
    (D t)^2/OriginalCharacterHorizontal318.P t ∈G ∧
    t*(D t)^2/OriginalCharacterHorizontal318.P t∈G := by
  let : IsFractionRing G.toSubring K := (inferInstance : IsFractionRing G K)
  let x := (D t)^2/OriginalCharacterHorizontal318.P t
  let y := t*(D t)^2/OriginalCharacterHorizontal318.P t
  have test (q : Ideal G) (claim : q.IsMaximal) :
      HasStalkValue G.toSubring q x ∧ HasStalkValue G.toSubring q y := by
    by_cases bot : q=⊥
    · subst q; exact ⟨bottom_stalk_value _ _,bottom_stalk_value _ _⟩
    let : q.IsPrime := claim.isPrime
    obtain ⟨V,incl,loc,fr⟩ := embedded_prime G.toSubring q
    let : Algebra G V := (Subring.inclusion incl).toAlgebra
    let : IsLocalization q.primeCompl V := loc
    let : IsFractionRing V K := fr
    let : IsDiscreteValuationRing V := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain G bot V
    let W : Subalgebra ℚ K := { V.toSubsemiring with algebraMap_mem' := fun z => incl (G.algebraMap_mem z) }
    let : IsFractionRing W K := fr
    let : IsDiscreteValuationRing W := (inferInstance : IsDiscreteValuationRing V)
    have hstable : ∀ z∈W,D z∈W :=
      preserves_stalk G.toSubring q V incl loc (D.restrictScalars ℤ) hD
    have bounds : x∈W ∧ y∈W := by
      by_cases ht : t∈W
      · apply OriginalCharacterHorizontal318.finite_chart W D hstable t ht r c
        · intro i
          have same : OriginalCharacterHorizontal318.b i=LinearContactSquareclass318.contacts i := by
            fin_cases i <;> rfl
          simpa only [same,contact] using he i
        · intro i
          have same : OriginalCharacterHorizontal318.b i=LinearContactSquareclass318.contacts i := by
            fin_cases i <;> rfl
          simpa only [same,contact] using hn i
      · have hs := (finite_or_infty V t).resolve_left ht
        obtain ⟨gi,gn⟩ := infinity_unit V t ht hs
        have t0 : t≠0 := by simpa [contact,LinearContactSquareclass318.contacts] using hn 0
        have r0 := he 0
        apply OriginalCharacterHorizontal318.infinity_chart W D hstable t t0 hs gi gn (r 0) (c 0)
        simpa [contact,LinearContactSquareclass318.contacts] using r0
    exact ⟨from_localization G.toSubring V incl loc bounds.1,from_localization G.toSubring V incl loc bounds.2⟩
  exact ⟨from_all_maximals G.toSubring x (fun q hq => (test q hq).1),
    from_all_maximals G.toSubring y (fun q hq => (test q hq).2)⟩

/-- The actual finite-section producer on an arbitrary original arithmetic
affine, with NO horizontal good-section input, valuation, elliptic-map
comparison or chosen vertical frame in the conclusion's hypotheses. -/
theorem produce (A : Subring K) [IsFractionRing A K]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (G : Subalgebra ℚ K)
    [IsFractionRing G K] [IsDedekindDomain G] (hAG : A≤G.toSubring)
    (gen : letI := (Subring.inclusion hAG).toAlgebra; IsLocalization (positiveIntegers A) G)
    (fibre : ∀ p : ℕ,p.Prime → IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (frame : KaehlerDifferential ℤ A →ₗ[A] A) (t : K)
    (roots : Fin 4 → K) (twists : Fin 4 → ℚˣ) (hn : ∀ i,contact t i≠0)
    (he : ∀ i,roots i^2=algebraMap ℚ K (twists i:ℚ)*contact t i) :
    (25725/4:K)*32*qcoeff t (fractionDerivative A frame t)∈A ∧
    (25725/4:K)*t*qcoeff t (fractionDerivative A frame t)∈A := by
  let D := fractionDerivative A frame
  have sA : ∀ z∈A,D z∈A := by
    intro z h
    let a : A := ⟨z,h⟩
    change fractionDerivative A frame (a:K)∈A
    rw [fractionDerivative_apply]; exact (frame (KaehlerDifferential.D ℤ A a)).property
  have sG := preserves_localization A (positiveIntegers A) G.toSubring hAG gen D sA
  obtain ⟨h0,h1⟩ := generic_pair G (asQ D) sG t roots twists hn he
  change (D t)^2/OriginalCharacterHorizontal318.P t ∈ G at h0
  change t*(D t)^2/OriginalCharacterHorizontal318.P t ∈ G at h1
  have ep : product t=OriginalCharacterHorizontal318.P t := by
    norm_num [product,contact,OriginalCharacterHorizontal318.P,LinearContactSquareclass318.contacts]
  have ck : (25725/4:K)∈G := by
    simpa only [map_div₀,map_ofNat] using G.algebraMap_mem (25725/4:ℚ)
  apply produce_pair A G.toSubring hAG gen fibre frame t roots twists hn he
  constructor
  · change (25725/4:K)*32*((D t)^2/product t)∈G
    rw [ep]
    have h32:(32:K)∈G := by exact_mod_cast G.natCast_mem 32
    exact G.mul_mem (G.mul_mem ck h32) h0
  · change (25725/4:K)*t*((D t)^2/product t)∈G
    rw [ep,mul_assoc,←mul_div_assoc]
    exact G.mul_mem ck h1
end original
end OriginalWholeAffineSections318
