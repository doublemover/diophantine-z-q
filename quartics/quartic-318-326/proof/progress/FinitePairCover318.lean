module
public import InfinityAdditionAlgebra318
public import TangentOpenAlgebra318
public import OpenJAffineScheme318
public section
noncomputable section
namespace FinitePairCover318
open InfinityAdditionAlgebra318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R:Type u} {S:Type v} [CommRing R] [CommRing S]

lemma two_unit (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) : IsUnit (2:R) := by
  have h : IsUnit ((2:R)*(-8*(4*A^3+27*B^2))) := by
    convert hD using 1 <;> ring
  exact isUnit_of_mul_isUnit_left h

/-- The four actual chart functions cannot all vanish at any domain-valued pair. -/
theorem not_all_zero [IsDomain S] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:PairRing A B →+* S)
    (hg:φ (RelativeChordAlgebra318.gap A B)=0)
    (hs:φ (TangentOpenAlgebra318.ordinateSum A B)=0)
    (hc:φ (numeratorY A B false)=0) (ht:φ (numeratorY A B true)=0) : False := by
  have hx : φ (X2 A B)=φ (X1 A B) := by
    apply sub_eq_zero.mp
    simpa only [RelativeChordAlgebra318.gap,X1,X2,map_sub] using hg
  have hy : φ (Y2 A B) = -φ (Y1 A B) := by
    have hh : φ (Y1 A B)+φ (Y2 A B)=0 := by
      simpa only [TangentOpenAlgebra318.ordinateSum,Y1,Y2,map_add] using hs
    linear_combination hh
  have hc' : (-2*φ (Y1 A B))^3=0 := by
    simp only [numeratorY,numeratorX,denominator,slopeNumerator,Bool.false_eq_true,ite_false,
      map_sub,map_mul,map_pow,map_add,hx,hy,sub_self,pow_succ,pow_zero,map_one,mul_one,one_mul,mul_zero,zero_mul,sub_zero] at hc
    linear_combination -hc
  have hz : φ (Y1 A B)=0 := by
    have hh := eq_zero_of_pow_eq_zero hc'
    have h2 : (2:S) ≠ 0 := by
      have hu : IsUnit (2:S) := by
        simpa only [map_ofNat] using (two_unit A B hD).map (φ.comp (coeffMap A B).toRingHom)
      exact hu.ne_zero
    exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr h2)
  have hd : 3*φ (X1 A B)^2+φ (coeffMap A B A)=0 := by
    have ht' : (3*φ (X1 A B)^2+φ (coeffMap A B A))^3=0 := by
      simp only [numeratorY,numeratorX,denominator,slopeNumerator,ite_true,map_sub,map_mul,map_pow,map_add,
        hx,hy,hz,neg_zero,add_zero,pow_succ,pow_zero,map_one,mul_one,one_mul,mul_zero,zero_mul,sub_zero] at ht
      linear_combination -ht
    exact eq_zero_of_pow_eq_zero ht'
  have he := congrArg φ (first_equation A B)
  simp only [map_sub,map_pow,map_mul,map_zero,hz,zero_pow (by decide : 2≠0),zero_sub] at he
  have ha : φ (coeffMap A B A) = -3*φ (X1 A B)^2 := by linear_combination hd
  have hb : φ (coeffMap A B B) = 2*φ (X1 A B)^3 := by
    rw [ha] at he
    linear_combination -he
  have hzero : φ (coeffMap A B (-16*(4*A^3+27*B^2)))=0 := by
    have hm (c:R) (n:ℕ) : coeffMap A B (c^n)=(coeffMap A B c)^n := (coeffMap A B).toRingHom.map_pow c n
    simp only [map_neg,map_mul,map_add,hm,map_pow,map_ofNat,ha,hb]
    ring
  exact (((hD.map (coeffMap A B).toRingHom).map φ).ne_zero hzero)

lemma cover_of_domain_tests {T:Type u} [CommRing T] (a b c d:T)
    (test:∀ (S:Type u) [CommRing S] [IsDomain S] (φ:T →+* S),
      φ a=0 → φ b=0 → φ c=0 → φ d=0 → False) (p:PrimeSpectrum T) :
    p ∈ PrimeSpectrum.basicOpen a ∨ p ∈ PrimeSpectrum.basicOpen b ∨
    p ∈ PrimeSpectrum.basicOpen c ∨ p ∈ PrimeSpectrum.basicOpen d := by
  by_contra h
  simp only [PrimeSpectrum.mem_basicOpen,not_or,not_not] at h
  letI := p.isPrime
  exact test (T ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal)
    (Ideal.Quotient.eq_zero_iff_mem.mpr h.1) (Ideal.Quotient.eq_zero_iff_mem.mpr h.2.1)
    (Ideal.Quotient.eq_zero_iff_mem.mpr h.2.2.1) (Ideal.Quotient.eq_zero_iff_mem.mpr h.2.2.2)

/-- The four exact principal opens cover the entire actual finite-pair coordinate scheme. -/
theorem basic_open_cover (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (p:PrimeSpectrum (PairRing A B)) :
    p ∈ PrimeSpectrum.basicOpen (RelativeChordAlgebra318.gap A B) ∨
    p ∈ PrimeSpectrum.basicOpen (TangentOpenAlgebra318.ordinateSum A B) ∨
    p ∈ PrimeSpectrum.basicOpen (numeratorY A B false) ∨
    p ∈ PrimeSpectrum.basicOpen (numeratorY A B true) := by
  exact cover_of_domain_tests (T:=PairRing A B) _ _ _ _
    (fun S _ _ φ => not_all_zero A B hD φ) p

/-- No smoothness or unit premise remains on the literal OpenJ family. -/
theorem literal_basic_open_cover (N:ℕ)
    (p:PrimeSpectrum (PairRing (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N))) :
    p ∈ PrimeSpectrum.basicOpen (RelativeChordAlgebra318.gap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ∨
    p ∈ PrimeSpectrum.basicOpen (TangentOpenAlgebra318.ordinateSum (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)) ∨
    p ∈ PrimeSpectrum.basicOpen (numeratorY (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) false) ∨
    p ∈ PrimeSpectrum.basicOpen (numeratorY (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) true) :=
  basic_open_cover _ _ (OpenJAffineScheme318.discriminant_unit N) p

@[expose] def chartElement (A B:R) : Fin 4 → PairRing A B :=
  ![RelativeChordAlgebra318.gap A B,TangentOpenAlgebra318.ordinateSum A B,
    numeratorY A B false,numeratorY A B true]

/-- The four actual chart functions generate the unit ideal, not merely a dense open. -/
theorem chart_span_top (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Ideal.span (Set.range (chartElement A B))=⊤ := by
  apply (PrimeSpectrum.iSup_basicOpen_eq_top_iff (R:=PairRing A B) (f:=chartElement A B)).mp
  apply top_unique
  intro p _
  simp only [TopologicalSpace.Opens.mem_iSup]
  rcases basic_open_cover A B hD p with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

end FinitePairCover318
