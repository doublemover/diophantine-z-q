module
public import AffineSectionExtension318
public section
noncomputable section
namespace ActualPELFiniteFiberSections318
open VerticalSection318 CodimensionOneExtension318 AffineSectionExtension318
set_option maxHeartbeats 1000000

/-- Homogeneous polynomial denominator for the four fixed branch values. -/
def sep {A:Type*} [CommRing A] (n d:A) : A := ∏ i : Fin 4, (n - (contacts i : A) * d)

private theorem map_sep {A B:Type*} [CommRing A] [CommRing B] (f:A→+*B) (n d:A) :
    f (sep n d)=sep (f n) (f d) := by simp [sep]

private theorem den_formula {K:Type*} [Field K] (n d:K) (hd:d≠0) :
    denominator (n/d)=sep n d/d^4 := by
  simp only [denominator,sep]
  simp_rw [show ∀i:Fin 4,n/d-(contacts i:K)=(n-(contacts i:K)*d)/d from
    fun i=>by field_simp [hd] <;> ring]
  rw [Finset.prod_div_distrib]
  simp

def num₀ {A:Type*} [CommRing A] (d m:A) : A := (J:A)^2*m^2*d^4
def num₁ {A:Type*} [CommRing A] (n d m:A) : A := (J:A)^2*n*m^2*d^3
def den {A:Type*} [CommRing A] (n d e:A) : A := e^2*sep n d

variable {R A K L:Type*} [CommRing R] [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [IsNoetherianRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Algebra R K] [Field L]

local instance loc (P:Ideal A) [P.IsPrime] :
    IsLocalRing (primeLocalization (K:=K) P) :=
  IsLocalization.AtPrime.isLocalRing (primeLocalization (K:=K) P) P

/-- With no point-evaluation map on K, determine the actual two section
values by first extending across every height-one prime, then evaluating
the extension in an integral point chart. Rational open denominators
only need nonzero images in L, NOT unit images in O. -/
theorem integral_values (D:Derivation R K K) (t:K)
    (data:∀(P:Ideal A) [P.IsPrime], P.height=1→
      LocalData (B:=primeLocalization (K:=K) P) D t)
    (O:Subring L) (ev:A→+*O) (n d m e:A)
    (ht:t=algebraMap A K n/algebraMap A K d)
    (hDt:D t=algebraMap A K m/algebraMap A K e)
    (hd:(ev d:L)≠0) (he:(ev e:L)≠0) (hs:(ev (sep n d):L)≠0) :
    (ev (num₀ d m):L)/(ev (den n d e):L)∈O ∧
    (ev (num₁ n d m):L)/(ev (den n d e):L)∈O ∧
    (ev (num₁ n d m):L)/(ev (den n d e):L)=
      ((ev n:L)/(ev d:L))*((ev (num₀ d m):L)/(ev (den n d e):L)) := by
  let φ := algebraMap A K
  let ψ := O.subtype.comp ev
  change t=φ n/φ d at ht
  change D t=φ m/φ e at hDt
  change ψ e≠0 at he
  change ψ (sep n d)≠0 at hs
  have nz (a:A) (ha:ψ a≠0) : φ a≠0 := by
    intro hz
    apply ha
    have h : a=0 := IsFractionRing.injective A K (hz.trans (map_zero φ).symm)
    rw [h,map_zero]
  have hdk := nz d hd
  have hek := nz e he
  have hsk := nz (sep n d) hs
  have hsj : sep (φ n) (φ d)≠0 := by rwa [←map_sep φ]
  obtain ⟨a,b,ha,hb⟩ := affine_sections D t data
  have hc : a*den n d e=num₀ d m ∧ b*den n d e=num₁ n d m := by
    constructor
    · apply IsFractionRing.injective A K
      change φ (a*den n d e)=φ (num₀ d m)
      rw [map_mul,show φ a=section0 D t from ha]
      simp only [section0]
      rw [hDt,ht,den_formula (φ n) (φ d) hdk]
      simp only [den,num₀,map_mul,map_pow,map_intCast,map_sep]
      field_simp [hdk,hek,hsj] <;> ring
    · apply IsFractionRing.injective A K
      change φ (b*den n d e)=φ (num₁ n d m)
      rw [map_mul,show φ b=section1 D t from hb]
      simp only [section1,section0]
      rw [hDt,ht,den_formula (φ n) (φ d) hdk]
      simp only [den,num₁,map_mul,map_pow,map_intCast,map_sep]
      field_simp [hdk,hek,hsj] <;> ring
  have hp : ψ (den n d e)≠0 := by
    simpa only [den,map_mul,map_pow] using mul_ne_zero (pow_ne_zero 2 he) hs
  have get (x y:A) (eq:x*den n d e=y) : ψ y/ψ (den n d e)=ψ x := by
    apply (div_eq_iff hp).mpr
    simpa only [map_mul] using (congrArg ψ eq).symm
  have h₀ := get a _ hc.1
  have h₁ := get b _ hc.2
  change ψ (num₀ d m)/ψ (den n d e)∈O ∧ ψ (num₁ n d m)/ψ (den n d e)∈O ∧ _
  refine ⟨by rw [h₀]; exact (ev a).property,by rw [h₁]; exact (ev b).property,?_⟩
  change ψ (num₁ n d m)/ψ (den n d e)=(ψ n/ψ d)*(ψ (num₀ d m)/ψ (den n d e))
  have hd' : ψ d≠0 := hd
  field_simp [hp,hd'] <;> simp [num₀,num₁] <;> ring
/-- On a genuine noncontact point with nonvanishing differential, the
first coefficient cannot vanish. Combined with the preceding ratio
this also supplies the two nonarchimedean marked-vector hypotheses. -/
theorem first_ne [CharZero L] (O:Subring L) (ev:A→+*O) (n d m e:A)
    (hd:(ev d:L)≠0) (hm:(ev m:L)≠0) (he:(ev e:L)≠0)
    (hs:(ev (sep n d):L)≠0) : (ev (num₀ d m):L)/(ev (den n d e):L)≠0 := by
  let ψ := O.subtype.comp ev
  change ψ d≠0 at hd
  change ψ m≠0 at hm
  change ψ e≠0 at he
  change ψ (sep n d)≠0 at hs
  change ψ (num₀ d m)/ψ (den n d e)≠0
  have hJ : (VerticalSection318.J:L)≠0 := by norm_num [VerticalSection318.J]
  apply div_ne_zero
  · simpa only [num₀,map_mul,map_pow,map_intCast] using
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ) (pow_ne_zero 2 hm)) (pow_ne_zero 4 hd)
  · simpa only [den,map_mul,map_pow] using mul_ne_zero (pow_ne_zero 2 he) hs
/-- Instantiates the exact two-vector membership shape occurring at a
finite place in SmallActualPELHeight318.via_scaled_vectors. Different
places may use different integral charts, frames and numerator lifts.
The frame identification and the integrality of its basis, not integrality
of either resulting vector, are the remaining geometric comparisons. -/
theorem marked_pair_mem {V:Type*} [AddCommGroup V] [Module L V]
    (D:Derivation R K K) (t:K)
    (data:∀(P:Ideal A) [P.IsPrime], P.height=1→
      LocalData (B:=primeLocalization (K:=K) P) D t)
    (O:Subring L) (ev:A→+*O) (n d m e:A)
    (ht:t=algebraMap A K n/algebraMap A K d)
    (hDt:D t=algebraMap A K m/algebraMap A K e)
    (hd:(ev d:L)≠0) (he:(ev e:L)≠0) (hs:(ev (sep n d):L)≠0)
    (frame:L≃ₗ[L]V) (C:Set V) (lattice:∀z∈O,frame z∈C) (s₀ s₁:V)
    (id₀:s₀=frame ((ev (num₀ d m):L)/(ev (den n d e):L)))
    (id₁:s₁=frame ((ev (num₁ n d m):L)/(ev (den n d e):L))) :
    ∀i:Fin 2, ![s₀,s₁] i∈C := by
  obtain ⟨h₀,h₁,-⟩ := integral_values D t data O ev n d m e ht hDt hd he hs
  intro i
  fin_cases i
  · change s₀∈C
    rw [id₀]
    exact lattice _ h₀
  · change s₁∈C
    rw [id₁]
    exact lattice _ h₁
end ActualPELFiniteFiberSections318
