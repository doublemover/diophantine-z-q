module
public import ActualGaussianWeberValuedKernelChart318
public import ActualGaussianWeberFormalChord318
public section
noncomputable section

namespace ActualGaussianWeberHenselianSpecializationJoin318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianChart318 ActualGaussianWeberFormalChord318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)

/-- The exact missing stock group comparison, at the actual same-place
origin coordinates. The three displayed equalities are the finite chord
slope, intercept and third-root correction, not an arbitrary first jet.
A full comparison includes equality/inverse/tangencies and proves kernel
closure in the same branch. -/
@[expose] def ChordComparison (h2 : (2:ResidueField V) ≠ 0) : Prop :=
  ∀ (P Q : WP F) (P₀ : OriginData V P) (Q₀ : OriginData V Q),
    specialize V h2 P=Point.zero → specialize V h2 Q=Point.zero →
    ∀ l v C : V,
      l*(1+Q₀.t*(Q₀.w+P₀.w)) = Q₀.t^2+P₀.t*Q₀.t+P₀.t^2-P₀.w^2 →
      v=P₀.w-l*P₀.t →
      C*(1-l^2)=2*l*v →
      specialize V h2 (P+Q)=Point.zero ∧
        ∃ S : OriginData V (P+Q), S.t=P₀.t+Q₀.t-C

/-- Only the relevant subtraction consequence of group compatibility is
needed for equality of same-fibre torsion points. -/
@[expose] def SameFibreDifference (h2 : (2:ResidueField V) ≠ 0) : Prop :=
  ∀ P Q : WP F, specialize V h2 P=specialize V h2 Q →
    specialize V h2 (P-Q)=Point.zero

/-- Green chart + order-five donor yields the first-order addition on the
same stock points, under exactly the displayed geometric comparison. -/
theorem actual_add_order_five (h2 : (2:ResidueField V) ≠ 0)
    (hCmp : ChordComparison V h2) {P Q : WP F}
    (P₀ : OriginData V P) (Q₀ : OriginData V Q)
    (hP : specialize V h2 P=Point.zero) (hQ : specialize V h2 Q=Point.zero)
    (t a b : V) (ht : t∈maximalIdeal V)
    (ha : P₀.t=t*a) (hb : Q₀.t=t*b) :
    specialize V h2 (P+Q)=Point.zero ∧
      ∃ S : OriginData V (P+Q), ∃ c : V, S.t=t*(a+b)+t^5*c := by
  have hc₁ : identityChart (t*a) P₀.w := by rw [←ha]; exact P₀.chart
  have hc₂ : identityChart (t*b) Q₀.w := by rw [←hb]; exact Q₀.chart
  obtain ⟨l,v,C,c,hl,hv,hC,hct⟩ := order_five t a b P₀.w Q₀.w ht hc₁ hc₂
  obtain ⟨hRed,S,hS⟩ := hCmp P Q P₀ Q₀ hP hQ l v C
    (by simpa only [ha,hb] using hl)
    (by simpa only [ha] using hv) hC
  refine ⟨hRed,S,-c,?_⟩
  rw [hS,ha,hb,hct]
  ring

theorem actual_nsmul_order_five (h2 : (2:ResidueField V) ≠ 0)
    (hCmp : ChordComparison V h2) {P : WP F}
    (hP : specialize V h2 P=Point.zero) (P₀ : OriginData V P) (n : ℕ) :
    specialize V h2 (n • P)=Point.zero ∧
      ∃ S : OriginData V (n • P), ∃ c : V, S.t=(n:V)*P₀.t+P₀.t^5*c := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    have hO : specialize V h2 (0:WP F)=Point.zero := rfl
    obtain ⟨S⟩ := from_kernel V h2 0 hO
    refine ⟨hO,S,0,?_⟩
    have hS : S.t=0 := V.subtype_injective (by simpa only [tCoord,map_zero] using S.t_exact)
    simp [hS]
  | succ n ih =>
    obtain ⟨h₁,S,c,hS⟩ := ih
    let t := P₀.t
    let a : V := (n:V)+t^4*c
    have ha : S.t=t*a := by rw [hS]; change (n:V)*t+t^5*c=t*((n:V)+t^4*c); ring
    have hb : P₀.t=t*(1:V) := by simp [t]
    rw [succ_nsmul]
    obtain ⟨h₂,T,d,hT⟩ := actual_add_order_five V h2 hCmp S P₀ h₁ hP
      t a 1 P₀.smallT ha hb
    refine ⟨h₂,T,c+d,?_⟩
    rw [hT,Nat.cast_succ]
    change t*((n:V)+t^4*c+1)+t^5*d=((n:V)+1)*t+t^5*(c+d)
    ring

/-- Kernel of the actual reduction has no m-torsion away from the
residue characteristic, once the literal chord comparison is supplied. -/
theorem actual_kernel_torsion_zero (h2 : (2:ResidueField V) ≠ 0)
    (hCmp : ChordComparison V h2) {P : WP F} (hP : specialize V h2 P=Point.zero)
    (m : ℕ) (hm : residue V (m:V) ≠ 0) (h : m • P=0) :
    P=0 := by
  obtain ⟨P₀⟩ := from_kernel V h2 P hP
  obtain ⟨_,S,c,hS⟩ := actual_nsmul_order_five V h2 hCmp hP P₀ m
  have hz : S.t=0 := by
    apply V.subtype_injective
    rw [S.t_exact,h]
    simp [tCoord]
  have hj : (m:V)*P₀.t+P₀.t^2*(P₀.t^3*c)=0 := by
    calc
      _ = (m:V)*P₀.t+P₀.t^5*c := by ring
      _ = _ := hS.symm.trans hz
  have ht := unit_linear_kernel (m:V) P₀.t (P₀.t^3*c) hm P₀.smallT hj
  exact point_zero_of_chart_zero V h2 hP P₀ ht

/-- Actual same-place specialization is surjective on points, and injective
on prime-to-residue-characteristic torsion. Green affine_lift supplies the
first assertion, FormalChord supplies the small chart induction. The
precisely remaining stock projective addition input stays explicit. -/
theorem actual_specialization [HenselianLocalRing V] (hF : (2:F) ≠ 0)
    (h2 : (2:ResidueField V) ≠ 0)
    (hCmp : ChordComparison V h2) (hDiff : SameFibreDifference V h2) :
    Function.Surjective (specialize V h2) ∧
      ∀ (m : ℕ) (_ : residue V (m:V) ≠ 0),
        Set.InjOn (specialize V h2) {P | m • P=(0:WP F)} := by
  refine ⟨specialize_surjective V hF h2,?_⟩
  intro m hm P hP Q hQ hEq
  change m • P=0 at hP
  change m • Q=0 at hQ
  have hK := hDiff P Q hEq
  have h0 : m • (P-Q)=0 := by rw [nsmul_sub,hP,hQ,sub_zero]
  exact sub_eq_zero.mp (actual_kernel_torsion_zero V h2 hCmp hK m hm h0)

end ActualGaussianWeberHenselianSpecializationJoin318
