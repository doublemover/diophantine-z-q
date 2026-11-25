module

public import OriginalRetainedDyadicInverseRay318
public import OriginalRetainedF33ExponentialFromLog318
public import OriginalRetainedActualExponentialInThree318

@[expose] public section
noncomputable section

namespace OriginalRetainedInverseToGlobalExp318

open AlgebraicGeometry CategoryTheory Filter
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedF33ExponentialQuotient318
open OriginalRetainedF33ExponentialFromLog318 OriginalRetainedDyadicInverseRay318
open OriginalRetainedActualExponentialInThree318 OriginalRetainedDyadicGroupLog318
open OriginalRetainedComplexPointFromE318 OriginalRetainedComplexPointsOverEEquiv318
open OriginalActualDoublingInverse318 OriginalDyadicChartLogLimit318
open scoped Topology CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {A Y : Scheme} (a : A⟶Y) [GrpObj (Over.mk a)]
variable {E : Type} [Field E] (σ : E→+*ℂ)
variable (P : Spec (CommRingCat.of E)⟶Y)
variable [comm : IsCommMonObj (OriginalRetainedComplexZeroByPasting318.fiber a (specOf σ≫P))]

/-- Only retags a point of the same original represented group. -/
def inverseGerm (pt : Tangent→Points a σ P) (λ : Tangent→Tangent) :
    Tangent→Additive (Points a σ P) := fun z=>Additive.ofMul (pt (λ z))

theorem inverseGerm_zero (pt : Tangent→Points a σ P) (λ : Tangent→Tangent)
    (origin : pt (λ 0)=1) : inverseGerm a σ P pt λ 0=0 :=
  congrArg Additive.ofMul origin

theorem inverseGerm_add (pt : Tangent→Points a σ P) (λ : Tangent→Tangent)
    (ρ : ℝ)
    (law : ∀ z w, ‖z‖≤ρ/8 → ‖w‖≤ρ/8 →
      pt (λ (z+w))=pt (λ z)*pt (λ w))
    (z w : Tangent) (hz : ‖z‖<ρ/8) (hw : ‖w‖<ρ/8) :
    inverseGerm a σ P pt λ (z+w)=inverseGerm a σ P pt λ z+inverseGerm a σ P pt λ w :=
  congrArg Additive.ofMul (law z w hz.le hw.le)

include comm in
/-- R166's normalized inverse yields one global homomorphism by R124's
actual dyadic continuation. Its E-read is literally the selected
original F33 lift, and agrees on the entire retained point on the
small ball. Neither global kernel nor analytic openness is an input. -/
theorem produce_same_global_exp_with_region
    (m : Tangent→Tangent→Tangent) (pt : Tangent→Points a σ P)
    {r C chart : ℝ}
    (rpos : 0<r) (hC : 0≤C) (Csmall : C*r≤1/3)
    (Bsmall : ((2*halfErrorConstant C)/(1-gain))*r≤1/2)
    (origin : pt 0=1) (zero : m 0 0=0)
    (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
    (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
    (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (l λ : Tangent→Tangent) (ex : Tangent→+Additive (Points a σ P)),
      0<ρ ∧ ρ≤r/4 ∧ l 0=0 ∧
      (∀ w, ‖w‖≤ρ/2 → ‖λ w‖≤ρ ∧ l (λ w)=w) ∧
      (∀ x y, ‖x‖≤ρ → ‖y‖≤ρ → ‖(l x-x)-(l y-y)‖≤(1/2:ℝ)*‖x-y‖) ∧
      (∀ z, ‖z‖<ρ/8 → (ex z).toMul=pt (λ z)) ∧
      (∀ v, Tendsto (fun t : ℂ=>t⁻¹ • (λ (t•v)-t•v)) (𝓝 0) (𝓝 0)) ∧
      (∀ (alt : Tangent→+Additive (Points a σ P)),
        (∀ z, ‖z‖<ρ/8 → (alt z).toMul=pt (λ z)) → ex=alt) := by
  obtain ⟨ρ,l,λ,ρpos,ρr,l0,_λ0,pt0,lread,add,rays,ηlip⟩ :=
    actual_inverse_on_marked_points_with_region m a P (specOf σ) pt rpos hC Csmall Bsmall origin zero
      fit inj law defectLip quad
  let f := inverseGerm a σ P pt λ
  have f0 : f 0=0 := inverseGerm_zero a σ P pt λ pt0
  have fadd (z w : Tangent) (hz : ‖z‖<ρ/8) (hw : ‖w‖<ρ/8) (_ : ‖z+w‖<ρ/8) :
      f (z+w)=f z+f w := inverseGerm_add a σ P pt λ ρ add z w hz hw
  have rad : 0<ρ/8 := div_pos ρpos (by norm_num)
  let ex := actualExp a σ P (ρ/8) rad f f0 fadd
  refine ⟨ρ,l,λ,ex,ρpos,ρr,l0,lread,ηlip,?_,rays,?_⟩
  · intro z hz
    exact congrArg Additive.toMul (reads_actual_local a σ P (ρ/8) rad f f0 fadd z hz)
  · intro alt ha
    apply unique_of_actual_germ a σ P (ρ/8) rad f f0 fadd alt
    intro z hz
    apply Additive.toMul.injective
    exact ha z hz


include comm in
/-- Historical statement, now derived from the same regional
producer without choosing a second logarithm or global map. -/
theorem produce_same_global_exp
    (m : Tangent→Tangent→Tangent) (pt : Tangent→Points a σ P)
    {r C chart : ℝ}
    (rpos : 0<r) (hC : 0≤C) (Csmall : C*r≤1/3)
    (Bsmall : ((2*halfErrorConstant C)/(1-gain))*r≤1/2)
    (origin : pt 0=1) (zero : m 0 0=0)
    (fit : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y‖≤chart)
    (inj : ∀ x y, ‖x‖≤chart → ‖y‖≤chart → pt x=pt y → x=y)
    (law : ∀ x y, ‖x‖≤r → ‖y‖≤r → pt (m x y)=pt x*pt y)
    (defectLip : ∀ ρ, 0≤ρ → ρ≤r → ∀ x y, ‖x‖≤ρ → ‖y‖≤ρ →
      ‖defect m x-defect m y‖≤C*ρ*‖x-y‖)
    (quad : ∀ x y, ‖x‖≤r → ‖y‖≤r → ‖m x y-(x+y)‖≤C*(max ‖x‖ ‖y‖)^2) :
    ∃ (ρ : ℝ) (λ : Tangent→Tangent) (ex : Tangent→+Additive (Points a σ P)),
      0<ρ ∧ ρ≤r/4 ∧
      (∀ z, ‖z‖<ρ/8 → (ex z).toMul=pt (λ z)) ∧
      (∀ v, Tendsto (fun t : ℂ=>t⁻¹ • (λ (t•v)-t•v)) (𝓝 0) (𝓝 0)) ∧
      (∀ (alt : Tangent→+Additive (Points a σ P)),
        (∀ z, ‖z‖<ρ/8 → (alt z).toMul=pt (λ z)) → ex=alt) := by
  obtain ⟨ρ,_l,λ,ex,rp,rr,_,_,_,localProof,rays,unique⟩ :=
    produce_same_global_exp_with_region a σ P m pt rpos hC Csmall Bsmall
      origin zero fit inj law defectLip quad
  exact ⟨ρ,λ,ex,rp,rr,localProof,rays,unique⟩

section SameSelectedFineFibre

variable {L : Type} [Field L] (i : L→+*E)
variable {A3 Y3 : Scheme} (a3 : A3⟶Y3) (forget : Y⟶Y3) (u : A⟶A3)
variable (cart : IsPullback u a a3 forget) [MonObj (Over.mk a3)]
variable (x3 : Spec (CommRingCat.of L)⟶Y3)
variable (named : specOf i≫x3=P≫forget)
variable (ex : Tangent→+Additive (Points a σ P))
variable (pt : Tangent→Points a σ P) (λ : Tangent→Tangent) (ρ : ℝ)
variable (localExact : ∀ z, ‖z‖<ρ/8 → (ex z).toMul=pt (λ z))

include localExact in
theorem local_E_lift_reads (z : Tangent) (hz : ‖z‖<ρ/8) :
    complexPoint a P (specOf σ) (arithmeticRead a σ P ex z)=pt (λ z) :=
  (lift_of_readOverE a P (specOf σ) (ex z).toMul).trans (localExact z hz)

include localExact in
/-- The exact same continued local point, now through the real [11]
forget on the named original x3 fibre. This is whole-morphism equality,
not an identity of selected scalar coordinates. -/
theorem local_three_lift_reads (z : Tangent) (hz : ‖z‖<ρ/8) :
    originalInThree a a3 forget u cart i σ P x3 named (arithmeticRead a σ P ex) z =
      pt (λ z)≫(complex a a3 forget u cart i σ P x3 named).hom := by
  rw [real_point_in_three a a3 forget u cart i σ P x3 named ex z,localExact z hz]

end SameSelectedFineFibre

end OriginalRetainedInverseToGlobalExp318
