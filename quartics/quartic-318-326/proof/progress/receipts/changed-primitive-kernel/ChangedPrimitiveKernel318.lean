module
public import PrimitiveCoefficientSquares318
public section
noncomputable section
namespace ChangedPrimitiveKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "a" => algebraMap R S
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "hS" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S) A B hD
local notation "E" => WeierstrassGluing318.scheme (a A) (a B)
local notation "c" => WeierstrassCoefficientMap318.coefficientMap (S:=S) A B
local notation "p" => WeierstrassGluing318.structureMap (a A) (a B)
local notation "e" => WeierstrassGluing318.infinity (a A) (a B)
local notation "tr" => CompletedIteratedAddition318.tripling (a A) (a B) hS

/-- Invertibility is inherited from the actual literal base, not a new condition on S. -/
@[expose, instance_reducible] def inverse_three : Invertible (3:S) :=
  (show IsUnit (3:S) from by
    simpa only [map_ofNat] using ((OpenJModel318.base_units N).2.1.map a)).invertible
variable [Invertible (3:S)]
local notation "T" => ThreeTorsionScheme318.scheme (a A) (a B) hS
local notation "ι" => ThreeTorsionCompletedDoubling318.inclusion (a A) (a B) hS

@[expose] def NowhereZero {X:Scheme} (t:X ⟶ E) : Prop := ∀x:X,t x ∉ Set.range e

theorem inclusion_nowhereZero : NowhereZero N S ι := by
  intro x
  rintro ⟨b,hb⟩
  have hf:e b ∈ Set.range (WeierstrassGluing318.finiteChart (a A) (a B)) := by
    rw [hb]
    exact ⟨ThreeTorsionScheme318.inclusion (a A) (a B) hS x,rfl⟩
  have hz:b ∈ e ⁻¹ᵁ (WeierstrassGluing318.finiteChart (a A) (a B)).opensRange:=hf
  rw [CompletedZeroTripling318.origin_preimage_finite] at hz
  exact hz

lemma forget_nowhereZero {X:Scheme} (t:X ⟶ E) (hn:NowhereZero N S t) :
    LiteralPrimitiveKernel318.NowhereZero N (t ≫ c) := by
  intro x hx
  apply hn x
  rw [PrimitiveCoefficientSquares318.zero_range]
  exact hx

lemma forget_tripling {X:Scheme} (t:X ⟶ E) (h:t ≫ tr=t ≫ p ≫ e) :
    (t ≫ c) ≫ CompletedIteratedAddition318.tripling A B hD=
      (t ≫ c) ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  calc
    _=(t ≫ tr) ≫ c := by rw [Category.assoc,CompletedAdditionCoefficient318.tripling,←Category.assoc]
    _=(t ≫ p ≫ e) ≫ c := by rw [h]
    _=_ := by
      simp only [Category.assoc,WeierstrassCoefficientMap318.coefficientMap_infinity]
      rw [←Category.assoc c (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.infinity A B),
        WeierstrassCoefficientMap318.coefficientMap_base,Category.assoc]

/-- Exact primitive representability for every coefficient algebra and every
Scheme test; the lift uses the actual cartesian inclusion square. -/
theorem universal {X:Scheme} (t:X ⟶ E) (h:t ≫ tr=t ≫ p ≫ e)
    (hn:NowhereZero N S t) : ∃!g:X ⟶ T,g ≫ ι=t := by
  obtain ⟨g,hg,_⟩:=LiteralPrimitiveKernel318.universal N (t ≫ c)
    (forget_tripling N S t h) (forget_nowhereZero N S t hn)
  let H:=PrimitiveCoefficientSquares318.inclusion_cartesian (S:=S) A B hD
  refine ⟨H.lift g t hg,H.lift_snd g t hg,?_⟩
  intro g' hg'
  haveI:=ThreeTorsionCompletedClosed318.inclusion_closed (a A) (a B) hS
  exact (cancel_mono ι).mp (hg'.trans (H.lift_snd g t hg).symm)

theorem exists_iff {X:Scheme} (t:X ⟶ E) :
    (∃g:X ⟶ T,g ≫ ι=t) ↔ (t ≫ tr=t ≫ p ≫ e) ∧ NowhereZero N S t := by
  constructor
  · rintro ⟨g,rfl⟩
    constructor
    · simp only [Category.assoc,ThreeTorsionCompletedTripling318.inclusion_tripling,
        ThreeTorsionCompletedDoubling318.inclusion_over_base_assoc]
    · intro x
      exact inclusion_nowhereZero N S (g x)
  · rintro ⟨h,hn⟩
    exact (universal N S t h hn).exists
end ChangedPrimitiveKernel318
