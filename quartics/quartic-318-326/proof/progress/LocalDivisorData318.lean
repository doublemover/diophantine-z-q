module
public import VerticalResidueDifferent318
public import ResidueDifferent318
public import SourceJacobianBound318
public section
noncomputable section
namespace LocalDivisorData318
open Module Algebra IsDiscreteValuationRing IsLocalRing LenstraVertical318
open Matrix SourceJacobianBound318

/-- Actual local field/ring realization. No different coefficient bound is a field. -/
structure LocalExtension where
  (A : Type)
  (K : Type)
  (B : Type)
  (L : Type)
  [ringA : CommRing A]
  [domainA : IsDomain A]
  [fieldK : Field K]
  [ringB : CommRing B]
  [domainB : IsDomain B]
  [fieldL : Field L]
  [algebraAK : Algebra A K]
  [fractionAK : IsFractionRing A K]
  [algebraKL : Algebra K L]
  [algebraAL : Algebra A L]
  [algebraAB : Algebra A B]
  [algebraBL : Algebra B L]
  [towerAKL : IsScalarTower A K L]
  [towerABL : IsScalarTower A B L]
  [finiteKL : FiniteDimensional K L]
  [charK : CharZero K]
  [charA : CharZero A]
  [charB : CharZero B]
  [separableKL : Algebra.IsSeparable K L]
  [integralBA : IsIntegralClosure B A L]
  [dvrA : IsDiscreteValuationRing A]
  [dvrB : IsDiscreteValuationRing B]
  [torsionAB : IsTorsionFree A B]
  [fractionBL : IsFractionRing B L]
  pi : A
  uniformizer : Irreducible pi

attribute [instance] LocalExtension.ringA LocalExtension.domainA LocalExtension.fieldK
  LocalExtension.ringB LocalExtension.domainB LocalExtension.fieldL
  LocalExtension.algebraAK LocalExtension.fractionAK LocalExtension.algebraKL
  LocalExtension.algebraAL LocalExtension.algebraAB LocalExtension.algebraBL
  LocalExtension.towerAKL LocalExtension.towerABL LocalExtension.finiteKL
  LocalExtension.charK LocalExtension.charA LocalExtension.charB
  LocalExtension.separableKL LocalExtension.integralBA LocalExtension.dvrA
  LocalExtension.dvrB LocalExtension.torsionAB LocalExtension.fractionBL

@[expose] def LocalExtension.different (E:LocalExtension) : ℕ := differentExponent E.A E.B
@[expose] def LocalExtension.ramification (E:LocalExtension) : ℕ :=
  (addVal E.B (algebraMap E.A E.B E.pi)).toNat
@[expose] def LocalExtension.basePrimeValue (E:LocalExtension) (p:ℕ) : ℕ :=
  (addVal E.A (p:E.A)).toNat

/-- Horizontal coefficient identifications, including the nonnegative amount
subtracted by the base canonical divisor at infinity. -/
structure HorizontalData (canonical pullback:ℝ) where
  extension : LocalExtension
  residue_char_zero : CharZero (ResidueField extension.B)
  correction : ℝ
  correction_nonneg : 0≤correction
  canonical_eq : canonical=(extension.different:ℝ)-correction
  pullback_eq : pullback=(extension.ramification:ℝ)

/-- Vertical coefficient identifications and actual branch/degree restrictions. -/
structure VerticalData (d:ℕ) (canonical pullback:ℝ) where
  extension : LocalExtension
  p : ℕ
  prime : p.Prime
  residue_char : CharP (ResidueField extension.B) p
  branch_prime : p≤d
  local_degree : Module.finrank extension.K extension.L≤d
  canonical_eq : canonical=(extension.different:ℝ)
  pullback_eq : pullback=
    (2*extension.ramification*extension.basePrimeValue p*
      ⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊:ℕ)

/-- The three local model cases. In the unramified case the geometric
coefficient is zero. In the branched cases the actual different supplies it. -/
inductive CoefficientData (d:ℕ) (canonical pullback:ℝ) : Type 1
  | horizontal (data:HorizontalData canonical pullback)
  | vertical (data:VerticalData d canonical pullback)
  | unramified (canonical_zero:canonical=0) (pullback_nonneg:0≤pullback)

/-- Local domination is derived, rather than stored as a height or
coefficient inequality. Actual local-ring/coefficient realization stays explicit. -/
theorem CoefficientData.bound {d:ℕ} {canonical pullback:ℝ}
    (D:CoefficientData d canonical pullback) : canonical≤pullback := by
  cases D with
  | horizontal H =>
    let E:=H.extension
    letI:CharZero (ResidueField E.B):=H.residue_char_zero
    have hr:=ResidueDifferent318.horizontal_bound E.A E.K E.B E.L
      E.pi E.uniformizer.ne_zero E.uniformizer.not_isUnit
    have hn:E.different≤E.ramification := hr.trans (Nat.sub_le _ _)
    have hR:(E.different:ℝ)≤E.ramification := by exact_mod_cast hn
    exact H.canonical_eq.trans_le (((sub_le_self _ H.correction_nonneg).trans hR).trans_eq H.pullback_eq.symm)
  | vertical V =>
    let E:=V.extension
    letI:Fact V.p.Prime:=⟨V.prime⟩
    letI:CharP (ResidueField E.B) V.p:=V.residue_char
    have h:=VerticalResidueDifferent318.ramified_vertical_bound E.A E.K E.B E.L
      V.p d E.pi E.uniformizer V.branch_prime V.local_degree
    have hR:(E.different:ℝ)≤(2*E.ramification*E.basePrimeValue V.p*
        ⌊Real.log (d:ℝ)/Real.log (V.p:ℝ)⌋₊:ℕ) := by exact_mod_cast h
    exact V.canonical_eq.trans_le (hR.trans_eq V.pullback_eq.symm)
  | unramified hz hp => simpa only [hz] using hp

/-- Model intersection data with actual local algebra in place of an assumed
nonexceptional coefficient inequality. Adjunction, projection and the actual
intersection-matrix realization remain geometric inputs. -/
structure ModelData (ι κ:Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
    (n d N:ℕ) where
  matrix:Matrix ι ι ℝ
  negative_definite:(-matrix).PosDef
  off_diagonal:∀i j,i≠j → 0≤matrix i j
  outside_matrix:Matrix ι κ ℝ
  outside_nonneg:∀i j,0≤outside_matrix i j
  pullbackExceptional:ι→ℝ
  canonicalExceptional:ι→ℝ
  pullbackOutside:κ→ℝ
  canonicalOutside:κ→ℝ
  local_data:∀j,CoefficientData d (canonicalOutside j) (pullbackOutside j)
  adjunction:∀i,(matrix *ᵥ (pullbackExceptional-canonicalExceptional)) i+
    (outside_matrix *ᵥ (pullbackOutside-canonicalOutside)) i≤0
  sectionExceptional:ι→ℝ
  sectionOutside:κ→ℝ
  sectionExceptional_nonneg:∀i,0≤sectionExceptional i
  sectionOutside_nonneg:∀j,0≤sectionOutside j
  pullback_section:(∑i,pullbackExceptional i*sectionExceptional i)+
    (∑j,pullbackOutside j*sectionOutside j)≤
      FiniteDivisorArithmetic318.horizontalContact (1/(n:ℚ))+
      2*(∑p∈(6*N).primeFactors,(⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊:ℝ)*Real.log p)


/-- Every nonexceptional coefficient comparison is supplied by the actual
local different argument or the unramified zero-coefficient identity. -/
theorem ModelData.local_domination {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {n d N:ℕ} (D:ModelData ι κ n d N) : ∀j,D.canonicalOutside j≤D.pullbackOutside j :=
  fun j=>(D.local_data j).bound

/-- Construct the exact existing finite-divisor input, proving its local
coefficient field rather than accepting that field from the caller. -/
@[expose] def ModelData.toFiniteData {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {n d N:ℕ} (D:ModelData ι κ n d N) : FiniteData ι κ n d N where
  matrix := D.matrix
  negative_definite := D.negative_definite
  off_diagonal := D.off_diagonal
  outside_matrix := D.outside_matrix
  outside_nonneg := D.outside_nonneg
  pullbackExceptional := D.pullbackExceptional
  canonicalExceptional := D.canonicalExceptional
  pullbackOutside := D.pullbackOutside
  canonicalOutside := D.canonicalOutside
  local_domination := D.local_domination
  adjunction := D.adjunction
  sectionExceptional := D.sectionExceptional
  sectionOutside := D.sectionOutside
  sectionExceptional_nonneg := D.sectionExceptional_nonneg
  sectionOutside_nonneg := D.sectionOutside_nonneg
  pullback_section := D.pullback_section

/-- Exact finite canonical-section bound, with the local-different inequality
removed from the geometric premises. -/
theorem ModelData.bound {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {n d N:ℕ} (D:ModelData ι κ n d N) (hn:2≤n) (hd:1≤d) (hN:1≤N) :
    D.toFiniteData.intersection≤3*NumberField.absLogHeight₁ (1/(n:ℚ))+
      2*Real.log (6*(N:ℝ))*Real.log d/Real.log 2 :=
  D.toFiniteData.bound hn hd hN

end LocalDivisorData318
