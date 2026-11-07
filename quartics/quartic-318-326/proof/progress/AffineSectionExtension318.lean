module
public import UnitRamifiedIntegral318
public import CodimensionOneExtension318
public section
noncomputable section
namespace AffineSectionExtension318
open VerticalSection318 IsLocalRing CodimensionOneExtension318
set_option maxHeartbeats 0

variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [IsLocalRing B]
  [Field K] [Algebra B K] [IsFractionRing B K] [Algebra R K]

/-- Concrete local geometry and frame data, not a supplied regularity or
integrality conclusion. All local rings below are actual rings in K. -/
inductive LocalData (D : Derivation R K K) (t : K) : Prop
  | vertical (p : ℕ) (dvr : IsDiscreteValuationRing B) (hp : Irreducible (p : B))
      (preserves : ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c) : LocalData D t
  | regular (qAlgebra : Algebra ℚ B) (x u : B) (hu : IsUnit u)
      (separated : ∀ i : Fin 4, residue B x ≠ residue B (contacts i : B))
      (derivative : D (algebraMap B K x) = algebraMap B K u)
      (coordinate : t = algebraMap B K x) : LocalData D t
  | finiteBranch (qAlgebra : Algebra ℚ B) (i : Fin 4) (u z dz : B)
      (hu : IsUnit u) (small : z ∈ maximalIdeal B) (nonzero : z ≠ 0) (hdz : IsUnit dz)
      (preserves : ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c)
      (derivative : D (algebraMap B K z) = algebraMap B K dz)
      (coordinate : t = (contacts i : K) + algebraMap B K u * (algebraMap B K z)^2) : LocalData D t
  | infinity (qAlgebra : Algebra ℚ B) (u z dz : B)
      (hu : IsUnit u) (small : z ∈ maximalIdeal B) (nonzero : z ≠ 0) (hdz : IsUnit dz)
      (preserves : ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c)
      (derivative : D (algebraMap B K z) = algebraMap B K dz)
      (coordinate : t = 1 / (algebraMap B K u * (algebraMap B K z)^2)) : LocalData D t

/-- Every geometric local case produces the two actual integral coefficients.
Neither the local derivative estimate nor local section regularity is an input. -/
theorem LocalData.integral (D : Derivation R K K) (t : K) (data : LocalData (B := B) D t) :
    (∃ b0 : B, algebraMap B K b0 = section0 D t) ∧
    (∃ b1 : B, algebraMap B K b1 = section1 D t) := by
  cases data with
  | vertical p dvr hp preserves =>
    letI := dvr
    exact VerticalSection318.sections_integral D preserves p hp t
  | regular qAlgebra x u hu separated derivative coordinate =>
    letI := qAlgebra
    subst t
    obtain ⟨b0,b1,-,h0,h1⟩ := UnitFrameHorizontal318.regular_sections D x u separated hu derivative
    exact ⟨⟨b0,h0⟩,⟨b1,h1⟩⟩
  | finiteBranch qAlgebra i u z dz hu small nonzero hdz preserves derivative coordinate =>
    letI := qAlgebra
    subst t
    obtain ⟨b0,b1,-,h0,h1⟩ := UnitRamifiedIntegral318.finite_branch_sections D preserves i u z dz hu small nonzero hdz derivative
    exact ⟨⟨b0,h0⟩,⟨b1,h1⟩⟩
  | infinity qAlgebra u z dz hu small nonzero hdz preserves derivative coordinate =>
    letI := qAlgebra
    subst t
    obtain ⟨b0,b1,-,h0,h1⟩ := UnitRamifiedIntegral318.infinity_sections D preserves u z dz hu small nonzero hdz derivative
    exact ⟨⟨b0,h0⟩,⟨b1,h1⟩⟩

section Affine
variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
  [IsNoetherianRing A] [Algebra A K] [IsFractionRing A K]

local instance localization_localRing (P : Ideal A) [P.IsPrime] :
    IsLocalRing (primeLocalization (K := K) P) :=
  IsLocalization.AtPrime.isLocalRing (primeLocalization (K := K) P) P

/-- The actual affine-frame producer: classify each actual height-one
localization by source coordinates or a reduced vertical DVR, and the two
rational section coefficients belong to the original affine ring. -/
theorem affine_sections (D : Derivation R K K) (t : K)
    (data : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      LocalData (B := primeLocalization (K := K) P) D t) :
    ∃ a0 a1 : A, algebraMap A K a0 = section0 D t ∧ algebraMap A K a1 = section1 D t := by
  have h0 : IsLocalization.IsInteger A (section0 D t) := by
    apply integer_of_height_one_localizations
    intro P hP hheight
    obtain ⟨⟨b,hb⟩,-⟩ := (data P hheight).integral D t
    change (b : K) = section0 D t at hb
    rw [←hb]
    exact b.property
  have h1 : IsLocalization.IsInteger A (section1 D t) := by
    apply integer_of_height_one_localizations
    intro P hP hheight
    obtain ⟨-,⟨b,hb⟩⟩ := (data P hheight).integral D t
    change (b : K) = section1 D t at hb
    rw [←hb]
    exact b.property
  obtain ⟨a0,ha0⟩ := h0
  obtain ⟨a1,ha1⟩ := h1
  exact ⟨a0,a1,ha0,ha1⟩

/-- The actual affine pair is uniquely determined by its rational sections. -/
theorem affine_sections_unique (D : Derivation R K K) (t : K)
    (data : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      LocalData (B := primeLocalization (K := K) P) D t) :
    ∃! a : A × A, algebraMap A K a.1 = section0 D t ∧ algebraMap A K a.2 = section1 D t := by
  obtain ⟨a0,a1,h0,h1⟩ := affine_sections D t data
  refine ⟨(a0,a1),⟨h0,h1⟩,?_⟩
  intro b hb
  apply Prod.ext
  · exact IsFractionRing.injective A K (hb.1.trans h0.symm)
  · exact IsFractionRing.injective A K (hb.2.trans h1.symm)

end Affine
end AffineSectionExtension318
