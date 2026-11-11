module
public import ContactResidueRegularFlat318
public import ContactUniversalNonzeroLocus318
public section
noncomputable section
namespace ContactUniversalResidueNonzero318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactUniversalGeometricSpecialization318 OriginalSectionPullbackComposition318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : A →ₐ[ℚ] T)
local instance : Algebra A T := g.toAlgebra
local instance residueCoefficient (m : Ideal T) : Algebra R (T⧸m) :=
  (((Ideal.Quotient.mkₐ ℚ m).comp g).comp (parameterCoefficient R c L)).toAlgebra
local notation "U" => universalLine R c L
local notation "σ" => universalSection R c L hz
local notation "q" => ContactRelativeCoefficientChange318.curveMap A T g c

abbrev line : Line (curve T c) := LineSheafPullback318.line q U
abbrev section : Γ((line R c L T g).object,⊤) := pull q U.object σ

/-- A literal condition on the image of every maximal residue point of
the coefficient test scheme in the EXISTING nonzero parameter open. -/
def MaximalPointsInLocus : Prop := ∀ m : Ideal T, ∀ hm : m.IsMaximal,
  letI := hm
  ProjectiveParameterNonzeroOpen318.fieldPoint R Γ(L.object,⊤) (CommRingCat.of (T⧸m))
    (parameterPoint R c L (CommRingCat.of (T⧸m)) ((Ideal.Quotient.mkₐ ℚ m).comp g)) ∈
      ContactUniversalNonzeroLocus318.locus R c L hz

/-- The actual twice-pulled universal section has nonzero residue fibers.
Both original composition isomorphisms are used only in the correct
forward direction: a zero pull would map to the forbidden zero section. -/
lemma residue_nonzero (hg : MaximalPointsInLocus R c L hz T g) :
    ContactResidueRegularFlat318.ResidueNonzero T c (line R c L T g)
      (section R c L hz T g) := by
  intro m hm
  letI := hm
  let K := CommRingCat.of (T⧸m)
  let h : T →ₐ[ℚ] K := Ideal.Quotient.mkₐ ℚ m
  have hn := (ContactUniversalNonzeroLocus318.geometric_nonzero_iff R c L hz
    K (h.comp g)).mp (hg m hm)
  intro he
  have hc := ContactHZeroCoefficientFunctor318.geometric_composition A T g c U
    K h σ
  have hd : pull (ContactRelativeCoefficientChange318.curveMap A K (h.comp g) c)
      U.object σ=0 := by
    rw [show pull (ContactRelativeCoefficientChange318.curveMap T K h c)
      (line R c L T g).object (section R c L hz T g)=0 from he,map_zero] at hc
    exact hc.symm
  exact hn (by rw [hd,map_zero])

/-- Both complete original chart zero projections of the actual pulled
universal section are flat on every affine coefficient test satisfying
the literal nonzero-locus condition, without a residue regularity premise. -/
theorem chart_flatness (hg : MaximalPointsInLocus R c L hz T g) :
    Flat (OriginalAffineSectionFlat318.projection T (finiteRing c)
      (LineSheafPullback318.line (finiteInto T c) (line R c L T g))
      (pull (finiteInto T c) (line R c L T g).object (section R c L hz T g))) ∧
    Flat (OriginalAffineSectionFlat318.projection T (infinityRing c)
      (LineSheafPullback318.line (infinityInto T c) (line R c L T g))
      (pull (infinityInto T c) (line R c L T g).object (section R c L hz T g))) :=
  ⟨ContactResidueRegularFlat318.finite_flat T c _ _ (residue_nonzero R c L hz T g hg),
   ContactResidueRegularFlat318.infinity_flat T c _ _ (residue_nonzero R c L hz T g hg)⟩
end ContactUniversalResidueNonzero318
