module
public import UnitLineDifferentials318
public import ActualDifferentialTriple318
public section
noncomputable section
namespace GlobalInvariantLine318
open AlgebraicGeometry CategoryTheory Opposite
open AffineDifferentialSheaf318 InvariantChartCover318 UnitLineDifferentials318
open InvariantNormalizedFrames318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- An actual global O-module line on the genuine glued elliptic-family scheme. -/
@[expose] def line (A B : R) : (WeierstrassGluing318.scheme A B).Modules :=
  SheafOfModules.unit (WeierstrassGluing318.scheme A B).ringCatSheaf
/-- Its genuine nowhere-vanishing invariant generator in the actual global section type. -/
@[expose] def invariantSection (A B : R) : (line A B).sections :=
  unitSection (WeierstrassGluing318.scheme A B)

@[expose] def xIdentification (A B : R) :
    (Scheme.Modules.restrictFunctor (finiteInto A B 0)).obj (line A B) ≅
      differentialSheaf (R:=R) (S:=FiniteInvariantDifferential318.XChart A B) :=
  localIso (finiteInto A B 0) (xFrame A B)
@[expose] def finiteIdentification (A B : R) :
    (Scheme.Modules.restrictFunctor (finiteInto A B 1)).obj (line A B) ≅
      differentialSheaf (R:=R) (S:=DifferentialChartMaps318.FiniteChart A B) :=
  localIso (finiteInto A B 1) (finiteFrame A B)
@[expose] def infinityIdentification (A B : R) :
    (Scheme.Modules.restrictFunctor (infinityInto A B)).obj (line A B) ≅
      differentialSheaf (R:=R) (S:=DifferentialChartMaps318.InfinityChart A B) :=
  localIso (infinityInto A B) (infinityFrame A B)

/-- The actual global generator restricts to the literal -dy/J0 differential. -/
theorem x_generator (A B : R) :
    (moduleSpecΓFunctor.map (xIdentification A B).hom)
      (show Γ(WeierstrassGluing318.scheme A B,finiteInto A B 0 ''ᵁ ⊤) from
        (invariantSection A B).val (op (finiteInto A B 0 ''ᵁ ⊤)))=
    (tilde.isoTop (R:=CommRingCat.of (FiniteInvariantDifferential318.XChart A B))
      (ModuleCat.of _ (KaehlerDifferential R (FiniteInvariantDifferential318.XChart A B)))).hom
        (FiniteInvariantDifferential318.xForm A B) :=
  localIso_unit _ _ _ (x_normalized A B)

/-- It restricts to the literal dx/(2y) differential on the other finite chart. -/
theorem finite_generator (A B : R) :
    (moduleSpecΓFunctor.map (finiteIdentification A B).hom)
      (show Γ(WeierstrassGluing318.scheme A B,finiteInto A B 1 ''ᵁ ⊤) from
        (invariantSection A B).val (op (finiteInto A B 1 ''ᵁ ⊤)))=
    (tilde.isoTop (R:=CommRingCat.of (DifferentialChartMaps318.FiniteChart A B))
      (ModuleCat.of _ (KaehlerDifferential R (DifferentialChartMaps318.FiniteChart A B)))).hom
        (InvariantChartForms318.finite A B) :=
  localIso_unit _ _ _ (finite_normalized A B)

/-- At infinity the same generator gives -du/J, retaining the required sign. -/
theorem infinity_generator (A B : R) :
    (moduleSpecΓFunctor.map (infinityIdentification A B).hom)
      (show Γ(WeierstrassGluing318.scheme A B,infinityInto A B ''ᵁ ⊤) from
        (invariantSection A B).val (op (infinityInto A B ''ᵁ ⊤)))=
    (tilde.isoTop (R:=CommRingCat.of (DifferentialChartMaps318.InfinityChart A B))
      (ModuleCat.of _ (KaehlerDifferential R (DifferentialChartMaps318.InfinityChart A B)))).hom
        (InvariantChartForms318.infinity A B) :=
  localIso_unit _ _ _ (infinity_normalized A B)

/-- Every point is in an actual open on which this global line is identified with
its genuine relative Kaehler differential sheaf. -/
theorem identification_cover (A B : R) (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (p : WeierstrassGluing318.scheme A B) :
    (∃ i, ∃ q, finiteInto A B i q=p) ∨ (∃ q, infinityInto A B q=p) :=
  InvariantChartCover318.charts_cover A B hD p

@[expose] def literalLine (N : ℕ) : (WeierstrassGluing318.literalScheme N).Modules :=
  line (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
@[expose] def literalInvariantSection (N : ℕ) : (literalLine N).sections :=
  invariantSection (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

theorem literal_identification_cover (N : ℕ) (p : WeierstrassGluing318.literalScheme N) :
    (∃ i, ∃ q, finiteInto (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) i q=p) ∨
    (∃ q, infinityInto (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) q=p) :=
  identification_cover _ _ (OpenJAffineScheme318.discriminant_unit N) p
end GlobalInvariantLine318
