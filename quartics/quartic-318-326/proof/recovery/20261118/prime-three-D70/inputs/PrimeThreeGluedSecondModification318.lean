module
public import PrimeThreeActualGluingTriangle318
public import ThreePieceOpenGlueMorphism318
public section
noncomputable section
namespace PrimeThreeGluedSecondModification318
open AlgebraicGeometry CategoryTheory
open PrimeThreeActualGluingTriangle318

/-- Every premise of the generic triangle is discharged by the actual
arithmetic/native overlap maps and proved intersections. -/
@[expose] def actualTriangle : ThreePieceOpenGlue318.Triangle where
  U := piece
  V i j _ := pair i j
  f := inclusion
  f_open := inclusion_openImmersion
  t := transition
  t_inv := transition_inverse
  T := Triple
  q := tripleMap
  q_transition := triple_transition
  triple := ordered_triple_pullback

/-- A single native glued scheme replacing first-U by its relative second
Rees modification and retaining the actual first V/W pieces unchanged.
This is not yet identified with a global ideal-sheaf blowup or proved regular. -/
abbrev gluedSecondModification : Scheme := ThreePieceOpenGlue318.glued actualTriangle

@[expose] def chartInclusion (i : Fin 3) : piece i ⟶ gluedSecondModification :=
  ThreePieceOpenGlue318.inclusion actualTriangle i

instance chartInclusion_openImmersion (i : Fin 3) : IsOpenImmersion (chartInclusion i) := by
  dsimp only [chartInclusion]
  infer_instance

/-- The actual piece morphisms descend to the whole first-blowup scheme. -/
@[expose] def toFirstBlowup : gluedSecondModification ⟶
    OriginalPrimeThreeNativeReesProj318.actualReesProj :=
  ThreePieceOpenGlueMorphism318.desc actualTriangle pieceToFirst pieceToFirst_compatible

@[reassoc] theorem chartInclusion_toFirstBlowup (i : Fin 3) :
    chartInclusion i ≫ toFirstBlowup = pieceToFirst i :=
  ThreePieceOpenGlueMorphism318.inclusion_desc actualTriangle pieceToFirst pieceToFirst_compatible i

/-- The displayed actual pieces cover the constructed global scheme. -/
theorem actual_pieces_cover (x : gluedSecondModification) :
    ∃ (i : Fin 3) (y : piece i), chartInclusion i y = x :=
  ThreePieceOpenGlueMorphism318.inclusions_jointly_surjective actualTriangle x

end PrimeThreeGluedSecondModification318
