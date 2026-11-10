module
public import AffineBaseFppfDescent318
public section
noncomputable section
namespace AffineBaseFppfFamilyDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open OriginalSchemeDescentData318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y : Scheme.{u}} [IsAffine Y] (C : Scheme.Cover.{u} Scheme.fppfPrecoverage Y)
abbrev total : Scheme.{u} := ∐ C.X
abbrev covering : total C ⟶ Y := Sigma.desc C.f

/-- Every genuine small fppf covering family over the affine base,
including infinite families and non-affine components, gives effective
original descent on its full coproduct covering scheme. -/
@[expose] def equivalence : Line Y ≌ Datum (covering C) := by
  let C' : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Y := C
  letI : Flat (covering C) := (C'.sigma.map_prop default).1
  letI : LocallyOfFinitePresentation (covering C) := (C'.sigma.map_prop default).2
  letI : Surjective (covering C) := inferInstanceAs (Surjective (Sigma.desc C.f))
  exact AffineBaseFppfDescent318.equivalence (covering C)

/-- On every original family component the forward map is the original
component pullback, through the specified actual coproduct path. -/
lemma component_map {L K : Line Y} (h : L ⟶ K) (i : C.I₀) :
    (Scheme.Modules.pullback (Sigma.ι C.X i)).map (((equivalence C).functor.map h).sheafHom) ≫
      (PullbackPathComposition318.iso (Sigma.ι C.X i) (covering C) (C.f i)
        (Sigma.ι_desc C.f i)).hom.app K.object =
    (PullbackPathComposition318.iso (Sigma.ι C.X i) (covering C) (C.f i)
        (Sigma.ι_desc C.f i)).hom.app L.object ≫ (Scheme.Modules.pullback (C.f i)).map h :=
  (PullbackPathComposition318.iso (Sigma.ι C.X i) (covering C) (C.f i)
    (Sigma.ι_desc C.f i)).hom.naturality h
end AffineBaseFppfFamilyDescent318
