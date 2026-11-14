module
public import OriginalModuleScalarPullback318
public import OriginalLineAutomorphismEquiv318
public import LineSheafPullback318
public section
noncomputable section
namespace OriginalLineAutPullback318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open OriginalLineAutomorphismScalar318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (L : Line Y)

lemma original_hom_eq_scalar (f : L.object ≅ L.object) :
    f.hom = ModuleScalar318.map L.object (scalar L f).val := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  exact scalar_action L f W s

/-- The actual automorphism scalar pulls back through the actual original
scheme appTop map, for the actual original line pullback. -/
lemma scalar_pullback (f : L.object ≅ L.object) :
    scalar (LineSheafPullback318.line p L) ((Scheme.Modules.pullback p).mapIso f) =
      Units.map p.appTop.hom.toMonoidHom (scalar L f) := by
  apply scalar_unique
  intro W s
  have he : ((Scheme.Modules.pullback p).mapIso f).hom =
      ModuleScalar318.map ((Scheme.Modules.pullback p).obj L.object)
        (p.appTop (scalar L f).val) := by
    rw [Functor.mapIso_hom, original_hom_eq_scalar L f,
      OriginalModuleScalarPullback318.pullback_scalar]
  rw [he]
  rfl

/-- Injectivity of the actual global section map makes original line
automorphism pullback faithful. Flatness is not required for this assertion. -/
lemma pullbackAut_injective (hp : Function.Injective p.appTop) :
    Function.Injective ((Scheme.Modules.pullback p).mapAut L.object) := by
  intro f g h
  apply (OriginalLineAutomorphismEquiv318.equivalence L).injective
  apply Units.ext
  apply hp
  have hs := congrArg
    (fun k : Aut (LineSheafPullback318.line p L).object =>
      scalar (LineSheafPullback318.line p L) k.asIso) h
  change scalar (LineSheafPullback318.line p L) ((Scheme.Modules.pullback p).mapIso f.asIso) =
    scalar (LineSheafPullback318.line p L) ((Scheme.Modules.pullback p).mapIso g.asIso) at hs
  rw [scalar_pullback, scalar_pullback] at hs
  exact congrArg Units.val hs

/-- An actual rigidification kills original line automorphisms whenever
the original global section map is injective. -/
lemma rigidified_aut_eq_one (hp : Function.Injective p.appTop) (f : Aut L.object)
    (r : (LineSheafPullback318.line p L).object ≅ SheafOfModules.unit X.ringCatSheaf)
    (hr : ((Scheme.Modules.pullback p).mapAut L.object f).asIso.hom ≫ r.hom = r.hom) :
    f = 1 := by
  apply pullbackAut_injective p L hp
  rw [map_one]
  apply Aut.ext
  apply Iso.ext
  apply (cancel_mono r.hom).mp
  simpa using hr
end OriginalLineAutPullback318
