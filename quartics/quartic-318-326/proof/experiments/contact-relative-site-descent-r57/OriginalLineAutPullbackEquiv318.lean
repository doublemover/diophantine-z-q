module
public import OriginalLineAutPullback318
public section
noncomputable section
namespace OriginalLineAutPullbackEquiv318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalLineAutomorphismScalar318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (L : Line Y)

/-- Bijectivity of the actual global-section map is exactly sufficient to
lift every automorphism of the actual pulled-back original line. -/
lemma pullbackAut_bijective (hp : Function.Bijective p.appTop) :
    Function.Bijective ((Scheme.Modules.pullback p).mapAut L.object) := by
  refine ⟨OriginalLineAutPullback318.pullbackAut_injective p L hp.injective, ?_⟩
  intro f
  let e : Γ(Y, ⊤) ≃+* Γ(X, ⊤) := RingEquiv.ofBijective p.appTop.hom hp
  let a := (Units.mapEquiv e.toMulEquiv).symm (scalar (LineSheafPullback318.line p L) f.asIso)
  let g := (OriginalLineAutomorphismEquiv318.equivalence L).symm a
  refine ⟨g, ?_⟩
  apply (OriginalLineAutomorphismEquiv318.equivalence (LineSheafPullback318.line p L)).injective
  change scalar (LineSheafPullback318.line p L) ((Scheme.Modules.pullback p).mapIso g.asIso) = _
  rw [OriginalLineAutPullback318.scalar_pullback]
  change Units.map p.appTop.hom.toMonoidHom
    ((OriginalLineAutomorphismEquiv318.equivalence L)
      ((OriginalLineAutomorphismEquiv318.equivalence L).symm a)) = _
  rw [MulEquiv.apply_symm_apply]
  exact (Units.mapEquiv e.toMulEquiv).apply_symm_apply _

/-- Faithfulness also detects actual isomorphisms between different lines,
not only endomorphisms of a single line. -/
lemma pullbackIso_injective (hp : Function.Injective p.appTop) (M : Line Y) :
    Function.Injective (fun f : L.object ≅ M.object => (Scheme.Modules.pullback p).mapIso f) := by
  intro f g h
  change (Scheme.Modules.pullback p).mapIso f = (Scheme.Modules.pullback p).mapIso g at h
  have ha : ((Scheme.Modules.pullback p).mapAut L.object) (Aut.of (f ≪≫ g.symm)) = 1 := by
    apply Aut.ext
    apply Iso.ext
    change (Scheme.Modules.pullback p).map (f.hom ≫ g.inv) = 𝟙 _
    rw [Functor.map_comp]
    change ((Scheme.Modules.pullback p).mapIso f).hom ≫
      ((Scheme.Modules.pullback p).mapIso g).inv = 𝟙 _
    rw [h]
    exact Iso.hom_inv_id _
  have hi : Aut.of (f ≪≫ g.symm) = 1 :=
    OriginalLineAutPullback318.pullbackAut_injective p L hp (by simpa using ha)
  have hh := congrArg (fun a : Aut L.object => a.asIso.hom) hi
  change f.hom ≫ g.inv = 𝟙 _ at hh
  apply Iso.ext
  apply (cancel_mono g.inv).mp
  simpa using hh
end OriginalLineAutPullbackEquiv318
