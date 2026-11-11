module
public import AlgHomDifferential318
public import CanonicalRestrictionComparison318
public section
noncomputable section
namespace DifferentialFunctor318
open KaehlerDifferential
set_option maxHeartbeats 200000
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- Actual universal-differential transport is functorial for arbitrary algebra maps. -/
theorem map_comp_apply (f : S →ₐ[R] T) (g : T →ₐ[R] U) (ω : KaehlerDifferential R S) :
    AlgHomDifferential318.map (g.comp f) ω=
      AlgHomDifferential318.map g (AlgHomDifferential318.map f ω) := by
  have hw : ω ∈ Submodule.span S (Set.range (D R S)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨s,rfl⟩
    simp only [AlgHomDifferential318.map_D,AlgHom.comp_apply]
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add,ihx,ihy]
  · intro s x hx ih
    simp only [AlgHomDifferential318.map_smul,AlgHom.comp_apply,ih]

theorem map_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    AlgHomDifferential318.map (g.comp f)=
      (AlgHomDifferential318.map g).comp (AlgHomDifferential318.map f) := by
  apply LinearMap.ext
  intro ω
  exact map_comp_apply f g ω

theorem map_id_apply (ω : KaehlerDifferential R S) :
    AlgHomDifferential318.map (AlgHom.id R S) ω=ω := by
  have hw : ω ∈ Submodule.span S (Set.range (D R S)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨s,rfl⟩
    simp only [AlgHomDifferential318.map_D,AlgHom.id_apply]
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add,ihx,ihy]
  · intro s x hx ih
    simp only [AlgHomDifferential318.map_smul,AlgHom.id_apply,ih]

end DifferentialFunctor318
