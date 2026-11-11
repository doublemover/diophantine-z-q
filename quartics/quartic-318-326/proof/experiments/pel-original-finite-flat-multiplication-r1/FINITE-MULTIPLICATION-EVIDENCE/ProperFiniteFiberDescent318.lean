module
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace ProperFiniteFiberDescent318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A proper map whose composite with a surjective map is finite is finite.
The actual full fibers are finite images of the composite fibers. -/
theorem finite {X Y Z:Scheme} (f:X⟶Y) (g:Y⟶Z)
    (hf:Function.Surjective f) [IsFinite (f≫g)] [IsProper g]:IsFinite g:=by
  haveI:LocallyQuasiFinite g:=locallyQuasiFinite_iff_finite_preimage_singleton.mpr (by
    intro z
    have he:g⁻¹' {z}=f '' ((f≫g)⁻¹' {z}):=by
      ext y
      constructor
      · intro hy
        obtain ⟨x,rfl⟩:=hf y
        exact ⟨x,hy,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        exact hx
    rw [he]
    exact ((f≫g).finite_preimage_singleton z).image f)
  exact IsFinite.of_isProper_of_locallyQuasiFinite g
end ProperFiniteFiberDescent318
