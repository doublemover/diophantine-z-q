module
public import FinitePlacePrincipalImage318
public import InducedLattice318
public section
noncomputable section
namespace KSImageFrameNorms318
open NumberField SectionHeight318 FinitePlacePrincipalLattice318 FinitePlacePrincipalImage318
set_option maxHeartbeats 900000
variable {K : Type*} [Field K] [NumberField K]

/-- FrameNorms equality needs local equality, not merely equality of degrees. -/
theorem frame_ext (F H : FrameNorms K) (ha : F.arch=H.arch)
    (hf : F.finiteNorm=H.finiteNorm) : F=H := by
  cases F
  cases H
  cases ha
  cases hf
  rfl

/-- Actual image/product lattice identities imply the exact adelic KS
identity. H is a specified Hodge metric: it is never manufactured from F
by taking square roots. All finite places, including those dividing k,
and every infinite place are required. -/
theorem induced_eq_square (F H : FrameNorms K) (k : K) (hk : k≠0)
    (α β : FinitePlace K → K) (hα : ∀ v, α v≠0) (hβ : ∀ v, β v≠0)
    (hF : ∀ v, F.finiteNorm v=(v (α v))⁻¹)
    (hH : ∀ v, H.finiteNorm v=(v (β v))⁻¹)
    (himage : ∀ v, (lattice v (α v)).map (scalarMap v k)=productLattice v (β v) (β v))
    (harch : ∀ w, F.arch w=(H.arch w)^2) :
    InducedLattice318.induced F k hk=InducedLattice318.square H := by
  apply frame_ext
  · funext w
    exact harch w
  · funext v
    change F.finiteNorm v/v k=(H.finiteNorm v)^2
    rw [hF v,hH v]
    exact norm_of_image_square v k (α v) (β v) hk (hα v) (hβ v) (himage v)

/-- The literal 210 correction is derived only after the all-place
embedded-lattice and archimedean identifications. -/
theorem degree_210 (F H : FrameNorms K)
    (α β : FinitePlace K → K) (hα : ∀ v, α v≠0) (hβ : ∀ v, β v≠0)
    (hF : ∀ v, F.finiteNorm v=(v (α v))⁻¹)
    (hH : ∀ v, H.finiteNorm v=(v (β v))⁻¹)
    (himage : ∀ v, (lattice v (α v)).map (scalarMap v (210:K))=productLattice v (β v) (β v))
    (harch : ∀ w, F.arch w=(H.arch w)^2) :
    F.normalizedDegree=2*H.normalizedDegree+Real.log 210 :=
  InducedLattice318.ks_degree F H
    (induced_eq_square F H 210 (by norm_num) α β hα hβ hF hH himage harch)
end KSImageFrameNorms318
