module
public import OpenQuotientSameFibers318
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
namespace OpenSquaredChart318
open OpenQuotientSameFibers318 Topology
set_option maxHeartbeats 1600000
variable {X : Type*} [TopologicalSpace X]

theorem restricted_chart_open (e : OpenPartialHomeomorph X ℂ) (U : Set X)
    (hU : IsOpen U) (hsub : U⊆e.source) : IsOpenMap (fun x : U => e x) := by
  intro W hW
  have he : (fun x : U => e x) '' W=e '' (Subtype.val '' W) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
      exact ⟨y,hy,rfl⟩
  rw [he]
  apply e.isOpen_image_of_subset_source (hU.isOpenMap_subtype_val W hW)
  rintro x ⟨y,hy,rfl⟩
  exact hsub y.property

theorem restricted_square_open (e : OpenPartialHomeomorph X ℂ) (U : Set X)
    (hU : IsOpen U) (hsub : U⊆e.source) : IsOpenMap (fun x : U => e x^2) :=
  (Complex.isOpenQuotientMap_pow 2).isOpenMap.comp (restricted_chart_open e U hU hsub)

theorem square_image_open (e : OpenPartialHomeomorph X ℂ) (U : Set X)
    (hU : IsOpen U) (hsub : U⊆e.source) : IsOpen ((fun x => e x^2) '' U) := by
  have he : (fun x => e x^2) '' U=(fun z : ℂ => z^2) '' (e '' U) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx,rfl⟩
  rw [he]
  exact (Complex.isOpenQuotientMap_pow 2).isOpenMap _ (e.isOpen_image_of_subset_source hU hsub)

theorem square_image_quotient (e : OpenPartialHomeomorph X ℂ) (U : Set X)
    (hU : IsOpen U) (hsub : U⊆e.source) :
    IsOpenQuotientMap (imageMap (fun x => e x^2) U) :=
  imageMap_openQuotient _ U ((e.continuousOn.mono hsub).pow 2) (restricted_square_open e U hU hsub)
end OpenSquaredChart318
