module
public import InertiaLabels318
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace ProjectiveGalois318
set_option maxHeartbeats 0
variable {F E ι:Type*} [Field F] [Field E] [Algebra F E]

@[expose] def coordinateMap : (ι→F)→ₛₗ[algebraMap F E](ι→E) where
  toFun x i:=algebraMap F E (x i)
  map_add' x y:=by ext i;exact map_add _ _ _
  map_smul' c x:=by ext i;exact map_mul _ _ _

theorem coordinateMap_injective : Function.Injective (coordinateMap (F:=F) (E:=E) (ι:=ι)) := by
  intro x y h
  ext i
  exact (algebraMap F E).injective (congrFun h i)

@[expose] def automorphismMap (sigma:E≃ₐ[F]E) :
    (ι→E)→ₛₗ[sigma.toRingHom](ι→E) where
  toFun x i:=sigma (x i)
  map_add' x y:=by ext i;exact map_add _ _ _
  map_smul' c x:=by ext i;exact map_mul _ _ _

theorem automorphismMap_injective (sigma:E≃ₐ[F]E) :
    Function.Injective (automorphismMap (ι:=ι) sigma) := by
  intro x y h
  ext i
  exact sigma.injective (congrFun h i)

/-- Projective invariance gives a scalar multiple through the actual
Mathlib projective equivalence relation, not an assumed normalization. -/
theorem scalar_of_projective_fixed (x:ι→E) (hx:x≠0) (sigma:E≃ₐ[F]E)
    (h:Projectivization.map (automorphismMap sigma) (automorphismMap_injective sigma)
      (Projectivization.mk E x hx)=Projectivization.mk E x hx) :
    ∃c:Eˣ,∀i,sigma (x i)=(c:E)*x i := by
  rw [Projectivization.map_mk,Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c,hc⟩:=h
  refine ⟨c,?_⟩
  intro i
  have hi:=congrFun hc i
  exact hi.symm

/-- Normalize one nonzero coordinate and use the actual fixed-field theorem.
This proves descent rather than supplying rational coordinate ratios. -/
theorem normalized_coordinates [FiniteDimensional F E] [IsGalois F E]
    (x:ι→E) (hx:x≠0)
    (hfix:∀sigma:E≃ₐ[F]E,∃c:Eˣ,∀i,sigma (x i)=(c:E)*x i) :
    ∃(y:ι→F) (c:E), y≠0 ∧ c≠0 ∧ ∀i,algebraMap F E (y i)=c*x i := by
  classical
  obtain ⟨j,hj⟩:=Function.ne_iff.mp hx
  have hrat:∀i,∃a:F,algebraMap F E a=x i/x j := by
    intro i
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F:=F) (x i/x j)).mpr
    intro sigma
    obtain ⟨c,hc⟩:=hfix sigma
    rw [map_div₀ sigma,hc i,hc j]
    exact mul_div_mul_left _ _ c.ne_zero
  choose y hy using hrat
  have hy0:y≠0:=by
    intro hz
    have h:=hy j
    rw [hz,Pi.zero_apply,map_zero,div_self hj] at h
    exact zero_ne_one h
  refine ⟨y,(x j)⁻¹,hy0,inv_ne_zero hj,?_⟩
  intro i
  rw [hy,div_eq_mul_inv,mul_comm]

/-- A genuine projective point fixed by all automorphisms of a finite
Galois extension lies in the image of the actual projective base-change map. -/
theorem projective_descent [FiniteDimensional F E] [IsGalois F E]
    (P:Projectivization E (ι→E))
    (hfix:∀sigma:E≃ₐ[F]E,Projectivization.map (automorphismMap sigma)
      (automorphismMap_injective sigma) P=P) :
    ∃Q:Projectivization F (ι→F),
      Projectivization.map coordinateMap coordinateMap_injective Q=P := by
  let x:=P.rep
  have hx:x≠0:=Projectivization.rep_nonzero P
  have hscalar:∀sigma:E≃ₐ[F]E,∃c:Eˣ,∀i,sigma (x i)=(c:E)*x i:=by
    intro sigma
    apply scalar_of_projective_fixed x hx sigma
    simpa only [x,Projectivization.mk_rep] using hfix sigma
  obtain ⟨y,c,hy,hc,hcoord⟩:=normalized_coordinates x hx hscalar
  refine ⟨Projectivization.mk F y hy,?_⟩
  rw [Projectivization.map_mk]
  rw [←Projectivization.mk_rep P]
  apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
  refine ⟨c,?_⟩
  ext i
  exact (hcoord i).symm

/-- Source-specific branch descent: actual Galois permutations preserving the
five distinct inertia labels fix the projective points, which then descend
through the genuine projective base-change map. The actual curve embedding
and the Galois/inertia compatibility remain geometric inputs. -/
theorem five_labelled_points_descend [FiniteDimensional F E] [IsGalois F E]
    (P:Fin 5→Projectivization E (ι→E))
    (perm:(E≃ₐ[F]E)→Equiv.Perm (Fin 5))
    (hlabel:∀sigma i,InertiaLabels318.fiveLabels (perm sigma i)=
      InertiaLabels318.fiveLabels i)
    (hequiv:∀sigma i,Projectivization.map (automorphismMap sigma)
      (automorphismMap_injective sigma) (P i)=P (perm sigma i)) :
    ∃Q:Fin 5→Projectivization F (ι→F),∀i,
      Projectivization.map coordinateMap coordinateMap_injective (Q i)=P i := by
  have hp:∀i,∃Q:Projectivization F (ι→F),
      Projectivization.map coordinateMap coordinateMap_injective Q=P i:=by
    intro i
    apply projective_descent
    intro sigma
    rw [hequiv,InertiaLabels318.labelled_permutation_fixed (perm sigma) (hlabel sigma)]
    rfl
  choose Q hQ using hp
  exact ⟨Q,hQ⟩

end ProjectiveGalois318
