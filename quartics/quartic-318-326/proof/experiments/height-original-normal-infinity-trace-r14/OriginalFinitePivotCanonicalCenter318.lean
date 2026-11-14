module
public import FinitePivotGlobalCanonicalSections318
public import OriginalOddPlaceSmoothCenter318
public section
noncomputable section
namespace OriginalFinitePivotCanonicalCenter318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 FourRootPivot318
open FinitePivotCanonicalSource318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w) (i : Fin 4)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
local notation "d" => D.coefficients
local notation "C" => FinitePivotCanonicalSource318.Chart V D.pi (D.unit i) d a i
local notation "Q" => OddTwistDilatationCoordinates318.coefficient D.pi (D.unit i) (a i)
  (others V d i) (others V a i)
structure Center where
  coordinate : V
  otherRoots : Fin 3 → V
  root_equation : ∀ j,(otherRoots j)^2=Polynomial.eval coordinate (Q j)
  root_unit : ∀ j,IsUnit (otherRoots j)
  contact : algebraMap V (K c tau) (Polynomial.eval coordinate
    (OddTwistDilatationCoordinates318.contact D.pi (D.unit i) (a i)))=(tau:K c tau)
  original_pivot : algebraMap V (K c tau) (D.pi*coordinate)=D.normalizedRoots i
  original_other : ∀ j,algebraMap V (K c tau) (otherRoots j)=D.normalizedRoots (indices i j.succ)

variable (hi : D.exponent i=1)
include hi in
lemma pivot_coefficient : d i=(D.unit i:V)*D.pi := by simp [Data.coefficients,hi]

include hi in
/-- The actual original signed point produces the required smooth chart
center; other twist parities and all unit roots are derived from contact
separation, rather than inserted as model hypotheses. -/
theorem exists_center (ht : w (tau:K c tau)≤1)
    (hsep : ∀ j : Fin 3,IsUnit (a i-a (indices i j.succ))) :
    Nonempty (Center c tau w D i) := by
  have he := OriginalOddPlaceSmoothCenter318.other_exponents_zero c tau w D i ht hi hsep
  obtain ⟨T,r,hT,hr,hrel⟩ := OriginalAllPlaceRootBounds318.finite_coordinates c tau w D ht
  have hy : (r i)^2=(D.unit i:V)*D.pi*(T-a i) := by
    simpa [Data.coefficients,hi] using hrel i
  obtain ⟨Z,hZ,hvalue,hroots⟩ := OddTwistDilatationCoordinates318.exists_chart_coordinates
    D.pi (D.unit i) (a i) (others V d i) (others V a i) T (r i)
    (fun j => r (indices i j.succ)) hy (fun j => hrel (indices i j.succ)) D.irreducible
  have htexp : T=a i+D.pi*(↑(D.unit i)⁻¹:V)*Z^2 := by
    simpa only [OddTwistDilatationCoordinates318.contact,eval_add,eval_C,eval_mul,eval_pow,eval_X]
      using hvalue.symm
  have hunits (j : Fin 3) : IsUnit (r (indices i j.succ)) := by
    apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
    rw [hrel (indices i j.succ),htexp]
    have hd : d (indices i j.succ)=(D.unit (indices i j.succ):V) := by
      simp [Data.coefficients,he j]
    rw [hd]
    exact (D.unit (indices i j.succ)).isUnit.mul
      (OddTwistDilatationCenter318.other_contact_unit V D.pi D.irreducible (D.unit i) (a i)
        (a (indices i j.succ)) Z (hsep j))
  refine ⟨⟨Z,fun j => r (indices i j.succ),hroots,hunits,?_,?_,?_⟩⟩
  · rw [hvalue,hT]
  · rw [←hZ,hr]
  · exact fun j => hr (indices i j.succ)

variable (P : Center c tau w D i)
@[expose] def point : C →+* V :=
  OddTwistDilatationEtale318.point V D.pi (D.unit i) (a i) (others V d i) (others V a i)
    P.coordinate P.otherRoots P.root_equation P.root_unit
@[expose] def modelPoint : DVRNormalizedFiniteOrder318.Order V d a →+* V :=
  (point c tau w D i P).comp (sourceMap V D.pi (D.unit i) d a i (pivot_coefficient c tau w D i hi))
lemma point_scalar (r : V) : point c tau w D i P (algebraMap V C r)=r :=
  OddTwistDilatationEtale318.point_scalar _ _ _ _ _ _ _ _ _ _ _
lemma point_scalarMap : (point c tau w D i P).comp (scalarMap V D.pi (D.unit i) d a i)=
    Polynomial.evalRingHom (Polynomial.eval P.coordinate
      (OddTwistDilatationCoordinates318.contact D.pi (D.unit i) (a i))) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,scalarMap,OddTwistDilatationSourceMap318.originalScalar,
      coe_eval₂RingHom,eval₂_C,point_scalar,Polynomial.evalRingHom_apply,eval_C]
  · simp only [RingHom.comp_apply,scalarMap,OddTwistDilatationSourceMap318.originalScalar,
      coe_eval₂RingHom,eval₂_X,Polynomial.evalRingHom_apply,eval_X]
    exact OddTwistDilatationEtale318.point_contact _ _ _ _ _ _ _ _ _ _
lemma modelPoint_polynomial (p : V[X]) : modelPoint c tau w D i hi P
    (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V d a) p)=Polynomial.eval
      (Polynomial.eval P.coordinate (OddTwistDilatationCoordinates318.contact D.pi (D.unit i) (a i))) p := by
  change point c tau w D i P (sourceMap _ _ _ _ _ _ _ _) = _
  rw [sourceMap_polynomial]
  exact RingHom.congr_fun (point_scalarMap c tau w D i P) p

lemma modelPoint_roots (k : Fin 4) : algebraMap V (K c tau) (modelPoint c tau w D i hi P
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) k))=
      D.normalizedRoots k := by
  obtain ⟨j,rfl⟩ := (indexEquiv i).surjective k
  change algebraMap V (K c tau) (point c tau w D i P (sourceMap _ _ _ _ _ _ _ _))=_
  rw [sourceMap_root,originalRoot_index]
  refine Fin.cases ?_ (fun j => ?_) j
  · change algebraMap V (K c tau) (point c tau w D i P
      (algebraMap V C D.pi*OddTwistDilatationEtale318.coordinate V D.pi (D.unit i) (a i)
        (others V d i) (others V a i)))=D.normalizedRoots (indices i 0)
    rw [map_mul,point_scalar,indices_zero]
    change algebraMap V (K c tau) (D.pi*OddTwistDilatationEtale318.point _ _ _ _ _ _ _ _ _ _ _)=_
    rw [OddTwistDilatationEtale318.point_coordinate]
    exact P.original_pivot
  · change algebraMap V (K c tau) (OddTwistDilatationEtale318.point _ _ _ _ _ _ _ _ _ _
      (ThreeRootCoordinates318.generator _ j))=_
    rw [OddTwistDilatationEtale318.point_signed_root]
    exact P.original_other j

/-- The full original generic scheme point is recovered, with root
indices restored before comparing the actual original proper model. -/
theorem generic_extension : Spec.map (CommRingCat.ofHom (algebraMap V (K c tau))) ≫
    (Spec.map (CommRingCat.ofHom (modelPoint c tau w D i hi P)) ≫
      NormalizedWholeOpenMaps318.finiteChart V d a)=D.genericPoint :=
  NormalizedGenericPointExtension318.finite_extension V (K c tau) d a (tau:K c tau)
    D.normalizedRoots D.root_equation
    (Polynomial.eval P.coordinate (OddTwistDilatationCoordinates318.contact D.pi (D.unit i) (a i)))
    P.contact (modelPoint c tau w D i hi P) (modelPoint_polynomial c tau w D i hi P)
    (modelPoint_roots c tau w D i hi P)
end OriginalFinitePivotCanonicalCenter318
