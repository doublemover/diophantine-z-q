module
public import SelectedLiteralTorsionKernel318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.GroupTheory.OrderOfElement
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318

namespace SelectedPrimitiveOpen318

variable (n m : ℕ)
variable [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]

/-- The kernel's étale zero is clopen. The external finite étale inputs are
on the actual pullback of the actual arbitrary-m multiplication morphism,
not on an unspecified finite algebra. -/
instance zeroClosed : IsClosedImmersion (zeroSection n m) := by
  haveI : IsClosedImmersion (zeroSection n m ≫ kernelProjection n m) := by
    rw [zeroSection_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (zeroSection n m) (kernelProjection n m)

instance zeroOpen : IsOpenImmersion (zeroSection n m) := by
  haveI : Etale (zeroSection n m ≫ kernelProjection n m) := by
    rw [zeroSection_projection]
    infer_instance
  haveI : Etale (zeroSection n m) := Etale.of_comp (zeroSection n m) (kernelProjection n m)
  exact IsOpenImmersion.of_flat_of_mono (zeroSection n m)

/-- The lower order tests use [d] inside the same full kernel, so we do not
need extra étaleness inputs for [d]. Index i stands for the order i+1. -/
@[expose] def lowerZero (i : Fin (m-1)) : Set (Kernel n m) :=
  mulInside n m (i.val+1) ⁻¹' Set.range (zeroSection n m)

theorem lowerZero_closed (i : Fin (m-1)) : IsClosed (lowerZero n m i) :=
  (zeroSection n m).isClosedEmbedding.isClosed_range.preimage
    (mulInside n m (i.val+1)).continuous

theorem lowerZero_open (i : Fin (m-1)) : IsOpen (lowerZero n m i) :=
  (zeroSection n m).isOpenEmbedding.isOpen_range.preimage
    (mulInside n m (i.val+1)).continuous

/-- The actual open primitive locus, obtained by excluding the genuine
lower order zero loci. It does not choose an arbitrary integer-coordinate
algebra or supply evaluation points by hand. -/
@[expose] def primitive : (Kernel n m).Opens :=
  ⟨(⋃ i : Fin (m-1), lowerZero n m i)ᶜ,
    (isClosed_iUnion_of_finite (lowerZero_closed n m)).isOpen_compl⟩

theorem primitive_closed : IsClosed ((primitive n m : (Kernel n m).Opens) : Set (Kernel n m)) :=
  (isOpen_iUnion (lowerZero_open n m)).isClosed_compl

abbrev PrimitiveScheme := (primitive n m).toScheme
abbrev inclusionOpen : PrimitiveScheme n m ⟶ Kernel n m := (primitive n m).ι
abbrev primitiveProjection : PrimitiveScheme n m ⟶ Base n :=
  inclusionOpen n m ≫ kernelProjection n m

instance primitiveInclusionClosed : IsClosedImmersion (inclusionOpen n m) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact primitive_closed n m

/-- Hence the primitive locus is itself a finite étale cover, not just an
open piece of a finite cover (which need not be finite). -/
theorem finite_etale : IsFinite (primitiveProjection n m) ∧
    Etale (primitiveProjection n m) := ⟨inferInstance,inferInstance⟩

/-- There is an actual coordinate algebra over the literal open-j base.
The scheme used to extract it is the primitive open above. -/
theorem coordinate_algebra :
    ∃ R : CommRingCat, ∃ f : CommRingCat.of (OpenJModel318.Base n) ⟶ R,
      ∃ i : PrimitiveScheme n m ≅ Spec R,
        i.hom ≫ Spec.map f = primitiveProjection n m ∧
          f.hom.Finite ∧ f.hom.Etale := by
  haveI : IsFinite (primitiveProjection n m) := (finite_etale n m).1
  haveI : Etale (primitiveProjection n m) := (finite_etale n m).2
  letI : IsAffine (PrimitiveScheme n m) := isAffine_of_isAffineHom (primitiveProjection n m)
  let i := (PrimitiveScheme n m).isoSpec
  obtain ⟨f,hf⟩ := Spec.map_surjective (i.inv ≫ primitiveProjection n m)
  have hf₁ : IsFinite (Spec.map f) := by rw [hf]; infer_instance
  have hf₂ : Etale (Spec.map f) := by rw [hf]; infer_instance
  refine ⟨_,f,i,?_,(IsFinite.SpecMap_iff f).mp hf₁,
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := f)).mp hf₂⟩
  rw [hf]
  simp

private theorem zero_iff_range {T : Scheme} [Subsingleton T]
    (p : T ⟶ Kernel n m) (x : T) :
    pointOf n m p = 0 ↔ p x ∈ Set.range (zeroSection n m) := by
  constructor
  · intro hp
    have h : p ≫ inclusion n m = (p ≫ kernelProjection n m) ≫ origin n :=
      congrArg Subtype.val hp
    have hfac : p = (p ≫ kernelProjection n m) ≫ zeroSection n m := by
      apply (cancel_mono (inclusion n m)).mp
      simpa only [Category.assoc,zeroSection_inclusion] using h
    rw [hfac,Scheme.Hom.comp_apply]
    exact ⟨_,rfl⟩
  · intro hx
    have hr : Set.range p ⊆ Set.range (zeroSection n m) := by
      rintro _ ⟨y,rfl⟩
      exact Subsingleton.elim x y ▸ hx
    let q := IsOpenImmersion.lift (zeroSection n m) p hr
    have hq : q ≫ zeroSection n m = p := IsOpenImmersion.lift_fac _ _ _
    have hbase : q = p ≫ kernelProjection n m := by
      have h := congrArg (fun f => f ≫ kernelProjection n m) hq
      simpa only [Category.assoc,zeroSection_projection,Category.comp_id] using h
    apply Subtype.ext
    change p ≫ inclusion n m = (p ≫ kernelProjection n m) ≫ origin n
    rw [← hbase,← hq,Category.assoc,zeroSection_inclusion]

private theorem pointOf_mulInside {T : Scheme} (p : T ⟶ Kernel n m) (k : ℕ) :
    (pointOf n m (p ≫ mulInside n m k)).val = (k • pointOf n m p).val := by
  rw [mul_value]
  change (p ≫ mulInside n m k) ≫ inclusion n m = (p ≫ inclusion n m) ≫ mulMap n k
  simp only [Category.assoc,mulInside_inclusion]

private theorem lowerZero_iff {T : Scheme} [Subsingleton T] (p : T ⟶ Kernel n m)
    (x : T) (i : Fin (m-1)) :
    p x ∈ lowerZero n m i ↔ (i.val+1) • pointOf n m p = 0 := by
  have h := zero_iff_range n m (p ≫ mulInside n m (i.val+1)) x
  change mulInside n m (i.val+1) (p x) ∈ Set.range (zeroSection n m) ↔ _
  simp only [Scheme.Hom.comp_apply] at h
  have hbase :
      (p ≫ mulInside n m (i.val+1)) ≫ kernelProjection n m = p ≫ kernelProjection n m := by
    rw [Category.assoc,mulInside_projection]
  have hzero :
      (0 : Points n ((p ≫ mulInside n m (i.val+1)) ≫ kernelProjection n m)).val =
        (0 : Points n (p ≫ kernelProjection n m)).val := by
    change ((p ≫ mulInside n m (i.val+1)) ≫ kernelProjection n m) ≫ origin n =
      (p ≫ kernelProjection n m) ≫ origin n
    exact congrArg (fun b : T ⟶ Base n => b ≫ origin n) hbase
  have hpoint := pointOf_mulInside n m p (i.val+1)
  rw [← h]
  constructor
  · intro hz
    apply Subtype.ext
    exact hpoint.symm.trans ((congrArg Subtype.val hz).trans hzero)
  · intro hz
    apply Subtype.ext
    exact hpoint.trans ((congrArg Subtype.val hz).trans hzero.symm)

/-- Genuine primitive means exact order m on field-valued points, not just
nonzero in the m-kernel. The same statement holds on any singleton test. -/
theorem primitive_iff_order {T : Scheme} [Subsingleton T] (p : T ⟶ Kernel n m)
    (x : T) (hm : 0 < m) :
    p x ∈ primitive n m ↔ addOrderOf (pointOf n m p) = m := by
  classical
  let a := pointOf n m p
  have hk : m • a = 0 := pointOf_killed n m p
  have hd : addOrderOf a ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
  have hn : 0 < addOrderOf a := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact (Nat.ne_of_gt hm) hd
  change p x ∉ ⋃ i : Fin (m-1), lowerZero n m i ↔ addOrderOf a = m
  constructor
  · intro hp
    by_contra hneq
    have hlt : addOrderOf a < m := lt_of_le_of_ne (Nat.le_of_dvd hm hd) hneq
    let i : Fin (m-1) := ⟨addOrderOf a - 1,by omega⟩
    have hi : i.val+1 = addOrderOf a := by
      change addOrderOf a - 1 + 1 = addOrderOf a
      omega
    apply hp
    refine mem_iUnion_of_mem i ((lowerZero_iff n m p x i).2 ?_)
    change (i.val+1) • a = 0
    rw [hi]
    exact addOrderOf_nsmul_eq_zero _
  · intro ho hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    have hz := (lowerZero_iff n m p x i).1 hi
    have hdiv₀ : addOrderOf a ∣ i.val+1 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    have hdiv : m ∣ i.val+1 :=
      Eq.mp (congrArg (fun o : ℕ => o ∣ i.val+1) ho) hdiv₀
    have hle := Nat.le_of_dvd (Nat.succ_pos _) hdiv
    have hlt := i.isLt
    omega

end SelectedPrimitiveOpen318
#print axioms SelectedPrimitiveOpen318.coordinate_algebra
#print axioms SelectedPrimitiveOpen318.primitive_iff_order
