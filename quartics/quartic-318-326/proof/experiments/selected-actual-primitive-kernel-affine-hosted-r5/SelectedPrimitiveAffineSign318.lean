module
public import SelectedPrimitiveOpen318
public import NegationPoints318
public import CompletedFieldPoints318
public import Mathlib.AlgebraicGeometry.ResidueField
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318

namespace SelectedPrimitiveAffineSign318

abbrev R (n : ℕ) := OpenJModel318.Base n
abbrev A (n : ℕ) := OpenJAffineScheme318.A n
abbrev B (n : ℕ) := OpenJAffineScheme318.B n
abbrev D (n : ℕ) := ShortAffineJacobian318.Ring (A n) (B n)
abbrev X (n : ℕ) := ShortAffineJacobian318.x (A n) (B n)
abbrev Y (n : ℕ) := ShortAffineJacobian318.y (A n) (B n)
abbrev sign (n : ℕ) := ChartNegation318.affineNeg (A n) (B n)
abbrev affine (n : ℕ) := ShortAffineScheme318.scheme (A n) (B n)
abbrev affineStructure (n : ℕ) := ShortAffineScheme318.structureMap (A n) (B n)
abbrev chart (n : ℕ) := WeierstrassGluing318.finiteChart (A n) (B n)

variable (n m : ℕ)
variable [IsFinite (kernelProjection n m)] [Etale (kernelProjection n m)]

abbrev intoCurve : PrimitiveScheme n m ⟶ Curve n :=
  inclusionOpen n m ≫ inclusion n m

private theorem primitive_ne_zero {T : Scheme} [Subsingleton T]
    (p : T ⟶ PrimitiveScheme n m) (t : T) (hm : 1 < m) :
    pointOf n m (p ≫ inclusionOpen n m) ≠ 0 := by
  have hp : (p ≫ inclusionOpen n m) t ∈ primitive n m := by
    rw [Scheme.Hom.comp_apply]
    have h : (primitive n m).ι (p t) ∈ Set.range (primitive n m).ι := ⟨p t,rfl⟩
    simpa only [Scheme.Opens.range_ι] using h
  have ho := (primitive_iff_order n m _ _ (by omega)).1 hp
  intro hz
  rw [hz,addOrderOf_zero] at ho
  omega

/-- The primitive scheme with order >1 lies in the genuine short affine chart.
Residue-field maps are used only to recognize the open image, not to assert
an equality of Scheme maps. -/
theorem intoCurve_range (hm : 1 < m) :
    Set.range (intoCurve n m) ⊆ Set.range (chart n) := by
  rintro _ ⟨s,rfl⟩
  let T := PrimitiveScheme n m
  let K : Type _ := T.residueField s
  let p : Spec (CommRingCat.of K) ⟶ T := T.fromSpecResidueField s
  obtain ⟨b,hb⟩ := Spec.map_surjective ((p ≫ inclusionOpen n m) ≫ kernelProjection n m)
  letI : Algebra (R n) K := b.hom.toAlgebra
  have hring : CommRingCat.ofHom (algebraMap (R n) K) = b := by
    apply CommRingCat.hom_ext
    rfl
  have hb' : Spec.map (CommRingCat.ofHom (algebraMap (R n) K)) =
      (p ≫ inclusionOpen n m) ≫ kernelProjection n m := by rw [hring]; exact hb
  let f : CompletedFieldPoints318.SchemePoints (K := K) (A n) (B n) :=
    ⟨(p ≫ inclusionOpen n m) ≫ inclusion n m, by
      simpa only [Category.assoc,inclusion_over] using hb'.symm⟩
  rcases CompletedFieldPoints318.finite_or_infinity (A n) (B n) f with ⟨g,hg⟩ | hg
  · have hh : g.val ≫ chart n = (p ≫ inclusionOpen n m) ≫ inclusion n m :=
      congrArg Subtype.val hg
    have hs : p (default : Spec (CommRingCat.of K)) = s :=
      Scheme.fromSpecResidueField_apply (X := T) s default
    have hx := congrArg (fun q : Spec (CommRingCat.of K) ⟶ Curve n => q default) hh
    refine ⟨g.val default,?_⟩
    change chart n (g.val default) = inclusion n m (inclusionOpen n m s)
    simpa only [Scheme.Hom.comp_apply,hs] using hx
  · exfalso
    apply primitive_ne_zero n m p default hm
    apply Subtype.ext
    have hh : (p ≫ inclusionOpen n m) ≫ inclusion n m =
        Spec.map (CommRingCat.ofHom (algebraMap (R n) K)) ≫ origin n :=
      congrArg Subtype.val hg
    change (p ≫ inclusionOpen n m) ≫ inclusion n m =
      ((p ≫ inclusionOpen n m) ≫ kernelProjection n m) ≫ origin n
    exact hh.trans (congrArg (fun q : Spec (CommRingCat.of K) ⟶ Base n => q ≫ origin n) hb')

/-- The actual factor through the finite affine chart, with no chosen
evaluation point in its definition. -/
@[expose] def intoAffine (hm : 1 < m) : PrimitiveScheme n m ⟶ affine n :=
  IsOpenImmersion.lift (chart n) (intoCurve n m) (intoCurve_range n m hm)

@[reassoc] theorem intoAffine_chart (hm : 1 < m) :
    intoAffine n m hm ≫ chart n = intoCurve n m :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem intoAffine_structure (hm : 1 < m) :
    intoAffine n m hm ≫ affineStructure n = primitiveProjection n m := by
  have h : chart n ≫ projection n = affineStructure n :=
    WeierstrassGluing318.finiteChart_structure (A n) (B n)
  calc
    _ = intoAffine n m hm ≫ (chart n ≫ projection n) :=
      congrArg (fun q : affine n ⟶ Base n => intoAffine n m hm ≫ q) h.symm
    _ = (intoAffine n m hm ≫ chart n) ≫ projection n := (Category.assoc _ _ _).symm
    _ = intoCurve n m ≫ projection n :=
      congrArg (fun q : PrimitiveScheme n m ⟶ Curve n => q ≫ projection n)
        (intoAffine_chart n m hm)
    _ = _ := by
      change (inclusionOpen n m ≫ inclusion n m) ≫ projection n =
        inclusionOpen n m ≫ kernelProjection n m
      simp only [Category.assoc,inclusion_over]

instance closed_intoAffine (hm : 1 < m) : IsClosedImmersion (intoAffine n m hm) := by
  haveI : IsClosedImmersion (intoAffine n m hm ≫ chart n) := by
    rw [intoAffine_chart]
    infer_instance
  exact IsClosedImmersion.of_comp (intoAffine n m hm) (chart n)

/-- Actual primitive short-model coordinate ring, presented as a quotient of
the literal two-coordinate equation ring. The same isomorphism identifies
its structural map, so x is in the same finite étale algebra, not a model ring. -/
theorem affine_quotient (hm : 1 < m) :
    ∃ I : Ideal (D n), ∃ e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)),
      intoAffine n m hm =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection n m = e.hom ≫ Spec.algebraMap (R n) (D n ⧸ I) ∧
      Module.Finite (R n) (D n ⧸ I) ∧ Algebra.Etale (R n) (D n ⧸ I) := by
  obtain ⟨I,e,he⟩ := IsClosedImmersion.Spec_iff.mp (closed_intoAffine n m hm)
  let j : Spec (CommRingCat.of (D n ⧸ I)) ⟶ affine n :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have he₀ : intoAffine n m hm = e.hom ≫ j := he
  have hj : j ≫ affineStructure n = Spec.algebraMap (R n) (D n ⧸ I) := by
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.algebraMap (R n) (D n) = _
    rw [← Spec.map_comp]
    rfl
  have hb : primitiveProjection n m = e.hom ≫ Spec.algebraMap (R n) (D n ⧸ I) := by
    calc
      _ = intoAffine n m hm ≫ affineStructure n := (intoAffine_structure n m hm).symm
      _ = (e.hom ≫ j) ≫ affineStructure n :=
        congrArg (fun f : PrimitiveScheme n m ⟶ affine n => f ≫ affineStructure n) he₀
      _ = e.hom ≫ (j ≫ affineStructure n) := Category.assoc _ _ _
      _ = _ := congrArg (fun f : affine n ⟶ Base n => e.hom ≫ f) hj
  have hb' : Spec.algebraMap (R n) (D n ⧸ I) = e.inv ≫ primitiveProjection n m := by
    rw [hb,← Category.assoc,e.inv_hom_id,Category.id_comp]
  haveI : IsFinite (primitiveProjection n m) := (finite_etale n m).1
  haveI : Etale (primitiveProjection n m) := (finite_etale n m).2
  have hf : IsFinite (Spec.algebraMap (R n) (D n ⧸ I)) := by rw [hb']; infer_instance
  have ht : Etale (Spec.algebraMap (R n) (D n ⧸ I)) := by rw [hb']; infer_instance
  refine ⟨I,e,he,hb,?_,?_⟩
  · exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  · exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap (R n) (D n ⧸ I)))).mp ht)

abbrev curveNeg : Curve n ⟶ Curve n := GluedNegation318.negation (A n) (B n)

private theorem neg_mul_commute (k : ℕ) :
    curveNeg n ≫ mulMap n k = mulMap n k ≫ curveNeg n := by
  have h := mul_value n k (projection n) (-identityPoint n)
  rw [neg_nsmul] at h
  change mulMap n k ≫ curveNeg n = ((𝟙 (Curve n)) ≫ curveNeg n) ≫ mulMap n k at h
  simpa only [Category.id_comp] using h.symm

/-- Restrict the actual global negation to the same arbitrary-m kernel. -/
@[expose] def kernelNeg : Kernel n m ⟶ Kernel n m :=
  pullback.lift (inclusion n m ≫ curveNeg n) (kernelProjection n m) (by
    rw [Category.assoc,neg_mul_commute n m,← Category.assoc,kernel_equation,Category.assoc,
      GluedNegation318.infinity_fixed])

@[reassoc] theorem kernelNeg_inclusion :
    kernelNeg n m ≫ inclusion n m = inclusion n m ≫ curveNeg n := by simp [kernelNeg]

@[reassoc] theorem kernelNeg_projection :
    kernelNeg n m ≫ kernelProjection n m = kernelProjection n m := by simp [kernelNeg]

@[reassoc] theorem kernelNeg_twice :
    kernelNeg n m ≫ kernelNeg n m = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc,kernelNeg_inclusion,kernelNeg_inclusion_assoc,
      GluedNegation318.negation_twice,Category.comp_id,Category.id_comp]
  · simp only [Category.assoc,kernelNeg_projection,Category.id_comp]

@[reassoc] theorem zero_kernelNeg :
    zeroSection n m ≫ kernelNeg n m = zeroSection n m := by
  apply pullback.hom_ext
  · simp only [Category.assoc,kernelNeg_inclusion,zeroSection_inclusion_assoc,
      zeroSection_inclusion,GluedNegation318.infinity_fixed]
  · simp only [Category.assoc,kernelNeg_projection]

theorem lower_kernelNeg_commute (k : ℕ) :
    kernelNeg n m ≫ mulInside n m k = mulInside n m k ≫ kernelNeg n m := by
  apply pullback.hom_ext
  · simp only [Category.assoc,kernelNeg_inclusion,mulInside_inclusion,
      kernelNeg_inclusion_assoc,mulInside_inclusion_assoc,neg_mul_commute n k]
  · simp only [Category.assoc,kernelNeg_projection,mulInside_projection]

private theorem neg_primitive_range :
    Set.range (inclusionOpen n m ≫ kernelNeg n m) ⊆ Set.range (inclusionOpen n m) := by
  rintro _ ⟨t,rfl⟩
  rw [Scheme.Hom.comp_apply,Scheme.Opens.range_ι]
  have ht : inclusionOpen n m t ∈ primitive n m := by
    have hr : (primitive n m).ι t ∈ Set.range (primitive n m).ι := ⟨t,rfl⟩
    simpa only [Scheme.Opens.range_ι] using hr
  change inclusionOpen n m t ∉ ⋃ i : Fin (m-1), lowerZero n m i at ht
  change kernelNeg n m (inclusionOpen n m t) ∉ ⋃ i : Fin (m-1), lowerZero n m i
  intro hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change (kernelNeg n m ≫ mulInside n m (i.val+1)) (inclusionOpen n m t) ∈
    Set.range (zeroSection n m) at hi
  rw [lower_kernelNeg_commute] at hi
  obtain ⟨b,hb⟩ := hi
  have hh := congrArg (kernelNeg n m) hb
  have hb' : (zeroSection n m ≫ kernelNeg n m) b =
      (mulInside n m (i.val+1) ≫ kernelNeg n m ≫ kernelNeg n m) (inclusionOpen n m t) := hh
  rw [zero_kernelNeg,kernelNeg_twice,Category.comp_id] at hb'
  exact ht (Set.mem_iUnion_of_mem i ⟨b,hb'⟩)

/-- The signed point is in the same primitive locus, scheme-theoretically. -/
@[expose] def primitiveNeg : PrimitiveScheme n m ⟶ PrimitiveScheme n m :=
  IsOpenImmersion.lift (inclusionOpen n m) (inclusionOpen n m ≫ kernelNeg n m)
    (by exact neg_primitive_range n m)

@[reassoc] theorem primitiveNeg_open :
    primitiveNeg n m ≫ inclusionOpen n m = inclusionOpen n m ≫ kernelNeg n m :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem primitiveNeg_twice : primitiveNeg n m ≫ primitiveNeg n m = 𝟙 _ := by
  apply (cancel_mono (inclusionOpen n m)).mp
  simp only [Category.assoc,primitiveNeg_open,primitiveNeg_open_assoc,kernelNeg_twice,
    Category.comp_id,Category.id_comp]

theorem primitiveNeg_affine (hm : 1 < m) :
    primitiveNeg n m ≫ intoAffine n m hm =
      intoAffine n m hm ≫ GluedNegation318.finiteNeg (A n) (B n) := by
  apply (cancel_mono (chart n)).mp
  calc
    _ = (inclusionOpen n m ≫ inclusion n m) ≫ curveNeg n := by
      rw [Category.assoc,intoAffine_chart]
      change primitiveNeg n m ≫ inclusionOpen n m ≫ inclusion n m = _
      rw [primitiveNeg_open_assoc,Category.assoc,kernelNeg_inclusion,← Category.assoc]
    _ = (intoAffine n m hm ≫ chart n) ≫ curveNeg n :=
      congrArg (fun q : PrimitiveScheme n m ⟶ Curve n => q ≫ curveNeg n)
        (intoAffine_chart n m hm).symm
    _ = intoAffine n m hm ≫ (chart n ≫ curveNeg n) := Category.assoc _ _ _
    _ = intoAffine n m hm ≫ (GluedNegation318.finiteNeg (A n) (B n) ≫ chart n) :=
      congrArg (fun q : affine n ⟶ Curve n => intoAffine n m hm ≫ q)
        (GluedNegation318.finiteChart_negation (A n) (B n))
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual Scheme involution induces the checked (x,-y) operation on
the actual affine quotient ring. Existence is not a supplied algebra action. -/
theorem quotient_sign (hm : 1 < m) (I : Ideal (D n))
    (e : PrimitiveScheme n m ≅ Spec (CommRingCat.of (D n ⧸ I)))
    (he : intoAffine n m hm = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ τ : (D n ⧸ I) →ₐ[R n] (D n ⧸ I),
      τ.comp (Ideal.Quotient.mkₐ (R n) I) = (Ideal.Quotient.mkₐ (R n) I).comp (sign n) ∧
      τ.comp τ = AlgHom.id (R n) (D n ⧸ I) := by
  let q := Ideal.Quotient.mkₐ (R n) I
  let j : Spec (CommRingCat.of (D n ⧸ I)) ⟶ affine n :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have he₀ : intoAffine n m hm = e.hom ≫ j := he
  have he' : j = e.inv ≫ intoAffine n m hm := by
    calc
      j = (𝟙 _) ≫ j := (Category.id_comp _).symm
      _ = (e.inv ≫ e.hom) ≫ j :=
        congrArg (fun k : Spec (CommRingCat.of (D n ⧸ I)) ⟶ _ => k ≫ j) e.inv_hom_id.symm
      _ = e.inv ≫ (e.hom ≫ j) := Category.assoc _ _ _
      _ = _ := congrArg (fun k : PrimitiveScheme n m ⟶ affine n => e.inv ≫ k) he₀.symm
  obtain ⟨f,hf⟩ := Spec.map_surjective (e.inv ≫ primitiveNeg n m ≫ e.hom)
  have hsq : CommRingCat.ofHom q.toRingHom ≫ f =
      CommRingCat.ofHom (sign n).toRingHom ≫ CommRingCat.ofHom q.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_comp,hf]
    change (e.inv ≫ primitiveNeg n m ≫ e.hom) ≫ j =
      j ≫ GluedNegation318.finiteNeg (A n) (B n)
    calc
      _ = e.inv ≫ (primitiveNeg n m ≫ (e.hom ≫ j)) := by simp only [Category.assoc]
      _ = e.inv ≫ (primitiveNeg n m ≫ intoAffine n m hm) :=
        congrArg (fun k : PrimitiveScheme n m ⟶ affine n => e.inv ≫ (primitiveNeg n m ≫ k))
          he₀.symm
      _ = e.inv ≫ (intoAffine n m hm ≫ GluedNegation318.finiteNeg (A n) (B n)) :=
        congrArg (fun k : PrimitiveScheme n m ⟶ affine n => e.inv ≫ k) (primitiveNeg_affine n m hm)
      _ = (e.inv ≫ intoAffine n m hm) ≫ GluedNegation318.finiteNeg (A n) (B n) :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k : Spec (CommRingCat.of (D n ⧸ I)) ⟶ affine n =>
        k ≫ GluedNegation318.finiteNeg (A n) (B n)) he'.symm
  have hsq' (d : D n) : f.hom (q d) = q (sign n d) :=
    congrArg (fun g => g.hom d) hsq
  let τ : (D n ⧸ I) →ₐ[R n] (D n ⧸ I) :=
    { toRingHom := f.hom
      commutes' := fun r => by
        change f.hom (algebraMap (R n) (D n ⧸ I) r) = algebraMap (R n) (D n ⧸ I) r
        simpa only [(sign n).commutes,q.commutes] using
          hsq' (algebraMap (R n) (D n) r) }
  have hτ : τ.comp q = q.comp (sign n) := AlgHom.ext hsq'
  refine ⟨τ,hτ,?_⟩
  ext a
  obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective a
  change f.hom (f.hom (q d)) = q d
  rw [hsq' d,hsq' (sign n d)]
  exact congrArg q (congrArg (fun g : D n →ₐ[R n] D n => g d)
    (ChartNegation318.affineNeg_twice (A n) (B n)))

section Fields
variable {K : Type} [Field K] [Algebra (R n) K]

/-- On the literal short curve x separates exactly the two possible signs.
The second disjunct is composition with the checked affine Scheme
negation's ring map, not an independently chosen negative label. -/
theorem same_x_iff (f g : D n →ₐ[R n] K) :
    f (X n) = g (X n) ↔ g = f ∨ g = f.comp (sign n) := by
  constructor
  · intro hx
    have fe := (AffineEquationFunctor318.ofHom (A n) (B n) f).property
    have ge := (AffineEquationFunctor318.ofHom (A n) (B n) g).property
    change f (Y n)^2 - f (X n)^3 - algebraMap (R n) K (A n) * f (X n) -
      algebraMap (R n) K (B n) = 0 at fe
    change g (Y n)^2 - g (X n)^3 - algebraMap (R n) K (A n) * g (X n) -
      algebraMap (R n) K (B n) = 0 at ge
    rw [hx] at fe
    have hy : (g (Y n) - f (Y n)) * (g (Y n) + f (Y n)) = 0 := by
      linear_combination ge - fe
    rcases mul_eq_zero.mp hy with hy | hy
    · exact Or.inl (AffineEquationFunctor318.hom_ext _ _ _ _ hx.symm
        (sub_eq_zero.mp hy))
    · refine Or.inr (AffineEquationFunctor318.hom_ext _ _ _ _ ?_ ?_)
      · simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_x] using hx.symm
      · simpa only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg] using
          (eq_neg_of_add_eq_zero_left hy : g (Y n) = -f (Y n))
  · rintro (rfl | rfl)
    · rfl
    · simp

/-- Any actual quotient of the finite short chart inherits the exact x
separation. The comparison takes place after restriction along the genuine
surjective quotient map, so equality is equality of geometric points of
that quotient. -/
theorem same_x_in_quotient (I : Ideal (D n))
    (f g : (D n ⧸ I) →ₐ[R n] K) :
    f (Ideal.Quotient.mk I (X n)) = g (Ideal.Quotient.mk I (X n)) ↔
      g = f ∨ g.comp (Ideal.Quotient.mkₐ (R n) I) =
        (f.comp (Ideal.Quotient.mkₐ (R n) I)).comp (sign n) := by
  rw [show f (Ideal.Quotient.mk I (X n)) = g (Ideal.Quotient.mk I (X n)) ↔
    (f.comp (Ideal.Quotient.mkₐ (R n) I)) (X n) =
      (g.comp (Ideal.Quotient.mkₐ (R n) I)) (X n) from Iff.rfl,
    same_x_iff]
  constructor
  · rintro (h | h)
    · left
      ext a
      obtain ⟨d,rfl⟩ := Ideal.Quotient.mk_surjective a
      exact congrArg (fun k : D n →ₐ[R n] K => k d) h
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h
end Fields

end SelectedPrimitiveAffineSign318
#print axioms SelectedPrimitiveAffineSign318.affine_quotient
#print axioms SelectedPrimitiveAffineSign318.quotient_sign
#print axioms SelectedPrimitiveAffineSign318.same_x_in_quotient
