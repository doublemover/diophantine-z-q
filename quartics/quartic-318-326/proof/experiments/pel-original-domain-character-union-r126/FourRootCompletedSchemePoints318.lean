module
public import FourRootSchemeChartInputs318
public section
noncomputable section
namespace FourRootCompletedSchemePoints318
open AlgebraicGeometry CategoryTheory
open FourRootNormalizedPointCharts318
open FourRootSchemeChartInputs318
variable (b:Fin 4→ℂ)
@[expose] def SchemePoints:={f:Spec (CommRingCat.of ℂ)⟶FourRootGluedScheme318.scheme b//
  f≫FourRootGluedScheme318.structureMap b=Spec.algebraMap ℂ ℂ}
@[expose] def finitePoint (p:FinitePoints b):SchemePoints b:=
  ⟨finiteInput b ((FourRootAffineCoordinateRing318.pointEquiv b).symm p),finite_base b _⟩
@[expose] def infinityPoint (p:InfinityPoints b):SchemePoints b:=
  ⟨infinityInput b ((FourRootInfinityCoordinateRing318.pointEquiv b).symm p),infinity_base b _⟩
@[expose] def center (s:InfinitySigns):InfinityPoints b:=
  ⟨(0,s.val),s.property.1,by simpa using s.property.2⟩

lemma finitePoint_injective:Function.Injective (finitePoint b):=by
  intro p q h
  exact (FourRootAffineCoordinateRing318.pointEquiv b).symm.injective
    (finite_injective b (congrArg Subtype.val h))
lemma infinityPoint_injective:Function.Injective (infinityPoint b):=by
  intro p q h
  exact (FourRootInfinityCoordinateRing318.pointEquiv b).symm.injective
    (infinity_injective b (congrArg Subtype.val h))
lemma finite_ne_center (p:FinitePoints b) (s:InfinitySigns):
    finitePoint b p≠infinityPoint b (center b s):=by
  intro h
  have hu:=transition_unit b _ _ (congrArg Subtype.val h)
  simp [FourRootInfinityCoordinateRing318.pointEquiv,center] at hu

/-- The actual localized algebra map has precisely the native reciprocal
coordinate. This is not inferred merely from matching complex tuples. -/
lemma overlap_point (p:InfinityPoints b) (hp:p.val.1≠0):
    finitePoint b (toFinite b ⟨p,hp⟩).val=infinityPoint b p:=by
  let g:FourRootCoordinateOverlap318.Infinity b→ₐ[ℂ]ℂ:=
    (FourRootInfinityCoordinateRing318.pointEquiv b).symm p
  have hg:g (FourRootInfinityCoordinateRing318.coordinate b none)=p.val.1:=by
    simp [g,FourRootInfinityCoordinateRing318.pointEquiv]
  let hu:IsUnit (g (FourRootInfinityCoordinateRing318.coordinate b none)):=by
    rw [hg];exact isUnit_iff_ne_zero.mpr hp
  let e:=overlapEvaluation b g hu
  have he:e (FourRootCoordinateOverlap318.ui b)=p.val.1⁻¹:=by
    have hi:=congrArg e (FourRootCoordinateOverlap318.u_ui b)
    simp only [map_mul,map_one] at hi
    have hu':e (FourRootCoordinateOverlap318.u b)=p.val.1:=by
      exact (overlapEvaluation_map b g hu _).trans hg
    rw [hu'] at hi
    exact mul_left_cancel₀ hp (hi.trans (mul_inv_cancel₀ hp).symm)
  have hf:e.comp (FourRootCoordinateOverlap318.toInfinityBase b)=
      (FourRootAffineCoordinateRing318.pointEquiv b).symm (toFinite b ⟨p,hp⟩).val:=by
    apply FourRootAffineCoordinateRing318.hom_ext
    intro k
    cases k with
    | none=>
      simp [AlgHom.comp_apply,FourRootCoordinateOverlap318.toInfinityBase_t,he,
        FourRootAffineCoordinateRing318.pointEquiv,toFinite,inv_pow]
    | some k=>
      simp [AlgHom.comp_apply,FourRootCoordinateOverlap318.toInfinityBase_z,he,
        FourRootCoordinateOverlap318.s,overlapEvaluation_map,g,
        FourRootInfinityCoordinateRing318.pointEquiv,
        FourRootAffineCoordinateRing318.pointEquiv,toFinite,div_eq_mul_inv]
  apply Subtype.ext
  change finiteInput b _=infinityInput b g
  rw [←hf]
  exact input_agreement b g hu

@[expose] def completedPoint:Completed b→SchemePoints b
  | .inl p=>finitePoint b p
  | .inr s=>infinityPoint b (center b s)
lemma completed_infinity (p:InfinityPoints b):
    completedPoint b (infinityChart b p)=infinityPoint b p:=by
  by_cases h:p.val.1=0
  · rw [infinityChart,dif_pos h]
    apply congrArg (infinityPoint b)
    apply Subtype.ext
    exact Prod.ext h.symm rfl
  · rw [infinityChart_nonzero b p h]
    exact overlap_point b p h

/-- The open affine cover is used on the actual spectrum of the field,
not just on the predefined tuple carrier. -/
lemma field_chart_cases (f:Spec (CommRingCat.of ℂ)⟶FourRootGluedScheme318.scheme b):
    (∃a,a≫FourRootGluedScheme318.finiteChart b=f) ∨
    (∃a,a≫FourRootGluedScheme318.infinityChart b=f):=by
  rcases FourRootGluedScheme318.charts_cover b (f default) with ha|ha
  · left
    have h:Set.range f⊆Set.range (FourRootGluedScheme318.finiteChart b):=by
      rintro _ ⟨p,rfl⟩
      obtain ⟨a,ha⟩:=ha
      exact ⟨a,ha.trans (congrArg f (Subsingleton.elim default p))⟩
    exact ⟨IsOpenImmersion.lift _ f h,IsOpenImmersion.lift_fac _ _ h⟩
  · right
    have h:Set.range f⊆Set.range (FourRootGluedScheme318.infinityChart b):=by
      rintro _ ⟨p,rfl⟩
      obtain ⟨a,ha⟩:=ha
      exact ⟨a,ha.trans (congrArg f (Subsingleton.elim default p))⟩
    exact ⟨IsOpenImmersion.lift _ f h,IsOpenImmersion.lift_fac _ _ h⟩

lemma completedPoint_bijective:Function.Bijective (completedPoint b):=by
  constructor
  · intro p q h
    rcases p with p|p <;> rcases q with q|q
    · exact congrArg Sum.inl (finitePoint_injective b h)
    · exact (finite_ne_center b p q h).elim
    · exact (finite_ne_center b q p h.symm).elim
    · apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun z:InfinityPoints b=>z.val.2) (infinityPoint_injective b h)
  · intro p
    rcases field_chart_cases b p.val with ⟨a,ha⟩|⟨a,ha⟩
    · have hab:a≫FourRootGluedScheme318.finiteBase b=Spec.algebraMap ℂ ℂ:=by
        rw [←FourRootGluedScheme318.finite_structure,←Category.assoc,ha]
        exact p.property
      let f:FourRootCoordinateOverlap318.Affine b→ₐ[ℂ]ℂ:=Spec.homEquivAlgHom ⟨a,hab⟩
      have hf:Spec.map (CommRingCat.ofHom f.toRingHom)=a:=
        congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨a,hab⟩)
      refine ⟨.inl ((FourRootAffineCoordinateRing318.pointEquiv b) f),?_⟩
      apply Subtype.ext
      change finiteInput b ((FourRootAffineCoordinateRing318.pointEquiv b).symm
        ((FourRootAffineCoordinateRing318.pointEquiv b) f))=p.val
      rw [Equiv.symm_apply_apply,finiteInput,hf,ha]
    · have hab:a≫FourRootGluedScheme318.infinityBase b=Spec.algebraMap ℂ ℂ:=by
        rw [←FourRootGluedScheme318.infinity_structure,←Category.assoc,ha]
        exact p.property
      let f:FourRootCoordinateOverlap318.Infinity b→ₐ[ℂ]ℂ:=Spec.homEquivAlgHom ⟨a,hab⟩
      have hf:Spec.map (CommRingCat.ofHom f.toRingHom)=a:=
        congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨a,hab⟩)
      refine ⟨infinityChart b ((FourRootInfinityCoordinateRing318.pointEquiv b) f),?_⟩
      rw [completed_infinity]
      apply Subtype.ext
      change infinityInput b ((FourRootInfinityCoordinateRing318.pointEquiv b).symm
        ((FourRootInfinityCoordinateRing318.pointEquiv b) f))=p.val
      rw [Equiv.symm_apply_apply,infinityInput,hf,ha]

/-- Exact FULL complex-valued points of the actual glued Scheme. This
includes the eight separately normalized infinity signs and is independent
of source-curve uniformization or numerical branch identification. -/
@[expose] def schemePointEquiv:Completed b≃SchemePoints b:=
  Equiv.ofBijective (completedPoint b) (completedPoint_bijective b)
@[simp] theorem schemePointEquiv_finite (p:FinitePoints b):
    schemePointEquiv b (.inl p)=finitePoint b p:=rfl
@[simp] theorem schemePointEquiv_infinity (s:InfinitySigns):
    schemePointEquiv b (.inr s)=infinityPoint b (center b s):=rfl
end FourRootCompletedSchemePoints318
