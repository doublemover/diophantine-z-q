module
public import SelectedGeneralizedGeometricMulJet318
public import SelectedActualAugmentedCotangent318
public import Mathlib.RingTheory.Noetherian.Basic
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SelectedGeneralizedGluedCarrier318 SelectedGeneralizedGeometricIdentityJets318
open SelectedGeneralizedGeometricJetAxes318 SelectedGeneralizedGeometricMulJet318
open SelectedActualAugmentedCotangent318
open scoped SelectedActualAugmentedCotangent318

namespace SelectedActualKernelOriginConormal318

universe u
variable {R : Type u} [CommRing R] {d : Rˣ}
variable (add : ActualAddition d) (M : ℕ)

abbrev Kernel := pullback (multiply add M) (identitySection d)
abbrev first : Kernel add M ⟶ Carrier d := pullback.fst _ _
abbrev second : Kernel add M ⟶ Base R := pullback.snd _ _

theorem first_over : first add M ≫ overBase d = second add M := by
  have h := congrArg (fun f : Kernel add M ⟶ Carrier d => f ≫ overBase d)
    (pullback.condition : first add M ≫ multiply add M = second add M ≫ identitySection d)
  simpa only [Category.assoc,multiply_over,identity_over,Category.comp_id] using h

private theorem origin_mul : identitySection d ≫ multiply add M = identitySection d := by
  let p := zeroPoint d (𝟙 (Base R))
  have h (m : ℕ) : iterate add p m = p := by
    induction m with
    | zero => rfl
    | succ m ih =>
      change sum add (iterate add p m) p = p
      rw [ih]
      exact sum_zero add p
  have H := (multiply_test add p M).trans (congrArg Subtype.val (h M))
  change ((𝟙 (Base R)) ≫ identitySection d) ≫ multiply add M =
    (𝟙 (Base R)) ≫ identitySection d at H
  simpa only [Category.id_comp] using H

/-- The actual identity of the literal multiplication kernel. -/
def kernelOrigin : Base R ⟶ Kernel add M :=
  pullback.lift (identitySection d) (𝟙 _) (by rw [origin_mul add M,Category.id_comp])

private def sp {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

private theorem sp_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    sp (g.comp f) = sp g ≫ sp f := by
  unfold sp
  rw [← Spec.map_comp] <;> rfl

private theorem sp_over {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    sp f ≫ Spec.algebraMap R A = Spec.algebraMap R B := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

variable {T : Type u} [CommRing T] [Algebra R T]
variable (e : Spec (CommRingCat.of T) ≅ Kernel add M)
variable (he : e.hom ≫ second add M = Spec.algebraMap R T)

private def originInSpec : Base R ⟶ Spec (CommRingCat.of T) :=
  kernelOrigin add M ≫ e.inv

include he in
private theorem originInSpec_over :
    originInSpec add M e ≫ Spec.algebraMap R T = Spec.algebraMap R R := by
  rw [← he]
  change (kernelOrigin add M ≫ e.inv) ≫ (e.hom ≫ second add M) = _
  rw [Category.assoc,Iso.inv_hom_id_assoc]
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  change 𝟙 (Base R) = Spec.map (𝟙 (CommRingCat.of R))
  exact (Spec.map_id _).symm

include he in
/-- Augmentation is read off the actual origin arrow, not chosen. -/
def augmentation : T →ₐ[R] R :=
  Spec.homEquivAlgHom ⟨originInSpec add M e,originInSpec_over add M e he⟩

private theorem augmentation_spec :
    sp (augmentation add M e he) = originInSpec add M e :=
  congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply
    ⟨originInSpec add M e,originInSpec_over add M e he⟩)

/-- Exact Spec readout of the SAME augmentation of any given
affine comparison of this literal kernel. -/
theorem augmentation_spec_origin :
    Spec.map (CommRingCat.ofHom (augmentation add M e he).toRingHom) =
      kernelOrigin add M≫e.inv := augmentation_spec add M e he

abbrev inclusion : Spec (CommRingCat.of T) ⟶ Carrier d := e.hom ≫ first add M

include he in
private theorem inclusion_over :
    inclusion add M e ≫ overBase d = Spec.algebraMap R T := by
  rw [Category.assoc,first_over,he]

include he in
private theorem inclusion_killed :
    inclusion add M e ≫ multiply add M = Spec.algebraMap R T ≫ identitySection d := by
  rw [Category.assoc,pullback.condition,← Category.assoc,he]

private theorem spec_augmentation_inclusion :
    sp (augmentation add M e he) ≫ inclusion add M e = identitySection d := by
  rw [augmentation_spec]
  change (kernelOrigin add M ≫ e.inv) ≫ (e.hom ≫ first add M) = _
  rw [Category.assoc,Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

private theorem inclusion_cancel {X : Scheme} (f g : X ⟶ Spec (CommRingCat.of T))
    (h : f ≫ inclusion add M e = g ≫ inclusion add M e) : f=g := by
  apply (cancel_mono e.hom).1
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · change (f ≫ e.hom) ≫ second add M = (g ≫ e.hom) ≫ second add M
    rw [← first_over add M]
    simpa only [Category.assoc] using congrArg (fun j : X ⟶ Carrier d => j ≫ overBase d) h

/-- The actual kernel's identity conormal has a generator in the same
affine algebra. The only affine input is the true kernel isomorphism
over the original coefficient ring; no chart parameter is assumed. -/
theorem produces_origin_conormal :
    let ε := augmentation add M e he
    ∃ t : T, t∈I ε ∧ I ε = Ideal.span {t} ⊔ (I ε)^2 ∧
      algebraMap R T (M:R)*t ∈ (I ε)^2 := by
  let ε := augmentation add M e he
  let V := cotangent ε
  let u := universal ε
  let K := inclusion add M e
  have hu : (TrivSqZeroExt.fstHom R R V).comp u = ε := by
    apply AlgHom.ext
    intro x
    exact universal_fst ε x
  have hbase : (sp u ≫ K) ≫ overBase d = jetBase R V := by
    rw [Category.assoc,inclusion_over add M e he]
    exact sp_over u
  have hzero : augScheme R V ≫ (sp u ≫ K) = identitySection d := by
    change sp (TrivSqZeroExt.fstHom R R V) ≫ (sp u ≫ K) = _
    rw [← Category.assoc,← sp_comp,hu]
    exact spec_augmentation_inclusion add M e he
  obtain ⟨v,hv⟩ := exists_geomJet d (sp u ≫ K) hbase hzero
  have hkill : M • v=0 := (jet_killed_iff add v M).1 (by
    rw [← hv,Category.assoc,inclusion_killed add M e he,← Category.assoc,sp_over] <;> rfl)
  let W := quotientTest ε v
  let q : V →ₗ[R] W := quotientMap ε v
  have hq : q v = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Set.mem_singleton _))
  let left : T →ₐ[R] TrivSqZeroExt R W := (TrivSqZeroExt.map q).comp u
  let zero : T →ₐ[R] TrivSqZeroExt R W :=
    (Algebra.ofId R (TrivSqZeroExt R W)).comp ε
  have hleft : sp left ≫ K = geomJet d (q v) := by
    change sp ((TrivSqZeroExt.map q).comp u) ≫ K = _
    rw [sp_comp,Category.assoc,hv]
    exact geomJet_natural d q v
  have hzero' : sp zero ≫ K = jetBase R W ≫ identitySection d := by
    change sp ((Algebra.ofId R (TrivSqZeroExt R W)).comp ε) ≫ K = _
    rw [sp_comp,Category.assoc,spec_augmentation_inclusion add M e he] <;> rfl
  have heq : sp left = sp zero :=
    inclusion_cancel add M e _ _ (by rw [hleft,hq,geomJet_zero_map,hzero'])
  have heq' : Spec.map (CommRingCat.ofHom left.toRingHom) =
      Spec.map (CommRingCat.ofHom zero.toRingHom) := heq
  have hmap : left.toRingHom = zero.toRingHom :=
    congrArg (fun f : CommRingCat.of T ⟶ CommRingCat.of (TrivSqZeroExt R W) => f.hom)
      (Spec.map_injective heq')
  have htest : left = zero := AlgHom.toRingHom_injective hmap
  exact global_generator_from_zero_test ε v M hkill htest

/-- FG comes from finiteness of the same actual kernel coordinate
algebra over the selected Noetherian base, not from the jet theorem. -/
theorem produces_finite_origin_conormal [IsNoetherianRing R] [Module.Finite R T] :
    let ε := augmentation add M e he
    ∃ t : T, (I ε).FG ∧ t ∈ I ε ∧ I ε = Ideal.span {t} ⊔ (I ε)^2 ∧
      algebraMap R T (M:R)*t ∈ (I ε)^2 := by
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  obtain ⟨t,ht,hgen,hm⟩ := produces_origin_conormal add M e he
  exact ⟨t,(I (augmentation add M e he)).fg_of_isNoetherianRing,ht,hgen,hm⟩

end SelectedActualKernelOriginConormal318

#print axioms SelectedActualKernelOriginConormal318.produces_origin_conormal
#print axioms SelectedActualKernelOriginConormal318.produces_finite_origin_conormal
