module
public import SourceBranchSignStabilizer318
public import SourceSignChart318
public import ContactGlobalSignFaithful318
public import SourceCharacterFields318
public section
noncomputable section
namespace SourceBranchPointAction318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318 Polynomial
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F)
/-- The actual field-valued point of the whole contact normalization, via
its specified whole finite chart. -/
@[expose] def point:Spec (CommRingCat.of F)⟶ContactProjectiveModel318.model c:=
  Spec.map (CommRingCat.ofHom p.toRingHom)≫SourceGlobalAffine318.chartEmbedding c
variable (i:Fin 4) (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
include ht
lemma base_polynomial:algebraMap R F=
    (Polynomial.aeval (algebraMap ℚ F (LinearContactSquareclass318.contacts i))).toRingHom:=by
  apply Polynomial.ringHom_ext
  · intro q
    exact (SourceBranchSignStabilizer318.scalarPolynomial q).trans (Polynomial.aeval_C _ _).symm
  · exact ht.trans (Polynomial.aeval_X _).symm
/-- The source point lies over the literal labelled contact in the same
projective line, not just a root equation in an unrelated affine model. -/
theorem over_contact:point c p≫ContactProjectiveModel318.modelMap c=
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (algebraMap ℚ F (LinearContactSquareclass318.contacts i))).toRingHom)≫
        JLineAtlas318.chart ℚ 1:=by
  unfold point ContactProjectiveModel318.modelMap
  rw [Category.assoc,SourceGlobalAffine318.chartEmbedding_over_contact_line,←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change p (algebraMap R (SourceOrder c) q)=_
  rw [AlgHom.commutes,base_polynomial i ht]
  rfl

/-- Exact stabilizer of every field-valued branch point under the actual
whole-source maps. This is not a claim about a nonreduced fiber scheme. -/
theorem fixed_iff (b:Fin 4→Bool):
    point c p≫ContactGlobalSigns318.map c b=point c p↔∀j:Fin 4,j≠i→b j=false:=by
  rw [←SourceBranchSignStabilizer318.fixed_iff c p i ht b]
  constructor
  · intro h
    have hh:(Spec.map (CommRingCat.ofHom p.toRingHom)≫SourceSignChart318.map c b)≫
        SourceGlobalAffine318.chartEmbedding c=
      Spec.map (CommRingCat.ofHom p.toRingHom)≫SourceGlobalAffine318.chartEmbedding c:=by
      simpa only [Category.assoc,SourceSignChart318.actual_square,point] using h
    have ha:Spec.map (CommRingCat.ofHom p.toRingHom)≫SourceSignChart318.map c b=
        Spec.map (CommRingCat.ofHom p.toRingHom):=
      (cancel_mono (SourceGlobalAffine318.chartEmbedding c)).mp hh
    unfold SourceSignChart318.map at ha
    rw [←Spec.map_comp] at ha
    apply AlgHom.ext
    intro x
    exact congrArg (fun f=>f.hom x) (Spec.map_injective ha)
  · intro h
    have ha:Spec.map (CommRingCat.ofHom p.toRingHom)≫SourceSignChart318.map c b=
        Spec.map (CommRingCat.ofHom p.toRingHom):=by
      unfold SourceSignChart318.map
      rw [←Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom h)
    unfold point
    rw [Category.assoc,←SourceSignChart318.actual_square,←Category.assoc,ha]
omit ht
/-- Exactly one freely chosen bit remains in the branchpoint stabilizer. -/
@[expose] def supportedEquiv (i:Fin 4):{b:Fin 4→Bool // ∀j:Fin 4,j≠i→b j=false}≃Bool where
  toFun b:=b.val i
  invFun bit:=⟨fun j=>if j=i then bit else false,by intro j h; simp [h]⟩
  left_inv b:=by
    apply Subtype.ext
    funext j
    by_cases h:j=i
    · subst j; simp
    · simpa only [if_neg h] using (b.property j h).symm
  right_inv bit:=by simp
lemma supported_iff (i:Fin 4) (b:Fin 4→Bool):
    (∀j:Fin 4,j≠i→b j=false)↔b=(fun _=>false)∨b=SourceCharacterFields318.flip i:=by
  constructor
  · intro hb
    cases hi:b i
    · left
      funext j
      by_cases hji:j=i
      · subst j;exact hi
      · exact hb j hji
    · right
      funext j
      by_cases hji:j=i
      · subst j;simp [SourceCharacterFields318.flip,hi]
      · simp [SourceCharacterFields318.flip,hji,hb j hji]
  · rintro (rfl|rfl) <;> intro j hj <;> simp [SourceCharacterFields318.flip,hj]
include ht
/-- The only stabilizing sign patterns are the identity and the single
flip of the root vanishing at this contact. -/
theorem fixed_exactly (b:Fin 4→Bool):
    point c p≫ContactGlobalSigns318.map c b=point c p↔
      b=(fun _=>false)∨b=SourceCharacterFields318.flip i:=by
  rw [fixed_iff c p i ht,supported_iff]
theorem stabilizer_card:Nat.card
    {b:Fin 4→Bool // point c p≫ContactGlobalSigns318.map c b=point c p}=2:=by
  rw [Nat.card_congr ((Equiv.subtypeEquivRight (fixed_iff c p i ht)).trans (supportedEquiv i))]
  simp
/-- There are two distinct actual whole-Scheme maps in the point stabilizer,
not only two Boolean indices. -/
theorem stabilizer_image_card:Nat.card (Set.range
    (fun b:{b:Fin 4→Bool // point c p≫ContactGlobalSigns318.map c b=point c p}=>
      ContactGlobalSigns318.map c b.val))=2:=by
  have hi:Function.Injective
      (fun b:{b:Fin 4→Bool // point c p≫ContactGlobalSigns318.map c b=point c p}=>
        ContactGlobalSigns318.map c b.val):=by
    intro b d h
    exact Subtype.ext (ContactGlobalSignFaithful318.injective c h)
  rw [←Nat.card_congr (Equiv.ofInjective _ hi)]
  exact stabilizer_card c p i ht
end SourceBranchPointAction318
