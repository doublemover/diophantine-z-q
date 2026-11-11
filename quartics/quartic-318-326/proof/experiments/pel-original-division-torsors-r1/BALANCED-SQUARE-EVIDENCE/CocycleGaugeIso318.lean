module
public import CocycleGaugeMaps318
public section
noncomputable section
namespace CocycleGaugeIso318
open AlgebraicGeometry CategoryTheory Opposite
open CocycleGaugeMaps318
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {ι:Type u} (U:ι→X.Opens)
lemma multiply_one:ClutchedModule318.multiply (1:Γ(X,⊤))=𝟙 _:=by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change (ClutchedModule318.multiply (1:Γ(X,⊤))).app W s=s
  rw [ClutchedModule318.multiply_apply,map_one,mul_one]
lemma scale_mul (a b:∀i,Γ(X,U i)ˣ) (i:ι):
    scale U a i≫scale U b i=scale U (fun i=>a i*b i) i:=by
  simp only [scale,←Functor.map_comp,ClutchedGaugeMultiplication318.multiply_comp,
    Units.val_mul,map_mul]
lemma scale_one (i:ι):scale U (fun _=>1) i=𝟙 _:=by
  simp only [scale,Units.val_one,map_one,multiply_one]
  exact (Scheme.Modules.pushforward (U i).ι).map_id _
lemma scale_inv (a:∀i,Γ(X,U i)ˣ) (i:ι):
    scale U a i≫scale U (fun i=>(a i)⁻¹) i=𝟙 _:=by
  rw [scale_mul]
  simpa only [mul_inv_cancel] using scale_one U i
variable (c d:UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.units X).obj U)
    (a:∀i,Γ(X,U i)ˣ)
    (h:∀i j,d.transition i j=UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.units X).obj U a i j*c.transition i j)
include h in
lemma inverse_relation (i j:ι):c.transition i j=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units X).obj U
      (fun i=>(a i)⁻¹) i j*d.transition i j:=by
  rw [h]
  simp only [UnitTransitionCocycle318.coboundary,map_inv,inv_inv]
  simp only [mul_assoc,mul_left_comm,mul_comm,inv_mul_cancel_left,mul_inv_cancel,mul_one,one_mul]
include h in
lemma map_inverse:map U c d a h≫map U d c (fun i=>(a i)⁻¹) (inverse_relation U c d a h)=𝟙 _:=by
  apply CocycleModule318.hom_ext U c
  intro i
  rw [Category.assoc,map_coefficient,←Category.assoc,map_coefficient,
    Category.assoc,scale_inv,Category.comp_id,Category.id_comp]
/-- Explicit gauge isomorphism, with the inverse built from the actual inverse
units. No cover or pointwise-injectivity premise is used. -/
@[expose] def iso:CocycleModule318.object U c≅CocycleModule318.object U d where
  hom:=map U c d a h
  inv:=map U d c (fun i=>(a i)⁻¹) (inverse_relation U c d a h)
  hom_inv_id:=map_inverse U c d a h
  inv_hom_id:=by
    apply CocycleModule318.hom_ext U d
    intro i
    rw [Category.assoc,map_coefficient,←Category.assoc,map_coefficient,Category.assoc]
    have hs:=scale_inv U (fun i=>(a i)⁻¹) i
    simp only [inv_inv] at hs
    rw [hs,Category.comp_id,Category.id_comp]
lemma hom_coefficient (i:ι):(iso U c d a h).hom≫CocycleModule318.coefficient U d i=
    CocycleModule318.coefficient U c i≫scale U a i:=map_coefficient U c d a h i
lemma inv_coefficient (i:ι):(iso U c d a h).inv≫CocycleModule318.coefficient U c i=
    CocycleModule318.coefficient U d i≫scale U (fun i=>(a i)⁻¹) i:=
  map_coefficient U d c (fun i=>(a i)⁻¹) (inverse_relation U c d a h) i
lemma hom_inv:(iso U c d a h).hom≫(iso U c d a h).inv=𝟙 _ :=(iso U c d a h).hom_inv_id
lemma inv_hom:(iso U c d a h).inv≫(iso U c d a h).hom=𝟙 _ :=(iso U c d a h).inv_hom_id
end CocycleGaugeIso318
