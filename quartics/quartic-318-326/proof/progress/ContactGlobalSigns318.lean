module
public import FourRootOrderSigns318
public import ContactProjectiveModel318
public section
noncomputable section
namespace ContactGlobalSigns318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (b:Fin 4→Bool)
local instance modelIntegral:IsIntegralHom (ContactProjectiveModel318.modelMap c):=
  ContactProjectiveModel318.modelMap_integral c
@[expose] def openEquiv:OpenOrder c≃ₐ[OpenBase]OpenOrder c:=
  FourRootOrderSigns318.signEquiv (fun i=>algebraMap R OpenBase (coefficient c i)) b
@[expose] def openMap:ContactKummerCover318.cover c⟶ContactKummerCover318.cover c:=
  Spec.map (CommRingCat.ofHom (openEquiv c b).toRingHom)
theorem openMap_twice:openMap c b≫openMap c b=𝟙 _:=by
  unfold openMap ContactKummerCover318.cover
  rw [←Spec.map_comp,←Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun e:OpenOrder c≃ₐ[OpenBase]OpenOrder c=>e x)
    (FourRootOrderSigns318.signEquiv_trans_self _ b)
theorem openMap_over_base:openMap c b≫ContactKummerCover318.structureMap c=
    ContactKummerCover318.structureMap c:=by
  unfold openMap ContactKummerCover318.structureMap
  rw [←Spec.map_comp]
  congr 1
  ext r
  exact (openEquiv c b).commutes r
theorem openMap_over_line:openMap c b≫ContactProjectiveModel318.coverMap c=
    ContactProjectiveModel318.coverMap c:=by
  rw [ContactProjectiveModel318.coverMap,←Category.assoc,openMap_over_base]

/-- The specified literal root-sign map extends to the entire actual
normalization, including all finite branch points and infinity. -/
@[expose] def map:ContactProjectiveModel318.model c⟶ContactProjectiveModel318.model c:=by
  letI:=ContactProjectiveModel318.modelMap_integral c
  exact (ContactProjectiveModel318.coverMap c).normalizationDesc
    (openMap c b≫ContactProjectiveModel318.sourceOpen c) (ContactProjectiveModel318.modelMap c)
    (by rw [Category.assoc,ContactProjectiveModel318.sourceOpen,ContactProjectiveModel318.modelMap,
          (ContactProjectiveModel318.coverMap c).toNormalization_fromNormalization,openMap_over_line])
@[reassoc] theorem on_open:ContactProjectiveModel318.sourceOpen c≫map c b=
    openMap c b≫ContactProjectiveModel318.sourceOpen c:=
  (ContactProjectiveModel318.coverMap c).toNormalization_normalizationDesc _ _ _
@[reassoc] theorem over_line:map c b≫ContactProjectiveModel318.modelMap c=
    ContactProjectiveModel318.modelMap c:=
  (ContactProjectiveModel318.coverMap c).normalizationDesc_comp _ _ _

theorem twice:map c b≫map c b=𝟙 _:=by
  letI:=ContactProjectiveModel318.modelMap_integral c
  apply Scheme.Hom.normalization.hom_ext (ContactProjectiveModel318.coverMap c)
    _ _ (ContactProjectiveModel318.modelMap c)
  · change ContactProjectiveModel318.sourceOpen c≫(map c b≫map c b)=
      ContactProjectiveModel318.sourceOpen c≫𝟙 _
    rw [←Category.assoc,on_open,Category.assoc,on_open,←Category.assoc,
      openMap_twice,Category.id_comp,Category.comp_id]
  · rw [Category.assoc,over_line,over_line]
    rfl
  · rw [Category.id_comp]
    rfl
/-- Actual whole-Scheme sign involution, with its specified extension map as hom. -/
@[expose] def iso:ContactProjectiveModel318.model c≅ContactProjectiveModel318.model c where
  hom:=map c b
  inv:=map c b
  hom_inv_id:=twice c b
  inv_hom_id:=twice c b
@[simp] theorem iso_hom:(iso c b).hom=map c b:=rfl
end ContactGlobalSigns318
