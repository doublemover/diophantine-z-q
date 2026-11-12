module
public import FourRootActualGenericField318
public section
set_option pp.explicit true
set_option pp.universes true
#check @FourRootActualGenericField318.product_nonsquare
#check @FourRootActualGenericField318.independent
#check @FourRootActualGenericField318.actual_field
#check @FourRootActualGenericField318.actual_degree
#check @FourRootActualGenericField318.tensor_domain
#check @FourRootActualGenericField318.affine_domain

-- These calls mirror existing consumers, retaining intended hb explicitly.
example (b:Fin 4→ℂ) (hb:Function.Injective b):
    IsField (KummerTensorField318.Raw (FourRootActualGenericField318.parameter b)):=
  FourRootActualGenericField318.actual_field b hb
example (b:Fin 4→ℂ) (hb:Function.Injective b):
    Module.finrank (RatFunc ℂ)
      (KummerTensorField318.Raw (FourRootActualGenericField318.parameter b))=16:=
  FourRootActualGenericField318.actual_degree b hb
