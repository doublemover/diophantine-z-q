module
public import ActualTwoDescentPrimaryAllRoots318
public section
noncomputable section
namespace ActualTwoDescentPrimaryBaerExtension318
set_option maxHeartbeats 16000000

open ActualTwoDescentPrimaryAllRoots318
variable {G H K : Type} [CommGroup G] [CommGroup H] [CommGroup K]

lemma actual_primary_baer (hP : IsPGroup 2 G) (hs : Function.Surjective (powMonoidHom (α:=G) 2)) :
    Module.Baer ℤ (Additive G) := by
  letI := primaryAdditiveDivisible hP hs
  letI := AddGroup.divisibleByIntOfDivisibleByNat (A:=Additive G)
  exact Module.Baer.of_divisible (Additive G)

/-- An ACTUAL homomorphism from a subgroup extends into the actual divisible primary target, via pinned Baer injectivity. -/
lemma actual_primary_hom_extension (hP : IsPGroup 2 G)
    (hs : Function.Surjective (powMonoidHom (α:=G) 2))
    (i : K →* H) (hi : Function.Injective i) (g : K →* G) :
    ∃ f : H →* G, ∀ x, f (i x)=g x := by
  let ia : Additive K →+ Additive H :=
    { toFun := fun x => Additive.ofMul (i x.toMul)
      map_zero' := congrArg Additive.ofMul (map_one i)
      map_add' := fun x y => congrArg Additive.ofMul (map_mul i x.toMul y.toMul) }
  let ga : Additive K →+ Additive G :=
    { toFun := fun x => Additive.ofMul (g x.toMul)
      map_zero' := congrArg Additive.ofMul (map_one g)
      map_add' := fun x y => congrArg Additive.ofMul (map_mul g x.toMul y.toMul) }
  obtain ⟨fa,hfa⟩ := (actual_primary_baer hP hs).extension_property_addMonoidHom ia
    (fun x y h => congrArg Additive.ofMul (hi (congrArg Additive.toMul h))) ga
  let f : H →* G :=
    { toFun := fun x => (fa (Additive.ofMul x)).toMul
      map_one' := congrArg Additive.toMul (map_zero fa)
      map_mul' := fun x y => congrArg Additive.toMul (map_add fa (Additive.ofMul x) (Additive.ofMul y)) }
  exact ⟨f,fun x => congrArg Additive.toMul (DFunLike.congr_fun hfa (Additive.ofMul x))⟩

end ActualTwoDescentPrimaryBaerExtension318
