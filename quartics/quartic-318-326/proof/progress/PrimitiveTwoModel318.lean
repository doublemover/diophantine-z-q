module
public import LiteralTwoTorsion318
public import PrimitivePointedModel318
public section
noncomputable section
namespace PrimitiveTwoModel318
open Polynomial PrimitiveDiamond318 InvariantBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def label : Fin 3→Points 2 :=
  ![⟨(1,0),by unfold PrimitiveTorsion318.Primitive; decide⟩,
    ⟨(0,1),by unfold PrimitiveTorsion318.Primitive; decide⟩,
    ⟨(1,1),by unfold PrimitiveTorsion318.Primitive; decide⟩]

lemma label_bijective : Function.Bijective label := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [label]
  · rintro ⟨⟨a,b⟩,hp⟩
    fin_cases a <;> fin_cases b
    · simp [PrimitiveTorsion318.Primitive] at hp
    · exact ⟨1,rfl⟩
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩

@[expose] def labels : Fin 3≃Points 2:=Equiv.ofBijective label label_bijective

abbrev Base:=OpenJModel318.Base 2
abbrev Cover:=LiteralTwoTorsion318.Ring 2
abbrev SplitRing:=(LiteralTwoTorsion318.splitting 2).S

@[expose] def splitEquiv : SplitRing⊗[Base]Cover≃ₐ[SplitRing](Points 2→SplitRing) :=
  (LiteralTwoTorsion318.splitEquiv 2).trans
    (AlgEquiv.piCongrLeft' SplitRing (fun _=>SplitRing)
      ((finCongr (ShortTwoTorsion318.degree (OpenJAffineScheme318.A 2) (OpenJAffineScheme318.B 2))).trans labels))

lemma unit_two_one (g:(ZMod 2)ˣ) : g=1 := by
  have hh:∀ g:(ZMod 2)ˣ,g=1:=by decide
  exact hh g

@[expose] def action (H:Subgroup (ZMod 2)ˣ) : H→Cover≃ₐ[Base]Cover :=
  fun _=>AlgEquiv.refl

lemma equivariant (H:Subgroup (ZMod 2)ˣ) :
    ∀(g:H)(b:SplitRing⊗[Base]Cover)(x:Points 2),
      splitEquiv (baseAction SplitRing (action H) g b) x=splitEquiv b (g•x) := by
  intro g b x
  have hx:g•x=x:=by
    change (g:(ZMod 2)ˣ)•x=x
    rw [unit_two_one (g:(ZMod 2)ˣ),one_smul]
  rw [hx]
  congr 1
  simp [baseAction,action]

/-- The actual rank-three primitive-two cover supplies its own finite-etale
splitting and scalar action. No cover algebra or splitting is a user premise.
This specializes only N=2, not the source's general modular/PEL level. -/
@[expose] def pointedComponent (Ω:Type) [Field Ω] (H:Subgroup (ZMod 2)ˣ)
    (β:Cover→+*Ω) :=
  PrimitivePointedModel318.component 2 Cover SplitRing Ω H (action H) splitEquiv
    (equivariant H) β


/-- The exact field-valued point of this constructed primitive-two cover has
a proper normal arithmetic model, without supplied relative-cover or splitting
objects. The restriction to level two is explicit. -/
theorem proper_model (Ω:Type) [Field Ω] (H:Subgroup (ZMod 2)ˣ) (β:Cover→+*Ω) :
    let c:=pointedComponent Ω H β
    AlgebraicGeometry.IsProper (PointedArithmeticModel318.structureMap c) ∧
      AlgebraicGeometry.Flat (PointedArithmeticModel318.structureMap c) ∧
      AlgebraicGeometry.Surjective (PointedArithmeticModel318.structureMap c) :=
  PointedArithmeticModel318.proper_flat_surjective _ (by decide)

end PrimitiveTwoModel318
