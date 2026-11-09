module
public import IntegralAllBranchOverlapMaps318
public section
noncomputable section
namespace IntegralBranchTensorTransport318
open AlgebraicGeometry CategoryTheory
open IntegralBranchCoordinates318 IntegralBranchBicanonical318
open IntrinsicTensorChartSections318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
variable {S : Type u} [CommRing S] [Algebra R S]
local instance : Module S (KaehlerDifferential R S) :=
  IntegralReciprocalTensorIdentity318.nativeCotangentModule R S

@[expose] def differential (i : Fin 4) (f : B R c i →ₐ[R] S) : KaehlerDifferential R S :=
  AlgHomDifferential318.map f (KaehlerDifferential.D R (B R c i) (sourceCoordinate R c i))
@[expose] def jacobian (i : Fin 4) (f : B R c i →ₐ[R] S) : S :=
  2 * algebraMap R S (↑(c i)⁻¹ : R) * f (sourceCoordinate R c i)

/-- The original cleared polynomial identity is retained under any specified
integral chart map, with its exact twist and factor two. -/
theorem mapped_cleared (i : Fin 4) (f : B R c i →ₐ[R] S) :
    f (sourceP R c i) * f (coefficient0 R c i) = jacobian R c i f ^ 2 := by
  have h := congrArg f (cleared R c i)
  simpa only [map_mul,map_pow,map_ofNat,AlgHom.commutes,jacobian] using h

theorem mapped_differential (i : Fin 4) (f : B R c i →ₐ[R] S) :
    KaehlerDifferential.D R S (f (sourceT R c i)) =
      jacobian R c i f • differential R c i f := by
  rw [differential,AlgHomDifferential318.map_D]
  apply SquareCoordinateDifferential318.D_of_square
  have h := congrArg f (coordinate_square R c i)
  simpa only [map_sub,map_mul,map_pow,AlgHom.commutes] using h

variable {Y : Scheme.{u}} (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (hp : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Equality is proved on the whole supplied common affine open. The maps
must preserve the SAME original quartic and coordinate, and that quartic
must be a unit there; generic nonvanishing does not suffice. -/
theorem weighted0_agreement (i k : Fin 4) (f : B R c i →ₐ[R] S) (g : B R c k →ₐ[R] S)
    (hP : f (sourceP R c i)=g (sourceP R c k))
    (ht : f (sourceT R c i)=g (sourceT R c k))
    (hu : IsUnit (f (sourceP R c i))) :
    weightedSquare j p hp (f (coefficient0 R c i)) (differential R c i f) =
      weightedSquare j p hp (g (coefficient0 R c k)) (differential R c k g) := by
  apply weightedSquare_agreement j p hp (f (sourceP R c i))
    (f (coefficient0 R c i)) (jacobian R c i f)
    (g (coefficient0 R c k)) (jacobian R c k g)
    (differential R c i f) (differential R c k g)
    (KaehlerDifferential.D R S (f (sourceT R c i))) hu
  · exact mapped_cleared R c i f
  · rw [hP]; exact mapped_cleared R c k g
  · exact mapped_differential R c i f
  · rw [ht]; exact mapped_differential R c k g

/-- Both original J²-scaled sections agree, including the coordinate factor
in the second section. No invertibility of J is used. -/
theorem scaled_agreement (i k : Fin 4) (f : B R c i →ₐ[R] S) (g : B R c k →ₐ[R] S)
    (hP : f (sourceP R c i)=g (sourceP R c k))
    (ht : f (sourceT R c i)=g (sourceT R c k))
    (hu : IsUnit (f (sourceP R c i))) (n : Fin 2) :
    weightedSquare j p hp
      (f ((VerticalSection318.J : B R c i)^2 *
        (if n=0 then coefficient0 R c i else coefficient1 R c i))) (differential R c i f) =
    weightedSquare j p hp
      (g ((VerticalSection318.J : B R c k)^2 *
        (if n=0 then coefficient0 R c k else coefficient1 R c k))) (differential R c k g) := by
  have he := weighted0_agreement R c j p hp i k f g hP ht hu
  by_cases hn : n=0
  · simpa only [hn,ite_true,map_mul,map_pow,map_intCast,weightedSquare_mul] using
      congrArg (fun z => (j.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ((VerticalSection318.J:S)^2)) • z) he
  · simp only [hn,ite_false,coefficient1,
      map_mul,map_pow,map_intCast,weightedSquare_mul,ht,he]
end IntegralBranchTensorTransport318
