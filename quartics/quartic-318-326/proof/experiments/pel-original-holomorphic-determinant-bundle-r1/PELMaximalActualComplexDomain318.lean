module
public import PELOriginalMaximalSphere318
public section
noncomputable section
namespace PELMaximalActualComplexDomain318
open Set Metric
open scoped ComplexConjugate
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionRealRepresentation318
open PELMaximalHalfOctagonCoordinates318 PELMaximalHalfOctagonOriginalPoints318
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonBoundary318
open PELMaximalHalfOctagonBoundaryAction318
set_option maxHeartbeats 2400000

/-- Original scaled Klein coordinates as a continuous function on the
ambient complex plane. The denominator is everywhere positive. This is
not declared complex differentiable. -/
@[expose] def coordinates (z : ℂ) : ℝ × ℝ :=
  (alpha*beta*(2*z.re/(Complex.normSq z+1)),beta*((Complex.normSq z-1)/(Complex.normSq z+1)))

theorem coordinates_halfPlane (τ : HalfPlane) : coordinates τ=(scaledFirst τ,scaledSecond τ) := rfl

theorem coordinates_continuous : Continuous coordinates := by
  have hN : Continuous (fun z : ℂ => Complex.normSq z+1) :=
    PELHeightCompactSublevels318.normSq_continuous.add continuous_const
  have hn (z : ℂ) : Complex.normSq z+1≠0 := by nlinarith [Complex.normSq_nonneg z]
  exact (continuous_const.mul ((continuous_const.mul Complex.continuous_re).div hN hn)).prodMk
    (continuous_const.mul ((PELHeightCompactSublevels318.normSq_continuous.sub continuous_const).div hN hn))

@[expose] def closedDomain : Set ℂ := Set.range (fun P : upperCut => (cutPoint P:ℂ))
@[expose] def openDomain : Set ℂ := {z | 0<z.im ∧ centerHomeomorph (coordinates z)∈strictPolygon}

theorem closedDomain_membership (z : ℂ) : z∈closedDomain ↔ 0<z.im ∧ coordinates z∈upperCut := by
  constructor
  · rintro ⟨P,rfl⟩
    exact ⟨(cutPoint P).property,by rw [coordinates_halfPlane,cutPoint_coordinates]; exact P.property⟩
  · rintro ⟨hz,hP⟩
    refine ⟨⟨coordinates z,hP⟩,?_⟩
    exact congrArg (fun τ : HalfPlane => (τ:ℂ)) (cutPoint_recovers ⟨z,hz⟩ hP)

theorem closedDomain_compact : IsCompact closedDomain :=
  isCompact_range (continuous_subtype_val.comp cutPoint_continuous)

theorem openDomain_open : IsOpen openDomain :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (strict_open.preimage (centerHomeomorph.continuous.comp coordinates_continuous))

theorem openDomain_subset : openDomain⊆closedDomain := by
  rintro z ⟨hz,hz'⟩
  exact (closedDomain_membership z).mpr
    ⟨hz,(centered_membership (coordinates z)).mpr (strict_subset hz')⟩

theorem openDomain_ne_univ : openDomain≠Set.univ := by
  intro h
  have hh : (0:ℂ)∈openDomain := h.symm ▸ Set.mem_univ 0
  exact (lt_irrefl (0:ℝ)) (by simpa using hh.1)

@[expose] def point (P : upperCut) : closedDomain := ⟨(cutPoint P:ℂ),⟨P,rfl⟩⟩

theorem point_continuous : Continuous point :=
  (continuous_subtype_val.comp cutPoint_continuous).subtype_mk _

theorem point_bijective : Function.Bijective point := by
  constructor
  · intro P Q h
    have hh : cutPoint P=cutPoint Q := Subtype.ext (congrArg Subtype.val h)
    apply Subtype.ext
    rw [←cutPoint_coordinates P,←cutPoint_coordinates Q,hh]
  · rintro ⟨z,P,hP⟩
    exact ⟨P,Subtype.ext hP⟩

/-- A genuine closed-disk parameterization of the ACTUAL complex half-cut,
not a new complex structure transported from the Klein disk. -/
@[expose] def cutComplexHomeomorph : upperCut ≃ₜ closedDomain :=
  (Equiv.ofBijective point point_bijective).toHomeomorphOfContinuousClosed
    point_continuous point_continuous.isClosedMap

@[expose] def actualClosedDisk : closedDomain ≃ₜ ReflectedDiskJoukowski318.Disk :=
  cutComplexHomeomorph.symm.trans upperCutDisk

/-- The anti-holomorphic reflection in the actual complex coordinate. -/
@[expose] def mirror (τ : HalfPlane) : HalfPlane :=
  ⟨-conj (τ:ℂ),by simpa using τ.property⟩

theorem mirror_coordinates (τ : HalfPlane) :
    coordinates (mirror τ)=(-scaledFirst τ,scaledSecond τ) := by
  apply Prod.ext <;> simp [coordinates,mirror,scaledFirst,scaledSecond,firstDisk,secondDisk]
  <;> ring

theorem cutPoint_reflection (P : upperCut) : cutPoint (reflectedCut P)=mirror (cutPoint P) := by
  apply PELActualOriginalSideGluing318.scaled_injective
  change (scaledFirst (cutPoint (reflectedCut P)),scaledSecond (cutPoint (reflectedCut P)))=
    coordinates (mirror (cutPoint P))
  rw [cutPoint_coordinates,mirror_coordinates]
  have h := cutPoint_coordinates P
  rw [congrArg Prod.fst h,congrArg Prod.snd h]
  rfl

theorem closedDomain_reflection (z : ℂ) : -conj z∈closedDomain ↔ z∈closedDomain := by
  have forward (w : ℂ) (hw : w∈closedDomain) : -conj w∈closedDomain := by
    obtain ⟨P,rfl⟩ := hw
    refine ⟨reflectedCut P,?_⟩
    exact congrArg (fun τ : HalfPlane => (τ:ℂ)) (cutPoint_reflection P)
  constructor
  · intro h
    simpa using forward (-conj z) h
  · exact forward z

/-- The auxiliary radial disk normalization has the right real symmetry,
but no holomorphic assertion. A later conformal replacement must preserve
this actual reflection and prove its own boundary extension. -/
theorem actualDisk_reflection (P : upperCut) :
    (actualClosedDisk (point (reflectedCut P))).val=
      ReflectedDiskJoukowski318.reflected (actualClosedDisk (point P)).val := by
  change (upperCutDisk (cutComplexHomeomorph.symm (cutComplexHomeomorph (reflectedCut P)))).val=
    ReflectedDiskJoukowski318.reflected (upperCutDisk (cutComplexHomeomorph.symm (cutComplexHomeomorph P))).val
  rw [Homeomorph.symm_apply_apply,Homeomorph.symm_apply_apply]
  exact disk_reflection P
end PELMaximalActualComplexDomain318
