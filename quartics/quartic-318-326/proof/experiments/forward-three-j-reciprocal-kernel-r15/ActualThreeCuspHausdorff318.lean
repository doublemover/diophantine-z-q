module
public import ActualThreeFilledQJ318
public import ActualJAllLevels318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 ActualThreeCuspOverlap318 ActualThreeCuspFilling318 QuotientJ318
namespace ActualThreeCuspHausdorff318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem identification_nonzero (b:Base (image 3)) (c:End 3) (q:disc c)
    (he:original b=cuspChart c q) : q.val≠0 := by
  intro hz
  have hq:q=zeroPoint c:=Subtype.ext hz
  exact original_ne_cusp b c (he.trans (congrArg (cuspChart c) hq))

theorem identification_j (b:Base (image 3)) (c:End 3) (q:disc c)
    (he:original b=cuspChart c q) :
    jMap 3 b=ActualQJ318.G (q.val^ActualThreeFilledQJ318.natWidth c)/(q.val^ActualThreeFilledQJ318.natWidth c) := by
  have hne:=identification_nonzero b c q he
  let p:Punctures:=⟨c,⟨q.val,hne,q.property⟩⟩
  have hb:b=oldMap p:=
    (original_openEmbedding).injective (he.trans (original_oldMap p).symm)
  rw [hb]
  exact ActualThreeFilledQJ318.j_oldMap c p.2

/-- The genuine j-growth separates every added cusp from every old point. -/
theorem separate_cusp (b:Base (image 3)) (c:End 3) :
    ∃U V:Set (Filled),IsOpen U ∧ IsOpen V ∧
      original b∈U ∧ cusp c∈V ∧ Disjoint U V := by
  let M:ℝ:=‖jMap 3 b‖+1
  obtain ⟨epsilon,hepsilon,hlarge⟩:=ActualThreeFilledQJ318.small_parameter_large_j c M
  let A:Set (Base (image 3)):={x | ‖jMap 3 x‖<M}
  let B:Set (disc c):={q | ‖q.val‖<epsilon}
  have hA:IsOpen A:=isOpen_lt (ActualJAllLevels318.continuous_j 3).norm continuous_const
  have hB:IsOpen B:=isOpen_lt continuous_subtype_val.norm continuous_const
  refine ⟨original '' A,cuspChart c '' B,
    (original_openEmbedding).isOpenMap _ hA,(cuspChart_openEmbedding c).isOpenMap _ hB,
    ⟨b,by dsimp [A,M];linarith,rfl⟩,⟨zeroPoint c,by simpa [B,zeroPoint] using hepsilon,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨q,hq,heq⟩
  have hl:=hlarge q hq (identification_nonzero x c q heq.symm)
  rw [←identification_j x c q heq.symm] at hl
  exact (not_lt_of_ge hl.le) hx

theorem separate_old (b c:Base (image 3)) (hbc:b≠c) :
    ∃U V:Set (Filled),IsOpen U ∧ IsOpen V ∧
      original b∈U ∧ original c∈V ∧ Disjoint U V := by
  obtain ⟨U,V,hU,hV,hb,hc,hdis⟩:=t2_separation hbc
  refine ⟨original '' U,original '' V,
    (original_openEmbedding).isOpenMap _ hU,(original_openEmbedding).isOpenMap _ hV,
    ⟨b,hb,rfl⟩,⟨c,hc,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hyx:y=x:=(original_openEmbedding).injective he
  subst y
  exact Set.disjoint_left.mp hdis hx hy

theorem separate_two_cusps (c d:End 3) (hcd:c≠d) :
    ∃U V:Set (Filled),IsOpen U ∧ IsOpen V ∧
      cusp c∈U ∧ cusp d∈V ∧ Disjoint U V :=
  ⟨Set.range (cuspChart c),Set.range (cuspChart d),
    (cuspChart_openEmbedding c).isOpen_range,(cuspChart_openEmbedding d).isOpen_range,
    ⟨zeroPoint c,rfl⟩,⟨zeroPoint d,rfl⟩,cuspCharts_disjoint c d hcd⟩

/-- The actual all-cusp attachment is Hausdorff; the possible doubled-origin
failure of arbitrary open gluing is ruled out by proved end separation and j-growth. -/
theorem filled_t2 : T2Space (Filled) := by
  constructor
  intro x y hxy
  rcases original_or_cusp x with ⟨b,rfl⟩|⟨c,rfl⟩
  · rcases original_or_cusp y with ⟨b',rfl⟩|⟨d,rfl⟩
    · exact separate_old b b' (fun he=>hxy (congrArg (original) he))
    · exact separate_cusp b d
  · rcases original_or_cusp y with ⟨b,rfl⟩|⟨d,rfl⟩
    · obtain ⟨U,V,hU,hV,hb,hc,hd⟩:=separate_cusp b c
      exact ⟨V,U,hV,hU,hc,hb,hd.symm⟩
    · exact separate_two_cusps c d (fun he=>hxy (congrArg (cusp) he))

theorem punctured_dense (c:End 3) : Dense {q:disc c | q.val≠0} :=
  (dense_compl_singleton (0:ℂ)).preimage (disc_open c).isOpenEmbedding_subtypeVal.isOpenMap

/-- The original genuine quotient is dense in the simultaneous cusp attachment. -/
theorem original_dense : DenseRange (original) := by
  intro z
  rcases TwoChartGluing318.jointly_surjective (overlap) z with ⟨b,rfl⟩|⟨⟨c,q⟩,rfl⟩
  · exact subset_closure ⟨b,rfl⟩
  · have hc:cuspChart c q∈closure (cuspChart c '' {q:disc c | q.val≠0}):=
      mem_closure_image (cuspChart_openEmbedding c).continuous.continuousAt (punctured_dense c q)
    apply closure_mono _ hc
    rintro z ⟨r,hr,rfl⟩
    exact ⟨oldMap ⟨c,⟨r.val,hr,r.property⟩⟩,original_oldMap _⟩

/-- An actual compact Hausdorff second-countable compactification with dense
open original quotient and a finite, distinctly embedded cusp complement. -/
theorem actual_compactification :
    CompactSpace (Filled) ∧ T2Space (Filled) ∧ SecondCountableTopology (Filled) ∧
      IsOpenEmbedding (original) ∧ DenseRange (original) ∧
        Injective (cusp) ∧ Set.range (original)=(Set.range (cusp))ᶜ :=
  ⟨ActualThreeCuspCompact318.filled_compactSpace,filled_t2,filled_secondCountable,
    original_openEmbedding,original_dense,cusp_injective,range_original⟩

@[expose] def infinityCusp : Filled := cusp ActualThreeCuspExhaustion318.infinityEnd
@[expose] def zeroCusp : Filled := cusp ActualThreeCuspExhaustion318.zeroEnd

theorem named_cusps_distinct : infinityCusp ≠ zeroCusp := by
  intro h
  exact ActualThreeCuspExhaustion318.ends_distinct (cusp_injective h)

theorem cusp_range_pair : Set.range cusp={infinityCusp,zeroCusp} := by
  ext z
  constructor
  · rintro ⟨c,rfl⟩
    rcases ActualThreeCuspExhaustion318.end_exhaustion c with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl|rfl)
    · exact ⟨ActualThreeCuspExhaustion318.infinityEnd,rfl⟩
    · exact ⟨ActualThreeCuspExhaustion318.zeroEnd,rfl⟩

/-- Exactly these two actual cusp origins, and no other points, are added. -/
theorem original_range_complement_pair :
    Set.range original={infinityCusp,zeroCusp}ᶜ := by
  rw [range_original,cusp_range_pair]

end ActualThreeCuspHausdorff318
