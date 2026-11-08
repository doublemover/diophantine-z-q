module
public import AllCuspQJ318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 QuotientJ318
namespace AllCuspHausdorff318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem identification_nonzero (N:ℕ) (hN:5≤N) (b:Base (image N)) (c:End N) (q:disc N hN c)
    (he:original N hN b=cuspChart N hN c q) : q.val≠0 := by
  intro hz
  have hq:q=zeroPoint N hN c:=Subtype.ext hz
  exact original_ne_cusp N hN b c (he.trans (congrArg (cuspChart N hN c) hq))

theorem identification_j (N:ℕ) (hN:5≤N) (b:Base (image N)) (c:End N) (q:disc N hN c)
    (he:original N hN b=cuspChart N hN c q) :
    jMap N b=ActualQJ318.G (q.val^AllCuspQJ318.natWidth N hN c)/(q.val^AllCuspQJ318.natWidth N hN c) := by
  have hne:=identification_nonzero N hN b c q he
  let p:Punctures N hN:=⟨c,⟨q.val,hne,q.property⟩⟩
  have hb:b=oldMap N hN p:=
    (original_openEmbedding N hN).injective (he.trans (original_oldMap N hN p).symm)
  rw [hb]
  exact AllCuspQJ318.j_oldMap N hN c p.2

/-- The genuine j-growth separates every added cusp from every old point. -/
theorem separate_cusp (N:ℕ) (hN:5≤N) (b:Base (image N)) (c:End N) :
    ∃U V:Set (Filled N hN),IsOpen U ∧ IsOpen V ∧
      original N hN b∈U ∧ cusp N hN c∈V ∧ Disjoint U V := by
  let M:ℝ:=‖jMap N b‖+1
  obtain ⟨epsilon,hepsilon,hlarge⟩:=AllCuspQJ318.small_parameter_large_j N hN c M
  let A:Set (Base (image N)):={x | ‖jMap N x‖<M}
  let B:Set (disc N hN c):={q | ‖q.val‖<epsilon}
  have hA:IsOpen A:=isOpen_lt (HolomorphicQuotientJ318.jMap_continuous N hN).norm continuous_const
  have hB:IsOpen B:=isOpen_lt continuous_subtype_val.norm continuous_const
  refine ⟨original N hN '' A,cuspChart N hN c '' B,
    (original_openEmbedding N hN).isOpenMap _ hA,(cuspChart_openEmbedding N hN c).isOpenMap _ hB,
    ⟨b,by dsimp [A,M];linarith,rfl⟩,⟨zeroPoint N hN c,by simpa [B,zeroPoint] using hepsilon,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨q,hq,heq⟩
  have hl:=hlarge q hq (identification_nonzero N hN x c q heq.symm)
  rw [←identification_j N hN x c q heq.symm] at hl
  exact (not_lt_of_ge hl.le) hx

theorem separate_old (N:ℕ) (hN:5≤N) (b c:Base (image N)) (hbc:b≠c) :
    ∃U V:Set (Filled N hN),IsOpen U ∧ IsOpen V ∧
      original N hN b∈U ∧ original N hN c∈V ∧ Disjoint U V := by
  obtain ⟨U,V,hU,hV,hb,hc,hdis⟩:=t2_separation hbc
  refine ⟨original N hN '' U,original N hN '' V,
    (original_openEmbedding N hN).isOpenMap _ hU,(original_openEmbedding N hN).isOpenMap _ hV,
    ⟨b,hb,rfl⟩,⟨c,hc,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hyx:y=x:=(original_openEmbedding N hN).injective he
  subst y
  exact Set.disjoint_left.mp hdis hx hy

theorem separate_two_cusps (N:ℕ) (hN:5≤N) (c d:End N) (hcd:c≠d) :
    ∃U V:Set (Filled N hN),IsOpen U ∧ IsOpen V ∧
      cusp N hN c∈U ∧ cusp N hN d∈V ∧ Disjoint U V :=
  ⟨Set.range (cuspChart N hN c),Set.range (cuspChart N hN d),
    (cuspChart_openEmbedding N hN c).isOpen_range,(cuspChart_openEmbedding N hN d).isOpen_range,
    ⟨zeroPoint N hN c,rfl⟩,⟨zeroPoint N hN d,rfl⟩,cuspCharts_disjoint N hN c d hcd⟩

/-- The actual all-cusp attachment is Hausdorff; the possible doubled-origin
failure of arbitrary open gluing is ruled out by proved end separation and j-growth. -/
theorem filled_t2 (N:ℕ) (hN:5≤N) : T2Space (Filled N hN) := by
  constructor
  intro x y hxy
  rcases original_or_cusp N hN x with ⟨b,rfl⟩|⟨c,rfl⟩
  · rcases original_or_cusp N hN y with ⟨b',rfl⟩|⟨d,rfl⟩
    · exact separate_old N hN b b' (fun he=>hxy (congrArg (original N hN) he))
    · exact separate_cusp N hN b d
  · rcases original_or_cusp N hN y with ⟨b,rfl⟩|⟨d,rfl⟩
    · obtain ⟨U,V,hU,hV,hb,hc,hd⟩:=separate_cusp N hN b c
      exact ⟨V,U,hV,hU,hc,hb,hd.symm⟩
    · exact separate_two_cusps N hN c d (fun he=>hxy (congrArg (cusp N hN) he))

theorem punctured_dense (N:ℕ) (hN:5≤N) (c:End N) : Dense {q:disc N hN c | q.val≠0} :=
  (dense_compl_singleton (0:ℂ)).preimage (disc_open N hN c).isOpenEmbedding_subtypeVal.isOpenMap

/-- The original genuine quotient is dense in the simultaneous cusp attachment. -/
theorem original_dense (N:ℕ) (hN:5≤N) : DenseRange (original N hN) := by
  intro z
  rcases TwoChartGluing318.jointly_surjective (overlap N hN) z with ⟨b,rfl⟩|⟨⟨c,q⟩,rfl⟩
  · exact subset_closure ⟨b,rfl⟩
  · have hc:cuspChart N hN c q∈closure (cuspChart N hN c '' {q:disc N hN c | q.val≠0}):=
      mem_closure_image (cuspChart_openEmbedding N hN c).continuous.continuousAt (punctured_dense N hN c q)
    apply closure_mono _ hc
    rintro z ⟨r,hr,rfl⟩
    exact ⟨oldMap N hN ⟨c,⟨r.val,hr,r.property⟩⟩,original_oldMap N hN _⟩

/-- An actual compact Hausdorff second-countable compactification with dense
open original quotient and a finite, distinctly embedded cusp complement. -/
theorem actual_compactification (N:ℕ) (hN:5≤N) :
    CompactSpace (Filled N hN) ∧ T2Space (Filled N hN) ∧ SecondCountableTopology (Filled N hN) ∧
      IsOpenEmbedding (original N hN) ∧ DenseRange (original N hN) ∧
        Injective (cusp N hN) ∧ Set.range (original N hN)=(Set.range (cusp N hN))ᶜ :=
  ⟨AllCuspCompact318.filled_compactSpace N hN,filled_t2 N hN,filled_secondCountable N hN,
    original_openEmbedding N hN,original_dense N hN,cusp_injective N hN,range_original N hN⟩

end AllCuspHausdorff318
