# Hamiltonian reduction

This is the detailed design of part 41 of `DESIGN.md`, *Hamiltonian
reduction*. It covers the milestones *Marsden–Weinstein reduction* and
*Reduction at a coadjoint orbit and the shifting construction* of
`atlas/symplectic-group-actions.md`, which follow McDuff–Salamon
[McDuffSalamon2017], Proposition 5.4.13 with Remark 5.4.14, and Example
5.3.11 with Proposition 5.4.15. The original sources are J. Marsden and
A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Rep. Math.
Phys. 5 (1974), and K. Meyer, *Symmetries and integrals in mechanics* (1973);
for the shifting construction, Guillemin–Sternberg, *Symplectic Techniques in
Physics* (1984), §26, and Ortega–Ratiu, *Momentum Maps and Hamiltonian
Reduction* (2004), §6.1. Tau Ceti's files cite the same works.

All names below are in the namespace given with them. Paths of new files are
under `SymplecticGeometry/`; Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, as in `DESIGN.md`. Signs follow *Group
actions, moment maps and periods* of `DESIGN.md`: the page's moment map $\mu$
is `fun x ↦ -μ x` for Tau Ceti's predicates.

## Setting

Throughout, as in Tau Ceti's `Hamiltonian/Reduction/ReducedSpace.lean`:

```lean
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  (h : σ.IsEquivariantMomentMap μ)
```

`𝔤` abbreviates `GroupLieAlgebra I G`, and `hG` the hypothesis that `G` acts
by symplectomorphisms,
`∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ`,
in the form Tau Ceti's theorems take it. `T2Space M` is the page's Hausdorff
convention; Tau Ceti's regularity lemmas in
`Hamiltonian/EquivariantMomentMap/LevelAction.lean` ask for it. The building
declarations are stated in Tau Ceti's sign and live in Tau Ceti's namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside `levelSubMulAction`,
so that they can move there unchanged. The two milestones are in
`SymplecticGeometry`, in the page's sign.

## What exists, and what the part adds

Tau Ceti has, at the pinned commit:

- the quotient manifold theorem for a free, proper, smooth action
  (`ProperSMul.orbitRelQuotientChartedSpace`,
  `ProperSMul.instIsManifoldOrbitRelQuotient`, `isSubmersion_quotientMk`,
  `ker_mfderiv_quotientMk`, `orbitRelQuotientDiffeomorph`;
  `Geometry/Manifold/GroupAction/Quotient.lean`), with the model space
  `ProperSMul.QuotientModelSpace E E'` of dimension `dim E' - dim E`;
- a regular level `{x // μ x = c}` as an embedded submanifold
  (`IsMomentMap.levelChartedSpace`, `isManifold_level`,
  `isSmoothEmbedding_coe_level`, `range_mfderiv_coe_level`), and the kernel
  of the restricted form (`ker_bilinFormAt_mpullback_coe_level`;
  `Hamiltonian/MomentMap/Submanifold.lean`);
- the reduced form for *level data*: any `i : Z → M` onto a level with
  tangent images `ker dμ`, any surjective submersion `p : Z → Q` whose
  vertical vectors are `di⁻¹(𝔤_c · i z)`, and a group `K` acting on `Z` over
  `p`, transitively on the fibres, through `φ : K → G`
  (`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`,
  `IsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator`;
  `Hamiltonian/MomentMap/ReducedForm.lean`);
- freeness gives regularity
  (`IsEquivariantMomentMap.forall_differential_surjective_of_stabilizer_eq_bot`),
  smooth actions restrict to embedded invariant submanifolds
  (`Manifold.IsSmoothEmbedding.contMDiffSMul`,
  `Geometry/Manifold/GroupAction/Restrict.lean`), and proper actions to
  invariant subspaces (`Topology.IsEmbedding.properSMul_of_isEmbedding`, the
  proof of `IsEquivariantMomentMap.properSMul_levelSubMulAction`);
- the Marsden–Weinstein–Meyer theorem for the quotient of `μ⁻¹(c)` by the
  coadjoint stabilizer `G_c`, when `G` acts properly on all of `M`
  (`Hamiltonian/Reduction/ReducedSpace.lean`);
- the coadjoint orbit `G ⧸ G_η` as a manifold with its KKS form
  `Module.Dual.coadjointOrbitForm η`, symplectic and invariant, whose moment
  map in Tau Ceti's sign is the orbit map
  `(Lie.coadjointRepresentation ℝ I G).orbitMap η`
  (`isEquivariantMomentMap_coadjointOrbitForm`), an injective immersion
  (`injective_differential_orbitMap_coadjointRepresentation`), with
  dimension `finrank_quotientModelSpace_add_finrank_lieAnnihilator`
  (`Geometry/Symplectic/Coadjoint/Orbit.lean`,
  `Geometry/Lie/Adjoint/Representation/Coadjoint/Orbit.lean`);
- the product of two equivariant moment maps
  (`IsEquivariantMomentMap.prod`,
  `Hamiltonian/EquivariantMomentMap/Prod.lean`), and the generation of a
  connected Lie group by its exponential image
  (`closure_range_lieExp_eq_top`, `Geometry/Lie/Exponential/Generation.lean`).

Mathlib has proper actions and the Hausdorff orbit space
(`t2Space_quotient_mulAction_of_properSMul`), and nothing on reduction.

Missing in both, and added here: the zero level as a space of the whole
group `G` and its quotient by `G` when `G` acts freely and properly on the
level only; coisotropy of the level and its characteristic leaves; the
identification of the tangent spaces of the quotient; the preimage of an
embedded coadjoint orbit as a manifold, its quotient, the formula for its
reduced form, and its comparison with the reduced space at zero of the
product $M\times\mathcal O$.

## Decisions

`DESIGN.md` leaves three questions to this file.

- **Properness only on the level.** The level is a type of its own with an
  action of all of `G`: `h.zeroLevel : SubMulAction G M`, whose points are
  those with `μ x = 0`, with the subspace topology. Since `0` is fixed by
  the coadjoint action, the level is invariant under `G` and not only under
  `G_0`. Properness is the hypothesis `[ProperSMul G h.zeroLevel]` on this
  action, which is exactly the page's assumption, and freeness is
  `∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥`, the form of Tau Ceti's
  `forall_differential_surjective_of_stabilizer_eq_bot`. When `G` acts
  properly on `M`, `properSMul_zeroLevel` supplies the hypothesis, by the
  argument of Tau Ceti's `properSMul_levelSubMulAction`. The level's atlas
  is Tau Ceti's `IsMomentMap.levelChartedSpace` carried along the identity
  of points, as `levelSubMulActionChartedSpace` does for `G_c`, and the
  quotient's atlas is `ProperSMul.orbitRelQuotientChartedSpace` for `G`
  acting on it. So nothing asks for a proper action on `M`.
- **Embedded coadjoint orbits.** An orbit is given by a covector `η`, as the
  manifold `G ⧸ G_η` of Tau Ceti with its orbit map
  `ι = (Lie.coadjointRepresentation ℝ I G).orbitMap η`. Tau Ceti proves `ι`
  an injective immersion. Embeddedness is the hypothesis
  `Topology.IsEmbedding fun q ↦ ⇑(ι q)`, into `𝔤 → ℝ` with the product
  topology. `Module.Dual ℝ 𝔤` carries no topology or norm in Mathlib, and
  on the dual of a finite-dimensional space the topology of pointwise
  convergence is the usual one, so this is the page's condition without
  choosing a basis or a norm. An injective immersion that is a topological
  embedding is a smooth embedding, so a `Manifold.IsSmoothEmbedding`
  hypothesis would add nothing.
- **The quotient by `G` and Tau Ceti's quotient by `G_c`.** At `c = 0` the
  stabilizer `G_0` is all of `G` as a set, but Tau Ceti's quotient is by the
  subgroup `G_0` with a Lie group structure `d` of its own
  (`Lie.EmbeddedLieSubgroupData`), and it needs `[ProperSMul G M]`. The part
  reduces by `G` itself and uses Tau Ceti's reduction only through its
  level-data theorems, which take any `K` acting through `φ : K → G`; here
  `K = G` and `φ = id`. No comparison of the two quotients is built: no
  milestone uses one, and when `G` acts properly on `M` both are quotients
  of free proper actions with the same orbits, so
  `ProperSMul.orbitRelQuotientDiffeomorph` gives it at once if a later part
  needs it.

Further choices of this design:

- **The reduced form is not a definition.** As in Tau Ceti, it is the
  unique `η` of an `∃!` statement. The statements about it (its values on
  tangent vectors, its comparison under the diffeomorphism of the coadjoint
  orbit case) take any `η` with the pullback equation, so no
  `Classical.choose` is needed.
- **Atlases as definitions.** As in Tau Ceti, the atlases of the level and
  of its quotient depend on hypotheses, so they are
  `@[instance_reducible] def`s, and statements bring them in with `letI`.
  The level is modelled on `Fin n → ℝ` with
  `hn : finrank ℝ E' - finrank ℝ 𝔤 = n`, the quotient on
  `ProperSMul.QuotientModelSpace E (Fin n → ℝ)`.
- **The coadjoint orbit case through the product.** The preimage
  $Q=\mu^{-1}(\mathcal O)$ gets its manifold structure from the zero level
  of the product $M\times\mathcal O$, along the graph homeomorphism
  $x\mapsto(x,\iota^{-1}(\mu x))$; this needs the orbit embedded. Then `G`
  acts on $Q$ freely, properly and smoothly by hypothesis and transport, so
  the quotient manifold theorem applies to $Q$ directly, and the quotient
  diffeomorphism with the zero-level quotient of the product is Tau Ceti's
  `ProperSMul.orbitRelQuotientDiffeomorph` of the graph. Freeness, properness
  and regularity on the product's level all follow from those on $Q$, so the
  zero-level results apply to the product unchanged. This route does not
  use Tau Ceti's shifting map of `EquivariantMomentMap/Shifting.lean` or
  `Reduction/ShiftingForm.lean`: the formula of the milestone is the
  pullback of the product form along the graph, which is a sum by
  `SmoothTwoForm.prod_def` and `SmoothForm.mpullback_mpullback`.
- **Signs in the coadjoint orbit case.** `DESIGN.md` takes Tau Ceti's
  `coadjointOrbitForm η` as the page's orbit form, with Tau Ceti moment map
  `ι`. With Tau Ceti's moment map `μ` on `M`, the product form
  `σ.prod η.coadjointOrbitForm`, which is the page's
  $\omega\oplus\omega_{\mathcal O}$ with its plus sign, has the Tau Ceti
  moment map `fun p ↦ μ p.1 + ι p.2`
  (`h.prod η.isEquivariantMomentMap_coadjointOrbitForm`). If
  $\mu^{\mathrm p}=-\mu$ is the page's moment map, this is
  $-(\mu^{\mathrm p}(x)-\iota(q))$, that is, minus the page's
  $\widetilde\mu$, as the sign convention asks. Its zero level is
  $\{(x,q):\mu^{\mathrm p}(x)=\iota(q)\}$. So the preimage is defined in Tau
  Ceti's sign as `{x | -μ x ∈ Set.range ι}`, which is the page's
  $\mu^{-1}(\mathcal O)$ for $\mu^{\mathrm p}$.
- **Transversality.** The page concludes that $\mu$ is transverse to
  $\mathcal O$. Freeness on $Q$ makes $d\mu$ onto at every point of $Q$,
  which is stronger, and the milestone states that.

## Files

All in `Geometry/Symplectic/Hamiltonian/Reduction/`, beside Tau Ceti's
files of that folder (none of which is named `ZeroLevel` or
`CoadjointOrbit`).

### `ZeroLevel/Basic.lean`

The zero level as a `G`-space, its manifold structure, its quotient by `G`,
and the reduced form, in `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.
Write `Z := h.zeroLevel` and `π := Quotient.mk (MulAction.orbitRel G Z)`,
and let `hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥`.

- `def zeroLevel : SubMulAction G M`, carrier `μ ⁻¹' {0}`, invariant by
  `h.apply_smul` and `map_zero`; `@[simp] mem_zeroLevel :
  x ∈ h.zeroLevel ↔ μ x = 0`, `coe_zeroLevel`.
- `properSMul_zeroLevel [ProperSMul G M] : ProperSMul G h.zeroLevel`.
- `isCancelSMul_zeroLevel (hfree) : IsCancelSMul G h.zeroLevel`.
- `def zeroLevelChartedSpace (hσ : σ.IsNondegenerate) (hfree) (hn) :
  ChartedSpace (Fin n → ℝ) h.zeroLevel`, which is
  `h.levelSubMulActionChartedSpace 0` with the regularity of
  `forall_differential_surjective_of_stabilizer_eq_bot`.
- With it: `isManifold_zeroLevel`, `isSmoothEmbedding_coe_zeroLevel`
  (`Subtype.val : Z → M` is a smooth embedding), `range_mfderiv_coe_zeroLevel`
  (`range (mfderiv … Subtype.val z) = ker (h.differential z)`),
  `contMDiffSMul_zeroLevel`, and `finrank_add_finrank_zeroLevel
  (z : Z) : n + finrank ℝ 𝔤 = finrank ℝ E'` (a free point makes
  `dim 𝔤 ≤ dim M`, so the subtraction in `hn` is honest).
- `def zeroLevelQuotientChartedSpace (hσ) (hfree) (hn)
  [ProperSMul G h.zeroLevel] :
  ChartedSpace (ProperSMul.QuotientModelSpace E (Fin n → ℝ))
  (MulAction.orbitRel.Quotient G h.zeroLevel)`.
- With both atlases: `isManifold_zeroLevelQuotient`,
  `isSubmersion_quotientMk_zeroLevel`, and

  ```lean
  theorem ker_mfderiv_quotientMk_zeroLevel (z : h.zeroLevel) :
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) π z).ker =
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent z).comap
          (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap
  ```

  from `ProperSMul.ker_mfderiv_quotientMk`: `di` carries the orbit tangent
  space of `Z` onto that of `M`, since `di ∘ eval_Z z = eval_M z`
  (`mfderiv_fundamentalVectorField_of_map_smul`), and `di` is injective. This
  is the hypothesis `hker` of the level-data theorem, since
  `lieAnnihilator ℝ 𝔤 0 = ⊤`.
- The reduced form:

  ```lean
  theorem existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback
      (hσ : σ.IsSymplectic) (hG) (hfree) (hn) [ProperSMul G h.zeroLevel] :
      letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree hn
      letI := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree hn
      ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
          (MulAction.orbitRel.Quotient G h.zeroLevel),
        η.IsSymplectic ∧
          SmoothForm.mpullback π (h.isSubmersion_quotientMk_zeroLevel …).contMDiff η =
            SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_zeroLevel …).contMDiff σ
  ```

  from `existsUnique_isSymplectic_mpullback_eq_mpullback` with `K = G`,
  `φ = id`.
- `finrank_quotientModelSpace_zeroLevel (z : h.zeroLevel) :
  finrank ℝ (ProperSMul.QuotientModelSpace E (Fin n → ℝ)) + 2 * finrank ℝ 𝔤 =
  finrank ℝ E'`, from Tau Ceti's
  `IsMomentMap.finrank_add_finrank_add_finrank_lieAnnihilator` at `c = 0`.

The file credits Tau Ceti's
`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`, whose proof
it adapts from `G_c` to `G`.

### `ZeroLevel/Leaves.lean`

Coisotropy and characteristic leaves, with the atlases of `Basic.lean`.

- `isCoisotropicMap_coe_zeroLevel (hσ : σ.IsNondegenerate) (hfree) (hn) :
  hσ.IsCoisotropicMap 𝓘(ℝ, Fin n → ℝ) (Subtype.val : h.zeroLevel → M)`, from
  Tau Ceti's `IsMomentMap.isCoisotropicMap_of_forall_eq` at `c = 0`, with
  `lieAnnihilator ℝ 𝔤 0 = ⊤`.
- `ker_bilinFormAt_mpullback_coe_zeroLevel`: with `ProperSMul`, the kernel
  of `(i^* σ)_z` is the kernel of `dπ_z`, combining Tau Ceti's
  `IsMomentMap.ker_bilinFormAt_mpullback` (for maps whose tangent images are
  `ker dμ`, as `range_mfderiv_coe_zeroLevel` says; at `c = 0`) with
  `ker_mfderiv_quotientMk_zeroLevel`.
- For connected `G`, the leaves of the characteristic foliation
  `IsCoisotropicMap.characteristicFoliation` of the inclusion, with
  smoothness `1` and closedness `hσ.isClosed`, are the orbits:

  ```lean
  theorem leaf_characteristicFoliation_zeroLevel [ConnectedSpace G]
      (hσ : σ.IsSymplectic) (hfree) (hn) [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
      ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree hn).characteristicFoliation
          (h.isSmoothEmbedding_coe_zeroLevel …).isImmersion
          (h.isSmoothEmbedding_coe_zeroLevel …).contMDiff hσ.isClosed le_rfl).leaf z =
        MulAction.orbit G z
  ```

  A curve tangent to the foliation is tangent to `ker dπ`, so `π` is
  constant along it and its ends lie in one orbit; the leaf relation is
  generated by such curves, so leaves lie in orbits. Conversely
  `t ↦ lieExp (t • ξ) • z` is tangent to the orbit directions, which are the
  foliation's, so `z` and `lieExp ξ • z` lie on one leaf, and connected `G`
  is generated by `range lieExp` (`closure_range_lieExp_eq_top`). For a
  disconnected group the leaves are the orbits of the identity component;
  no statement is made for it, as the page restricts to connected groups.

### `ZeroLevel/Tangent.lean`

The tangent spaces of the quotient, and the first milestone.

- With `K z := LinearMap.ker (h.differential z)` and the orbit directions
  `L z := ((InfinitesimalAction.fundamental I G I' M).orbitTangent z).comap (K z).subtype`:

  ```lean
  def zeroLevelTangentEquiv (z : h.zeroLevel) :
      (K z ⧸ L z) ≃ₗ[ℝ]
        TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) (π z)
  ```

  built from the isomorphism `T_z Z ≃ K z` of `range_mfderiv_coe_zeroLevel`
  and the injectivity of `di`, followed by `dπ_z`, which is onto with kernel
  `L z` by `ker_mfderiv_quotientMk_zeroLevel`
  (`LinearMap.quotKerEquivOfSurjective`).
- `zeroLevelTangentEquiv_mk`: for `v : T_z Z`, the class of `di v` goes to
  `dπ_z v`.
- `eval₂_zeroLevelTangentEquiv`: if `SmoothForm.mpullback π _ η =
  SmoothForm.mpullback Subtype.val _ σ`, then for `v w : K z`,
  `η.eval₂ (π z) (e (Submodule.Quotient.mk v)) (e (Submodule.Quotient.mk w)) =
  σ.eval₂ z v w`, with `e = h.zeroLevelTangentEquiv z`.
- **Milestone** `SymplecticGeometry.symplecticReduction_zeroLevel`, in the
  page's sign: for `[ConnectedSpace G]`, `hω : ω.IsSymplectic`, `hG`,
  `h : ω.IsEquivariantMomentMap fun x ↦ -μ x`,
  `hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥`,
  `[ProperSMul G h.zeroLevel]` and `hn`, with both atlases, the conjunction
  of
  1. `∀ x, μ x = 0 → Function.Surjective (h.differential x)` (zero is a
     regular value; `h.differential x` is $-d\mu(x)$);
  2. `Subtype.val : h.zeroLevel → M` is a smooth embedding, and
     `Nonempty h.zeroLevel → n + finrank ℝ 𝔤 = finrank ℝ E'`;
  3. the inclusion is a coisotropic map;
  4. every leaf of its characteristic foliation is a `G`-orbit, as in
     `leaf_characteristicFoliation_zeroLevel`;
  5. the `∃!` of `existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback`;
  6. `Nonempty h.zeroLevel →
     finrank ℝ (ProperSMul.QuotientModelSpace E (Fin n → ℝ)) + 2 * finrank ℝ 𝔤 = finrank ℝ E'`;
  7. `eval₂_zeroLevelTangentEquiv` for every `η` with the pullback equation.

  `hfree` is passed to the atlases as
  `fun x hx ↦ hfree x (neg_eq_zero.1 hx)`. Its docstring ends with
  "Milestone: *Marsden–Weinstein reduction*."

### `CoadjointOrbit/Level.lean`

The preimage of an embedded coadjoint orbit as a manifold, in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`. Fix `η : 𝔤*`, write
`O := G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer η`,
`ι := (Lie.coadjointRepresentation ℝ I G).orbitMap η`,
`hP := h.prod η.isEquivariantMomentMap_coadjointOrbitForm` (the product
moment map `fun p ↦ μ p.1 + ι p.2` of `σ.prod η.coadjointOrbitForm`),
`hemb : Topology.IsEmbedding fun q : O ↦ ⇑(ι q)`, and
`hfree : ∀ x ∈ h.orbitLevel η, MulAction.stabilizer G x = ⊥`.

- `def orbitLevel (η) : SubMulAction G M`, carrier `{x | -μ x ∈ Set.range ι}`
  (invariant since `ι` is equivariant); `@[simp] mem_orbitLevel`,
  `properSMul_orbitLevel [ProperSMul G M]`.
- `def orbitLevelGraph (hemb) : h.orbitLevel η ≃ₜ hP.zeroLevel`,
  `x ↦ (x, q)` with `ι q = -μ x`, inverse `Prod.fst`; `orbitLevelGraph_fst`,
  `orbitMap_orbitLevelGraph_snd : ι (h.orbitLevelGraph hemb x).2 = -μ x`
  (names of the components to be fixed by the implementation), and
  `orbitLevelGraph_smul` (equivariance). Continuity of the inverse of `ι` on
  its image is `hemb`.
- `stabilizer_zeroLevel_prod_eq_bot` and
  `properSMul_zeroLevel_prod [ProperSMul G (h.orbitLevel η)]`: freeness and
  properness pass to the product's zero level along the graph.
- `def orbitLevelChartedSpace (hσ : σ.IsNondegenerate) (hemb) (hfree) (hm) :
  ChartedSpace (Fin m → ℝ) (h.orbitLevel η)`, with
  `hm : finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I _) - finrank ℝ 𝔤 = m`:
  the pullback along the graph of `hP.zeroLevelChartedSpace` (the product
  form is nondegenerate, the product model has dimension
  `dim M + dim O`).
- With it: `isManifold_orbitLevel`, `contMDiffSMul_orbitLevel`,
  `orbitLevelGraphDiffeomorph` (the graph as a diffeomorphism),
  `contMDiff_orbitLevelProj` for `x ↦ (h.orbitLevelGraph hemb x).2 : O`
  (the page's $\mu|_Q$), and `isSmoothEmbedding_coe_orbitLevel`: the
  inclusion is `Prod.fst` on the product level, an immersion since a
  tangent vector `(0, w)` of the level has `dι w = 0`, so `w = 0` by
  `injective_differential_orbitMap_coadjointRepresentation`, and a
  topological embedding by the graph.
- `differential_surjective_of_mem_orbitLevel (hσ) (hfree) :
  ∀ x ∈ h.orbitLevel η, Function.Surjective (h.differential x)`, from Tau
  Ceti's pointwise freeness lemma; it implies transversality to the orbit.

### `CoadjointOrbit/Quotient.lean`

The reduced space $Q/G$ and the second milestone, with `π_Q` and `π_P` the
orbit projections of `h.orbitLevel η` and of `hP.zeroLevel`.

- `def orbitLevelQuotientChartedSpace … [ProperSMul G (h.orbitLevel η)]`, on
  `ProperSMul.QuotientModelSpace E (Fin m → ℝ)`;
  `isManifold_orbitLevelQuotient`, `isSubmersion_quotientMk_orbitLevel`.
- `def orbitLevelQuotientDiffeomorph : MulAction.orbitRel.Quotient G (h.orbitLevel η) ≃ₘ⟮…⟯
  MulAction.orbitRel.Quotient G hP.zeroLevel`, Tau Ceti's
  `ProperSMul.orbitRelQuotientDiffeomorph` of `MulEquiv.refl G` and
  `orbitLevelGraphDiffeomorph`; `orbitLevelQuotientDiffeomorph_mk`.
- `mpullback_orbitLevelGraph_prod`: the product form pulled back along
  `Subtype.val ∘ orbitLevelGraph` is
  `SmoothForm.mpullback Subtype.val _ σ + SmoothForm.mpullback orbitLevelProj _ η.coadjointOrbitForm`.
- `existsUnique_isSymplectic_mpullback_quotientMk_orbitLevel (hσ) (hG) … :
  ∃! ω_red, ω_red.IsSymplectic ∧ SmoothForm.mpullback π_Q _ ω_red =
  SmoothForm.mpullback Subtype.val _ σ +
  SmoothForm.mpullback orbitLevelProj _ η.coadjointOrbitForm`: the product's
  zero-level form pulled back along `orbitLevelQuotientDiffeomorph`;
  uniqueness because `π_Q` is a surjective submersion.
- `mpullback_orbitLevelQuotientDiffeomorph`: if `ω_red` satisfies that
  equation and `ω̃` satisfies the zero-level equation of the product, then
  `SmoothForm.mpullback orbitLevelQuotientDiffeomorph _ ω̃ = ω_red`.
- `finrank_quotientModelSpace_orbitLevel (x : h.orbitLevel η) :
  finrank ℝ (ProperSMul.QuotientModelSpace E (Fin m → ℝ)) + 2 * finrank ℝ 𝔤 =
  finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I _)`.
- **Milestone** `SymplecticGeometry.symplecticReduction_coadjointOrbit`, in
  the page's sign: for `[ConnectedSpace G]`, `hω`, `hG`,
  `h : ω.IsEquivariantMomentMap fun x ↦ -μ x`, `η`, `hemb`, freeness on
  `h.orbitLevel η` (whose points are those with `μ x ∈ Set.range ι`),
  `[ProperSMul G (h.orbitLevel η)]` and `hm`, with the atlases, the
  conjunction of
  1. $d\mu$ is onto at every point of $Q$ (so $\mu$ is transverse to
     $\mathcal O$);
  2. the inclusion of $Q$ is a smooth embedding;
  3. the `∃!` above, whose formula is the page's
     $\pi^*\omega_{\mathrm{red}}=i^*\omega+(\mu|_Q)^*\omega_{\mathcal O}$;
  4. the dimension formula, for nonempty $Q$;
  5. `orbitLevelQuotientDiffeomorph` carries the reduced form of the
     product's zero level to that of $Q$, as in
     `mpullback_orbitLevelQuotientDiffeomorph`.

  Its docstring ends with "Milestone: *Reduction at a coadjoint orbit and
  the shifting construction*."

Connectedness is not used by the coadjoint orbit case; the milestone keeps
the page's hypothesis, and the building lemmas do without it.

## What the part uses

Only Tau Ceti and Mathlib: the declarations named above. No other part of
this library; the part stays at level 0 of the build order.

## Edge cases

- An empty level: every statement holds vacuously, and the dimension
  statements ask for a point, since `hn` and `hm` use truncated subtraction.
- `dim G = 0`: a connected `G` is trivial, `𝔤* = 0`, the level is `M`, and
  the quotient is `M` with `ω`.
- Odd-dimensional `M`: no symplectic form exists, so `hω` is never
  satisfied; the statements make no parity assumption.

## Issues

In order; each is a few hundred lines.

1. **`ZeroLevel/Basic.lean`**: the zero level as a `G`-space, its atlas, the
   quotient by `G`, its vertical directions, the reduced form and the
   dimension. Waits for nothing.
2. **`ZeroLevel/Leaves.lean`**: coisotropy of the level and its
   characteristic leaves as orbits. Waits for issue 1.
3. **`ZeroLevel/Tangent.lean`**: `zeroLevelTangentEquiv` with its API and
   the milestone *Marsden–Weinstein reduction*. Waits for issues 1 and 2.
4. **`CoadjointOrbit/Level.lean`**: the preimage of an embedded orbit, the
   graph homeomorphism with the product's zero level, its atlas, the
   embedding and regularity. Waits for issue 1.
5. **`CoadjointOrbit/Quotient.lean`**: the quotient, its diffeomorphism with
   the product's zero-level quotient, the reduced form with its formula, the
   dimension, and the milestone *Reduction at a coadjoint orbit and the
   shifting construction*. Waits for issue 4.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 5.3.11, Propositions 5.4.13 and 5.4.15, Remark 5.4.14.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001],
  Lecture 23.
