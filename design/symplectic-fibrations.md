# Symplectic fibrations

This is the detailed design of part 48 of `DESIGN.md`, *Symplectic
fibrations*. It covers two milestones of `atlas/symplectic-fibrations.md`:
*Fibrations with symplectic fibres are symplectic fibrations* and
*Symplectic connections correspond to vertically closed 2-forms*. Both
follow McDuff–Salamon [McDuffSalamon2017], §6.1 (Definition 6.1.2, Lemma
6.1.3) and §6.3 (equation (6.3.4), Lemma 6.3.5, Exercise 6.3.6), with
Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], Theorems 1.2.4 and
1.2.5, and Seidel [Seidel1997Thesis], Lemma 7.2. The part also lays the
groundwork for parts 49, 51 and 53–56: smooth atlases of a map, their
structure groups, and forms that restrict to the fibre forms.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. All statements about Mathlib, Tau Ceti and the library were
checked against the versions pinned when this file was written (Tau Ceti
`c9d170eed5a8`). Names from *Parallel transport* are those that its design
gives (`design/parallel-transport.md`).

## Setting and notation

- **Manifolds.** The base `B`, the total space `M` and the model fibre `F`
  are modelled by `IB : ModelWithCorners ℝ EB HB`,
  `IM : ModelWithCorners ℝ EM HM` and `IF : ModelWithCorners ℝ EF HF`, on
  finite-dimensional spaces, with `[IsManifold _ ∞ _]`. Statements that use
  parallel transport also assume `[IB.Boundaryless]`, `[IM.Boundaryless]`,
  `[T2Space B]` and `[T2Space M]`, as *Parallel transport* does. The map is
  `π : M → B`.
- **Atlases.** An atlas of `π` with fibre `F` is Tau Ceti's
  `A : TauCeti.MapFiber.Atlas F π` (`Topology/FiberBundle/MapFiber.lean`),
  a trivialization `A.trivAt b : Bundle.Trivialization F π` whose base set
  contains `b`, for every `b`. It is smooth when
  `hA : A.IsContMDiff ∞ IB IF IM` (`Geometry/Manifold/FiberBundle/MapFiber.lean`):
  each `A.trivAt b` is smooth on its source with a smooth inverse on its
  target. This is the smooth fibration of *Fibrations, connections and
  diffeomorphism groups*.
- **Fibre inclusions.** The fibre over `b'` read through a chart `e` with
  `hb' : b' ∈ e.baseSet` is the library's
  `Bundle.Trivialization.fiberInclusion e hb' : C(F, M)`,
  `v ↦ e.symm (b', v)` (`Topology/FiberBundle/Basic.lean`), as the note of
  the review of #2280 asked.
- **Forms.** Forms are Tau Ceti's `SmoothForm` and `SmoothTwoForm`. A
  condition on a pull-back along a map that is smooth only under a
  hypothesis is stated with the rough pull-back `TauCeti.mpullback` of
  `τ.val`, so that the statement carries no proof of smoothness. The fibre
  form is `σ : SmoothTwoForm IF F`, with `σ.IsSymplectic` where the page
  asks for a symplectic fibre. The vertical space at `x` is
  `(mfderiv IM IB π x).ker`.
- **Signs.** The page's bracket is Mathlib's `VectorField.mlieBracket`, and
  no Hamiltonian vector field or moment map enters this part, so no sign
  changes (*Fibrations, connections and diffeomorphism groups*).

## Decisions

These settle the points that `DESIGN.md` leaves to this file.

- **No structure `FiberAtlas`.** Tau Ceti already has the atlas
  (`TauCeti.MapFiber.Atlas`, indexed by the points of `B`) and its
  smoothness (`TauCeti.MapFiber.Atlas.IsContMDiff`), with the fibre bundle
  of a map (`fiberBundle`, `contMDiffFiberBundle`) and the diffeomorphism
  with its charted total space (`totalSpaceDiffeomorph`). A new structure
  would repeat it, so the part adds predicates on Tau Ceti's atlas instead,
  in the namespace `TauCeti.MapFiber.Atlas`, as `AGENTS.md` asks for
  declarations on Tau Ceti's types. The name `SymplecticGeometry.FiberAtlas`
  of `DESIGN.md` is replaced by `TauCeti.MapFiber.Atlas` there.
- **Structure groups.** A structure group is a subgroup
  `H : Subgroup (F ≃ₘ^n⟮IF, IF⟯ F)`. Coordinate changes are compared between
  two atlases, `A.CoordChangeMem A' H`; the structure group of one atlas is
  the case `A' = A`. A reduction of the structure group of `A` from `H` to
  `K` is an atlas `A'` with `A'.HasStructureGroup K` and
  `A.CoordChangeMem A' H`: the conjunction is written out, with no
  definition, since it has no API of its own. Any two smooth atlases are
  compatible through the whole group (`coordChangeMem_top`), so a smooth
  atlas with structure group `K` is a reduction of every smooth atlas to `K`.
- **Oriented and symplectic atlases** are `A.HasStructureGroup` of Tau
  Ceti's `Diffeomorph.orientationPreservingSubgroup` for an orientation
  `oF : TauCeti.Manifold.Orientation IF F ι` and of
  `TauCeti.SmoothForm.diffeomorphStabilizer σ`. No predicate is added for
  either.
- **Place.** The atlas and structure-group material does not mention
  symplectic forms, so it goes under `Geometry/Manifold/FiberBundle/`, as
  the review of #2280 suggested. The files under
  `Geometry/Symplectic/Fibration/` keep what concerns forms.
- **Fibres as manifolds.** No fibre is given a manifold structure of its
  own: fibres are read through `fiberInclusion`. Tau Ceti's
  `TauCeti.ManifoldTotalSpace.fiberChartedSpace` and
  `TauCeti.chartedSpaceOfExistsTrivialization` are not used (`M` is already
  a manifold), nor is `TauCeti.fiberBundleCoreOfGroupCocycle` (the bundle
  is given, not glued). Tau Ceti's `TauCeti.verticalForm` gives the
  families of forms on `F` in `LocalForm.lean`.
- **Connected base.** `SymplecticFibres.lean` needs a connected base, as
  the review of #2280 noted. The milestone assumes `M` compact and
  connected. Connectedness of `M` makes it nonempty, so `F` is nonempty and
  `π` is onto. Then `B`, the image of `M` under `π`, is connected. So the
  milestone needs no hypothesis on `B` beyond the setting.
- **Generality of the connection milestone.** The direction "vertically
  closed ⇒ symplectic transport" is proved for any two-form that is
  vertically closed and nondegenerate on the vertical spaces, read in any
  smooth charts, with no symplectic atlas. This is the page's remark that
  the first proof needs no symplectic fibration, and it is what
  `SymplecticFibres.lean` uses. The milestone is then stated for a
  symplectic atlas, as on the page.
- **Departure from `DESIGN.md` in files.** The atlases move from
  `Fibration/Basic.lean` to `Geometry/Manifold/FiberBundle/MapFiber.lean`
  and `StructureGroup.lean`. `Fibration/Connection.lean` is split: the
  connection $\mathrm{Ver}^\tau$ and connection two-forms, which need no
  parallel transport, go to `Fibration/HorizontalDistribution.lean`;
  symplectic connections and the milestone stay in `Connection.lean`.
  `DESIGN.md` is corrected in the same pull request.

## Files

### `Geometry/Manifold/FiberBundle/MapFiber.lean`

The library's counterpart of Tau Ceti's file of that name: smooth atlases
of a map, read pointwise. About 300 lines.

- `Bundle.Trivialization.contMDiff_fiberInclusion`: if `e.symm` is smooth
  on `e.target`, then `e.fiberInclusion hb` is smooth.
- `Bundle.Trivialization.injective_mfderiv_fiberInclusion` and
  `range_mfderiv_fiberInclusion`: for a trivialization smooth with smooth
  inverse, the derivative of `e.fiberInclusion hb` at `v` is injective, and
  its range is the vertical space `(mfderiv IM IB π x).ker` at
  `x = e.fiberInclusion hb v`. This links pull-backs along fibre inclusions
  to pointwise conditions on vertical vectors.
- `Bundle.Trivialization.coordChangeDiffeomorph`: for two such
  trivializations and `b` in both base sets, the diffeomorphism
  `F ≃ₘ⟮IF, IF⟯ F` with `coe_coordChangeDiffeomorph`
  (`⇑(…) = e.coordChange e' b`) and `coordChangeDiffeomorph_symm`.
- `TauCeti.MapFiber.Atlas.IsContMDiff.isSubmersion`: for `1 ≤ n` and a
  boundaryless `M`, `π` is a submersion, `Manifold.IsSubmersion IM IB n π`,
  from `isRegularPoint_proj` at every point, by Tau Ceti's
  `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv`.
- The bridge from Tau Ceti's smooth fibre bundles:
  `TauCeti.ManifoldTotalSpace.mapFiberAtlas F E`, the atlas of the projection
  `fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj` with
  `trivAt b := (trivializationAt F E b).compHomeomorph (homeomorph F E).symm`
  (Mathlib's `Bundle.Trivialization.compHomeomorph`), with
  `isContMDiff_mapFiberAtlas` under `[ContMDiffFiberBundle ∞ F E IB IF]`
  (from `contMDiffOn_trivialization` and `contMDiffOn_trivialization_symm`)
  and `coordChange_mapFiberAtlas` (the bundle's coordinate changes). Tau
  Ceti's associated bundles are smooth fibre bundles by
  `TauCeti.AssociatedBundle.contMDiffFiberBundle`, so the bridge covers
  them too.

### `Geometry/Manifold/FiberBundle/StructureGroup.lean`

Structure groups of atlases and their reductions. About 250 lines.

- `TauCeti.MapFiber.Atlas.CoordChangeMem A A' H`: for all `b b' x` with
  `x` in the base sets of `A.trivAt b` and `A'.trivAt b'`, some `φ ∈ H` has
  `⇑φ = (A.trivAt b).coordChange (A'.trivAt b') x`; with
  `coordChangeMem_iff`.
- `TauCeti.MapFiber.Atlas.HasStructureGroup A H := A.CoordChangeMem A H`,
  with `hasStructureGroup_iff`.
- API: `coordChangeMem_top` for smooth atlases (from
  `coordChangeDiffeomorph`), `CoordChangeMem.mono`, `CoordChangeMem.symm`,
  `CoordChangeMem.trans` (through the chart of the middle atlas at the
  point, by Mathlib's `Bundle.Trivialization.coordChange_coordChange`), and
  `HasStructureGroup.mono`. So compatibility through `H` is an equivalence
  relation on the atlases with structure group `H`.
- `TauCeti.AssociatedBundle.hasStructureGroup_mapFiberAtlas`: if a subgroup
  `H` contains Mathlib's `Diffeomorph.smul IG IF ∞ g` for every `g : G`,
  the atlas of an associated bundle `AssociatedBundle G P F` has structure
  group `H`. Its coordinate changes act by the elements
  `e.coordChange e' b 1` of `G`. This gives oriented atlases from
  orientation-preserving actions and symplectic atlases from symplectic
  actions.

### `Geometry/Manifold/FiberBundle/RestrictsTo.lean`

Forms that restrict to the fibre forms. Nothing in it needs `σ` to be
symplectic.

- `TauCeti.MapFiber.Atlas.RestrictsTo A σ τ`, for
  `σ : SmoothForm IF F ℝ k` and `τ : SmoothForm IM M ℝ k`: for every `b`,
  every `b'` and every `hb' : b' ∈ (A.trivAt b).baseSet`,
  `TauCeti.mpullback IF IM ((A.trivAt b).fiberInclusion hb') τ.val = σ.val`.
  This is the predicate of *Fibre forms* in `DESIGN.md`, $\iota_b^*\tau=\sigma_b$.
  With `restrictsTo_iff`.
- Independence of the chart: `restrictsTo_iff_forall_exists`, for an
  atlas with structure group `diffeomorphStabilizer σ`: it is enough that
  one chart at each point pull `τ` back to `σ` (by
  `fiberInclusion_coordChange`). `RestrictsTo.of_coordChangeMem`: the
  predicate passes to an atlas compatible with `A` through
  `diffeomorphStabilizer σ`, so it depends only on the fibre forms, as the
  page's note on the definition says.
- `RestrictsTo.hasStructureGroup`: a smooth atlas along which some `τ`
  restricts to `σ` has structure group `diffeomorphStabilizer σ`, since
  each coordinate change pulls $\sigma$ back to itself. This is how
  `SymplecticFibres.lean` produces its symplectic atlas.
- Affine structure: `Bundle.Trivialization.mpullback_fiberInclusion_mpullback_eq_zero` (for
  `k ≥ 1`, `π^*β` pulls back to zero along fibre inclusions, since
  `π ∘ fiberInclusion` is constant), `restrictsTo_add_iff` (if `τ`
  restricts to `σ`, then `τ + β` does exactly when `β` pulls back to zero
  on every fibre), `RestrictsTo.add_mpullback` (Thurston's $\tau+K\pi^*\beta$,
  for part 49), and `convex_setOf_restrictsTo`.

### `Geometry/Symplectic/Fibration/Basic.lean`

Vertically nondegenerate forms and compatible symplectic forms. It imports
`FiberBundle/RestrictsTo.lean`.

- `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate π τ`: for every `x`,
  `((τ.bilinFormAt x).restrict (mfderiv IM IB π x).ker).Nondegenerate`. It
  says that every fibre is a symplectic submanifold when `τ` is closed.
  `RestrictsTo.isVerticallyNondegenerate`: under `hA`, a form that
  restricts to a nondegenerate `σ` is vertically nondegenerate (by
  `range_mfderiv_fiberInclusion`); and the converse
  `IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusion`.
- Compatible symplectic forms for a symplectic atlas are written
  `ω.IsSymplectic ∧ A.RestrictsTo σ ω`, with no definition: Definition
  6.1.2 of [McDuffSalamon2017].
- Compatible forms for an oriented atlas (Definition 6.2.1),
  `TauCeti.MapFiber.Atlas.IsOrientedCompatible hA oB oF ω`, for
  `oB : Manifold.Orientation IB B (Fin m)`,
  `oF : Manifold.Orientation IF F (Fin (2 * k))` and `dim M = 2 * n`, a
  structure with three fields: `ω.IsSymplectic`; on each fibre, the smooth
  pull-back of `ω` along `fiberInclusion` (smooth by `hA`) is nondegenerate
  and its `IsNondegenerate.volumeOrientation` is `oF`; and each chart
  `A.trivAt b` preserves orientation at every point of its source, Tau
  Ceti's `IsOrientationPreservingAt`, from the symplectic orientation
  `hω.isNondegenerate.volumeOrientation` of `M` to
  `oB.prod oF` (Tau Ceti's product orientation, reindexed along
  `2 * n = m + 2 * k`). The fibre has even dimension, so the order of the
  factors in the product does not matter. It takes `hA` because the
  fibre forms must be smooth forms to have a symplectic orientation. Used
  by `IsOrientedCompatible.isVerticallyNondegenerate` here and by the
  corollary of `SymplecticFibres.lean`, and by parts 49 and 56.

### `Geometry/Symplectic/Fibration/HorizontalDistribution.lean`

The connection $\Gamma_\tau$ of a two-form, and connection two-forms; no
parallel transport. About 550 lines.

- `TauCeti.SmoothTwoForm.IsVerticallyClosed π τ`: for every `x`, all
  vertical `η₁ η₂` and every `v`, `mextDeriv τ.val x ![η₁, η₂, v] = 0`; with
  `isVerticallyClosed_iff`, `IsClosed.isVerticallyClosed`,
  `IsVerticallyClosed.add`, `IsVerticallyClosed.smul`, and
  `isVerticallyClosed_add_mpullback_iff` (adding `π^*β` changes nothing,
  since `d(π^*β)` vanishes on two vertical vectors).
- `TauCeti.SmoothTwoForm.horizontalDistribution π τ x :=
  (τ.bilinFormAt x).orthogonal (mfderiv IM IB π x).ker`, Mathlib's
  orthogonal of the vertical space: the page's
  $\mathrm{Hor}_x=\mathrm{Ver}_x^{\tau}$ (equation (6.3.4)), with
  `mem_horizontalDistribution_iff`.
- `IsVerticallyNondegenerate.isEhresmannConnection`: for a smooth
  submersion `π` (`Manifold.IsSubmersion IM IB ∞ π`) and a vertically
  nondegenerate `τ`, `TauCeti.IsEhresmannConnection IM IB ∞ π
  (τ.horizontalDistribution π)`. The complement condition is Mathlib's
  `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`
  (an alternating form is reflexive). For smoothness and rank, take near a
  point a frame of the vertical spaces (Tau Ceti's
  `Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`) and smooth
  lifts of a frame of the base. Subtracting from each lift its projection
  onto the vertical spaces along the orthogonal (the library's
  `LinearAlgebra/BilinearForm/Orthogonal.lean`) gives a frame of the
  horizontal spaces. The coefficients of that projection solve a linear
  system whose matrix, the values of `τ` on the vertical frame, is
  invertible and smooth.
- `horizontalDistribution_eq_iff`: two vertically nondegenerate forms that
  agree on pairs of vertical vectors define the same connection exactly
  when their difference vanishes on `(η, v)` for every vertical `η`. The
  pointwise statement is a new lemma `LinearMap.BilinForm.orthogonal_eq_orthogonal_iff`
  in the library's `LinearAlgebra/BilinearForm/Orthogonal.lean`.
- `exists_restrictsTo_horizontalDistribution_eq`: for a smooth atlas with
  structure group `diffeomorphStabilizer σ`, `σ` nondegenerate
  (`hσ : σ.IsNondegenerate`), and an Ehresmann connection
  `hD : TauCeti.IsEhresmannConnection IM IB ∞ π D`, the form whose value at
  `x` is the fibre form evaluated on the vertical parts of its arguments,
  the parts along `D x`, restricts to `σ` and has
  `τ.horizontalDistribution π = D`. In a chart `e` it is the pull-back of
  `σ` along `x ↦ (e x).2` composed with the projection onto the vertical
  spaces, which is smooth since `D` is. The charts agree on overlaps since
  their coordinate changes preserve `σ`. The hypothesis `hσ` is needed:
  for `σ = 0` the form is zero, and its horizontal distribution is the
  whole tangent space, not `D`, once the fibre has positive dimension.
  With `hσ` the form is vertically nondegenerate, and it vanishes on
  `(η, v)` for `η` vertical and `v ∈ D x`, so `D x` lies in its horizontal
  space; both are complements of the vertical space, so they agree.
- Connection two-forms. `exists_restrictsTo_isVerticallyClosed`: for a
  smooth atlas with structure group `diffeomorphStabilizer σ`, `σ` closed,
  and `B` Hausdorff and σ-compact, some `τ` restricts to `σ` and is
  vertically closed. This is Exercise 6.3.6 of [McDuffSalamon2017] and
  Theorem 1.2.5 of [GuilleminLermanSternberg1996]: the sum over a smooth
  partition of unity `ρ` of `B` subordinate to the base sets of
  `(ρ i ∘ π) • (pull-back of σ along x ↦ (e_i x).2)`. It is smooth by the
  Tau Ceti's `TauCeti.isSmoothForm_sum_finsupport_smul_mpullback`.
  It restricts to `σ` because the weights sum to one and each chart pulls
  back to `σ`. For vertical closedness write `θ_i` for the pull-back of
  `σ` along `x ↦ (e_i x).2`; it is closed, as `σ` is. So the derivative of
  the sum is `Σ_i d(ρ i ∘ π) ∧ θ_i`. On `(η₁, η₂, v)` with `η₁`, `η₂`
  vertical, a single term need not vanish: it leaves
  `d(ρ i ∘ π)(v) · θ_i(η₁, η₂)`. But since the structure group is
  `diffeomorphStabilizer σ`, all the `θ_i` take the same value on a
  vertical pair, the value of the fibre form, and
  `Σ_i d(ρ i ∘ π) = d(Σ_i ρ i ∘ π) = d 1 = 0`, so the sum vanishes. This is
  where the structure-group hypothesis is used. Also
  `convex_setOf_restrictsTo_isVerticallyClosed`.

### `Geometry/Symplectic/Fibration/Connection.lean`

Symplectic connections and the milestone. Waits for *Parallel transport*.
About 450 lines.

- `TauCeti.IsEhresmannConnection.IsSymplectic hD A σ`: for every smooth
  curve `γ : ℝ → B`, all times `s t` and all `b b'` with `γ s` in the base
  set of `A.trivAt b` and `γ t` in that of `A.trivAt b'`,
  `TauCeti.mpullback IF IF (hD.parallelTransportIn (A.trivAt b) (A.trivAt b') γ s t) σ.val = σ.val`.
  The page's symplectic connection, with transport read in the charts of
  the atlas, as *Fibrations, connections and diffeomorphism groups* says. A
  proper `π` is needed for transport, and a compact `F` gives it by Tau
  Ceti's `TauCeti.isProperMap_of_forall_exists_trivialization`.
  `isSymplectic_iff_forall_exists`: for a symplectic atlas one pair of
  charts per curve suffices, by `parallelTransportIn_coordChange`.
- `IsVerticallyClosed.mpullback_parallelTransportIn`: for `π` proper, `hA`,
  and `τ` vertically closed and vertically nondegenerate, transport by
  `τ.horizontalDistribution π` along `γ` from `s` to `t`, read in charts
  `e e'` of `A`, pulls the pull-back of `τ` along
  `e'.fiberInclusion (γ t)` back to its pull-back along
  `e.fiberInclusion (γ s)`. No structure group is assumed. The transport is
  the flow of the horizontal lift of a compactly supported time-dependent
  field (`parallelTransport_eq_timeDependentFlowOf`). The derivative in
  time of the pulled-back form is the pull-back of the Lie derivative
  along that lift (Tau Ceti's `hasDerivAt_mpullback_eulerianField`,
  `Geometry/Manifold/DifferentialForm/Flow/Eulerian.lean`). By Cartan's
  formula (`TauCeti.SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add`)
  this is $\iota(v^\sharp)d\tau+d\,\iota(v^\sharp)\tau$. On vertical vectors
  the first term vanishes by vertical closedness. The second is the
  derivative of a form that vanishes on vertical vectors, since
  $v^\sharp$ is horizontal, so its pull-back to a fibre is zero.
- The milestone, `IsEhresmannConnection.isSymplectic_iff_isVerticallyClosed`:
  for `[CompactSpace F]`, `hA`, `A.HasStructureGroup (diffeomorphStabilizer σ)`,
  `σ.IsSymplectic` and `hτ : A.RestrictsTo σ τ`, the connection
  `(hτ.isVerticallyNondegenerate hA _).isEhresmannConnection
  (hA.isSubmersion ENat.LEInfty.out)`
  is symplectic exactly when `τ.IsVerticallyClosed π`. Its docstring ends
  with "Milestone: *Symplectic connections correspond to vertically closed
  2-forms*." One direction is the previous item. For the other, the time
  derivatives above vanish, so $d\tau(v^\sharp,\eta_1,\eta_2)=0$ for
  every horizontal lift, through curves with any given velocity. Also
  $d\tau$ vanishes on three vertical vectors, because $\sigma$ is closed and
  the fibre inclusions span the vertical spaces. A vector is the sum of
  its horizontal and vertical parts.
- `IsSymplectic.exists_restrictsTo_isVerticallyClosed`: every symplectic
  connection is $\Gamma_\tau$ for a connection two-form, from
  `exists_restrictsTo_horizontalDistribution_eq` and the milestone.

### `Geometry/Symplectic/Fibration/LocalForm.lean`

The local form of a two-form in a chart, reused by *Coupling forms*. About
350 lines.

The setting is a two-form `τ` on the product `EB × F`, modelled by
`𝓘(ℝ, EB).prod IF`, over an open set `U ×ˢ univ`. It is the pull-back of a
form on `M` along `A.trivAt b`'s inverse composed with a chart of `B`. A
basis `bs : Basis ι ℝ EB` gives coordinates `x i := bs.coord i` and
constant fields `∂ i := bs i`.

- The components, as families indexed by `x ∈ U` and read through
  `TauCeti.verticalForm`: the slices $\sigma(x)=\iota_x^*\tau$, the
  one-forms $\alpha_i(x)$ (the slices of $\iota(\partial_i,0)\tau$), and the
  functions $f_{ij}=\tau((\partial_i,0),(\partial_j,0))$. Then
  `eq_verticalForm_add_sum`: on `U ×ˢ univ`,
  $\tau=\sigma+\sum_i\alpha_i\wedge dx_i+\sum_{i<j}f_{ij}\,dx_i\wedge dx_j$,
  with the forms on `EB` and `F` pulled back along the projections and the
  sign of $\alpha_i$ fixed by this formula, as on the page.
- `isVerticallyClosed_iff_local`: on `U ×ˢ univ`, `τ` is vertically closed
  for `Prod.fst` exactly when every $\sigma(x)$ is closed and
  $\partial_i\sigma(x)+d_F\alpha_i(x)=0$ for every `i`,
  where $d_F$ is the exterior derivative of `F`
  (equations (6.3.5)–(6.3.7) of [McDuffSalamon2017]).
- `horizontalLift_local`: when every $\sigma(x)$ is nondegenerate, the lift
  of `∂ i` for `τ.horizontalDistribution Prod.fst` at `(x, v)` is
  `(∂ i, X i x v)`, where `X i x` is the vector field on `F` with
  $\iota(X_i)\sigma(x)=\alpha_i(x)$. It is smooth in `(x, v)`, by
  inverting $\sigma(x)$ (Tau Ceti's `IsNondegenerate.symplecticFormAt`).

### `Geometry/Symplectic/Fibration/SymplecticFibres.lean`

The first milestone, by the page's second route. Waits for *Parallel
transport*, including its radial trivializations. About 400 lines.

- `exists_hasStructureGroup_restrictsTo_of_isVerticallyClosed`: let `M` be
  compact and connected, `hA` hold, and let `τ` be vertically closed and
  vertically nondegenerate. Then there are `σ : SmoothTwoForm IF F` with
  `σ.IsSymplectic` and a smooth atlas `A'` of `π` with
  `A'.HasStructureGroup (diffeomorphStabilizer σ)` and `A'.RestrictsTo σ τ`.
  `π` is proper since `M` is compact. Fix `b₀` and let `σ` be the pull-back
  of `τ` along `(A.trivAt b₀).fiberInclusion`; it is closed by vertical
  closedness and nondegenerate by `IsVerticallyNondegenerate`. Near any
  `b`, *Parallel transport*'s
  `IsEhresmannConnection.exists_trivialization_parallelTransport` for
  `τ.horizontalDistribution π` gives a smooth trivialization by transport
  along rays from `b`. By `IsVerticallyClosed.mpullback_parallelTransportIn`
  it pulls `τ` back to the fibre form over `b` at every point. The set of
  `b` whose fibre form is carried to `σ` by a diffeomorphism of `F` is
  therefore open, and so is its complement. Since `B` is connected (see
  *Decisions*), it is all of `B`. Each radial trivialization, composed in
  the fibre with such a diffeomorphism (Mathlib's
  `Bundle.Trivialization.transFiberHomeomorph`, smooth with smooth
  inverse), is the chart of `A'` at `b`. `RestrictsTo.hasStructureGroup`
  gives the structure group.
- The milestone, `exists_hasStructureGroup_restrictsTo`: the case of a
  symplectic `ω` with `ω.IsVerticallyNondegenerate π`, that is, every fibre
  a symplectic submanifold. Its docstring ends with "Milestone:
  *Fibrations with symplectic fibres are symplectic fibrations*." The atlas
  `A'` is compatible with `A` through the whole group by
  `coordChangeMem_top`, so it is a reduction of `A` in the page's sense.
- `IsOrientedCompatible.exists_hasStructureGroup_restrictsTo`: the same
  for a form compatible with an oriented atlas, which parts 49 and 56 use.

## What other parts use

- *Compatible symplectic forms*: `RestrictsTo`, `RestrictsTo.add_mpullback`,
  `IsOrientedCompatible`, `IsVerticallyNondegenerate.isEhresmannConnection`
  ($\mathrm{Hor}=\mathrm{Ver}^\tau$ in Thurston's step 2), symplectic and
  oriented atlases, and reductions of the structure group (`Surface.lean`).
- *Integration over the fibre*: smooth atlases with an oriented structure
  group, from `StructureGroup.lean`; its operator becomes
  `TauCeti.MapFiber.Atlas.fiberIntegral`.
- *Coupling forms*: `IsVerticallyClosed`, connection two-forms and their
  existence, `IsEhresmannConnection.IsSymplectic`, the milestone, and
  `LocalForm.lean`.
- *Hamiltonian fibrations*: reductions of the structure group to
  `TauCeti.SmoothForm.hamiltonianGroup σ`, as `HasStructureGroup` and
  `CoordChangeMem`.
- *Sphere bundles over surfaces*: oriented atlases and
  `IsOrientedCompatible`.
- *Principal connections*: the bridge for associated bundles and
  `TauCeti.AssociatedBundle.hasStructureGroup_mapFiberAtlas`, where a
  statement needs the atlas of $P\times_GF$.

The part uses no other unmerged part than *Parallel transport*, and that
only in `Connection.lean` and `SymplecticFibres.lean`.

## Building issues

In the order they can be done; each is one pull request of a few hundred
lines.

1. **Smooth atlases of a map.** `Geometry/Manifold/FiberBundle/MapFiber.lean`.
   Waits for nothing.
2. **Structure groups.** `Geometry/Manifold/FiberBundle/StructureGroup.lean`.
   Waits for 1.
3. **Forms restricting to the fibre forms.**
   `Geometry/Manifold/FiberBundle/RestrictsTo.lean` and
   `Fibration/Basic.lean`. Waits for 2.
4. **The connection of a two-form.** The lemma
   `LinearMap.BilinForm.orthogonal_eq_orthogonal_iff` and the first four
   items of `Fibration/HorizontalDistribution.lean`. Waits for 3.
5. **Connection two-forms.** The rest of
   `Fibration/HorizontalDistribution.lean`. Waits for 4.
6. **The local form.** `Fibration/LocalForm.lean`. Waits for 4.
7. **Symplectic connections and vertically closed forms.**
   `Fibration/Connection.lean`. Waits for 5 and for *Parallel transport*'s
   transport in trivializations (`ParallelTransport/Smooth.lean`).
8. **Fibrations with symplectic fibres.** `Fibration/SymplecticFibres.lean`.
   Waits for 7 and for *Parallel transport*'s radial trivializations
   (`RadialTrivialization.lean`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Definitions 6.1.2 and 6.2.1, Lemma 6.1.3) and §6.3 (equations
  (6.3.4)–(6.3.7), Lemma 6.3.5, Exercise 6.3.6).
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity Diagrams*][GuilleminLermanSternberg1996],
  §1.2 (Theorems 1.2.4 and 1.2.5).
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis],
  Lemma 7.2.
* [M. J. Gotay, R. Lashof, J. Śniatycki, A. Weinstein, *Closed forms on symplectic fibre bundles*][GotayLashofSniatyckiWeinstein1983],
  Theorem 4.
