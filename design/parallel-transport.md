# Parallel transport

This is the detailed design of part 47 of `DESIGN.md`, *Parallel transport*.
The part has no milestone. It gives *Symplectic fibrations* and *Coupling
forms* (parts 48 and 53) what they need of Ehresmann connections on a
smooth map: horizontal lifts of curves of the base, parallel transport
between fibres and its readings in local trivializations, smooth dependence
on a family of curves, the local triviality of proper submersions by
transport along rays, and the curvature of a connection. It serves
`atlas/symplectic-fibrations.md`, §6.3 (connections, holonomy, symplectic
connections) and §6.4 (curvature), which follow McDuff–Salamon
[McDuffSalamon2017], §§6.1, 6.3 and 6.4 (Exercise 6.1.1, p. 266, and
pp. 275–279) and Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996],
§1.3. The general theory of connections on fibred manifolds that it builds is
that of I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in
Differential Geometry*, Springer (1993), §9, and the local triviality of a
proper submersion is C. Ehresmann's theorem (*Les connexions infinitésimales
dans un espace fibré différentiable*, Colloque de topologie, Bruxelles
(1950), 29–55), both cited by Tau Ceti's `EhresmannConnection.lean`.

All new files are in Tau Ceti's folder `Geometry/Manifold/Submersion/`, beside
`EhresmannConnection.lean`; paths of new files are under
`SymplecticGeometry/`, Tau Ceti paths under `.lake/packages/TauCeti/TauCeti/`.
Every new declaration is about Tau Ceti's notions, so it is in the namespace
`TauCeti.IsEhresmannConnection` (dot notation on a proof
`hD : TauCeti.IsEhresmannConnection I J ∞ f D`), `Manifold.IsSubmersion` or
`TauCeti`, as `AGENTS.md` asks, and could move to Tau Ceti unchanged.

## Setting

As in Tau Ceti's file, `P` is the total space, modelled by
`I : ModelWithCorners ℝ E H`, and `B` the base, modelled by
`J : ModelWithCorners ℝ F G`, both with finite-dimensional models,
`[IsManifold I ∞ P]`, `[IsManifold J ∞ B]`, `[I.Boundaryless]`,
`[J.Boundaryless]`, `[T2Space P]` and `[T2Space B]`. The map is `f : P → B`
with `hf : ContMDiff I J ∞ f`, and the connection is
`hD : TauCeti.IsEhresmannConnection I J ∞ f D`; Tau Ceti's predicate gives
only differentiability of `f`, so `hf` is a separate hypothesis. A curve of
the base is `γ : ℝ → B` with `hγ : ContMDiff 𝓘(ℝ) J ∞ γ`, and its velocity
at `u` is `mfderiv 𝓘(ℝ) J γ u 1`. A curve `c : ℝ → P` is horizontal when
`TauCeti.IsHorizontalMap 𝓘(ℝ) D c` (`Distribution/Horizontal.lean`); no new
predicate is introduced for horizontal curves or lifts.

The points of `DESIGN.md` that the part's design decides:

- **Proper submersions.** Existence of transport is stated for a proper map,
  `hfp : IsProperMap f`; uniqueness of lifts needs no properness. A fibration
  with compact fibre in the sense of *Fibrations, connections and
  diffeomorphism groups* is proper by Tau Ceti's
  `TauCeti.isProperMap_of_forall_exists_trivialization`
  (`Topology/FiberBundle/Proper.lean`), and a map from a compact space to a
  Hausdorff one is proper by Mathlib; so the pages' closed total spaces are
  covered either way, and no version for locally trivial maps is made.
  Surjectivity of `f` is never assumed: Tau Ceti's connection only asks for
  surjective derivatives.
- **Curves over `ℝ`.** Transport runs along smooth curves `ℝ → B` from a time
  `s` to a time `t`, the model *Over `ℝ`* of *Manifolds, families and signs*,
  so that Tau Ceti's time-dependent flows apply directly. It depends only on
  the curve on `Set.uIcc s t` (`parallelTransport_congr`), which is how a path
  on `[0, 1]` that extends smoothly, or a reparametrized concatenation, is
  used. A concatenation `Path.trans` is not smooth in general; a later part
  that concatenates reparametrizes each piece by `Real.smoothTransition`
  first, and `parallelTransport_comp` with `parallelTransport_congr` give
  the transport of the result.
- **Fibres.** The fibres stay subsets `f ⁻¹' {b}` of `P`. Transport is a map
  `P → P`, and "a diffeomorphism between fibres" is stated twice: as the
  restriction of a diffeomorphism of `P` that carries one fibre onto the other
  (`exists_diffeomorph_eqOn_parallelTransport`), and, in local
  trivializations `e e' : Bundle.Trivialization Z f`, as a diffeomorphism of
  the model fibre `Z` (`parallelTransportIn`), the reading that
  *Fibrations, connections and diffeomorphism groups* prescribes. The only
  statement that needs a fibre as a manifold of its own is the local
  triviality of a proper submersion, whose fibre has no other name; it uses
  Tau Ceti's regular-fibre atlas `TauCeti.regularFiberChartedSpace`
  (`Geometry/Manifold/RegularValue/ManifoldLevel.lean`), the atlas of a
  level set of a submersion. `TauCeti.ManifoldTotalSpace.fiberChartedSpace`
  is the atlas of a fibre of a fibre bundle and is not used here.
- **Smoothness in parameters.** What the radial trivialization needs, and all
  that later parts need, is the local smoothness of transport along a smooth
  family `Γ : N × ℝ → B` of curves in the parameter and the point
  (`exists_contMDiff_parallelTransport_param`). It comes from the merged
  library file `Geometry/Manifold/Flow/TimeDependent.lean` of *Smooth
  families* (`TauCeti.contMDiff_timeDependentFlowOf_param`).
- **Holonomy** (the note of the review of #2280: parts 47, 48 or 53). The
  holonomy around a loop `γ` at `b`, read in a trivialization `e` at `b`, is
  `hD.parallelTransportIn e e γ 0 1` of this part, a diffeomorphism of the
  fibre `Z`; no separate definition is made. Part 48 states symplectic
  transport with `parallelTransportIn`, and part 53's `Holonomy.lean` keeps
  what concerns symplectic charts, Hamiltonian holonomy and flux. The change
  of trivialization is `parallelTransportIn_coordChange`, so that the
  independence of the chart in *Fibrations, connections and diffeomorphism
  groups* is one rewrite.
- **Flatness** (the second note of that review). Flatness is stated with Tau
  Ceti's `TauCeti.IsInvolutiveDistribution`; the part proves no Frobenius
  theorem and needs no foliation API, since no later part uses flat
  connections beyond the equivalence of `Curvature.lean`.

## What exists

Tau Ceti has the connection and the pointwise lift
(`TauCeti.IsEhresmannConnection`, `horizontalLift`, `mfderiv_horizontalLift`,
`eq_horizontalLift_iff`) and the existence of connections on submersions from
a σ-compact manifold (`Manifold.IsSubmersion.exists_isEhresmannConnection`),
all in `Submersion/EhresmannConnection.lean`; horizontal maps
(`TauCeti.IsHorizontalMap`); time-dependent flows with uniqueness, joint
smoothness, the escape criterion and completeness for compactly supported
fields (`TauCeti.timeDependentFlowOf`, `timeDependentFlowOf_eq_of_hasMFDerivAt`,
`mem_timeDependentFlowDomain_of_isCompact_of_mapsTo`,
`isCompleteVectorField_timeDependentSuspensionField`,
`timeDependentFlowDiffeomorph`, `Flow/TimeDependent.lean`); the library adds
smoothness in a parameter and uniqueness on intervals
(`TauCeti.contMDiff_timeDependentFlowOf_param`,
`TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`); naturality of the
bracket under related fields
(`ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`,
`Distribution/Kernel.lean`, and `VectorField/Related.lean`); involutive and
smooth distributions with local frames (`Distribution.lean`); and regular
fibres as manifolds (`RegularValue/ManifoldLevel.lean`). Tau Ceti's Riemannian
submersions have horizontal lifts of fields for the metric complement only
(`Riemannian/Submersion/Connection.lean`), not for an arbitrary connection.

Neither Mathlib nor Tau Ceti has horizontal lifts of curves, parallel
transport, the curvature of an Ehresmann connection, or the direction of
Ehresmann's theorem from a proper submersion to local trivializations (the
atlas's correspondence page records this for Exercise 6.1.1).

## Files

### `Geometry/Manifold/Submersion/HorizontalLiftField.lean`

Horizontal lifts of vector fields and their smoothness.

- `TauCeti.IsEhresmannConnection.contMDiff_horizontalLift`: for a manifold
  `Q`, smooth maps `g : Q → P` and `w : Q → TangentBundle J B` with
  `(w q).proj = f (g q)`, the map
  `q ↦ (⟨g q, hD.horizontalLift (g q) (w q).2⟩ : TangentBundle I P)` is
  smooth (`C^∞`, or `C^n` from `C^(n+1)` data). Near a point, `D` has a
  smooth frame (Tau Ceti's `IsContMDiffDistribution`), its image under `df`
  is a frame of `TB` along `f`, and the coefficients of `w` in it are smooth
  by inverting the matrix of that frame in a chart. Every other smoothness
  statement of the part is a case of this one, with `Q` a product of `P`
  with times and parameters.
- `TauCeti.IsEhresmannConnection.horizontalLiftField hD V`, for
  `V : Π b : B, TangentSpace J b`: the field
  `x ↦ (hD.horizontalLift x (V (f x)) : TangentSpace I x)`, with
  `horizontalLiftField_def`, `horizontalLiftField_mem` (it lies in `D x`),
  `mfderiv_horizontalLiftField` (`df` maps it to `V (f x)`, so it is
  `f`-related to `V`), `horizontalLiftField_eq_zero` (where `V (f x) = 0`),
  `horizontalLiftField_add`, `horizontalLiftField_smul` (by a function on
  `B` composed with `f`), and `contMDiff_horizontalLiftField` for a smooth
  `V`, and jointly for a time-dependent `V : ℝ → Π b, TangentSpace J b`.
- The projection of an integral curve of a lifted time-dependent field is an
  integral curve of the field on `B` (the chain rule and
  `mfderiv_horizontalLiftField`). For `V` vanishing outside a compact `K` at
  all times and a proper `f`, the lift vanishes outside the compact
  `f ⁻¹' K`, so its suspension is complete by Tau Ceti's
  `isCompleteVectorField_timeDependentSuspensionField`; this needs no lemma
  of its own.

About 300 lines.

### `Geometry/Manifold/Submersion/ParallelTransport/Basic.lean`

Horizontal lifts of curves and parallel transport.

- `TauCeti.IsEhresmannConnection.eqOn_of_isHorizontalMap` (uniqueness): two
  differentiable horizontal curves `c₁ c₂ : ℝ → P` with `f ∘ c₁ = γ = f ∘ c₂` on
  `Set.Icc a b`, for a `C²` curve `γ`, a `C²` map `f` and `1 ≤ n`, equal at one
  point of it, agree on it; with `Set.Icc a b`
  replaced by `univ` as `eq_of_isHorizontalMap`. The velocity of a horizontal
  curve over `γ` is `hD.horizontalLift (c u) (γ' u)` (`eq_horizontalLift_iff`),
  so near each time both curves solve one time-dependent equation, the lift of
  the field that is constant, equal to the chart velocity of `γ`, in a chart of
  `B`; local uniqueness for its suspension (Tau Ceti's
  `IsMIntegralCurveOn.eventuallyEq_of_isPreconnected`) and connectedness of the
  interval conclude.
- `TauCeti.IsEhresmannConnection.exists_isHorizontalMap_lift` (existence),
  under `hfp`, `1 ≤ n` and `f`, `γ` of class `C^(n+1)`: for `f x = γ s` there
  is `c : ℝ → P` with `ContMDiff 𝓘(ℝ) I n c`, `TauCeti.IsHorizontalMap 𝓘(ℝ) D c`,
  `f ∘ c = γ` and `c s = x`. On an interval that `γ` maps into one chart of `B`, `c` is a
  trajectory of the lift of the chart-constant field above, cut off by a bump
  function to compact support, which is complete since `f` is proper; its
  projection solves the base equation and so is `γ`. Uniqueness glues the
  pieces: the times up to which a lift exists form an open and closed set.
- `TauCeti.IsEhresmannConnection.parallelTransport hD γ s t : P → P`: at `x`,
  the value at `t` of the horizontal lift of `γ` through `x` at time `s`
  (chosen among differentiable horizontal curves `c` over `γ` on `Set.uIcc s t` with
  `c s = x`) when one exists, and `x` otherwise. API, with `hx : f x = γ s`
  where needed:
  - `parallelTransport_eq` (`hD.parallelTransport γ s t x = c t` for every
    such lift `c`; the characterization, used instead of the definition),
    `parallelTransport_mem_preimage` (it lies over `γ t`),
    `parallelTransport_self` (`s = t` gives `x`, with no hypothesis),
    `parallelTransport_parallelTransport` (from `s` to `t`, then from `t` to
    `u`, is from `s` to `u`), and so `bijOn_parallelTransport` and
    `invOn_parallelTransport` (the transport from `t` to `s` inverts it
    between `f ⁻¹' {γ s}` and `f ⁻¹' {γ t}`);
  - `parallelTransport_comp` (for a smooth `φ : ℝ → ℝ`, the transport along
    `γ ∘ φ` from `s` to `t` is that along `γ` from `φ s` to `φ t`; this is
    independence of the parametrization, with no monotonicity),
    `parallelTransport_congr` (curves equal on `Set.uIcc s t` have the same
    transport), `parallelTransport_const` (the identity for a constant curve);
  - `parallelTransport_eq_timeDependentFlowOf`: if a jointly smooth
    time-dependent `V` on `B`, vanishing outside a compact set, has
    `V u (γ u) = γ' u` on `Set.uIcc s t`, the transport is the flow of the
    lift of `V` from `s` to `t` on `f ⁻¹' {γ s}`;
  - `exists_diffeomorph_eqOn_parallelTransport`: a diffeomorphism
    `Ψ : P ≃ₘ⟮I, I⟯ P` equal to the transport on `f ⁻¹' {γ s}` and mapping it
    onto `f ⁻¹' {γ t}`: the composition, over a subdivision of `Set.uIcc s t`
    into pieces inside charts, of the diffeomorphisms
    `TauCeti.timeDependentFlowDiffeomorph` of the cut-off chart-constant
    fields.

About 600 lines. If it runs over, the last two items move to
`ParallelTransport/Smooth.lean`.

### `Geometry/Manifold/Submersion/ParallelTransport/Smooth.lean`

Readings in trivializations and families of curves. The trivializations are
Mathlib's `Bundle.Trivialization Z f`, for a fibre `Z` modelled by
`IZ : ModelWithCorners ℝ EZ HZ`, assumed smooth on `e.source` with a smooth
inverse on `e.target`, as in *Fibrations, connections and diffeomorphism
groups*; these two hypotheses are written out, since the bundled atlases are
part 48's.

- `TauCeti.IsEhresmannConnection.parallelTransportIn hD e e' γ s t : Z → Z`,
  `v ↦ (e' (hD.parallelTransport γ s t (e.symm (γ s, v)))).2`, with
  `parallelTransportIn_def`; `contMDiff_parallelTransportIn` when
  `γ s ∈ e.baseSet` and `γ t ∈ e'.baseSet` (from
  `exists_diffeomorph_eqOn_parallelTransport`);
  `parallelTransportIn_parallelTransportIn` (composition through a middle
  trivialization), `parallelTransportIn_self` (`s = t` and `e = e'` give
  the identity), and the bundled
  `parallelTransportInDiffeomorph : Z ≃ₘ⟮IZ, IZ⟯ Z` with
  `coe_parallelTransportInDiffeomorph` and its inverse, the transport from
  `t` to `s`. For a loop at `b` and one trivialization at `b`, this is the
  holonomy.
- `parallelTransportIn_coordChange`: replacing `e` and `e'` by `e₂` and
  `e₂'` conjugates the reading by Mathlib's `Bundle.Trivialization.coordChange` at
  `γ s` and `γ t`.
- `TauCeti.IsEhresmannConnection.exists_contMDiff_parallelTransport_param`:
  for a boundaryless finite-dimensional manifold `N` (model `IN`), a smooth
  `Γ : N × ℝ → B`, times `s t` and `a₀ : N`, there are a neighbourhood `U` of
  `a₀` and a smooth `Ψ : N × P → P` with
  `Ψ (a, x) = hD.parallelTransport (fun u ↦ Γ (a, u)) s t x` for `a ∈ U` and
  `f x = Γ (a, s)`. The route is that of the previous file with parameters:
  near `a₀`, one subdivision of `[s, t]` serves for all `a` (compactness), the
  chart-constant fields depend smoothly on `a`, and
  `TauCeti.contMDiff_timeDependentFlowOf_param` gives the smoothness of each
  piece. The local form avoids gluing smooth maps.

About 400 lines.

### `Geometry/Manifold/Submersion/RadialTrivialization.lean`

Local triviality by transport along rays, the direction of Exercise 6.1.1 of
[McDuffSalamon2017] that Tau Ceti lacks.

- `TauCeti.IsEhresmannConnection.exists_trivialization_parallelTransport`:
  under `hf` and `hfp`, for a trivialization `e : Bundle.Trivialization Z f`
  smooth with smooth inverse and `b₀ ∈ e.baseSet`, there is a trivialization
  `e'` with the same fibre, smooth with smooth inverse, `b₀ ∈ e'.baseSet`, and
  for every `b ∈ e'.baseSet` a smooth curve `γ` equal on `Set.Icc 0 1` to the
  ray `t ↦ (extChartAt J b₀).symm (c + t • (y - c))` from `c = extChartAt J b₀
  b₀` to `y = extChartAt J b₀ b`, with
  `e'.symm (b, v) = hD.parallelTransport γ 0 1 (e.symm (b₀, v))`. Its base set
  is the preimage of a ball around `c` in the chart target; `γ` composes the
  ray with a fixed smooth bounded `φ : ℝ → ℝ` equal to the identity on
  `[0, 1]`, so that it is smooth on `ℝ`. Smoothness of `e'` and of its inverse
  is `exists_contMDiff_parallelTransport_param` with `N` the ball (for the
  inverse, the rays run backwards). This is the form that part 48's
  `SymplecticFibres.lean` uses: transport by a connection that preserves the
  fibre forms gives trivializations that preserve them.
- `Manifold.IsSubmersion.exists_trivialization_of_isProperMap`: a smooth
  proper submersion `f` from a σ-compact `P` has, at every `b₀`, a
  trivialization with fibre `{x // f x = b₀}`, carrying the regular-fibre
  atlas `TauCeti.regularFiberChartedSpace`, smooth with smooth inverse. A
  connection comes from `Manifold.IsSubmersion.exists_isEhresmannConnection`;
  the trivialization is the one of the previous item for the fibre itself, the
  map `(b, v) ↦ hD.parallelTransport γ_b 0 1 v`, smooth by
  `TauCeti.isSmoothEmbedding_coe_regularFiber`. Every value of a submersion is
  regular, and `J.Boundaryless` makes `b₀` an interior point. The converse,
  that a smooth fibration with compact fibre is proper, is Tau Ceti's
  `TauCeti.isProperMap_of_forall_exists_trivialization`.

About 350 lines.

### `Geometry/Manifold/Submersion/Curvature.lean`

The curvature of an Ehresmann connection, with the page's sign: Mathlib's
`VectorField.mlieBracket` is the page's usual bracket, so the book's
$\Omega_\Gamma$ is the negative of this one (*Fibrations, connections and
diffeomorphism groups*).

- `TauCeti.IsEhresmannConnection.curvature hD v₁ v₂ : Π x : P, TangentSpace I x`,
  for `v₁ v₂ : Π b : B, TangentSpace J b`: the field
  $[v_1^\sharp,v_2^\sharp]-[v_1,v_2]^\sharp$, written
  `mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) -
  hD.horizontalLiftField (mlieBracket J v₁ v₂)`, with `curvature_def`.
- `curvature_mem_ker`: for smooth `v₁ v₂` it is vertical,
  `curvature v₁ v₂ x ∈ (mfderiv I J f x).ker`, since the lifts are `f`-related
  to `v₁ v₂` (`ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`
  and `TauCeti.mfderiv_mlieBracket_of_eventually_related`); with
  `horizontalLiftField_mem`, it is the vertical part of the bracket of the
  lifts, the page's $[v_1^\sharp,v_2^\sharp]^{\mathrm{Ver}}$, and
  `curvature_eq_zero_iff_mem` says it vanishes at `x` exactly when that
  bracket is horizontal there.
- Tensoriality: `curvature_swap` (it is alternating), `curvature_add_left`,
  `curvature_smul_left` (for smooth `g : B → ℝ`,
  `curvature (g • v₁) v₂ x = g (f x) • curvature v₁ v₂ x`, from Mathlib's
  Leibniz rules for `mlieBracket` and `horizontalLiftField_smul`), and the
  pointwise dependence `curvature_congr`: for smooth fields, the value at `x`
  depends only on `v₁ (f x)` and `v₂ (f x)`. Part 53's local formula for
  $\Omega_\Gamma(\partial_i,\partial_j)$ applies it to coordinate fields.
- `curvature_eq_zero_iff_isInvolutiveDistribution`: the curvature at each `x`
  of all `v₁ v₂` that are `C^n` at `f x` vanishes exactly when
  `TauCeti.IsInvolutiveDistribution I D`.
  One direction is `IsInvolutiveDistribution.mlieBracket_mem` with
  `curvature_mem_ker` and the complement condition `isCompl_ker`; for the
  other, the lifts of the coordinate fields of a chart of `B` form a local
  frame of `D`, their brackets are horizontal when the curvature vanishes,
  and so are those of their combinations by the Leibniz rule
  (`isInvolutiveDistribution_iff`).

About 300 lines.

## What other parts use

- *Symplectic fibrations* (`Connection.lean`, `SymplecticFibres.lean`):
  `parallelTransport`, `parallelTransportIn` and its `coordChange` lemma for
  symplectic transport and its chart independence;
  `exists_trivialization_parallelTransport` for the second route of the
  milestone *Fibrations with symplectic fibres are symplectic fibrations*;
  `horizontalLiftField` for $v^\sharp$ in the Cartan formula route.
- *Coupling forms* (`Holonomy.lean`, `Curvature.lean`): holonomy as
  `parallelTransportIn e e γ 0 1`, its smoothness in a family of loops
  (`exists_contMDiff_parallelTransport_param`), the isotopy
  `t ↦ parallelTransportIn e e' γ 0 t` over a disc, and `curvature` with
  `curvature_mem_ker` and `curvature_congr`.

The part uses no other unmerged part. Besides Mathlib and Tau Ceti, it uses
only the merged `Geometry/Manifold/Flow/TimeDependent.lean` of *Smooth
families*.

## Building issues

In the order they can be done; each is one pull request of a few hundred
lines.

1. **Horizontal lifts of vector fields.** `HorizontalLiftField.lean`. Waits
   for nothing.
2. **Horizontal lifts of curves and parallel transport.**
   `ParallelTransport/Basic.lean`. Waits for 1.
3. **Parallel transport in trivializations and in families.**
   `ParallelTransport/Smooth.lean`. Waits for 2.
4. **Local triviality of proper submersions.** `RadialTrivialization.lean`.
   Waits for 3.
5. **Curvature of an Ehresmann connection.** `Curvature.lean`. Waits for 1
   only, so it can be done beside 2–4.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Exercise 6.1.1), §6.3 and §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity Diagrams*][GuilleminLermanSternberg1996],
  §1.3 (curvature, with the usual bracket).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential
  Geometry*, Springer (1993), §9 (connections on fibred manifolds and their
  parallel transport).
* C. Ehresmann, *Les connexions infinitésimales dans un espace fibré
  différentiable*, Colloque de topologie (espaces fibrés), Bruxelles (1950),
  29–55.
