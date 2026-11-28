# Convexity

This is the detailed design of part 42 of `DESIGN.md`, *Convexity*. It covers
one milestone of `atlas/symplectic-group-actions.md`, *Convexity and
connectedness of moment-map fibers*, connectedness of the fibres over critical
values included. The statement is Atiyah's and Guillemin–Sternberg's
([Atiyah1982], Theorem 1; [McDuffSalamon2017], Theorem 5.5.1;
[CannasdaSilva2001], Theorem 1.5.1). The proof chosen here is the
local-to-global one of Bjorndahl and Karshon ([BjorndahlKarshon2010],
Theorem 10, Proposition 29 and Theorem 30), with the local input taken from
Tau Ceti's weight-model chart at a fixed point of the stabilizer.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Group
actions, moment maps and signs follow *Group actions, moment maps and periods*
of `DESIGN.md`: a torus is a Lie group `G` with
`[IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]`, as in Tau Ceti's
`MomentMap/ConvexHull.lean`, and the page's moment map $\mu$ enters Tau Ceti's
predicates as `fun x ↦ -μ x`.

## What exists, and what the part adds

Tau Ceti has every statement of the milestone except two: that the image is
convex, and that the fibres are connected. It also has the topological
local-to-global theorem that gives both from local convexity at every point.

- **The fixed set.** `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`
  (`Geometry/Manifold/Riemannian/Isometry/FixedPoints/Components.lean`): a
  compact group acting on a compact manifold has finitely many fixed
  components. `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`
  (`Geometry/Symplectic/Manifold/Invariants/FixedLocus.lean`): for a group of
  symplectic isometries, the part `TauCeti.fixedPointsOfFinrank 𝓘(ℝ, E) K M d`
  of the fixed set where the fixed tangent subspace has dimension `d` is a
  symplectic submanifold, modelled on any `L : Submodule ℝ E` of dimension
  `d`. `TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`
  (`.../FixedPoints/Submanifold.lean`): a preconnected subset of the fixed set
  lies in one of these parts. The invariant metric comes from
  `TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`
  (`Geometry/Manifold/Riemannian/Invariant.lean`).
- **The moment map on the fixed set.**
  `TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isPreconnected` and
  `finite_image_fixedPoints` (`Geometry/Symplectic/Hamiltonian/MomentMap/FixedPoints.lean`).
- **Half of convexity.** `TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`
  (`MomentMap/ConvexHull.lean`), for a nondegenerate form on a compact
  manifold, connected or not.
- **The local model at a fixed point.** `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`
  (`Geometry/Symplectic/Hamiltonian/WeightModel/NormalForm.lean`): at a point
  fixed by a whole torus acting symplectically, an equivariant Darboux chart
  onto a ball of `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` in which
  $\mu$ is $\mu(p)$ plus `TauCeti.weightMomentMap α`. Zero weights are allowed,
  so the fixed point need not be isolated.
- **Local convexity of the weight model.**
  `TauCeti.image_mem_nhdsWithin_range_weightMomentMap` (the model is open onto
  its image, a convex cone by `TauCeti.convex_range_weightMomentMap`) and
  `TauCeti.isPreconnected_preimage_weightMomentMap_inter` (its fibres are
  preconnected inside every invariant ball), in
  `Geometry/Symplectic/Hamiltonian/WeightModel/Convexity.lean`.
- **Stabilizers and restriction.** `TauCeti.Lie.isEmbeddedLieSubgroup_stabilizer`
  and `TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer`
  (`Geometry/Lie/Subgroup/Stabilizer.lean`): the stabilizer $G_x$ is an
  embedded Lie subgroup with Lie algebra the isotropy algebra $\mathfrak g_x$.
  `TauCeti.SmoothTwoForm.IsMomentMap.comp_monoidHom`
  (`Geometry/Symplectic/Hamiltonian/EquivariantMomentMap/Restrict.lean`): a
  moment map restricts along a homomorphism of Lie groups. The Lie group
  structure on a closed connected subgroup of a torus is that of
  `Geometry/Lie/Subgroup/Torus.lean`.
- **The local-to-global theorem.** `Analysis/Convex/LocalToGlobal.lean`:
  the predicate `TauCeti.IsConvexChart f U` (an open `U` on which `f` is open
  onto a convex image, with preconnected fibres), with
  `IsConvexChart.continuousLinearEquiv_comp`;
  `TauCeti.exists_isConvexChart_inter_preimage_ball`, which turns an open set
  on which `f` is open onto a convex set `C ⊇ f '' U`, with preconnected
  fibres, into a convexity chart around each of its points; and
  `IsProperMap.convex_range_of_isConvexChart` and
  `IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`, for a
  proper map from a preconnected Hausdorff space to a finite-dimensional real
  normed space covered by convexity charts.

Neither library has local convexity of a moment map at a point that is not
fixed by the whole group.

The part adds two things: local convexity of a torus moment map at every
point, and the fixed components as symplectic submanifolds. The milestone
follows from them and the results above.

## Decisions

`DESIGN.md` leaves two questions to this file: the route to connectedness of
every fibre, and whether it needs an induction on the torus.

- **The route: local to global, with no induction.** The book's argument
  ([McDuffSalamon2017], pp. 233–240) proves that the levels of a Morse–Bott
  function with no index or coindex one are connected, and then inducts on the
  number of components of $\mu$. It gives connected fibres only over regular
  values. Over a critical value the fibre of the first $k$ components is not a
  manifold, and the step of the induction needs one. Atiyah's passage to
  critical values by continuity is made rigorous most directly with the fact
  that each point has small neighbourhoods whose images are neighbourhoods in a
  cone, which is the local convexity used here anyway. So this part takes
  Bjorndahl–Karshon's route for the whole
  theorem: convexity of the image and connectedness of every fibre both come
  out of the local-to-global theorem, and there is no induction on the torus.
  The Morse–Bott lemma on connected levels (`Morse/Bott/Level.lean` in
  `DESIGN.md`) is then not needed. It is not a milestone, so the part drops it,
  and with it the Morse–Bott results of Tau Ceti that `DESIGN.md` listed for
  it.
- **Local convexity from the stabilizer's weight chart.** Bjorndahl–Karshon
  get local convexity at a point $x$ from the local normal form along the
  orbit of $x$ (their Proposition 29). Tau Ceti has only its linear part
  (`MomentMap/LinearNormalForm.lean`). For a torus a weaker local statement is
  enough, and it follows from the chart at a fixed point:
  - Let $K$ be the identity component of $G_x$, a torus with Lie algebra
    $\mathfrak k=\mathfrak g_x$, and let $\mathfrak q$ be a linear complement
    of $\mathfrak k$ in $\mathfrak g$. Restricted to $K$, $\mu$ composed with
    the restriction $\mathfrak g^*\to\mathfrak k^*$ is a moment map, and $K$
    fixes $x$. So Tau Ceti's weight chart for $K$ at $x$ gives coordinates
    $z=(z_0,z_+)$, with $z_0$ the coordinates of weight zero and $z_+$ the
    others, in which the $\mathfrak k^*$-part of $\mu$ is
    $\mu_{\mathfrak k}(x)+\Phi(z_+)$, $\Phi$ the weight model.
  - The $\mathfrak q^*$-part $\mu_{\mathfrak q}$ has differential
    $v\mapsto\omega_x(\zeta_M(x),v)$ in the direction $\zeta\in\mathfrak q$
    (up to the sign convention), and $\zeta\mapsto\zeta_M(x)$ is injective on
    $\mathfrak q$. The orbit directions $\zeta_M(x)$ are fixed by $K$, since $G$
    is commutative, so they lie in the weight-zero subspace. This subspace is
    $\omega_x$-orthogonal to the others, and $\omega_x$ is nondegenerate on it.
    So $d\mu_{\mathfrak q}(x)$ vanishes in the $z_+$ directions and is onto
    from the $z_0$ directions.
  - By the inverse function theorem, a change of the $z_0$ coordinates alone,
    keeping $z_+$, makes $\mu_{\mathfrak q}$ the linear coordinate
    $\mu_{\mathfrak q}(x)+u$. In these coordinates
    $\mu=\mu(x)+(\Phi(z_+),u)$ after identifying
    $\mathfrak g^*=\mathfrak k^*\times\mathfrak q^*$. On a product of small
    balls in $(u,w,z_+)$, with $w$ the remaining $z_0$ coordinates, $\mu$ is
    open onto the cone $\mu(x)+\operatorname{range}\Phi\times\mathfrak q^*$,
    and its fibres are products of a ball with a fibre of $\Phi$ inside a ball,
    preconnected by Tau Ceti's `isPreconnected_preimage_weightMomentMap_inter`.
  Tau Ceti's slice model, `exists_isConvexChart_of_eqOn_add_weightMomentMap`
  with the weights extended by zero on $\mathfrak q$ and $u$ read in the
  covectors vanishing on $\mathfrak k$, then gives a convexity chart around
  $x$, at every point of a manifold with a
  symplectic torus action and a moment map, compact or not.
- **The local-to-global theorem is Tau Ceti's.** The part defines no
  predicate of local convexity: the local result is stated with Tau Ceti's
  `IsConvexChart`, and the global one applies Tau Ceti's two `IsProperMap`
  theorems, whose hypotheses (a preconnected Hausdorff source, a proper map,
  a convexity chart around every point) are those of [BjorndahlKarshon2010],
  Theorem 10, in this setting.
- **The dual of the Lie algebra carries no norm.** Tau Ceti's moment maps take
  values in `Module.Dual ℝ (GroupLieAlgebra I G)`, which has no topology
  instance. The moment-map statements therefore compose $\mu$ with an arbitrary
  linear equivalence `e : Module.Dual ℝ (GroupLieAlgebra I G) ≃ₗ[ℝ] V` onto a
  finite-dimensional normed space, as Tau Ceti's `MomentMap/Submanifold.lean`
  does with coordinates. In the global theorem, convexity and fibres pass back
  through `e` (`Convex.linear_image`, injectivity of `e`), so the milestone
  mentions no `e`.
- **Hypotheses on the action.** A symplectic action is the hypothesis
  `hG : ∀ g : G, SmoothForm.mpullback (fun x ↦ g • x) _ σ = σ`, as in
  `exists_weightModelChart`. Local convexity needs `σ.IsSymplectic`: closedness
  makes $\omega(\zeta_M,\eta_M)$ locally constant, hence zero near $x$ when
  $\eta\in\mathfrak k$, which is what makes the $\mathfrak q^*$-part invariant
  under $K$. The fixed components need the model `𝓘(ℝ, E')` of Tau Ceti's
  fixed-locus theorems, so the milestone is stated for
  `[ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M]` with `E'` finite-dimensional.
  Effectiveness is not assumed.
- **Signs.** Convexity and connectedness are unchanged by $\mu\mapsto-\mu$.
  Everything except the milestone is stated in Tau Ceti's sign, in Tau Ceti's
  namespaces, so that it can move there. The milestone is stated in the page's
  sign with the hypothesis `σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) (fun x ↦ -μ x)`,
  and reads the results for $-\mu$, negating images.

## Files

### `Geometry/Symplectic/Manifold/FixedComponent.lean`

The fixed components of a compact group of symplectomorphisms as symplectic
submanifolds. For a compact Lie group `G` acting smoothly on a σ-compact
manifold modelled on a finite-dimensional `E'`, preserving a nondegenerate
`σ`, and `x ∈ MulAction.fixedPoints G M`:

- `TauCeti.isOpen_preimage_val_fixedPointsOfFinrank_connectedComponentIn`, for any
  group of isometries and every `d`: the component of the fixed set through `x`
  is open in the part `fixedPointsOfFinrank 𝓘(ℝ, E') G M d`, since the fixed
  set is locally connected (`locallyConnectedSpace_fixedPoints`); it is
  contained in the part with `d` the dimension of the fixed tangent subspace
  at `x` by `subset_fixedPointsOfFinrank_of_isPreconnected`;
- `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints_of_compactSpace`:
  for `L : Submodule ℝ E'` of that dimension, there is a manifold structure on
  `connectedComponentIn (MulAction.fixedPoints G M) x` modelled on `L` whose
  inclusion is a symplectic submanifold embedding with tangent images the
  fixed tangent subspaces. It is Tau Ceti's
  `exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints`
  for the averaged metric.

It cites [McDuffSalamon2017], Lemma 5.5.7.

### `Geometry/Symplectic/Hamiltonian/MomentMap/LocalConvexity.lean`

Local convexity of a torus moment map, in Tau Ceti's sign and namespace. With
`G` a torus acting smoothly on a boundaryless Hausdorff manifold `M` modelled
by `I'` on a finite-dimensional space, `σ.IsSymplectic`, `hG` as above, and
`h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ`:

```lean
theorem TauCeti.SmoothTwoForm.IsMomentMap.exists_isConvexChart
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (e : Module.Dual ℝ (GroupLieAlgebra I G) ≃ₗ[ℝ] V) (x : M) :
    ∃ U, x ∈ U ∧ TauCeti.IsConvexChart (e ∘ μ) U
```

with `V` a finite-dimensional real normed space.

The proof is the one under *Decisions*. Its steps, each a lemma of the file
unless Mathlib or Tau Ceti has it:

1. the identity component `K` of `MulAction.stabilizer G x` as a torus acting
   on `M` with fixed point `x`, and the restricted moment map
   (`IsMomentMap.comp_monoidHom` along the inclusion);
2. the vanishing of $\omega(\zeta_M,\eta_M)$ near $x$ for $\eta$ in the Lie
   algebra of `K`, hence the `K`-invariance of the $\mathfrak q^*$-part near
   $x$;
3. in the chart of `exists_weightModelChart` for `K`: the orbit directions lie
   in the weight-zero coordinates, and the derivative of the
   $\mathfrak q^*$-part at `0` is onto from them and zero on the others;
4. the change of the weight-zero coordinates by the implicit function theorem
   (`HasStrictFDerivAt.implicitToOpenPartialHomeomorph`), and the product form of
   $\mu$;
5. a convexity chart of the product form, from Tau Ceti's
   `exists_isConvexChart_of_eqOn_add_weightMomentMap`.

If step 4 or 5 grows, the product form can go first, as a separate lemma about
a map $(u,w,z_+)\mapsto(\Phi(z_+),u)$ with no moment map in it. The file cites
[BjorndahlKarshon2010], Proposition 29, and [Atiyah1982], §2, and credits Tau
Ceti's `exists_weightModelChart` and
`exists_isConvexChart_of_eqOn_add_weightMomentMap` by name.

### `Geometry/Symplectic/Hamiltonian/MomentMap/Convexity.lean`

The global results and the milestone. With `G` a torus acting smoothly on a
compact connected boundaryless manifold, `σ.IsSymplectic` and `hG`:

- `TauCeti.SmoothTwoForm.IsMomentMap.convex_range`: the image of $\mu$ is
  convex. From `IsMomentMap.exists_isConvexChart` and Tau Ceti's
  `IsProperMap.convex_range_of_isConvexChart` for `e ∘ μ` with `e` the
  equivalence of a basis (`Continuous.isProperMap` on a compact space), and
  `Convex.linear_image` for `e.symm`;
- `TauCeti.SmoothTwoForm.IsMomentMap.isConnected_preimage_singleton`: every
  nonempty fibre is connected, from Tau Ceti's
  `IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart` in the same
  way;
- `TauCeti.SmoothTwoForm.IsMomentMap.range_eq_convexHull_image_fixedPoints`:
  `range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M)`, from `convex_range`,
  Tau Ceti's `range_subset_convexHull_image_fixedPoints` and
  `image_subset_range`;
- the milestone, in the page's sign, with the model `𝓘(ℝ, E')`:

```lean
theorem atiyah_guillemin_sternberg
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) (fun x ↦ -μ x))
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    Finite (ConnectedComponents (MulAction.fixedPoints G M)) ∧
    (∀ x ∈ MulAction.fixedPoints G M, ∃ (L : Submodule ℝ E')
        (_ : ChartedSpace L (connectedComponentIn (MulAction.fixedPoints G M) x)),
        IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (MulAction.fixedPoints G M) x) ∧
        hσ.isNondegenerate.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
          (Subtype.val : connectedComponentIn (MulAction.fixedPoints G M) x → M)) ∧
    (∀ x ∈ MulAction.fixedPoints G M,
        ∀ y ∈ connectedComponentIn (MulAction.fixedPoints G M) x, μ y = μ x) ∧
    (μ '' MulAction.fixedPoints G M).Finite ∧
    range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) ∧
    ∀ η ∈ range μ, IsConnected (μ ⁻¹' {η})
```

  The finiteness of `μ '' MulAction.fixedPoints G M` makes the image a
  polytope. The theorem name follows the theorem's standard name, not the
  milestone's. Its docstring ends with the milestone line. The second and
  third conjuncts come from `FixedComponent.lean` and Tau Ceti's
  `apply_eq_of_isPreconnected` (with `isPreconnected_connectedComponentIn`);
  the others from the results above for $-\mu$, rewritten along negation
  (`convexHull_neg` and images under `Neg.neg`).

The file cites [Atiyah1982], [McDuffSalamon2017], Theorem 5.5.1,
[CannasdaSilva2001], Theorem 1.5.1, and [BjorndahlKarshon2010], Theorem 30.

## What the part uses

- From Mathlib: `convexHull`, `Convex.linear_image`, `IsProperMap`,
  `connectedComponentIn`, `ConnectedComponents`, the inverse function theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph`), `Module.Basis.dualBasis`.
- From Tau Ceti: the declarations listed under *What exists*.
- From other parts of the library: nothing. The part does not use *Equivariant
  normal forms*: its chart is Tau Ceti's `exists_weightModelChart` itself,
  read in Tau Ceti's sign.

## Issues

In order; each waits only for those it names.

1. **`Geometry/Symplectic/Manifold/FixedComponent.lean`**: the fixed
   components as symplectic submanifolds. Waits for nothing.
2. **`Geometry/Symplectic/Hamiltonian/MomentMap/LocalConvexity.lean`**: local
   convexity of a torus moment map. Waits for nothing.
3. **`Geometry/Symplectic/Hamiltonian/MomentMap/Convexity.lean`**: convexity,
   connected fibres, the image as a convex hull, and the milestone. Waits for
   issues 1 and 2.

Issues 1 and 2 can start at once.
