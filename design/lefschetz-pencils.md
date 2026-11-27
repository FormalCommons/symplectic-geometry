# Lefschetz pencils

This is the detailed design of part 66 of `DESIGN.md`, *Lefschetz pencils*.
It covers the milestone *Donaldson's Lefschetz pencil theorem in dimension
four* of `atlas/constructing-symplectic-manifolds.md`: McDuff–Salamon
[McDuffSalamon2017], Definition 7.4.10 and Theorem 7.4.12, with Donaldson
[Donaldson1999] for the construction, Auroux [Auroux1997; Auroux2000] for
transversality of sections of rank greater than one, and Gompf–Stipsicz,
*4-Manifolds and Kirby Calculus*, AMS (1999), §8.2, for the Euler
characteristic of a Lefschetz fibration.

All statements about Tau Ceti and Mathlib below were checked against the
pinned Tau Ceti `0651fdbae946` and the Mathlib it pins. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`, and paths of new files are
under `SymplecticGeometry/`.

## Setting and conventions

- **The four-manifold.** `M : Type` with `I : ModelWithCorners ℝ E H`,
  `[FiniteDimensional ℝ E]`, `hE : finrank ℝ E = 4`, `[IsManifold I ∞ M]`,
  `[T2Space M] [CompactSpace M] [ConnectedSpace M]`, and
  `ω : TauCeti.SmoothTwoForm I M` with `ω.IsSymplectic`. $M$ is oriented by
  $\omega$ (Tau Ceti's `Geometry/Symplectic/Orientation.lean`), and its
  fundamental class is that of this orientation.
- **The base.** $\mathbb CP^1$ is `ℙ ℂ (Fin 2 → ℂ)` as a real manifold
  through `Projectivization.instIsManifoldReal`, modelled on
  `𝓘(ℝ, Fin 1 → ℂ)`, as in `design/complex-projective-space.md`; its
  complex charts are Tau Ceti's `Projectivization.affineChart`.
- **Integrality.** As in *Blowups, sums and Donaldson hypersurfaces*: an
  integral lift is `a : H²(M; ℤ)` whose image in real singular cohomology is
  the image of $[\omega]$ under `TauCeti.deRhamHom`. Then
  $m=\langle a\smile a,[M]\rangle$ and $\langle K\smile a,[M]\rangle$ are
  integers under `evalFundamentalClass`. They do not depend on the lift,
  since two lifts differ by torsion, which pairs to zero with every class;
  the milestone fixes the lift, as the page does for the hypersurface
  theorem.
- **The canonical class.** $K=-c_1(TM,J)$, where $J$ is any structure
  compatible with $\omega$,
  with $c_1$ *First Chern number*'s `SymplecticGeometry.Bundle.firstChernClass`
  of the complex tangent bundle, exactly as in `design/adjunction.md`. Only
  this $J$ enters $K$; the pencil carries its own tame structure.
- **Euler characteristic and genus.** $\chi(M)$ is Tau Ceti's
  `TauCeti.eulerChar M`, with the finite CW type instance
  `TauCeti.FiniteCWType.of_isManifold`. The genus of a closed connected
  oriented surface is `TauCeti.surfaceGenus`, as in *Adjunction*.
- **Fibres in real homology.** "The fibre closure $\bar F$ represents
  $\mathrm{PD}(k[\omega])$ in real homology" is the equation
  $(k\,[\omega]_{\mathbb R})\frown[M]=i_*[\bar F]$ in $H_2(M;\mathbb R)$,
  with Tau Ceti's cap product and fundamental classes, the form in which
  *Poincaré duals of submanifolds* states $d_Z\frown[X]=i_*[Z]$; no inverse
  of the duality map is needed.

## Decisions

`DESIGN.md` leaves two questions to this file; a third, the Euler
characteristic count, is settled here because neither library has the
multiplicativity of the Euler characteristic in fibre bundles.

### The definitions

A Lefschetz fibration is the book's Definition 7.4.10 with its almost
complex structure as data, since the book's definition contains one and the
pencil theorem produces one:

- `IsLefschetzFibration ω J π`, for `J : TauCeti.SmoothAlmostComplexStructure I X`
  and a smooth `π : X → ℙ ℂ (Fin 2 → ℂ)`, a structure of `Prop` with fields
  - `tames : ω.Tames J`;
  - `injOn_criticalPoints`: `π` is injective on its set of critical points
    (the complement of Tau Ceti's `IsRegularPoint`), so each fibre holds at
    most one;
  - `exists_model`: at every critical point `p` there are an open
    neighbourhood `U`, a `J`-holomorphic open embedding `φ : U → (Fin 2 → ℂ)`
    with `φ p = 0` (its differential intertwines `J` with multiplication by
    `I`) and an affine chart `c : ℙ ℂ (Fin 2 → ℂ) → (Fin 1 → ℂ)` whose
    domain contains `π p`, such that
    `c (π x) 0 = c (π p) 0 + (φ x 0) ^ 2 + (φ x 1) ^ 2` on `U`. The chart
    takes values in `Fin 1 → ℂ`, so the equation is read in its one
    coordinate. It is centred at `c (π p)` because an affine chart vanishes
    only at a coordinate point: without that term every critical value
    would be `[1:0]` or `[0:1]`;
  - `isNondegenerate_ker`: at every regular point the restriction of `ω` to
    the kernel of `dπ` is nondegenerate.

  The book's integrability of `J` near the critical points, and the
  holomorphy of `π` there, follow from the holomorphic chart, and are
  lemmas, not fields.
- `IsLefschetzPencil ω J B π`, for `B : Finset X` in a T1 space `X` and a smooth
  `π : B.complOpens → ℙ ℂ (Fin 2 → ℂ)` on the open complement (Mathlib's manifold
  structure on an open subset), with fields: `tames : ω.Tames J` on all of
  `X`; the restriction of `ω` and `J` makes `π` an `IsLefschetzFibration`;
  and at every `b ∈ B` a `J`-holomorphic open embedding `φ` near `b` with `φ b = 0` and
  `π x = Projectivization.mk ℂ (φ x) _` for `x ≠ b` near `b`.
- `fiberClosure B π t`, the set `Subtype.val '' (π ⁻¹' {t}) ∪ B`, with
  `fiberClosure_def` and `isClosed_fiberClosure`.

Both predicates come with the trivial example of the projection
`Prod.snd : Σ × ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ)` for a closed surface
with an area form, the product form and the product structure, which has
no critical points. The local quadric is in `Model.lean`.

### The transversality for pairs

The pencil is $\pi=[s^0:s^1]$ for a section $s=(s^0,s^1)$ of
$L^{\otimes k}\otimes\mathbb C^2$, in Donaldson's construction. *Asymptotically
holomorphic sections* plans uniform transversality of one section of
$L^{\otimes k}$. The pencil needs three more conditions, each uniform in $k$
in the metric $g_k$ of that part:

1. **The pair.** $s$ is $\eta$-transverse to zero: where $|s|<\eta$, its
   $(1,0)$-part $\partial s:T_xM\to\mathbb C^2\otimes L^{\otimes k}_x$ is onto
   with a right inverse of norm at most $\eta^{-1}$. Its zero set $B$ is then
   finite, and every zero is positive (below).
2. **Each component.** $s^0$, $s^1$ are each
   $\eta$-transverse as sections of $L^{\otimes k}$, which by part 64's
   `Connectivity.lean` makes the fibre closures over $[0:1]$ and $[1:0]$
   connected.
3. **The derivative of the quotient.** Away from $B$, on the set where
   $|s^0|\ge|s^1|$ write $f=s^1/s^0$ (and symmetrically): the section
   $\partial f$ of $T^*M^{1,0}\otimes f^*T\mathbb CP^1$ is $\eta$-transverse
   to zero. Its critical points are then nondegenerate in the sense that
   $\nabla\partial f$ is an isomorphism with inverse bounded by $\eta^{-1}$
   and $|\bar\partial f|=O(k^{-1/2})$, which is what the perturbation to the
   model needs.

Each condition is local and open: a perturbation of $C^1$ size less than
$\eta/2$ keeps an $\eta$-transverse section $\eta/2$-transverse. So the
three are obtained one after another, each with the colouring iteration of
part 64's `GlobalTransversality.lean`, keeping the earlier ones by the
openness. The local step is the quantitative transversality for
approximately holomorphic maps to $\mathbb C^r$, $r\le n=2$, which is
Auroux's avoidance estimate [Auroux2000, Proposition 2] for target dimension
greater than one; part 64's `LocalTransversality.lean` derives the scalar
case from the same estimate. The pair step and the derivative step are
Auroux's treatment of $L^{\otimes k}\otimes\mathbb C^r$ [Auroux1997] and
Donaldson's [Donaldson1999].

What this part needs from *Asymptotically holomorphic sections* is
therefore: the line bundle and the rescaled metrics (`LineBundle.lean`), the
asymptotically holomorphic sequences and the transversality predicate
(`AsymptoticallyHolomorphic/Basic.lean`), the peak sections (`PeakSection.lean`),
the avoidance estimate for every target dimension (from the issues in which
that part's design splits it), the colouring iteration for a general local
open condition (`GlobalTransversality.lean`), the zero-set criterion with
its class (`ZeroSet.lean`) and the connectivity (`Connectivity.lean`).
Where that part states one of these for $L^{\otimes k}$ only, this part's
`Transversality/` files state the rank-two form beside it, with the same
proof, and do not copy it.

The pointwise linear algebra is one lemma, used three times: a real-linear
map $A+B$ between complex vector spaces of the same dimension, with $A$
complex-linear invertible and $B$ antilinear, $\|B\|<\|A^{-1}\|^{-1}$, is
invertible and preserves the complex orientations (the homotopy $A+tB$); and
for a target of complex dimension one, $\|B\|<\|A\|$ makes the kernel
symplectic for a compatible form. The second is the linear core of part
64's `ZeroSet.lean`, which this part imports; the first goes in
`LinearAlgebra/ComplexStructure/Dominant.lean`. With it, the zeros of $s$ are
positive, and every vertical tangent space at a regular point where
$|\partial f|\ge\eta$ is symplectic.

### The local models

Near the base points and the critical points the asymptotically holomorphic
$s$ is replaced by the holomorphic model, following Donaldson
[Donaldson1999] and the sketch after Theorem 7.4.12 of [McDuffSalamon2017]:

- at a base point $b$, in a Darboux chart for $\omega$ whose differential at
  $b$ is complex-linear (Tau Ceti's
  `TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart` with
  a unitary correction), $s$ is interpolated by a cut-off to its
  complex-linear part at $b$, and $J$ to $J_0$; the pencil is then
  $[z_1:z_2]$ on a ball;
- at a critical point $p$, $f$ is interpolated to its holomorphic quadratic
  part, which is nondegenerate by condition 3, hence $z_1^2+z_2^2$ after a
  complex-linear change of coordinates, and $J$ to $J_0$;
- the critical values are made distinct, and different from $[0:1]$ and
  $[1:0]$, by adding to $f$, near each critical point, a small constant
  times a cut-off.

The cut-off regions have $g_k$-radius bounded below, so all errors are
$O(k^{-1/2})$ and conditions 1–3 survive with $\eta/2$; tameness of the new
$J$ and the symplectic vertical spaces follow from the dominant-part lemma.

### The blowup at the base points

The base points are blown up one after another with *Symplectic blowup*'s
`Weight/Basic.lean`, along the ball embeddings $\psi_b$ of radius $\lambda$ of
the Darboux charts above: these are disjoint for small $\lambda$, and each
blowup is the identity off its ball, so the remaining embeddings lift to it.
In the chart, the pencil $[z_1:z_2]$ composed with the blowdown is the
projection $\mathrm{pr}$ of the incidence set $\widetilde{\mathbb C}^2$
(*Complex blowup*'s `Model.lean`), so it extends smoothly over the divisor,
with no critical point there, and its fibres near $Z$ are the lines of
$\widetilde{\mathbb C}^2$, on which $\tilde\omega_\lambda$ restricts to
$\omega_0$: they are symplectic. So the extension is a Lefschetz fibration.

The identification with $M\#mk^2\,\overline{\mathbb CP}{}^2$, as the
approving review of #3195 asked, uses two facts of other parts: the blowup
of `Weight/Basic.lean` along $\psi$ is diffeomorphic to the complex blowup of
*Complex blowup*'s `Basic.lean` for the chart $\psi$, which *Symplectic
blowup* compares in `Normalized/Weight.lean` (the book's comparison of (7.1.14)
with Theorem 7.1.21); and *Complex blowup*'s `ConnectedSum.lean` gives an
orientation-preserving diffeomorphism from that blowup to
$M\#\overline{\mathbb CP}{}^2$. Iterating, the blowup at $N$ points is an iterated
connected sum, recorded by the predicate `IsReversedProjectiveSum oM oX N`
of `Geometry/Manifold/ConnectedSum/Iterate.lean`, defined by recursion on
`N`: for `N = 0`, an orientation-preserving diffeomorphism `M ≃ X`; for
`N + 1`, a manifold `Y : Type` with `IsReversedProjectiveSum oM oY N` and an
orientation-preserving diffeomorphism from `X` to a
`TauCeti.OrientedConnectedSum` of `Y` and $\overline{\mathbb CP}{}^2$. Here `X`
and `Y` are charted on `EuclideanSpace ℂ (Fin 2)`, an inner product space as
the oriented connected sum needs, and all orientations are indexed by `Fin 4`. By the
*Disc theorem* of *Connected sums* the choice of the balls does not matter,
but the predicate does not need that.

### The Euler characteristic count

The page's count is $\chi(\widetilde M)=2\chi(F)+\ell$ for a Lefschetz
fibration over $\mathbb CP^1$ with regular fibre $F$ and $\ell$ critical
points, and $\chi(\widetilde M)=\chi(M)+mk^2$. Neither library has the
multiplicativity of $\chi$ in fibre bundles. Tau Ceti has Euler's equality
for Morse–Bott functions, so the first equation is proved with one:

1. compose $\pi$ with a projective linear map of $\mathbb CP^1$ so that
   $[1:0]$ and $[0:1]$ are regular values (the critical values are finite);
   `IsLefschetzFibration` is preserved;
2. let $\mu$ be Tau Ceti's `projectiveMomentFunction` with weights $(0,1)$,
   a Morse function with critical points $[1:0]$ and $[0:1]$ of index $0$
   and $2$ (`isMorse_projectiveMomentFunction`);
3. $\mu\circ\pi$ is Morse–Bott: along the two fibres over the critical
   points of $\mu$ by Tau Ceti's
   `TauCeti.isNondegenerateCriticalSubmanifold_comp_regularFiber`,
   of index $0$ and $2$; at each critical point of $\pi$ it is
   $\mathrm{Re}(\lambda(z_1^2+z_2^2))$ plus a constant in the model, with
   $\lambda\neq0$ since $\mu$ is regular at the critical value, so a
   nondegenerate critical point of index $2$ (`Model.lean`); there are no
   other critical points, since `dπ` is onto elsewhere
   (`TauCeti.IsRegularPoint.mem_criticalPoints_comp_iff`);
4. Tau Ceti's `TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum`,
   over `ZMod 2`, gives $\chi(\widetilde M)=\chi(F_0)+\chi(F_\infty)+\ell$,
   turned into `eulerChar` by `TauCeti.eulerChar_eq_finsum_finrank_singularHomology`.

The pieces of a Morse–Bott family are connected, so the two fibres must be
connected. All regular fibres are diffeomorphic, by the local triviality
of proper submersions
(`Manifold.IsSubmersion.exists_trivialization_of_isProperMap` of
*Parallel transport*'s `RadialTrivialization.lean`) over the connected set
of regular values, so $F_0\cong F_\infty\cong F$, and it is enough that one
regular fibre is connected. For the pencil the fibre over $[0:1]$ is, by
condition 2, once the perturbation keeps $[0:1]$ a regular value.

The second equation is $\chi(X\#\overline{\mathbb CP}{}^2)=\chi(X)+1$, an
instance of $\chi(X\#Y)=\chi(X)+\chi(Y)-1-(-1)^n$ in dimension $n$: Tau
Ceti's `TauCeti.eulerChar_union_add_eulerChar_inter` for the two punctured
summands, which meet in an annulus, with `TauCeti.eulerChar_compl_of_finite`
and `TauCeti.eulerChar_complexProjectiveSpace`.

## Files

| File | Contents | Issue |
|---|---|---|
| `LinearAlgebra/ComplexStructure/Dominant.lean` | maps with dominant complex-linear part: invertibility and orientation | 1 |
| `Geometry/Manifold/ConnectedSum/EulerCharacteristic.lean` | the Euler characteristic of a connected sum | 2 |
| `Geometry/Manifold/ConnectedSum/Iterate.lean` | `IsReversedProjectiveSum` and its Euler characteristic | 2 |
| `Geometry/Symplectic/Lefschetz/Basic.lean` | `IsLefschetzFibration`, `IsLefschetzPencil`, `fiberClosure`, the product example | 3 |
| `Geometry/Symplectic/Lefschetz/Model.lean` | the local model $z_1^2+z_2^2$ | 3 |
| `Geometry/Symplectic/Lefschetz/EulerCharacteristic.lean` | $\chi=2\chi(F)+\ell$ | 4 |
| `Geometry/Symplectic/Lefschetz/Transversality/Pair.lean` | conditions 1 and 2 | 5 |
| `Geometry/Symplectic/Lefschetz/Transversality/Derivative.lean` | condition 3 and its consequences | 6 |
| `Geometry/Symplectic/Lefschetz/Perturbation.lean` | the local models near base and critical points; distinct critical values | 7 |
| `Geometry/Symplectic/Lefschetz/FiberClosure.lean` | the pencil on $M$: base points, fibre closures, genus | 8 |
| `Geometry/Symplectic/Lefschetz/Pencil.lean` | the fibration on the blowup, the count of singular fibres, the milestone | 9 |

### `LinearAlgebra/ComplexStructure/Dominant.lean`

Namespace `TauCeti.AlmostComplexStructure`, for almost complex structures
on finite-dimensional real normed spaces `V`, `W` of the same dimension.

- `ContinuousLinearEquiv.addOfNormLt`, in
  `Analysis/Normed/Operator/Perturbation.lean`: for $A$ invertible and
  $\|B\|\,\|A^{-1}\|<1$, the isomorphism $A+B$ (no complex structure is
  needed);
- `orientation_map_add_of_norm_lt`: for $A$ complex-linear, $A+B$ carries
  the orientation of the structure on `V` to that on `W` (Tau Ceti's
  `AlmostComplexStructure.orientation`), by the homotopy $A+tB$ and
  `Orientation.map` along a path of isomorphisms.

### `Geometry/Manifold/ConnectedSum/EulerCharacteristic.lean`

Beside Tau Ceti's `Geometry/Manifold/ConnectedSum/`, in the namespace
`TauCeti.ConnectedSum`.

- `eulerChar_connectedSum`: for compact boundaryless manifolds of dimension
  `n`, `eulerChar (ConnectedSum e₁ e₂) = eulerChar M₁ + eulerChar M₂ - 1 - (-1) ^ n`,
  with the finite CW type of `M₁`, `M₂` and the sum as instance arguments,
  which `FiniteCWType.of_isManifold` supplies; and the same for `OrientedConnectedSum`.

### `Geometry/Manifold/ConnectedSum/Iterate.lean`

Namespace `SymplecticGeometry`.

- `IsReversedProjectiveSum oM oX N`, as in *Decisions*, with the lemmas
  `isReversedProjectiveSum_zero_iff`, `IsReversedProjectiveSum.succ` (the
  constructor), and `IsReversedProjectiveSum.eulerChar_eq`:
  `eulerChar X = eulerChar M + N` in dimension four, by
  `eulerChar_orientedConnectedSum` and `EuclideanComplexProjectiveSpace.eulerChar_eq`.

### `Geometry/Symplectic/Lefschetz/Basic.lean`

Namespace `SymplecticGeometry`, with the setting above for a manifold `X`
of real dimension four, not yet compact.

- `IsLefschetzFibration`, `IsLefschetzPencil` and `fiberClosure`, as in
  *Decisions*, with `fiberClosure_def`.
- `IsLefschetzFibration.finite_criticalPoints` for compact `X` (critical
  points are isolated by the model), `IsLefschetzFibration.isOpen_regularValue`
  and `IsLefschetzFibration.isConnected_regularValue` (the complement of a
  finite set in $\mathbb CP^1$), and `IsLefschetzFibration.comp_projectivizationMap`:
  composing with the map of $\mathbb CP^1$ induced by `g : GL (Fin 2) ℂ`
  gives a Lefschetz fibration.
- `IsLefschetzFibration.isIntegrable_on`, and `IsLefschetzChart.isIntegrable_on`
  and `IsLefschetzChart.mdifferentiableAt_of_mem`: `J` is integrable, and `π`
  holomorphic, on the chart domains of the model.
- The example: `isLefschetzFibration_snd` and `isLefschetzPencil_empty`
  for the product of a closed surface with $\mathbb CP^1$, with the product
  form of an area form and `fubiniStudyForm` and the product structure.
- `IsLefschetzFibration.manifoldMorseIndex_comp`: the same as
  `manifoldMorseIndex_re_mul_quadric` of `Model.lean` for `μ ∘ π` at a
  critical point `p` of `π`, for any `μ` with nonzero derivative at `π p`,
  through the chart of `exists_model`.

### `Geometry/Symplectic/Lefschetz/Model.lean`

Namespace `SymplecticGeometry.LefschetzModel`.

- `quadric : (Fin 2 → ℂ) → ℂ`, $z_1^2+z_2^2$, with `quadric_def`; its only
  critical point is `0`, where its complex Hessian is nondegenerate;
- `manifoldMorseIndex_re_mul_quadric`: for `λ ≠ 0`, `0` is a
  nondegenerate critical point of `fun z ↦ (λ * quadric z).re`, of Morse
  index `2` (Tau Ceti's `manifoldMorseIndex`);
- the model $[z_1:z_2]$ on $\mathbb C^2\setminus0$ is `Projectivization.mkNonzero ℂ 1`
  of `Geometry/Manifold/Projectivization/Hopf.lean`, regular at every point
  (`isRegularPoint_mkNonzero`), whose fibres are the punctured complex lines
  (`preimage_mkNonzero_singleton_mk`).

### `Geometry/Symplectic/Lefschetz/EulerCharacteristic.lean`

- `IsLefschetzFibration.eulerChar_eq`: for a compact connected `X`, a
  Lefschetz fibration `π`, and connected regular fibres,
  `eulerChar X = 2 * eulerChar F + (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π).ncard` for any regular
  fibre `F` (as Tau Ceti's regular fibre manifold of `RegularValue/ManifoldLevel.lean`),
  by *Decisions*. With the genus, `eulerChar X = 4 - 4 * g + ℓ`, by
  `TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`.
- `IsLefschetzFibration.nonempty_diffeomorph_fiber`: regular fibres are
  pairwise diffeomorphic.

### `Geometry/Symplectic/Lefschetz/Transversality/Pair.lean`

Namespace `SymplecticGeometry`, in the setting of *Asymptotically
holomorphic sections* (the bundle $L$ with $c_1(L)=a$, its unitary
connection of curvature $-2\pi i\omega$, the compatible $J$, the metrics
$g_k$).

- The predicate of $\eta$-transversality for sections of
  $L^{\otimes k}\otimes\mathbb C^2$ (condition 1), and the existence, for
  every large $k$, of asymptotically holomorphic $s_k$ satisfying conditions
  1 and 2 with one $\eta$; the local step from the avoidance estimate in
  target dimension two, the global step from part 64's iteration.
- `finite_zeroSet`, `zeroSet_card_eq`: the zero set is finite, each zero is
  positive by `orientation_map_add_of_norm_lt`, and its cardinality is
  $\langle e(L^{\otimes k}\otimes\mathbb C^2),[M]\rangle=k^2m$, by Tau Ceti's
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sign`,
  the library's `eulerClass_prod` (`Topology/VectorBundle/Orientation/Whitney.lean`)
  and $c_1(L^{\otimes k})=ka$.

### `Geometry/Symplectic/Lefschetz/Transversality/Derivative.lean`

- Condition 3 and its existence, keeping 1 and 2, by the same scheme.
- Its consequences for $\pi_k=[s^0_k:s^1_k]$ off $B$, for large $k$: every
  critical point is isolated and nondegenerate in the sense of condition 3;
  at a regular point the vertical tangent space is symplectic (the linear
  core of part 64's `ZeroSet.lean`); the critical points stay at
  $g_k$-distance bounded below from $B$.

### `Geometry/Symplectic/Lefschetz/Perturbation.lean`

- The local modifications of *Decisions*, near base points and critical
  points, and the separation of critical values; the result is a section
  $s_k$ and a tame $J_k$ for which `[s⁰ : s¹]` is an `IsLefschetzPencil`
  with base set $s_k^{-1}(0)$, of cardinality $k^2m$, and whose model
  charts at the base points are Darboux charts.

### `Geometry/Symplectic/Lefschetz/FiberClosure.lean`

- `fiberClosure_eq_zeroSet`: the fibre closure over $[\alpha:\beta]$ is the
  zero set of $\beta s^0-\alpha s^1$; over a regular value this section
  satisfies part 64's zero-set criterion, so the fibre closure is a closed
  symplectic surface whose class is $\mathrm{PD}(c_1(L^{\otimes k}))$, and so
  represents $\mathrm{PD}(k[\omega])$ in real homology; it is connected
  over $[0:1]$ and $[1:0]$ by `Connectivity.lean` (over every regular value
  in `Pencil.lean`).
- `two_mul_genus_sub_two`: for a regular value with connected fibre
  closure $\Sigma$, embedded by `i`,
  $2g-2=mk^2+k\langle K\smile a,[M]\rangle$: *Adjunction*'s
  `TauCeti.SmoothEmbedding.adjunction_formula`, for a compatible structure
  that preserves $T\Sigma$ (built on a tubular neighbourhood of $\Sigma$ and
  extended by Tau Ceti's `TauCeti.SmoothTwoForm.Compatible.exists_compatible_eqOn`),
  with the normal orientations matched by *Adjunction*'s
  `shortExact_orientationAt_normalSpace`, and with $\Sigma\cdot\Sigma=\langle d_\Sigma\smile
  d_\Sigma,[M]\rangle=k^2m$ and $\langle c_1,i_*[\Sigma]\rangle=k\langle
  c_1\smile a,[M]\rangle$ from *Poincaré duals of submanifolds*
  (`DualClass/Basic.lean`: $d_\Sigma$ restricts to the Euler class of the normal
  bundle; `Orientation/DualClass.lean`), and the invariance of $c_1$ along
  the path of compatible structures.

### `Geometry/Symplectic/Lefschetz/Pencil.lean`

- `mkNonzero_eq_pr`: `Projectivization.mkNonzero ℂ 1` is the projection `pr` of *Complex
  blowup*'s incidence set composed with the inverse of its blowdown off
  $Z$, so `pr` extends it across the exceptional divisor, as a submersion
  there.
- The iterated blowup $\widetilde M$ of *Decisions*, with its form, its
  blowdown map $\beta$, the Lefschetz fibration $\tilde\pi$ with
  $\tilde\pi=\pi\circ\beta$ off the exceptional divisors, and
  `IsReversedProjectiveSum oM oM̃ (k ^ 2 * m)`.
- `card_criticalPoints`: $\ell=3mk^2+2k\langle K\smile a,[M]\rangle+\chi(M)$,
  from `IsLefschetzFibration.eulerChar_eq`, `IsReversedProjectiveSum.eulerChar_eq`
  and `two_mul_genus_sub_two`; the fibres of $\tilde\pi$ are the fibre
  closures, since `pr` meets each exceptional divisor once, so all of them
  are connected by `nonempty_diffeomorph_fiber`.
- **Milestone** `exists_isLefschetzPencil`: under the setting, for every
  integral lift `a` and compatible `J`, for all sufficiently large `k`
  (`∀ᶠ k in Filter.atTop`) there are a tame structure `J'`, a finite set
  `B : Finset M` with `B.card = m * k ^ 2` and `π` with `IsLefschetzPencil ω J' B π`,
  such that every fibre closure over a regular value is a closed connected
  symplectic surface representing $\mathrm{PD}(k[\omega])$ in real
  homology, of genus `g` with `2 * g - 2 = m * k ^ 2 + k * ⟨K ⌣ a, [M]⟩`;
  and a symplectic four-manifold `M̃ : Type`, with
  `IsReversedProjectiveSum oM oM̃ (m * k ^ 2)`, a tame structure and a
  Lefschetz fibration on it agreeing with `π` under the blowdown off the
  exceptional divisors, whose number of critical points is
  `3 * m * k ^ 2 + 2 * k * ⟨K ⌣ a, [M]⟩ + eulerChar M`. Its docstring ends
  with the line Milestone: *Donaldson's Lefschetz pencil theorem in dimension
  four*.

The milestone is stated with the hypotheses of the page: closed connected,
dimension four, $[\omega]$ integral; the number of singular fibres is the
number of critical points, since `injOn_criticalPoints` puts at most one in
a fibre.

## What the part uses

- Tau Ceti: `IsRegularPoint`, `IsRegularValue`, regular fibres
  (`Geometry/Manifold/RegularValue/ManifoldLevel.lean`); Morse and
  Morse–Bott functions (`Geometry/Manifold/Morse/Projectivization.lean`,
  `Morse/Submersion.lean`, `Morse/Bott/Submersion.lean`,
  `Morse/Bott/Inequalities.lean`); Euler characteristics
  (`AlgebraicTopology/Cellular/EulerCharacteristic/`); connected sums
  (`Geometry/Manifold/ConnectedSum/`); Euler numbers of sections
  (`Geometry/Manifold/VectorBundle/Section/EulerNumber.lean`); Darboux charts
  and compatible structures.
- *Asymptotically holomorphic sections*: the files listed under *The
  transversality for pairs*.
- *Symplectic blowup*: `Weight/Basic.lean`, and the comparison with the complex
  blowup in `Normalized/Weight.lean`.
- *Complex blowup*: `Model.lean` (`pr`), `Basic.lean`, `ConnectedSum.lean`.
- *Poincaré duals of submanifolds*: `DualClass/Basic.lean`,
  `Orientation/DualClass.lean`.
- *Parallel transport*: `RadialTrivialization.lean`.
- Merged: *Adjunction* (`adjunction_formula`), *First Chern number*
  (`firstChernClass`), *First Chern class of nondegenerate forms* (invariance
  of $c_1$), *Complex projective space* (`fubiniStudyForm`), the library's
  `Topology/VectorBundle/Orientation/Whitney.lean`.

Mathlib, Tau Ceti and this library were searched at the pinned versions for
Lefschetz fibrations and pencils, for the Euler characteristic of a fibre
bundle or of a connected sum, and for the local model $z_1^2+z_2^2$: none
has them. Tau Ceti has the Morse–Bott Euler equality, the Morse moment
function on projective space and the signed count of zeros used above.

## Building issues

In this order; sizes are estimates. All are sub-issues of #3295, *Build the
part Lefschetz pencils*.

| # | Issue | Files | Waits for | Size |
|---|---|---|---|---|
| 1 | Maps with dominant complex-linear part | `Dominant.lean` | — | 200 |
| 2 | Euler characteristic of connected sums; iterated sums with $\overline{\mathbb CP}{}^2$ | `ConnectedSum/EulerCharacteristic.lean`, `ConnectedSum/Iterate.lean` | — | 300 |
| 3 | Lefschetz fibrations and pencils, local models | `Basic.lean`, `Model.lean` | — | 400 |
| 4 | The Euler characteristic of a Lefschetz fibration | `Lefschetz/EulerCharacteristic.lean` | 3; *Parallel transport* `RadialTrivialization.lean` | 400 |
| 5 | Transversality of pairs | `Transversality/Pair.lean` | 1; *Asymptotically holomorphic sections* up to `GlobalTransversality.lean` | 500 |
| 6 | Transversality of the derivative of the quotient | `Transversality/Derivative.lean` | 5 | 500 |
| 7 | Holomorphic models near base and critical points | `Perturbation.lean` | 3, 6 | 500 |
| 8 | The pencil on $M$ | `FiberClosure.lean` | 7; *Asymptotically holomorphic sections* `ZeroSet.lean`, `Connectivity.lean`; *Poincaré duals of submanifolds* `DualClass/Basic.lean`, `Orientation/DualClass.lean` | 400 |
| 9 | The fibration on the blowup and the milestone | `Lefschetz/Pencil.lean` | 2, 4, 8; *Symplectic blowup* `Weight/Basic.lean`, `Normalized/Weight.lean`; *Complex blowup* `Model.lean`, `ConnectedSum.lean` | 400 |

Issues 1, 2 and 3 can start once this design is merged; the issue that splits #3295 names, for each issue
of another part above, the issue of that part's design that builds it, once
those designs (#3290, #3284, #3280, #3278) are merged.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Definition 7.4.10, Theorem 7.4.12.
* [S. K. Donaldson, *Lefschetz pencils on symplectic manifolds*][Donaldson1999].
* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997].
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000].
* R. E. Gompf, A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate
  Studies in Mathematics 20, AMS (1999), §8.2.
