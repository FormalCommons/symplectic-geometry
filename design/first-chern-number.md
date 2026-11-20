# First Chern number

This is the detailed design of part 13 of `DESIGN.md`, *First Chern number*.
It settles the question that `DESIGN.md` leaves to this file: how the first
Chern number is defined. It also lists the infrastructure the part needs that
neither Mathlib nor Tau Ceti has, as issues that come before the part's own.
The part proves three milestones of `atlas/linear-symplectic-geometry.md`:
*First Chern number of symplectic vector bundles over surfaces*, *Chern–Weil
formula for circle bundles over surfaces* and *First Chern number as an Euler
number*.

Sources: McDuff–Salamon [McDuffSalamon2017], §2.7 (Theorem 2.7.1, Lemma
2.7.3, Theorems 2.7.4 and 2.7.5); Milnor–Stasheff, *Characteristic Classes*,
§14 (the top Chern class of a complex bundle equals the Euler class of its
realification, with the complex orientation); Bott–Tu [BottTu1982], §§6, 11
and 20 (the Euler class as a count of zeros, and the Chern–Weil description
of $c_1$ for circle bundles).

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, as for `DESIGN.md`. Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`.

## The decision: a cohomological definition

The first Chern class of a complex vector bundle $E\to B$ is the Euler class of
its determinant line:

$$c_1(E) := e\bigl((\Lambda^{\mathrm{top}}_{\mathbb{C}}E)_{\mathbb{R}}\bigr)\in H^2(B;\mathbb{Z}),$$

with the canonical orientation of a complex line. In Lean this is Tau Ceti's
`TauCeti.complexEulerClass` with `r = 0`, applied to the determinant line
built from Tau Ceti's `TauCeti.FiniteRankBundleCore.det`. Over a compact
oriented surface $\Sigma$ the *first Chern number* is the pairing of this
class with the fundamental class, Tau Ceti's
`TauCeti.HomologicalOrientation.evalFundamentalClass`. A symplectic vector
bundle gets the Chern number of the complex bundle given by any compatible
complex structure.

The book defines $c_1$ through a splitting $\Sigma=\Sigma_1\cup_C\Sigma_2$,
symplectic trivializations over the two halves, and the Maslov indices of the
overlap loops. Here that description, and the description from coordinate
discs, are theorems (`Clutching` and `Splitting` below). Tau Ceti's
`TauCeti.clutchingNumber` is defined only on spheres $I^2/\partial I^2\to X$,
so it cannot define a number for every surface; it becomes a comparison
theorem. The reasons for this choice:

- **Functoriality is free.** $c_1(\varphi^*E)=\varphi^*c_1(E)$ is naturality
  of the Euler class and of the determinant, and $\langle\varphi^*c,[\Sigma']\rangle
  =\deg(\varphi)\langle c,[\Sigma]\rangle$ is Tau Ceti's
  `TauCeti.HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul`,
  for any continuous map and the homological degree.
  `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`
  identifies the homological degree with the signed count at a regular value,
  `TauCeti.degree`, for smooth maps. Starting from the splitting definition,
  functoriality needs splittings adapted to the preimages of a regular value,
  which is hard.
- **The Euler-number milestone is almost free.** For a line bundle the
  determinant is the bundle itself (`FiniteRankBundleCore.exteriorPowerOneNatIso`),
  and Tau Ceti proves
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`
  and computes the index at a transverse zero
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`).
- **Normalization goes through Poincaré–Hopf**, which Tau Ceti has for
  gradients of Morse functions
  (`TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`,
  with `TauCeti.exists_isMorse`). The splitting definition would need an
  explicit computation for every genus.
- **Well-definedness is not an issue.** The splitting definition must first
  show independence of the splitting and of the trivializations, which is the
  book's Lemma 2.7.3 together with a comparison of any two splittings.
- **Later pages need the integral class.** `atlas/almost-complex-structures.md`
  uses $c_1(TM,J)\in H^2(M;\mathbb{Z})$ for manifolds of any dimension, and
  `atlas/symplectic-fibrations.md` uses its naturality. The class defined here
  serves them unchanged, while a number defined only over surfaces would not.

What the Euler class does not give for free is additivity, the hard direction
of naturality, and the existence of bundles with every Chern number. All three
come from the disc clutching formula: the Chern number is the degree of the
determinant (for symplectic frames, the Maslov index) of the transition loop
between a frame over a disc and a frame over its complement. That formula is
the technical centre of the part.

### Departure from `DESIGN.md`

The overview placed the splitting definition and the extension lemma in
`Basic.lean`, and the comparison with `clutchingNumber` in `Clutching.lean`.
With the cohomological definition, the class and the number go in
`Topology/VectorBundle/Complex/FirstChernClass.lean`, `Basic.lean` holds the
symplectic number, the splitting description and the extension lemma move to
`Splitting.lean`, `Clutching.lean` holds the disc clutching formula, the
comparison with `clutchingNumber` moves to `ClutchingNumber.lean`, and
`Gluing.lean` is new. This pull request updates the *Files* bullet of part 13
in `DESIGN.md` to match.

## Conventions

- **Surfaces.** In Lean a surface is called `M` (the letter `Σ` is a token,
  not an identifier). A closed surface is
  `[TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [CompactSpace M]`, with `M : Type`, and
  an orientation `o : TauCeti.Manifold.Orientation (𝓡 2) M (Fin 2)`. The
  model `𝓡 2` is `𝓘(ℝ, EuclideanSpace ℝ (Fin 2))`, a case of the model of
  `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`,
  and the one of Mathlib's spheres. Connectedness, `[ConnectedSpace M]`, is
  a hypothesis exactly where the plan or `DESIGN.md` asks for it. The
  topological statements take a homological orientation
  `TauCeti.HomologicalOrientation M E 2` of a compact topological surface;
  the smooth statements pass `o.toHomologicalOrientation`.
- **Universes.** Tau Ceti's fundamental class and local indices live in
  `Type`, and `complexEulerClass` asks for the base and the model fibre in
  one universe. The determinant line has model fibre `Fin k → ℂ` with
  `k = 1` by `rank_det`, so the class is defined for bases `B : Type`. Every
  manifold in the plan is in `Type`.
- **Coefficients.** Integral cohomology is
  `(TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift ℤ)) ℤ
  (ModuleCat.of ℤ (ULift ℤ)) 2`, as for Tau Ceti's Euler classes. The
  Chern number is the underlying integer (`.down`).
- **Complex bundles.** A complex vector bundle is `[FiberBundle G E]
  [VectorBundle ℂ G E]` with `G` a finite-dimensional complex normed space,
  as for `complexEulerClass` and `clutchingNumber`. A smooth real bundle with
  a complex structure reaches this form through *Symplectic vector bundles*'
  map from `SymplecticGeometry.Bundle.ContMDiffComplexStructure` to Tau Ceti's
  `TauCeti.Bundle.ContinuousComplexStructure` and then `.Fiber`.
- **Coordinate discs and the clutching circle.** A coordinate disc
  (`SymplecticGeometry.CoordinateDisc o`, prerequisite 5) is an open
  embedding `φ : Metric.ball (0 : ℂ) 2 → M` that carries the standard
  orientation of `ℂ` to `o`. Its disc is $D=\varphi(\bar B_1)$ and its
  circle is $t\mapsto\varphi(e^{2\pi it})$, counterclockwise in the chart. So
  the circle is oriented as the boundary of $D$, which plays the role of the
  book's $\Sigma_1$. For a frame $\Phi_D$ over $D$ and a frame $\Phi_{out}$
  over $\Sigma\setminus\varphi(B_1)$ the transition loop is
  $\Psi=\Phi_D^{-1}\Phi_{out}$, the book's $\Phi_1^{-1}\Phi_2$. This is the
  convention of Tau Ceti's `clutchingFunction` (frame over the square, the
  trivialization near the collapsed boundary outside). Check: on
  $S^2=D_N\cup D_S$ with $w=1/z$, $\partial_w=-z^2\partial_z$, so the
  transition of $TS^2$ is $-z^2$, of degree $2=c_1(TS^2)$.
- **Connections.** The book's connection form $A\in\Omega^1(P,i\mathbb{R})$ is
  written $A=i\alpha$ with $\alpha$ a real 1-form, since Tau Ceti integrates
  only real forms. Its curvature $F_A=if$ has $f$ the real 2-form on $\Sigma$
  with $\pi^*f=d\alpha$. The book's $c_1=\frac{i}{2\pi}\int F_A$ becomes
  $c_1=-\frac1{2\pi}\int_\Sigma f$, and $\int\tau=-2\pi i\,c_1$ for
  $\tau=i\sigma$ becomes $\int\sigma=-2\pi c_1$. The circle acts on the unit
  circle bundle $P\subset L$ by scalar multiplication, $p\cdot e^{it}$, and the
  fundamental vector field of $1\in\mathbb{R}=\mathrm{Lie}(S^1)$ (through
  `Circle.exp`) is the one on which $\alpha$ is $1$. Check: for $TS^2$ with
  the round metric and $J$ the rotation by $+\pi/2$, a unit section $e_1$ with
  $\nabla e_1=\theta\otimes Je_1$ gives $d\theta=-K\,dA$, so
  $-\frac1{2\pi}\int d\theta=\frac{4\pi}{2\pi}=2$.
- **Why principal connections, not covariant derivatives.** Tau Ceti has
  covariant derivatives on vector bundles and their curvature
  (`CovariantDerivative.curvatureForm`), with values in the endomorphism
  bundle. The plan's milestone is phrased with a 1-form on the circle bundle,
  and its second half asks to realize a given 2-form as a curvature, which on
  the circle bundle is adding a pulled-back 1-form. Working on the circle
  bundle keeps both halves to scalar forms, which Tau Ceti integrates
  directly; the translation to covariant derivatives is not needed by any
  milestone.

## Files

All files are under `SymplecticGeometry/`. The part's own files are in
`Geometry/Manifold/VectorBundle/ChernNumber/`, as in `DESIGN.md`. One extra
file, the topological class and number, goes in
`Topology/VectorBundle/Complex/`, because it uses no smooth structure (a
folder here beside Tau Ceti's folder of the same name; no Tau Ceti file has
the name `FirstChernClass.lean` at that place). The prerequisites have files
of their own, listed with their issues.

### `Topology/VectorBundle/Complex/FirstChernClass.lean`

In the namespace `SymplecticGeometry.Bundle`, for a complex vector bundle
`E` with model `G` over `B : Type`, with `D := detCore ℂ G E` the determinant
core of prerequisite 1:

- `firstChernClass G E`, the Euler class
  `TauCeti.complexEulerClass (Fin D.rank → ℂ) D.core.Fiber h`, where
  `h : finrank ℂ (Fin D.rank → ℂ) = 0 + 1` comes from
  `FiniteRankBundleCore.rank_det` (`D.rank` is `1` only through that
  lemma, not by definition); and `firstChernClass_def` by `(rfl)`.
- `firstChernClass_pullback (f : C(B', B))`: the class of `f *ᵖ E` is the
  pull-back of the class of `E`, from the pull-back isomorphism of
  prerequisite 1 and
  `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`.
- `firstChernClass_congr`: a complex-linear fibrewise isomorphism, continuous
  on total spaces, preserves the class. Prerequisite 1 turns it into one of
  the determinants, and `TauCeti.complexEulerClass_eq_of_fiberwise` applies.
- `firstChernClass_trivial`: zero for `Bundle.Trivial B G`, from
  `TauCeti.complexEulerClass_trivial`.
- `firstChernClass_eq_complexEulerClass`: for a line bundle,
  `firstChernClass G E = complexEulerClass G E hG`.
- `firstChernClass_conj`: the conjugate bundle (Tau Ceti's
  `Topology/VectorBundle/Conjugate.lean`) has the negated class. Prerequisite
  1 gives a conjugate-linear fibrewise isomorphism between the two
  determinants, and
  `TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise`
  applies.
- `chernNumber o G E : ℤ`, for `o : TauCeti.HomologicalOrientation M E' 2`
  of a compact topological surface `M` (with `hn : finrank ℝ E' = 2`): the
  integer under `o.evalFundamentalClass hn _ (ContinuousMap.id M)
  (firstChernClass G E)`; with `chernNumber_def`.
- `chernNumber_neg_orientation`: reversing `o` negates it.
- `chernNumber_congr`, `chernNumber_trivial`, `chernNumber_conj`, from the
  lemmas above.
- `chernNumber_pullback (f : C(M', M))`: `chernNumber o' G (f *ᵖ E) =
  o'.degree o hn f * chernNumber o G E`, from `firstChernClass_pullback` and
  `evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul`.

No Whitney sum formula is claimed over a general base; additivity is proved
over surfaces only, from clutching.

### `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean`

- `chernNumber_pullback_eq_degree_mul`: for `φ : M' → M` smooth between
  closed oriented surfaces, `M` connected, the smooth form
  `chernNumber o'ₕ G (φ *ᵖ E) = TauCeti.degree o' o φ * chernNumber oₕ G E`,
  with `oₕ = o.toHomologicalOrientation`; from `chernNumber_pullback` and
  `degree_toHomologicalOrientation_eq_degree`.
- `symplecticChernNumber o ω : ℤ` for a symplectic vector bundle `(E, ω)` in
  the representation of *Symplectic vector bundles*: the `chernNumber` of the
  complex bundle of a compatible complex structure, chosen by the existence
  theorem of that part. `symplecticChernNumber_eq_chernNumber` gives the same
  value for every compatible or tame `J`. The proof: by that part's
  classification theorem (`.../Symplectic/Classification.lean`), the identity
  of `(E, ω)` is a symplectic isomorphism, so the two complex bundles are
  isomorphic.
- `symplecticChernNumber_neg`: `(E, -ω)` has the negated number, since `-J`
  is compatible with `-ω` and gives the conjugate bundle.
- `symplecticChernNumber_pullback` and `symplecticChernNumber_congr`, from
  the complex statements and the pull-backs and isomorphisms of symplectic
  bundles that *Symplectic vector bundles* gets from #57.

### `Geometry/Manifold/VectorBundle/ChernNumber/Clutching.lean`

The disc clutching formula, for the coordinate discs of prerequisite 5.

- `chernNumber_eq_sum_degree_clutching`: let `φ i`, `i : ι` finite, be
  coordinate discs with disjoint closed discs, `Φ i` a frame of `E` along
  `φ i` on the closed unit disc and `Φout` a frame over the complement of the
  open discs (frames in the sense of Tau Ceti's `Clutching.lean`: continuous
  families of `G ≃L[ℂ] E x`). The Chern number is the sum over `i` of the
  degrees of the normalized determinant
  (`ContinuousLinearEquiv.normalizedDet`) of the loop `(Φ i)⁻¹ ∘ Φout`
  around the `i`-th circle. Proof: the section of the determinant line that
  is the wedge of `Φout` outside, extended radially in each disc, has one
  zero per disc, with index the degree of the determinant of the transition
  (`TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`
  and `TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`).
  One disc is the case `ι = Unit`.
- `symplecticChernNumber_eq_sum_maslovIndex_clutching`: the same with
  symplectic frames (fibrewise symplectic isomorphisms with `stdForm (Fin
  n)`), with the sum of `TauCeti.GLSymplectic.maslovIndex` of the transition
  loops. Proof: make both frames unitary for a compatible `J` by complex
  Gram–Schmidt applied to the Lagrangian half of each frame, using Tau Ceti's
  `Topology/VectorBundle/GramSchmidt.lean`. The change of frame is a map `P`
  into $\mathrm{Sp}(2n)$ on the disc and `P'` on the complement. The new loop
  is $P^{-1}\Psi P'$. By `maslovIndex_mul`, its index is the old index plus
  those of $P^{-1}$ and $P'$ on the circles. The first is $0$ because `P` is
  defined on the whole disc, and the second is $0$ by
  `sum_degree_boundary_eq_zero` (prerequisite 6) applied to the Maslov phase.
  For realified unitary loops the Maslov index is the degree of the loop of
  complex determinants, `TauCeti.GLSymplectic.maslovIndex_map_ofUnitary`.

### `Geometry/Manifold/VectorBundle/ChernNumber/Gluing.lean`

Bundles from clutching data, and isomorphisms from homotopies.

- `clutchingLineBundle φ k`: over a closed surface with a coordinate disc
  `φ`, the smooth Hermitian line bundle glued from the trivial bundles over
  `φ '' ball 0 1` and over the complement of `φ '' closedBall 0 (1/2)`, with
  transition $e^{ik\theta}$ on the annulus between them. It is a
  `VectorBundleCore` with two charts and smooth unitary coordinate changes,
  so Mathlib's `VectorBundleCore` API gives its instances. With its standard
  symplectic form it is a symplectic line bundle, in the representation of
  Hermitian line bundles that #57 adds to *Symplectic vector bundles*.
  `symplecticChernNumber_clutchingLineBundle`: its number is `k`, by the
  clutching formula.
- `nonempty_iso_of_maslovIndex_eq`: two symplectic bundles of the same rank
  over a closed connected oriented surface whose clutching loops, for frames
  over a disc and over its complement, have the same Maslov index are
  isomorphic. Proof: equal index means the loops are freely homotopic, by the
  converse of the homotopy axiom from *Maslov index*. Realize the homotopy as
  a smooth map on the annulus between two concentric discs (Tau Ceti's
  smooth approximation, `Geometry/Manifold/SmoothApprox.lean`). Change the
  outer frame of one bundle on the annulus so that its transition loop
  becomes the other's. Then the frames of the two bundles match into a global
  symplectic isomorphism. The existence of the outer frame is *Symplectic
  vector bundles*' milestone *Unitary trivializations over surfaces with
  boundary*, applied to the complement of an open disc; the frame over the
  disc comes from contractibility (Tau Ceti's
  `TauCeti.exists_continuous_frame`, then smoothed).

### `Geometry/Manifold/VectorBundle/ChernNumber/Axioms.lean`

- The bundled data, in two layers so that "over the same surface" needs no
  equality of surfaces: `structure ClosedConnectedOrientedSurface` (a type
  `M : Type` with the instances above, `[ConnectedSpace M]` and an
  orientation), and `structure SymplecticSurfaceBundle
  (S : ClosedConnectedOrientedSurface)` (the complex rank `n`, a model fibre
  `F : Type` with `finrank ℝ F = 2 * n`, the fibres `E : S → Type` with the
  smooth bundle instances, and the symplectic form `ω` in the representation
  of *Symplectic vector bundles*).
- Operations on `SymplecticSurfaceBundle`, in this file, each a thin
  bundling of the construction of *Symplectic vector bundles* (#57):
  `SymplecticSurfaceBundle.Iso E E'`, the type of smooth fibrewise
  symplectic isomorphisms (not a `CategoryTheory.Iso`: no category is
  needed); `SymplecticSurfaceBundle.pullback (φ : S' → S) (hφ : ContMDiff …)
  E`; `SymplecticSurfaceBundle.whitneySum E E'`, the fibrewise direct sum
  with the sum of the forms; `SymplecticSurfaceBundle.trivial S n`; and
  `SymplecticSurfaceBundle.tangent S σ`, the tangent bundle with an area form
  `σ` inducing the orientation of `S`.
- `structure ChernNumberAxioms
  (c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ) :
  Prop` with four fields, as the plan states the axioms:
  - `nonempty_iso_iff`: `Nonempty (E.Iso E')` if and only if `E.n = E'.n`
    and `c S E = c S E'`;
  - `pullback`: `c S' (E.pullback φ hφ) = TauCeti.degree S'.o S.o φ * c S E`
    for every smooth `φ : S' → S`;
  - `whitneySum`: `c S (E.whitneySum E') = c S E + c S E'`;
  - `tangent`: `c S (tangent S σ) = 2 - 2 * TauCeti.surfaceGenus S` for every
    area form `σ` that induces the orientation of `S`.
- `symplecticChernNumber_whitneySum` (from block frames and
  `TauCeti.GLSymplectic.maslovIndex_sum`, through the clutching formula with
  frames from *Symplectic vector bundles*).
- `symplecticChernNumber_tangent`: for $T\Sigma$ with an area form $\sigma$
  inducing `o`, and a $\sigma$-compatible $J$, the complex orientation of
  $(T\Sigma,J)$ is the orientation of `M`. So the number is the Euler number
  of $T\Sigma$. For the gradient of a Morse function (`TauCeti.exists_isMorse`,
  with a Riemannian metric), the local indices are the signs of the
  Jacobians (`sectionIndex_eq_sign_det_of_hasFDerivAt`). Poincaré–Hopf with
  `k = ℚ` makes their sum the alternating sum of the rational Betti numbers.
  With the finite CW type `TauCeti.FiniteCWType.of_isManifold`, that sum is
  `eulerChar M` (`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology`),
  which is $2-b_1$ by
  `TauCeti.Manifold.Orientation.eulerChar_eq_two_sub_finrank_singularHomology_one`.
  Last, $2-b_1=2-2g$ by
  `TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank`
  and `TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`, given the
  evenness of $b_1$ from prerequisite 2.
- `symplecticChernNumber_nonempty_iso_iff`: the forward direction is
  `symplecticChernNumber_congr`; the converse is
  `nonempty_iso_of_maslovIndex_eq` with the clutching formula.
- `chernNumberAxioms_symplecticChernNumber`.
- `eq_symplecticChernNumber_of_chernNumberAxioms`: uniqueness. Fix `S` and
  let `c` satisfy the axioms. By `nonempty_iso_iff`, `c` is constant on
  isomorphism classes. A trivial bundle is the pull-back of itself along a
  constant map, of degree $0$ (`TauCeti.degree_const`), so `pullback` gives
  it `c = 0`. A bundle of rank `n ≥ 1` and number `k` is isomorphic to
  `clutchingLineBundle φ k` plus a trivial bundle, by
  `symplecticChernNumber_nonempty_iso_iff`. So `c` is `h k` for one function
  `h : ℤ → ℤ`. Since `L_a ⊕ L_b` and `L_(a+b) ⊕ trivial` are isomorphic,
  `whitneySum` makes `h` additive, so `h k = k * h 1`. Last, pull back
  $TS^2$ along a smooth map $\Sigma\to S^2$ of degree one (prerequisite 9):
  `tangent` on $S^2$ and `pullback` give `h 2 = 2`. Normalization on `S`
  alone would not suffice, since it says nothing for the torus.
- `existsUnique_chernNumberAxioms :
  ∃! c : ∀ S : ClosedConnectedOrientedSurface, SymplecticSurfaceBundle S → ℤ,
  ChernNumberAxioms c`, with the surface connected, as `DESIGN.md` and the
  plan say. It is one of the three theorems of the first milestone (see
  `Splitting.lean`), and its docstring ends with the line Milestone: *First
  Chern number of symplectic vector bundles over surfaces*.
- The plan's further remark about $c_1=0$ is the case `E' = trivial` of
  `nonempty_iso_iff`, and is stated as `symplecticChernNumber_eq_zero_iff`.

### `Geometry/Manifold/VectorBundle/ChernNumber/EulerNumber.lean`

- `chernNumber_eq_sum_sectionIndex`: let `L` be a complex line bundle over a
  compact homologically oriented surface, and `s` a continuous section with
  finitely many zeros. Then `chernNumber o ℂ L` is the sum over the zeros of
  `TauCeti.VectorBundleOrientation.sectionIndex` for the canonical
  orientation `TauCeti.VectorBundleOrientation.complex`. The proof is
  `firstChernClass_eq_complexEulerClass` followed by
  `evalFundamentalClass_eulerClass_eq_sum_sectionIndex`. The surface need not
  be connected. The clutching proofs use this general form.
- **Milestone** `chernNumber_eq_sum_sign_of_transverse`, the corollary in the
  plan's form: for a smooth complex line bundle over a closed oriented surface
  (a smooth real rank-2 bundle with a complex structure, in the
  representation of *Symplectic vector bundles*), and `s` a smooth section
  transverse to the zero section in Tau Ceti's sense
  (`TauCeti.sectionLinearization` surjective at every zero), the zero set is
  finite and the Chern number is the sum over the zeros of the signs $\pm1$
  of the Jacobians in oriented charts
  (`sectionIndex_eq_sign_det_of_hasFDerivAt`), the book's intersection
  indices. Finiteness: a transverse zero is isolated, by the inverse function
  theorem in a chart, and the zero set is compact. Milestone: *First Chern
  number as an Euler number*. With this definition the milestone does not
  depend on the other two.

### `Geometry/Manifold/VectorBundle/ChernNumber/ChernWeil.lean`

- Uses the circle bundle `P` of a Hermitian line bundle and its connection
  forms from prerequisites 3 and 4.
- `chernNumber_eq_integral_curvature`: for every connection form `α` on `P`
  (`hα : IsConnectionForm α`), `(chernNumber o ℂ L : ℝ) = -(2 * π)⁻¹ *
  TauCeti.integralTopForm o hα.curvature`. Proof: two connection forms
  differ by `π^* a`, so their curvatures differ by `d a`, whose integral is
  $0$ (`TauCeti.integralTopForm_mextDeriv_eq_zero`; no connectedness needed).
  So it suffices to compute one connection. Choose frames as in the clutching
  formula, one disc per component of `M`, normalized so that each transition
  is exactly $\Psi=\Phi_D^{-1}\Phi_{out}=e^{ik_j\theta}$
  (`Circle.joined_iff_circleDegree_eq`, and a change of frame on a collar).
  Take the connection that is flat for the outer frame. Since
  $\Phi_{out}=\Phi_D\Psi$, in the disc frame it reads
  $-k_j\beta(r)\,d\theta$, with $\beta$ a smooth cut-off equal to $1$ near
  the circle and $0$ near the centre. Its curvature is supported in the
  discs, where the integral is computed in polar coordinates: $-2\pi k_j$
  for each disc (`TauCeti.integralTopForm_eq_chartIntegral`), so the
  right-hand side is $\sum_j k_j$, the Chern number by the clutching formula.
- `exists_isConnectionForm_curvature_eq`: if `M` is connected, every smooth
  real 2-form `σ` with `∫ σ = -2π * chernNumber o ℂ L` is the curvature of a
  connection form. Proof: `σ - hα₀.curvature` has integral $0$, so it is
  exact by `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`
  (with `TauCeti.compactlySupportedForms_eq_top`). Then add the pull-back of
  a primitive to `α₀`.
- **Milestone** `chernNumber_eq_integral_curvature_and_exists`: the
  conjunction of the first statement, for every closed oriented surface, and
  the second, under `ConnectedSpace M`, as the plan and the *Milestones*
  table of `DESIGN.md` say. It is written with real forms, by the convention
  above. Milestone: *Chern–Weil formula for circle bundles over surfaces*.

### `Geometry/Manifold/VectorBundle/ChernNumber/ClutchingNumber.lean`

The comparison with Tau Ceti's `TauCeti.clutchingNumber`. For a based
sphere `p : Ω^ (Fin 2) X x` and a complex bundle `E` over `X`,
`clutchingNumber G E p` equals the Chern number of the pull-back of `E` to
$S^2$ along the map that `p` induces, for the orientation of $S^2$ for which
the collapse $I^2\to S^2$ preserves orientation in the interior. Proof: the
interior of the square is a coordinate disc, the frame along `p` is a frame
over it, and the trivialization near `x` is a frame over the complement; the
two clutching functions agree by the convention above. The theorem is
`clutchingNumber_eq_chernNumber`.

### `Geometry/Manifold/VectorBundle/ChernNumber/Splitting.lean`

The book's description and its key lemma. Both are part of the first
milestone, with `existsUnique_chernNumberAxioms`: the milestone is complete
only when `symplecticChernNumber_eq_boundaryMaslovIndex` and
`exists_extension_iff_boundaryMaslovIndex_eq_zero` are proved too, and both
docstrings end with the same milestone line.

- A *splitting* of a closed oriented surface is given by a smooth
  `f : M → ℝ` with regular value `0`: $\Sigma_1=\{f\le0\}$,
  $\Sigma_2=\{f\ge0\}$, $C=f^{-1}(0)$. `C` is a compact 1-manifold by Tau
  Ceti's regular fibres (`Geometry/Manifold/RegularValue/ManifoldLevel.lean`).
  It is collared in $\Sigma_1$, which has a fundamental class relative to
  `C` (`TauCeti.HomologicalOrientation.fundamentalClassRel`) whose boundary is
  a fundamental class of `C`, the boundary orientation
  (`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`).
- `boundaryMaslovIndex`: for `Ψ : C → Sp(2n)` continuous, the image of that
  class of `C` under the Maslov phase composed with `Ψ`, in
  $H_1(S^1;\mathbb{Z})\cong\mathbb{Z}$. `boundaryMaslovIndex_eq_sum`: when
  the components of `C` are parametrized by orientation-preserving loops,
  it is the sum of `TauCeti.GLSymplectic.maslovIndex` of the loops.
- `symplecticChernNumber_eq_boundaryMaslovIndex`: for symplectic frames over
  $\Sigma_1$ and $\Sigma_2$, the number is `boundaryMaslovIndex` of the
  transition $\Phi_1^{-1}\Phi_2$ on `C`, by the argument principle along a
  splitting (prerequisite 7) and the unitary reduction of `Clutching.lean`.
- `exists_extension_iff_boundaryMaslovIndex_eq_zero`: the book's Lemma 2.7.3,
  for a connected compact oriented surface whose boundary is not empty, in the
  representation that *Symplectic vector bundles* fixes for its last
  milestone. A continuous `Ψ` on the boundary extends continuously over the
  surface if and only if its boundary Maslov index is $0$. "Only if" is the
  argument principle. "If": cap the boundary circles with discs
  (prerequisite 8) and glue a bundle over the closed surface with clutching
  `Ψ`. Its number is $0$, so it is trivial by `nonempty_iso_iff`. A global
  frame then writes `Ψ` as a map defined on the surface times maps defined on
  the discs, and the latter are null-homotopic on the circles, which a collar
  absorbs.

## What the part uses

- **From other parts.** *Symplectic vector bundles*: the representation of
  symplectic bundles; existence of compatible complex structures and the map
  to `ContinuousComplexStructure`; the classification theorem; unitary
  trivializations over surfaces with boundary, applied to the complement of
  open coordinate discs. The isomorphisms, pull-backs and direct sums of
  symplectic bundles, the tangent bundle of a surface with an area form, and
  Hermitian line bundles are not yet in part 12 of `DESIGN.md` nor in its
  open design (#53); #57 adds them, and its issues block issues 3, 10, 13
  and 14 below. *Maslov index*, symplectic loops: the converse of the
  homotopy axiom. *Standard model*: `stdForm`. If *Symplectic vector
  bundles* states its trivialization milestone for abstract surfaces with
  boundary, the issue for `Gluing.lean` derives the case of the complement of
  open discs in a closed surface (a regular domain, as in `Splitting.lean`).
- **From Tau Ceti.** Everything named above: `complexEulerClass` and its
  fibrewise lemmas (`Topology/VectorBundle/Orientation/Complex/`), the Euler
  class API (`Topology/VectorBundle/Orientation/`), local indices and their
  computation (`.../SectionIndex.lean`, `.../SectionIndex/Degree.lean`), the
  winding number of a plane map
  (`AlgebraicTopology/Singular/LocalHomology/Winding.lean`), fundamental
  classes and degrees (`AlgebraicTopology/Cohomology/FundamentalClass.lean`,
  `Geometry/Manifold/Degree/`), finite-rank cores, their determinant,
  pull-backs and conjugates (`Topology/VectorBundle/FiniteRank/`), Morse
  functions and Poincaré–Hopf (`Geometry/Manifold/Morse/`), Euler
  characteristics and genus (`AlgebraicTopology/Cellular/EulerCharacteristic/`),
  generic sections (`Geometry/Manifold/VectorBundle/Section/Generic.lean`),
  the Maslov index of symplectic loops, frames and clutching
  (`Topology/VectorBundle/Complex/Clutching.lean`,
  `Topology/VectorBundle/Contractible.lean`), sphere bundles and their smooth
  structure (`Topology/VectorBundle/SphereBundle/`,
  `Geometry/Manifold/VectorBundle/Riemannian/Sphere.lean`), unitary frame
  bundles (`Topology/VectorBundle/OrthonormalFrame/Principal.lean`),
  integration and Stokes on closed manifolds
  (`Geometry/Manifold/DifferentialForm/Integration/`,
  `Geometry/Manifold/DeRham/`), smooth principal bundles
  (`Geometry/Manifold/FiberBundle/Principal.lean` and `Principal/`), descent of
  basic forms (`Geometry/Manifold/DifferentialForm/Pullback/Descent.lean` and
  `Submersion.lean`), relative fundamental classes
  (`AlgebraicTopology/Singular/LocalHomology/RelativeFundamentalClass.lean`,
  `BoundaryFundamentalClass.lean`), and `surfaceGenus`.
- **From Mathlib.** Vector bundles and their cores, pullbacks and products;
  `Circle` with its Lie group structure and `Circle.exp`; spheres as
  manifolds.

## Issues

Each issue is a few hundred lines. The prerequisites come first. They are
general infrastructure in files of their own, named after their mathematics,
and can start at once unless a blocker is named. Then come the part's own
issues, in an order where each issue's blockers come before it.

### Prerequisites

1. **Determinant line of a vector bundle.** Most of what is needed exists in
   Tau Ceti: `FiniteRankBundleCore.ofBundle` (`FiniteRank/Basic.lean`),
   `ofBundleIso`, `pullback_ofBundle` (`FiniteRank/Pullback.lean`),
   `CoordinateFunctor.mapCoreTrivialIso` (`FiniteRank/CoordinateFunctor.lean`),
   `exteriorPowerOneNatIso` and `rank_det` (`FiniteRank/ExteriorPower.lean`),
   and `FiniteRankBundleCore.conjugate` with `conjugatePullbackIso`
   (`FiniteRank/Conjugate.lean`). The issue adds only:
   - in `Topology/VectorBundle/FiniteRank/OfBundle.lean`,
     `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 G E (h :
     finrank 𝕜 G = n)`, the generalization of `ofBundle` to a bundle with any
     finite-dimensional model `G` over any `𝕜`, through
     `ContinuousLinearEquiv.ofFinrankEq`, with its rank, the fibrewise
     identification with `E`, and the analogues of `ofBundleIso` and
     `pullback_ofBundle`;
   - in `Topology/VectorBundle/Determinant.lean`,
     `SymplecticGeometry.Bundle.detCore 𝕜 G E :=
     (ofBundleOfFinrankEq 𝕜 G E rfl).det`, over any `𝕜`, with its fibrewise
     isomorphisms induced by those of `E`, compatibility with pull-back
     (through `CoordinateFunctor.functor_comp_pullbackFunctor`), the trivial
     bundle, and the identification with `E` in rank one;
   - the one step specific to `ℂ`: a natural isomorphism
     `det ∘ conjugate ≅ conjugate ∘ det` of `FiniteRankBundleCore ℂ B`, as a
     conjugate-linear fibrewise isomorphism between `detCore ℂ` of the
     conjugate bundle and `detCore ℂ G E`.

   Done when these are proved and build.
2. **Evenness of the first Betti number of a closed orientable surface.**
   `AlgebraicTopology/Singular/SurfaceGenus.lean` (the name of Tau Ceti's
   file, so that the two merge): `TauCeti.HomologicalOrientation.even_finrank_singularHomology_one`,
   for a compact connected homologically oriented surface, `finrank ℚ
   H₁(M; ℚ)` is even. Only this is new; the step from evenness to
   `χ = 2 - 2 * surfaceGenus` is already Tau Ceti's
   `eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank` with
   `genus_eq_surfaceGenus` (`AlgebraicTopology/Cellular/EulerCharacteristic/Genus.lean`;
   `TauCeti.IsMorse.finiteCWType` or `FiniteCWType.of_isManifold` gives the
   instance). Route: Tau Ceti's
   `TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`,
   given injectivity of the cap product with the fundamental class in degree
   one. That injectivity is the degree-one case of Poincaré duality, which
   Tau Ceti prepares in `AlgebraicTopology/Cohomology/CompactSupport/`
   (`HomologicalOrientation.dualityMap` and its criterion in `Duality.lean`)
   but does not finish. The issue first checks whether Tau Ceti has finished
   it since the pin. If not, duality for closed oriented manifolds from that
   criterion is likely several issues, and is split into them when the issues
   are created. Done when the evenness theorem is proved.
3. **The unit circle bundle of a Hermitian line bundle.**
   `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`. The circle
   bundle of a smooth Hermitian line bundle `L` is Tau Ceti's unit sphere
   bundle `TauCeti.sphereBundle ℂ L` (`Topology/VectorBundle/SphereBundle/Basic.lean`),
   with its charts `Bundle.Trivialization.sphereBundle`
   (`SphereBundle/LocallyTrivial.lean`) and its smooth structure
   (`isManifold_sphereBundle`, `isSmoothEmbedding_coe_sphereBundle` in
   `Geometry/Manifold/VectorBundle/Riemannian/Sphere.lean`); equivalently the
   rank-one unitary frame bundle, which Tau Ceti already makes a
   `PrincipalBundle` (`Topology/VectorBundle/OrthonormalFrame/Principal.lean`).
   The issue adds only: the right action of `Circle` by scalar
   multiplication, the `TauCeti.PrincipalBundle Circle` instance (from the
   unitary frame bundle, through Tau Ceti's `circleEquivUnitary : Circle ≃ₜ* unitary ℂ`
   and the identification of `unitary (ℂ →L[ℂ] ℂ)` with `unitary ℂ`), and the
   relation between the smooth structure of the sphere bundle as a
   submanifold and that of `TauCeti.ManifoldTotalSpace Circle` given by
   `TauCeti.PrincipalBundle.contMDiffFiberBundle_iff`, so that the projection
   is a smooth submersion. Blocked by the issue from #57 that fixes Hermitian
   line bundles. Done when these instances and the submersion property are
   proved.
4. **Connection forms on principal circle bundles.**
   `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`: for a
   smooth principal `Circle`-bundle `P` over `M`, the predicate
   `SymplecticGeometry.IsConnectionForm α` for a smooth real 1-form on the
   total space, invariant under the action and equal to $1$ on the
   fundamental vector field of $1$ (`TauCeti.rightFundamentalVectorField`
   composed with `Circle.exp`). Its curvature `IsConnectionForm.curvature
   (hα : IsConnectionForm α)`, the 2-form on `M` whose pull-back is `d α`,
   exists and is unique by descent of basic forms (`TauCeti.RoughForm.IsBasic`,
   `Manifold.IsSubmersion.exists_smoothForm_mpullback_eq_iff`).
   API: `IsConnectionForm.curvature_def`;
   `IsConnectionForm.mpullback_curvature` (the pull-back of the curvature is
   `d α`) and `IsConnectionForm.curvature_eq_iff` (it characterizes the
   curvature); `α + π^* a` is a connection form for every 1-form `a` on `M`,
   any two differ by such an `a`, and `curvature (α + π^* a) = curvature α +
   d a`; existence of a connection form, by a partition of unity from the
   `TauCeti.PrincipalBundle.trivializationOfSection` charts; and the local
   form $d\theta+\pi^*s^*\alpha$ in the trivialization of a local section
   `s`. Blocked by 3 only for its example; the definitions are for any `P`.
   Done when this API is proved and applied to the circle bundle of 3.
5. **Coordinate discs.**
   `AlgebraicTopology/Singular/LocalHomology/CoordinateDisc.lean`, beside
   Tau Ceti's homological orientations and winding numbers:
   `structure SymplecticGeometry.CoordinateDisc (o : TauCeti.HomologicalOrientation M E 2)`,
   an open embedding `Metric.ball (0 : ℂ) 2 → M` that carries the local
   orientations of `ℂ` to those of `o`, with `@[ext]`; its closed disc
   `CoordinateDisc.disc` (the image of `closedBall 0 1`, compact) and open
   disc, its boundary loop `CoordinateDisc.boundaryLoop` ($t\mapsto
   \varphi(e^{2\pi it})$), `CoordinateDisc.reverse` for the opposite
   orientation (precomposition with conjugation), the constructor
   `CoordinateDisc.ofChart` from an orientation-preserving smooth chart of a
   smoothly oriented surface (through `o.toHomologicalOrientation`), and
   `exists_coordinateDisc` (one centred at any point, and finitely many with
   disjoint closed discs at distinct points). Done when this API is proved.
6. **Argument principle for discs.**
   `AlgebraicTopology/Singular/LocalHomology/ArgumentPrinciple.lean`:
   `SymplecticGeometry.sum_degree_boundary_eq_zero`. Let `φ i`, `i : ι`
   finite, be coordinate discs of a compact homologically oriented surface
   with disjoint closed discs, and let `u` be continuous and nowhere zero on
   the complement of the open discs, with values in `ℂ`. Then the degrees
   (`Circle.degree`) of `u/|u|` around the boundary loops sum to $0$. Proof:
   extend `u` radially into each disc, with one zero at each centre. This is
   a section of the trivial line bundle with finitely many zeros. Its local
   index at a centre is the winding number of its boundary loop, by
   `TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul` and
   `TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`. The
   indices sum to the Euler number of the trivial bundle, which is $0$. This
   is the half of the book's Lemma 2.7.3 needed for discs. Blocked by 5.
7. **Argument principle along a splitting.** In the same file: let `X` be
   compact with collared boundary `∂X` and oriented interior, as in
   `RelativeFundamentalClass.lean`. Let `L` be an oriented real plane bundle
   over `X`, with a nowhere-zero section `s` on `∂X` and a section `t` with
   finitely many zeros, all in the interior, and equal to `s` on `∂X`. Then
   `SymplecticGeometry.sum_sectionIndex_eq_boundaryDegree`: the sum of the
   local indices of `t` is the degree of `s` against the boundary class
   `∂[X, ∂X]`. Route: excision and the connecting morphism of `(X, ∂X)`,
   with the pairing of the relative Thom class pulled back by `t`. Done when
   this and the corresponding Euler-number formula for a closed surface split
   along `f⁻¹(0)`, `SymplecticGeometry.eulerNumber_eq_boundaryDegree`, are
   proved. Blocked by 6.
8. **Capping a surface with boundary.** In the file that *Symplectic vector
   bundles* uses for surfaces with boundary: a compact oriented surface with
   boundary circles parametrized by orientation-reversing loops, glued to
   discs along them, is a closed oriented surface, by Tau Ceti's
   `Geometry/Manifold/Gluing/`. The main result is
   `SymplecticGeometry.capDiscs`, the closed surface, with
   `isOpenEmbedding_capDiscs_inl` and `capDiscs_coordinateDisc`, the caps as
   coordinate discs. Blocked by the issue of *Symplectic vector bundles*
   that fixes that representation, and by 5.
9. **A map of degree one onto the sphere.**
   `Geometry/Manifold/Degree/Collapse.lean`:
   `SymplecticGeometry.exists_contMDiff_degree_eq_one`, every closed
   connected oriented surface has a smooth map to $S^2$ of degree one, by
   collapsing the complement of a coordinate disc through a cut-off, with
   `TauCeti.degree` computed at the image of the centre. It also gives the
   facts about $S^2$ that uniqueness uses: its orientation
   `SymplecticGeometry.sphereOrientation` and `surfaceGenus_sphere`
   (`surfaceGenus = 0`, from Tau Ceti's homology of spheres). Blocked by 5.
   Done when both are proved.

### The part's own issues

10. **Chern classes and numbers.** `FirstChernClass.lean` and `Basic.lean`.
    Blocked by 1, by *Symplectic vector bundles*' issues for symplectic
    bundles and complex structures, by its classification issue for
    `symplecticChernNumber_eq_chernNumber`, and by the issues from #57 for
    pull-backs and isomorphisms of symplectic bundles.
11. **The Euler-number milestone.** `EulerNumber.lean`. Blocked by 10.
12. **The disc clutching formula.** `Clutching.lean`. Blocked by 6 and 10.
13. **Gluing.** `Gluing.lean`. Blocked by 12, by *Maslov index*'s
    symplectic-loop issue, by *Symplectic vector bundles*' issue for
    trivializations over surfaces with boundary, and by the issue from #57
    for Hermitian line bundles.
14. **The axioms.** `Axioms.lean`. Blocked by 2, 9 and 13, and by the issues
    from #57 for direct sums and area-form tangent bundles. If it is too
    long, `symplecticChernNumber_tangent` goes first, on its own.
15. **The Chern–Weil milestone.** `ChernWeil.lean`. Blocked by 3, 4 and 12.
16. **Comparison with clutching numbers.** `ClutchingNumber.lean`. Blocked
    by 12.
17. **The splitting description.** `Splitting.lean`, up to
    `symplecticChernNumber_eq_boundaryMaslovIndex`. Blocked by 7 and 12.
18. **The extension lemma.** `exists_extension_iff_boundaryMaslovIndex_eq_zero`
    in `Splitting.lean`. Blocked by 8, 14 and 17.

The first milestone needs issues 1, 2, 5–10, 12–14, 17 and 18, with the
named issues of other parts; it is done only when 14, 17 and 18 are all
merged. The Euler-number milestone needs 1, 10 and 11, and the Chern–Weil
milestone 1, 3–6, 10, 12 and 15. Issue 16 completes the comparison with Tau
Ceti.
