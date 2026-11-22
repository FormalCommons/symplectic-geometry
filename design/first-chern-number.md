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

**No decomposition of surfaces is needed.** `DESIGN.md` listed a
decomposition of closed surfaces among the missing infrastructure, because a
splitting definition needs splittings to exist and to be compared. With the
cohomological definition nothing is cut except along coordinate discs, which
exist around every point (prerequisite 5), and along the regular level set
of a function that `Splitting.lean` takes as data. Normalization uses
Poincaré–Hopf and Tau Ceti's genus lemmas instead of a classification of
surfaces, and uniqueness pulls back from $S^2$ along a degree-one map rather
than comparing surfaces of equal genus. So neither a decomposition nor the
classification of closed surfaces is used anywhere in the part.

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
`Gluing.lean` is new. The *Files* bullet of part 13 in `DESIGN.md` is
updated to match.

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
  (`SymplecticGeometry.CoordinateDisc o.toHomologicalOrientation`,
  prerequisite 5) is an open
  embedding `φ : CoordinateDisc.ball → M` (the ball `Metric.ball (0 : ℂ) 2`
  as an open set of `ℂ`) that carries the standard
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
`Geometry/Manifold/VectorBundle/ChernNumber/`, as in `DESIGN.md`. The
topological class and number, and the complex-linear maps of complex
bundles that `Basic.lean` needs, go in
`Topology/VectorBundle/Complex/`, because they use no smooth structure (a
folder here beside Tau Ceti's folder of the same name; no Tau Ceti file has
the name `FirstChernClass.lean` at that place, and `Structure.lean` is
named after Tau Ceti's file there so that the two can merge). Two general
lemmas on Euler classes of finite-rank cores go in
`Topology/VectorBundle/FiniteRank/EulerClass.lean`, and the complex-linear
equivalence of a real one that commutes with `I` in
`Topology/Algebra/Module/ComplexSmulI.lean`, named after Tau Ceti's file
where `ContinuousLinearMap.complexOfMapISmul` lives. The
prerequisites have files of their own, listed with their issues.

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
  pull-back of the class of `E`, from the pull-back equality of
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
- `chernNumber o hn G E : ℤ`, for `o : TauCeti.HomologicalOrientation M E' 2`
  of a compact topological surface `M` and `hn : finrank ℝ E' = 2`: the
  integer under `o.evalFundamentalClass hn _ (ContinuousMap.id M)
  (firstChernClass G E)`; with `chernNumber_def`.
- `chernNumber_neg_orientation`: reversing `o` negates it.
- `chernNumber_congr`, `chernNumber_trivial`, `chernNumber_conj`, from the
  lemmas above.
- `chernNumber_pullback (f : C(M', M))`, with `[PreconnectedSpace M]`:
  `chernNumber o' hn' G (f *ᵖ E) = o'.degree o hn' f * chernNumber o hn G E`, from
  `firstChernClass_pullback` and
  `evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul`, which needs
  the target compact and preconnected.

No Whitney sum formula is claimed over a general base; additivity is proved
over surfaces only, from clutching.

### `Topology/VectorBundle/FiniteRank/EulerClass.lean`

In the namespace `TauCeti.FiniteRankBundleCore`, for complex finite-rank
cores, used by `FirstChernClass.lean`:

- `complexEulerClass_eq_of_iso`: isomorphic cores have the same
  `TauCeti.complexEulerClass`, from
  `TauCeti.complexEulerClass_eq_of_fiberwise` applied to `isoFiberEquiv e`
  of `FiniteRank/Basic.lean`, which this file imports;
- `complexEulerClass_pullback`: the class of `A.pullback f` is the
  pull-back of the class of `A`, from
  `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`.

### `Topology/VectorBundle/Complex/Structure.lean`

In the namespace `TauCeti.Bundle.ContinuousComplexStructure`, for
continuous complex structures `J₁`, `J₂` on real bundles `V₁`, `V₂` over
one base and fibrewise real-linear equivalences `Φ`:

- `fiberEquivOfCommute`: if `Φ` intertwines `J₁` with `J₂`, the
  complex-linear equivalences `J₁.Fiber b ≃L[ℂ] J₂.Fiber b`, and
  `continuous_fiberEquivOfCommute` (continuous on total spaces, for any
  complex models, when `Φ` is);
- `fiberEquivConjOfAnticommute`: if `Φ` intertwines `J₁` with `-J₂`, the
  complex-linear equivalences from `J₁.Fiber b` to the conjugate
  `ConjugateBundle J₂.Fiber b`, and
  `continuous_fiberEquivConjOfAnticommute`.

They turn the real isomorphisms of *Symplectic vector bundles* into the
complex ones that `chernNumber_congr` takes.

### `Topology/Algebra/Module/ComplexSmulI.lean`

- `ContinuousLinearEquiv.complexOfMapISmul`: a continuous real-linear
  equivalence of complex modules that commutes with multiplication by `I`,
  as a continuous complex-linear one, from Tau Ceti's
  `ContinuousLinearMap.complexOfMapISmul`. `Structure.lean` builds its
  equivalences with it, and so does `pullbackFiberEquiv` in
  `Geometry/Manifold/VectorBundle/ComplexStructure.lean` of *Symplectic
  vector bundles*, which imports this file.

### `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean`

- `chernNumber_pullback_eq_degree_mul`: for `φ : M' → M` smooth between
  closed oriented surfaces, `M` connected, the smooth form
  `chernNumber o'ₕ hn G (φ *ᵖ E) = TauCeti.degree o' o φ * chernNumber oₕ hn G E`,
  with `oₕ = o.toHomologicalOrientation hn`, for `φ : C(M', M)` with
  `ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E') 1 φ` and both surfaces modelled on `E'`; from
  `chernNumber_pullback` and `degree_toHomologicalOrientation_eq_degree`.
- `symplecticChernNumber o hn G ω : ℤ` for a symplectic vector bundle
  `(E, ω)` in the representation of *Symplectic vector bundles*, with `o` a
  homological orientation and `G` the complex model of the complex bundles
  (`[Fact (finrank ℝ F = 2 * finrank ℂ G)]`): the `chernNumber` of the
  complex bundle of a continuous complex structure tamed by `ω`, chosen by
  `Classical.choose`, and `0` if there is none. Taking tame rather than
  compatible structures, at regularity `0`, keeps the definition free of
  hypotheses on the base; the existence theorem of that part gives one for
  every nondegenerate form. `symplecticChernNumber_eq_chernNumber` gives the
  same value for every compatible or tame `J`. The proof: two complex
  structures tamed by one form are isomorphic
  (`ContMDiffTwoForm.Tames.exists_complex_bundleEquiv` in
  `.../Symplectic/Classification.lean`).
- `symplecticChernNumber_neg`: `(E, -ω)` has the negated number, since `-J`
  is compatible with `-ω` and gives the conjugate bundle.
- `symplecticChernNumber_pullback` and `symplecticChernNumber_congr`, from
  the complex statements and the pull-backs and isomorphisms of symplectic
  bundles that *Symplectic vector bundles* gets from #57. Both take the form
  nondegenerate, so that a compatible complex structure exists.
- The file imports `Geometry/Manifold/VectorBundle/Symplectic/FirstChernClass.lean`
  of *First Chern class of nondegenerate forms*; `Tames.chernNumber_eq`,
  `symplecticChernNumber_neg`,
  `symplecticChernNumber_congr` and `symplecticChernNumber_pullback` follow
  from the first-Chern-class lemmas there.

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
  - `apply_pullback`: `c S' (E.pullback φ hφ) = TauCeti.degree S'.o S.o φ *
    c S E` for every smooth `φ : S' → S`;
  - `apply_whitneySum`: `c S (E.whitneySum E') = c S E + c S E'`;
  - `apply_tangent`: `c S (SymplecticSurfaceBundle.tangent S σ) = 2 - 2 *
    TauCeti.surfaceGenus S` for every area form `σ` that induces the
    orientation of `S`.
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
  constant map, of degree $0$ (`TauCeti.degree_const`), so `apply_pullback`
  gives it `c = 0`. A bundle of rank `n ≥ 1` and number `k` is isomorphic to
  `clutchingLineBundle φ k` plus a trivial bundle, by
  `symplecticChernNumber_nonempty_iso_iff`. So `c` is `h k` for one function
  `h : ℤ → ℤ`. Since `L_a ⊕ L_b` and `L_(a+b) ⊕ trivial` are isomorphic,
  `apply_whitneySum` makes `h` additive, so `h k = k * h 1`. Last, pull back
  $TS^2$ along a smooth map $\Sigma\to S^2$ of degree one (prerequisite 9):
  `apply_tangent` on $S^2$, with the orientation and area form of
  prerequisite 9, and `apply_pullback` give `h 2 = 2`. Normalization on `S`
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
  finitely many zeros. Then `chernNumber o hn G L`, for a model `G` of complex
  dimension one, is the sum over the zeros of
  `TauCeti.VectorBundleOrientation.sectionIndex` for the canonical
  orientation `TauCeti.VectorBundleOrientation.complex`. The proof is
  `firstChernClass_eq_complexEulerClass` followed by
  `evalFundamentalClass_eulerClass_eq_sum_sectionIndex`. The surface need not
  be connected. The clutching proofs use this general form.
- **Milestone** `chernNumber_eq_sum_sign_of_transverse`, the corollary in the
  plan's form: for a smooth complex line bundle over a closed oriented surface
  (a `C¹` real rank-2 bundle with a continuous complex structure
  `TauCeti.Bundle.ContinuousComplexStructure`, which the complex structures
  of *Symplectic vector bundles* give), and `s` a `C¹` section
  transverse to the zero section in Tau Ceti's sense
  (`TauCeti.sectionLinearization` surjective at every zero), the zero set is
  finite and the Chern number is the sum over the zeros of $\pm1$, according as
  the linearization preserves the orientations or not; in oriented charts, the
  sign of the Jacobian
  (`sectionIndex_eq_sign_det_of_hasFDerivAt`), the book's intersection
  indices. Finiteness is Tau Ceti's `TauCeti.finite_sectionZero_of_contMDiff`
  (`Geometry/Manifold/VectorBundle/Section/SmoothZero.lean`), its Fredholm
  and index hypotheses supplied by
  `ContinuousLinearMap.isFredholm_of_finiteDimensional` and
  `TauCeti.index_sectionLinearization_of_finiteDimensional`, as in
  `Section/Generic.lean`. Milestone: *First Chern
  number as an Euler number*. With this definition the milestone does not
  depend on the other two.

### `Geometry/Manifold/VectorBundle/ChernNumber/ChernWeil.lean`

- Uses the circle bundle `P` of a Hermitian line bundle and its connection
  forms from prerequisites 3 and 4.
- `chernNumber_eq_integral_curvature`: for every connection form `α` on `P`
  (`hα : IsCircleConnectionForm α`), `(chernNumber (o.toHomologicalOrientation hn) hn ℂ L :
  ℝ) = -(2 * π)⁻¹ * TauCeti.integralTopForm o hα.curvature`. Proof: two connection forms
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
- **Which homological orientation.** The statement uses
  `o.toHomologicalOrientation hn`, not the opposite one that Decision 6 of
  `design/pseudoholomorphic-energy.md` calls correctly signed ($s=-1$). The
  sign $s$ compares Tau Ceti's local orientations with the class of a
  positively oriented singular simplex, so only a comparison through
  singular chains meets it, such as
  `integralTopForm_eq_singularHomologyPeriod`. This proof forms no singular
  chain. The integral is computed in polar coordinates in charts positive
  for `o`. The Chern number is computed by the clutching formula, whose
  signs come from Tau Ceti's local indices for `o.toHomologicalOrientation`
  (`sectionIndex_eq_sign_det_of_hasFDerivAt`, as in
  `chernNumber_eq_sum_sign_of_transverse`). The discs join the two
  computations: they are taken as `CoordinateDisc.ofChart` of charts
  positive for `o`, which are coordinate discs for
  `o.toHomologicalOrientation`. Check on $S^2$ with the orientation of its
  complex structure: the Chern number of $TS^2$ for
  `o.toHomologicalOrientation` is $\chi(S^2)=2$ by the Euler-number
  milestone, and the integral side is $2$ by the computation in
  *Conventions*. With the opposite orientation the left side would be $-2$.
- `exists_isCircleConnectionForm_curvature_eq`: if `M` is connected, every smooth
  real 2-form `σ` with `TauCeti.integralTopForm o σ = -2π * chernNumber
  o.toHomologicalOrientation ℂ L` is the curvature of a
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

- **Surfaces with boundary.** The setting is that of Tau Ceti's
  `RelativeFundamentalClass.lean`: a compact Hausdorff `X`, an open embedding
  `ι : M → X` of a surface oriented by `o : HomologicalOrientation M E 2`,
  and a collared `f : N → X` whose image is the complement of `ι(M)`. The
  boundary degree of prerequisite 7, `o.boundaryDegree hn hι hιf hf u` for
  `u : C(∂X, Circle)`, pairs `u` with the boundary class
  `∂[X, ∂X]`.
- `boundaryMaslovIndex`: for `Ψ : C(∂X, GLSymplectic n ℝ)`, the boundary
  degree of `TauCeti.GLSymplectic.maslovPhase ∘ Ψ` (continuous by
  `continuous_maslovPhase`), with `boundaryMaslovIndex_def`.
  `boundaryMaslovIndex_eq_sum`: when the components of `∂X` are parametrized
  by loops compatible with the boundary class, it is the sum of
  `TauCeti.GLSymplectic.maslovIndex` of the loops (from
  `boundaryDegree_eq_sum_degree`).
- **Two settings meet this one.** A *splitting* of a closed oriented surface
  is given by a smooth `g : M → ℝ` with regular value `0`:
  $\Sigma_1=\{g\le0\}$, $\Sigma_2=\{g\ge0\}$, $C=g^{-1}(0)$. `C` is a compact
  1-manifold by Tau Ceti's regular fibres
  (`Geometry/Manifold/RegularValue/ManifoldLevel.lean`), collared in
  $\Sigma_1$ by Tau Ceti's band homeomorphism, so $X=\Sigma_1$ with interior
  $\{g<0\}$ is an instance; the collar is
  `SymplecticGeometry.isCollared_inclusion_levelSet` of prerequisite 7 (the
  inclusion of $g^{-1}(0)$ into $\{g\le0\}$ is `TauCeti.IsCollared`). A
  compact surface with boundary in the representation that
  *Symplectic vector bundles* fixes for its last milestone, a manifold over
  `𝓡∂ 2`, is an instance with `ι` the inclusion of the interior and `f` that
  of the boundary, collared by
  `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`; the issue proves
  the identification of the interior with the complement of the boundary,
  and turns the smooth orientation of the interior into a
  `HomologicalOrientation` with `toHomologicalOrientation`.
- `boundaryMaslovIndex_mul`: for `Ψ Ψ' : C(∂X, GLSymplectic n ℝ)`, the
  pointwise product has the sum of the two indices. Since `maslovPhase` is
  not multiplicative on the whole symplectic group, the polar argument is
  needed, but it is written once, for the group itself, and not again for
  boundary maps: the issue adds
  `TauCeti.GLSymplectic.maslovPhase_mul_homotopic` to this library's
  `Analysis/Matrix/SymplecticGroup/Maslov.lean` (part 5's file, named after
  Tau Ceti's, next to which `maslovIndex_mul` sits upstream). It says that
  on `GLSymplectic n ℝ × GLSymplectic n ℝ` the maps
  $(A,B)\mapsto\rho(AB)$ and $(A,B)\mapsto\rho(A)\rho(B)$ to `Circle` are
  homotopic (`ContinuousMap.Homotopic`), with $\rho$ = `maslovPhase`: apply
  `TauCeti.GLSymplectic.polarHomotopy` to each factor, and at the end use
  `maslovPhase_inclusion_mul` and `maslovPhase_inclusion_polarUnitary`.
  Then `boundaryMaslovIndex_mul` composes this homotopy with
  $x\mapsto(\Psi x,\Psi' x)$ and concludes by
  `boundaryDegree_eq_of_homotopy` (prerequisite 7) and
  `boundaryDegree_mul`. The loop statement `maslovIndex_mul` is the same
  composition with a loop in the product.
  `boundaryMaslovIndex_eq_zero_of_extend`: a `Ψ` that extends continuously
  over `X` has index $0$, by `boundaryDegree_eq_zero_of_extend`.
- `symplecticChernNumber_eq_boundaryMaslovIndex`: for symplectic frames over
  $\Sigma_1$ and $\Sigma_2$, the number is `boundaryMaslovIndex` on
  $\Sigma_1$ of the transition $\Phi_1^{-1}\Phi_2$ on `C`. Proof: make both
  frames unitary as in `Clutching.lean`, with changes of frame `P` over
  $\Sigma_1$ and `P'` over $\Sigma_2$, both with values in
  $\mathrm{Sp}(2n)$; on `C` the transition becomes $P^{-1}\Psi P'$. By
  `boundaryMaslovIndex_mul`, its index is that of `Ψ` plus those of
  $P^{-1}$ and `P'` restricted to `C`. The first vanishes by
  `boundaryMaslovIndex_eq_zero_of_extend`, as $P^{-1}$ is defined on all of
  $\Sigma_1$. The second needs no comparison of the boundary classes of
  $\Sigma_1$ and $\Sigma_2$: apply
  `evalFundamentalClass_eulerClass_eq_boundaryDegree` (prerequisite 7) to
  the trivial plane bundle, with the frame $1$ over $\Sigma_1$ and the
  nowhere-zero section `maslovPhase ∘ P'` over $\Sigma_2$. The boundary
  degree of `maslovPhase ∘ P'` on `C` is then the Euler number of the
  trivial bundle, which is $0$ by `TauCeti.eulerClass_trivial_eq_zero`. For
  the unitary transition the Maslov phase is the normalized complex
  determinant (`TauCeti.GLSymplectic.maslovPhase_ofUnitary`).
  Then the determinant of $\Phi_1$ is a
  frame of the determinant line over $\Sigma_1$, and the determinant of
  $\Phi_2$ is a nowhere-zero section over $\Sigma_2$; read in the first, the
  second is the determinant of the transition on `C`, and
  `evalFundamentalClass_eulerClass_eq_boundaryDegree` (prerequisite 7)
  applies.
- `exists_extension_iff_boundaryMaslovIndex_eq_zero`: the book's Lemma 2.7.3,
  for a connected compact oriented surface whose boundary is not empty, in the
  representation of *Symplectic vector bundles* above. A continuous `Ψ` on
  the boundary extends continuously over the surface if and only if its
  `boundaryMaslovIndex` is $0$. "Only if": the Maslov phase of an extension
  extends `maslovPhase ∘ Ψ` over `X`, and `boundaryDegree_eq_zero_of_extend`
  (prerequisite 7) applies. "If": cap the boundary circles with discs
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
     finite-dimensional model `G` over any `𝕜`. It is not built by hand: its
     core is the point-indexed core of `E` transported along
     `ContinuousLinearEquiv.ofFinrankEq` by Tau Ceti's
     `VectorBundleCore.congrModel` (`Topology/VectorBundle/Core/Congr.lean`),
     as `FiniteRank/Atlas/Biproduct.lean` does, so `indexAt_congrModel` gives
     `indexAt_eq`. Its API: `rank_ofBundleOfFinrankEq`;
     `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEqHomeomorph`, the
     identification of total spaces with that of `E`, from
     `congrModelHomeomorph` and `continuous_mk_congrModel_iff`;
     `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEqIso`, the analogue of
     `ofBundleIso` (an isomorphism of cores from a fibrewise isomorphism of
     bundles, continuous on total spaces); and
     `TauCeti.FiniteRankBundleCore.pullback_ofBundleOfFinrankEq`, the analogue
     of `pullback_ofBundle`;
   - in `Topology/VectorBundle/Determinant.lean`,
     `SymplecticGeometry.Bundle.detCore 𝕜 G E :=
     (ofBundleOfFinrankEq 𝕜 G E rfl).det`, over any `𝕜`, with `detCore_def`,
     `SymplecticGeometry.Bundle.detCoreMap` (the isomorphism of determinant
     cores induced by a fibrewise isomorphism of bundles),
     `SymplecticGeometry.Bundle.detCore_pullback` (compatibility with
     pull-back, an equality, through
     `CoordinateFunctor.functor_comp_pullbackFunctor`),
     `SymplecticGeometry.Bundle.detCoreTrivialIso` (the trivial bundle has a
     trivial determinant), and
     `SymplecticGeometry.Bundle.detCoreIsoOfFinrankEqOne` (the identification
     with `E` in rank one, from `exteriorPowerOneNatIso`);
   - the one step specific to `ℂ`, in
     `Topology/VectorBundle/FiniteRank/ConjugateExteriorPower.lean` beside
     Tau Ceti's `FiniteRank/Conjugate.lean`, in Tau Ceti's terms only.
     `FiniteRankBundleCore.det` is a function on objects, not a functor, so
     the natural statement is at a fixed degree. Following Tau Ceti's
     naming in `FiniteRank/` (`doubleConjugateIso` and
     `doubleConjugateNatIso`, `exteriorPowerOneIso` and
     `exteriorPowerOneNatIso`): the isomorphism at one object
     `TauCeti.FiniteRankBundleCore.exteriorPowerConjugateIso k A :
     (exteriorPower ℂ B k).obj ((conjugate B).obj A) ≅
     (conjugate B).obj ((exteriorPower ℂ B k).obj A)`, the natural one
     `TauCeti.FiniteRankBundleCore.exteriorPowerConjugateNatIso k : conjugate B
     ⋙ exteriorPower ℂ B k ≅ exteriorPower ℂ B k ⋙ conjugate B` with
     `@[simp] exteriorPowerConjugateNatIso_app`, and from them, objectwise,
     `TauCeti.FiniteRankBundleCore.detConjugateIso A :
     ((conjugate B).obj A).det ≅ (conjugate B).obj A.det`, using that
     conjugation keeps the rank (`rank_conjugate_obj`);
   - two supporting files: `Topology/VectorBundle/Core/Basic.lean`, with
     `VectorBundleCore.ext`, which `FiniteRank/OfBundle.lean` imports; and
     `Analysis/Normed/Operator/ExteriorPowerCoords.lean` beside Tau Ceti's
     file of that name, with
     `ContinuousLinearMap.exteriorPowerCoords_intrinsicStar` (compound
     matrices commute with entrywise conjugation), which
     `FiniteRank/ConjugateExteriorPower.lean` imports;
   - two steps that the conjugate case also needs, in
     `Topology/VectorBundle/FiniteRank/Conjugate.lean`:
     `TauCeti.FiniteRankBundleCore.continuous_star_conjugate` (conjugating
     coordinates is continuous from the conjugate core to the core) and
     `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEqConjugateIso` (the
     core of `ConjugateBundle E` is the conjugate of the core of `E`);
   - a shared step, added after this issue, in
     `Topology/VectorBundle/FiniteRank/Basic.lean` beside Tau Ceti's file of
     that name, importing only it:
     `TauCeti.FiniteRankBundleCore.isoFiberEquiv e x`, the fibrewise
     continuous linear equivalence on coordinates of an isomorphism
     `e : A ≅ D` of cores, the converse of Tau Ceti's `isoOfContinuousEquiv`,
     with `isoFiberEquiv_apply` and `continuous_isoFiberEquiv` (continuity on
     total spaces); `detCoreConjugateFiberwise` is built from it;
   - back in `Topology/VectorBundle/Determinant.lean`, since it is about this
     library's `detCore`: `SymplecticGeometry.Bundle.detCoreConjugateFiberwise`,
     a conjugate-linear fibrewise isomorphism between `detCore ℂ` of the
     conjugate bundle and `detCore ℂ G E`, from `detConjugateIso` and the
     steps above, in the
     form that
     `complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise`
     takes. So the Tau Ceti-namespaced files under `FiniteRank/` import, of
     this library, only each other and the two supporting files, which are
     stated in Mathlib's and Tau Ceti's terms, so that they can move
     upstream together.

   Done when these are proved and build.
2. **Evenness of the first Betti number of a closed orientable surface.**
   `AlgebraicTopology/Singular/SurfaceGenus.lean` (the name of Tau Ceti's
   file, so that the two merge): `TauCeti.HomologicalOrientation.even_finrank_singularHomology_one`,
   for a compact homologically oriented surface (connected or not), `finrank ℚ
   H₁(M; ℚ)` is even. Only this is new; the step from evenness to
   `χ = 2 - 2 * surfaceGenus` is already Tau Ceti's
   `eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank` with
   `genus_eq_surfaceGenus` (`AlgebraicTopology/Cellular/EulerCharacteristic/Genus.lean`;
   `TauCeti.IsMorse.finiteCWType` or `FiniteCWType.of_isManifold` gives the
   instance). The same file has `TauCeti.surfaceGenus_sphere`: the unit
   sphere of `EuclideanSpace ℝ (Fin 3)` has `surfaceGenus = 0`, from Tau
   Ceti's homology of spheres; uniqueness in `Axioms.lean` uses it. Route
   for the evenness: Tau Ceti's
   `TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`,
   given injectivity of the cap product with the fundamental class in degree
   one. `AlgebraicTopology/Cohomology/Cap/RationalCoefficients.lean` reduces
   it, for the image of the fundamental class under
   `TopCat.singularHomologyIntToRat`, to injectivity of the duality map with
   values in `ℚ`
   (`TauCeti.HomologicalOrientation.injective_singularCapLinearMap_of_injective_dualityMap`).
   It uses two new general files:
   `AlgebraicTopology/Cohomology/Cap/Basic.lean`, the singular cap product
   of a simplex along the unitors, and
   `Algebra/Homology/ShortComplex/PreservesHomology.lean`,
   `CategoryTheory.ShortComplex.map_homologyπ_comp_mapHomologyIso_inv`.
   Its chain map from integral to rational chains is the change of
   coefficients `SSet.restrictScalarsChainMap` of
   `AlgebraicTopology/SimplicialSet/Homology/RestrictScalars.lean`
   (`design/pseudoholomorphic-energy.md`), which it imports.
   That injectivity is the degree-one case of Poincaré duality, which
   Tau Ceti prepares in `AlgebraicTopology/Cohomology/CompactSupport/`
   (`HomologicalOrientation.dualityMap` and its criterion in `Duality.lean`)
   but does not finish. The issue first checks whether Tau Ceti has finished
   it since the pin. If not, duality for closed oriented manifolds from that
   criterion is likely several issues, and is split into them when the issues
   are created. Done when the evenness theorem is proved.
   The first of them brings from Tau Ceti's main branch, under Tau Ceti's
   names and namespaces so that a move of Tau Ceti past them deletes the
   files, the duality maps on open subsets, the two Mayer–Vietoris squares
   and duality for disjoint and directed unions of open sets, in
   `AlgebraicTopology/Cohomology/CompactSupport/Duality/{Basic,MayerVietoris,DirectedUnion}.lean`.
   The lemmas they use from other Tau Ceti files of the main branch go in
   files at those files' paths:
   `AlgebraicTopology/Cohomology/CompactSupport/{Extension,MayerVietoris,DirectedUnion}.lean`,
   `AlgebraicTopology/Singular/{DirectedUnion,MayerVietoris/Basic}.lean`,
   `AlgebraicTopology/Singular/LocalHomology/Orientation/OpenEmbedding.lean`,
   `Geometry/Manifold/Opens.lean` and `Topology/Sets/Opens.lean`.
   The chain and cohomology lemmas that Tau Ceti uses for the connecting
   square of Poincaré duality and Mayer–Vietoris go, in the same way, in
   `Algebra/Homology/ModuleCat/Basic.lean`,
   `AlgebraicTopology/Cohomology/{Cap/Relative,MayerVietoris/Compl}.lean`,
   `AlgebraicTopology/SimplicialSet/Homology/{Basic,MayerVietoris}.lean`,
   `AlgebraicTopology/Singular/{Relative,Subspace}.lean`,
   `AlgebraicTopology/Singular/Subdivision/Small/{Chains,Relative}.lean` and
   `Topology/Sets/Compacts.lean`.
   Tau Ceti's caps of chains supported in an open subspace, and their
   relative forms, come in the same way, in
   `AlgebraicTopology/Cohomology/Cap/Support.lean`.
   Tau Ceti's connecting square of the duality maps and the Mayer–Vietoris
   connecting maps comes in the same way, in
   `AlgebraicTopology/Cohomology/Cap/MayerVietoris/{Local,Basic}.lean`.
   The Mayer–Vietoris step of duality is the library's own
   `AlgebraicTopology/Cohomology/CompactSupport/Duality/Union.lean`, not a
   file of Tau Ceti's: `TauCeti.HomologicalOrientation.bijective_dualityMap_of_sup_eq_top`
   for a cover by two open sets, and `bijective_dualityMap_comap_sup` for two
   open sets of `M`. Besides duality in every degree for `U`, `V` and
   `U ∩ V`, both assume `Hⁿ⁺¹_c(U ∩ V; L) = 0`, which injectivity needs in
   the top degree; `TopCat.isZero_compactSupportCohomology_sup`, in the
   library's `AlgebraicTopology/Cohomology/CompactSupport/Vanishing.lean`,
   passes that vanishing on to `U ∪ V`, and
   `TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`, in the same
   file, to a directed union of open sets. The vanishing starts from
   `AlgebraicTopology/Cohomology/CompactSupport/Euclidean/Basic.lean`,
   `TopCat.isZero_compactSupportCohomology_of_starConvex` and
   `isZero_compactSupportCohomology_of_convex`: `Hᵏ_c(U) = 0` for
   `k ≠ dim F` when `U` embeds openly in `F` with star-convex or convex
   image. The step uses
   `Topology/Sets/Opens/Comap.lean`,
   `TopologicalSpace.Opens.range_val_comp_val_comap`, to read an open set of
   `M` as one of `U ∪ V`, and `comap_val_sup_comap_val_eq_top`, for the
   cover of `U ∪ V` by `U` and `V` so read, and
   `Algebra/Category/ModuleCat/Basic.lean`,
   `ModuleCat.bijective_zsmul_iff`, for the sign of the connecting square.
   Duality for every open subset of a finite-dimensional real normed space
   `F` is the library's
   `AlgebraicTopology/Cohomology/CompactSupport/Euclidean/Duality.lean`:
   `TauCeti.HomologicalOrientation.bijective_dualityMap_of_isOpenEmbedding`,
   for an open embedding `j : U → F` and any orientation of `U`. It uses
   `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`, in
   `Euclidean/Basic.lean`, `Hᵐ_c(U) = 0` for `m > dim F`, which the step to
   compact manifolds needs too, for the intersections. Both run
   Mayer–Vietoris over finite unions of open sets of `U` with convex images,
   starting from `isZero_compactSupportCohomology_of_convex` and Tau Ceti's
   `bijective_dualityMap_of_convex`. Those open sets come from
   `Analysis/Convex/Opens.lean`:
   `TopologicalSpace.Opens.infClosed_setOf_convex_image` and
   `Topology.IsOpenEmbedding.iSup_finset_sup_convex_image_eq_top`. The
   induction is `InfClosed.finset_sup_induction`, in `Order/SupClosed.lean`,
   Tau Ceti's `TauCeti.finset_sup_of_inf_closed` for a finite set of members
   of the family.
   Duality for a manifold is the library's
   `AlgebraicTopology/Cohomology/CompactSupport/Duality/Manifold.lean`:
   `TauCeti.HomologicalOrientation.bijective_dualityMap`, for every
   homologically oriented manifold, compact or not, and for compact `M` its
   form for capping with the fundamental class,
   `bijective_singularCap_fundamentalClass`. It imports
   `AlgebraicTopology/Cohomology/CompactSupport/Manifold.lean`, which proves
   `TopCat.isZero_compactSupportCohomology_of_chartedSpace`, `Hᵐ_c(M) = 0`
   above the dimension, which the Mayer–Vietoris step needs for the
   intersections. Both run the induction above over the open sets lying in
   one chart instead of those with convex image; that family comes from
   `Geometry/Manifold/ChartedSpace.lean`:
   `TopologicalSpace.Opens.infClosed_setOf_subset_chartAt_source` and
   `TopologicalSpace.Opens.iSup_finset_sup_subset_chartAt_source_eq_top`.
3. **The unit circle bundle of a Hermitian line bundle.**
   `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`, the file
   of *Symplectic vector bundles* (its section *The circle bundle of a
   Hermitian line bundle*). The type that carries the principal-bundle
   structure is the family of Tau Ceti's rank-one unitary frame bundle,
   `fun x ↦ OrthonormalFrameBundle.Fiber ℂ F L ℂ x` (fibre `ℂ ≃ₗᵢ[ℂ] L x`),
   which `OrthonormalFrameBundle.instPrincipalBundleFiber`
   (`Topology/VectorBundle/OrthonormalFrame/Principal.lean`) makes a
   principal bundle for `unitary (ℂ →L[ℂ] ℂ)`. The topological side is
   there already, and this design takes it from there rather than adding
   it again: the action of `Circle` on the unit circle subtype
   `{p : TotalSpace F L // ‖p.snd‖ = 1}` (on which Tau Ceti's
   `isManifold_sphereBundle` puts the smooth structure); the homeomorphism
   `SymplecticGeometry.Bundle.circleBundleHomeomorph` from the frame bundle
   onto it, `φ ↦ ⟨x, φ.frame 1⟩`, `Circle`-equivariant fibre by fibre
   (`circleBundleHomeomorph_op_circle_smul`); the isomorphism of structure
   groups `Unitary.continuousLinearMapCircleEquiv : unitary (ℂ →L[ℂ] ℂ) ≃ₜ*
   Circle` (`Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean`); and
   the instances `SymplecticGeometry.Bundle.instFiberBundleCircleFiber` and
   `instPrincipalBundleCircleFiber : TauCeti.PrincipalBundle Circle
   (Fiber ℂ F L ℂ)`, whose trivializations are those of the frame bundle
   read through that isomorphism (`Bundle.Trivialization.changeModelFiber`).
   That file states them for fibres with their own `InnerProductSpace ℂ`
   instances and `TauCeti.ContinuousFiberNorm F L`, and `Fact (finrank ℂ F
   = 1)`. This issue, and the issues that use `P`, work with a Hermitian
   line bundle `(g, hI)` in the representation of *Symplectic vector
   bundles*, and get those hypotheses from it by the three local instances
   that its section gives: `RiemannianBundle L` from `g.toRiemannianMetric`,
   the inner products `g.complexInnerProductSpace hI`, and
   `IsContinuousRiemannianBundle F L` from
   `instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric`, which
   gives `ContinuousFiberNorm F L`. This issue adds only the smooth side,
   in the same file, with the hypotheses of the sphere-bundle atlas that
   that section lists: the hypothesis of
   `TauCeti.PrincipalBundle.contMDiffFiberBundle_iff` for the `Circle`
   instance (smooth coordinate changes, from those of the unitary frame
   bundle and the smoothness of `continuousLinearMapCircleEquiv`), so that
   `TauCeti.ManifoldTotalSpace Circle` of the family is a smooth principal
   bundle; `SymplecticGeometry.Bundle.circleBundleDiffeomorph`,
   `circleBundleHomeomorph` as a diffeomorphism onto the submanifold
   subtype. Its equivariance is that of `circleBundleHomeomorph`, stated
   fibre by fibre: *Symplectic vector bundles* records why the file does
   not use the right action on the total space.
   The issue proves no submersion lemma of its own: once the bundle is a
   smooth fibre bundle, its projection is a smooth submersion by Tau Ceti's
   `TauCeti.ManifoldTotalSpace.isSubmersion_proj` (or
   `isSubmersionOfComplement_proj`, with the fibre's model space as
   complement; `Geometry/Manifold/FiberBundle/Submersion.lean`), which is
   what issue 4 applies to this bundle. No later issue needs the projection
   from the submanifold subtype as a submersion, so the design adds no named
   specialization for it.
   General lemmas that the proofs use have files of their own:
   `Geometry/Manifold/Instances/Sphere.lean` (`ContMDiffOn.of_coe_sphere`,
   smoothness on an open set of a map into a unit sphere, used for
   `Circle`), `Geometry/Manifold/VectorBundle/Riemannian/Hermitian.lean`
   (`Bundle.ContMDiffRiemannianMetric.contMDiffOn_hermitianPairing`, Tau
   Ceti's `contMDiff_hermitianPairing` on a set) and
   `Geometry/Manifold/VectorBundle/Riemannian/Norm.lean`
   (`ContMDiffOn.norm_bundle`, smoothness of the norm of a nowhere-zero
   section of a smooth Riemannian bundle), at the places of the Mathlib
   and Tau Ceti files of the same names.
   Blocked by the issue from #57 for the circle bundle. Done when these are
   proved.
4. **Connection forms on principal circle bundles.**
   `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`: for a
   smooth principal `Circle`-bundle `P` over `M`, the predicate
   `SymplecticGeometry.IsCircleConnectionForm α` for a smooth real 1-form on the
   total space, invariant under the action and equal to $1$ on the
   fundamental vector field of $1$ (`TauCeti.rightFundamentalVectorField` of
   `SymplecticGeometry.circleLieGenerator`, the velocity of `Circle.exp` at
   $0$, defined in `Geometry/Lie/Exponential/Circle.lean`, at the place of the
   Tau Ceti file of the same name, with the lemma that Tau Ceti's
   `circleExpGenerator` corresponds to it). Its curvature `IsCircleConnectionForm.curvature
   (hα : IsCircleConnectionForm α)`, the 2-form on `M` whose pull-back is `d α`,
   exists and is unique by descent of basic forms (`TauCeti.RoughForm.IsBasic`,
   `Manifold.IsSubmersion.exists_smoothForm_mpullback_eq_iff`).
   API: `IsCircleConnectionForm.curvature_def`;
   `IsCircleConnectionForm.mpullback_curvature` (the pull-back of the curvature is
   `d α`) and `IsCircleConnectionForm.curvature_eq_iff` (it characterizes the
   curvature); `α + π^* a` is a connection form for every 1-form `a` on `M`,
   any two differ by such an `a`, and `curvature (α + π^* a) = curvature α +
   d a`; existence of a connection form, by a partition of unity from the
   trivializations of the atlas; and the local form
   $d\theta+\pi^*s^*\alpha$ in the trivialization of a local section `s`
   (`TauCeti.PrincipalBundle.trivializationOfSection`). General lemmas that
   the proofs use have files of their own:
   `Geometry/Manifold/DeRham/Circle.lean` (the rotations of the circle preserve
   `TauCeti.circleAngularForm`), at the place of the Tau Ceti file of the same
   name, `Geometry/Manifold/FiberBundle/Principal/BasicForm.lean`
   (`TauCeti.PrincipalBundle.isBasic_of_mpullback_op_smul`: on a smooth
   principal bundle, an invariant form that vanishes on vertical vectors is
   basic), and `Geometry/Manifold/DifferentialForm/PartitionOfUnity.lean`
   (`SmoothPartitionOfUnity.IsSubordinate.isSmoothForm_finsum_smul_comp`: a
   locally finite sum of `C^n` local forms weighted by a smooth partition of
   unity is `C^n`), the case of the bundle of forms of
   `Geometry/Manifold/PartitionOfUnity.lean`
   (`SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul_comp_section`,
   the same for sections of any vector bundle). The example on the circle bundle imports
   `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean` of *Symplectic
   vector bundles*. Blocked by 3 only for its example; the definitions are for
   any `P`.
   Done when this API is proved and applied to the circle bundle of 3.
5. **Coordinate discs.**
   `AlgebraicTopology/Singular/LocalHomology/CoordinateDisc.lean`, beside
   Tau Ceti's homological orientations and winding numbers:
   `structure SymplecticGeometry.CoordinateDisc (o : TauCeti.HomologicalOrientation M E 2)`,
   an open embedding `CoordinateDisc.ball → M`, from the ball
   `Metric.ball (0 : ℂ) 2` as `TopologicalSpace.Opens ℂ` (so that it carries
   `TauCeti.complexHomologicalOrientation`), that carries the local
   orientations of `ℂ` to those of `o`, with `@[ext]`; its closed disc
   `CoordinateDisc.disc` (the image of `closedBall 0 1`, compact) and open
   disc `CoordinateDisc.openDisc`, its boundary circle
   `CoordinateDisc.boundaryCircle : C(Circle, M)` and
   boundary loop `CoordinateDisc.boundaryLoop` ($t\mapsto
   \varphi(e^{2\pi it})$), `CoordinateDisc.reverse` for the opposite
   orientation (precomposition with conjugation), the constructor
   `CoordinateDisc.ofChart` from an orientation-preserving smooth chart of a
   smoothly oriented surface (through `o.toHomologicalOrientation`), and
   `exists_coordinateDisc` (one centred at any point) and
   `exists_coordinateDisc_pairwise_disjoint` (finitely many at distinct
   points, with disjoint images). `CoordinateDisc.lean` imports
   supporting files of this part, each beside the Mathlib or Tau Ceti
   file it adds to: `LinearAlgebra/Complex/Orientation.lean`,
   `AlgebraicTopology/Singular/LocalHomology/Orientation/Smooth.lean`, and
   `Geometry/Manifold/Complex/FundamentalClass.lean`, for the reversal of
   `TauCeti.complexHomologicalOrientation` by conjugation that
   `CoordinateDisc.reverse` uses, and
   `AlgebraicTopology/Singular/LocalHomology/ChangeOfModel.lean`, beside
   Tau Ceti's `System.lean`, for `exists_coordinateDisc`: local homology
   transport does not depend on the model, so a homological orientation
   can be read with the model `ℂ`
   (`TauCeti.HomologicalOrientation.changeModel`). Done when this API is proved.
6. **Argument principle for discs.**
   `AlgebraicTopology/Singular/LocalHomology/ArgumentPrinciple.lean`:
   `SymplecticGeometry.sum_degree_boundary_eq_zero`. Let `φ i`, `i : ι`
   finite, be coordinate discs of a compact homologically oriented surface
   with disjoint closed discs, and let `u` be continuous and nowhere zero on
   the complement of the open discs, with values in `ℂ`. Then the degrees
   (`Circle.degree`) of `u/|u|` around the boundary loops sum to $0$. It is
   a corollary of prerequisite 7, with no argument of its own. The surface
   minus the open discs is an instance of the setting of 7: it is compact,
   its interior is the surface minus the closed discs, and its boundary
   circles are collared by thin annuli $1\le|z|<1+\delta$ of the coordinate
   discs. The issue picks widths $\delta_i\in(0,1)$ such that the images
   of the balls of radius $1+\delta_i$ are pairwise disjoint; they exist
   because the closed discs are finitely many disjoint compact sets, so
   they have pairwise disjoint open neighbourhoods, and for small $\delta_i$
   each enlarged closed disc lies in its neighbourhood. Then the collars
   are disjoint and miss the other closed discs, and together they give
   the open embedding that `TauCeti.IsCollar` requires. The wider annuli
   up to radius $2$ need not be disjoint, so they are not used. `u/|u|` is
   defined on all of it, so `boundaryDegree_eq_zero_of_extend` gives
   degree $0$. The boundary loops of the discs run against the boundary
   orientation of this surface, so `boundaryDegree_eq_sum_degree` is
   applied to their reversals (`Path.symm`); it gives minus the sum of the
   degrees along the boundary loops, which is therefore $0$. The work of
   the issue is that instance, which
   `AlgebraicTopology/Singular/LocalHomology/DiscComplement/Basic.lean`
   proves (`SymplecticGeometry.isOpenEmbedding_inclusion_discComplementInterior`,
   `SymplecticGeometry.range_inclusion_discComplementInterior`,
   `SymplecticGeometry.isCollared_discComplementBoundary`) and
   `ArgumentPrinciple.lean` imports. This is the half of the book's Lemma 2.7.3 needed for discs.
   Blocked by 5 and 7.
7. **Boundary degree and the argument principle on a surface with
   boundary.** The setting is that of `RelativeFundamentalClass.lean`: `X`
   compact Hausdorff, `ι : M → X` an open embedding of a surface with
   `o : HomologicalOrientation M E 2`, and `f : N → X` collared with image
   `∂X`, the complement of `ι(M)`. The topological files are kept apart
   from the smooth ones, so that no Topology file imports Geometry:
   - `AlgebraicTopology/Singular/CircleMap.lean`, needed by
     `BoundaryDegree.lean`: maps `Y → Circle` act additively on first
     homology, `(u * v)_* = u_* + v_*`
     (`ContinuousMap.singularHomologyFunctor_map_mul`), a self-map of the
     circle acts on `H₁(S¹)` by its `circleDegree`, and so `u` sends the class
     of a free loop `ℓ` to the degree of `u ∘ ℓ`
     (`ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one`). These give
     `boundaryDegree_mul` and `boundaryDegree_eq_sum_degree`.
   - `AlgebraicTopology/Singular/ModuleChains.lean`, needed by
     `CircleMap.lean`: with coefficients `k`, Mathlib's
     `singularHomologyFunctor` induces Tau Ceti's
     `ContinuousMap.singularHomologyMap`
     (`AlgebraicTopology.singularHomologyFunctor_obj_map_ofHom_hom`).
   - `AlgebraicTopology/Singular/Circle.lean`, used by
     `Complex.lean`:
     `Circle.singularHomologyOneIso_inv_eq_complexOrientation`, the
     generator of `Circle.singularHomologyOneIso` is the one of the unit
     circle of `ℂ` selected by `Complex.orientation`.
   - `AlgebraicTopology/Singular/Path.lean`, used by `Circle.lean`: the
     singular `1`-simplex of a closed path has equal faces
     (`TauCeti.TopCat.δ_zero_simplex₁_eq_δ_one_simplex₁`), and with any
     coefficients the boundary of `TauCeti.TopCat.transSimplex γ δ` is
     `γ + δ - γ.trans δ` (`TauCeti.TopCat.ιChainComplex_transSimplex_d`).
   - `Analysis/Complex/RadialProjection.lean`, used by
     `Complex.lean` and `BoundaryDegree.lean`:
     `Circle.radialProjection : C(ℂ ∖ {0}, Circle)`, `z ↦ z / |z|`, Tau
     Ceti's `complSingletonHomotopyEquivSphere 0` read in `Circle`.
   - `Analysis/Normed/Module/Ball/Collar.lean`, used by
     `DiscBoundaryClass.lean` and `DiscComplement/Basic.lean`: in a real
     normed space the unit sphere is
     collared in the closed unit ball
     (`Metric.isCollared_inclusion_sphere_closedBall`), and the
     open ball is the complement of the sphere in the closed ball
     (`Metric.range_inclusion_ball_eq_compl`).
   - `AlgebraicTopology/Singular/LocalHomology/OrientedChart.lean`:
     `OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`,
     the local orientation of the identity chart of an oriented inner
     product space, through the connecting morphism and radial projection,
     is the oriented generator of the unit sphere.
   - `Topology/OpenPartialHomeomorph/Basic.lean`, used by
     `LocalHomology/System.lean` and `Orientation/Chart.lean`: from Tau
     Ceti's main branch, `OpenPartialHomeomorph.sourceRestrict`, an open
     partial homeomorphism restricted to its source, and
     `OpenPartialHomeomorph.mem_refl_source`.
   - `AlgebraicTopology/Singular/LocalHomology/System.lean`, used by
     `Orientation/Chart.lean`: from Tau Ceti's main branch,
     `TauCeti.localHomologyMap_subtypeVal_comp_singularHomologyComplSingletonIsoOfChart_hom`,
     the local homology isomorphism of a chart is the map induced by its
     source restriction.
   - `AlgebraicTopology/Singular/LocalHomology/Orientation/Chart.lean`, used
     by `Orientation/Linear.lean`: from Tau Ceti's main branch, which the
     pinned version lags,
     `LinearIsometryEquiv.snd_ofSubsetMap_comp_complSingletonHomotopyEquivSphere`,
     linear isometries commute with radial projection.
   - `AlgebraicTopology/Singular/LocalHomology/Orientation/Linear.lean`, used
     by `Complex.lean` and `EulerNumber.lean`: from Tau Ceti's main branch,
     `Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`,
     on an inner product space the local orientation that an orientation
     selects is the one of the identity chart.
   - `AlgebraicTopology/Singular/LocalHomology/BoundaryClass.lean`, imported
     by `BoundaryDegree.lean`: in any dimension `n + 1`,
     `TauCeti.HomologicalOrientation.boundaryClass`, the image of
     `fundamentalClassRel` in `Hₙ(∂X; ℤ)` under the connecting morphism, with
     `boundaryClass_neg` and `map_subtypeVal_boundaryClass` (it vanishes in
     `Hₙ(X; ℤ)`).
   - `AlgebraicTopology/Singular/LocalHomology/Orientation/Plane.lean`, used
     by `Complex.lean` and by `Orientation/StdSimplex.lean` of part
     *Energy of pseudoholomorphic curves*: on a plane `E` oriented by `o`,
     with a linear isometry `φ : E ≃ₗᵢ[ℝ] ℂ` carrying `o` to
     `Complex.orientation`, the oriented local homology isomorphism of the
     identity chart at `p` is the connecting morphism, then radial
     projection after `y ↦ φ (y - p)`, then `Circle.singularHomologyOneIso`
     (`TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection`).
   - `AlgebraicTopology/Singular/LocalHomology/Complex.lean`, used by
     `DiscBoundaryClass.lean` and `BoundaryDegree.lean`: the local
     orientation of `ℂ` at `0` is the one selected by `Complex.orientation`
     (`TauCeti.complexHomologicalOrientation_apply_zero`), and radial
     projection sends it to the generator of `H₁(Circle)`
     (`SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation`).
   - `AlgebraicTopology/Singular/LocalHomology/DiscBoundaryClass.lean`, a
     prerequisite of `BoundaryDegree.lean`:
     the closed unit disc of `ℂ` in
     this setting, by `Collar.lean`; its fundamental class is sent to the
     local orientation of `ℂ` at `0`
     (`SymplecticGeometry.localHomologyMap_fundamentalClassRel_closedBall`).
   - `AlgebraicTopology/Singular/LocalHomology/BoundaryDegree.lean`, which
     imports `BoundaryClass.lean`: the definition `TauCeti.HomologicalOrientation.boundaryDegree o hn hι hιf hf
     (u : C(∂X, Circle)) : ℤ`, the image of the boundary class
     `singularHomologyδ (fundamentalClassRel …)` under `u`, read in ℤ through
     `Circle.singularHomologyOneIso`, with the sign for which the
     counterclockwise loop counts $+1$. Tau Ceti does not record the sign of
     its connecting morphism; it is settled on the closed unit disc, from
     `DiscBoundaryClass.lean`, and the definition fixes its sign by it:
     `SymplecticGeometry.boundaryDegree_closedBallComplToCircle`, and
     `SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`,
     for the complex orientation of the open disc the boundary class read
     in ℤ through `Circle.singularHomologyOneIso` is $+1$. API:
     `boundaryDegree_def`;
     `boundaryDegree_mul` (pointwise products add degrees);
     `boundaryDegree_eq_of_homotopy` (homotopic maps `∂X → Circle` have the
     same degree, from the homotopy invariance of singular homology);
     `boundaryDegree_neg_orientation`; `boundaryDegree_eq_zero_of_extend` (a
     `u` that extends continuously to `X` has degree $0$, since the boundary
     class dies in $H_1(X)$ by exactness); and `boundaryDegree_eq_sum_degree`
     (when the components of `∂X` are parametrized by loops whose classes add
     up to the boundary class, it is the sum of `Circle.degree` of `u` along
     them).
   - `Topology/VectorBundle/Orientation/SectionIndex/FiberwiseEquiv.lean`,
     used by `ArgumentPrinciple.lean`, beside Tau Ceti's `SectionIndex`
     files: `TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`,
     orientation-preserving fibrewise isomorphisms preserve local indices.
   - `Topology/VectorBundle/Orientation/ArgumentPrinciple.lean`, beside Tau
     Ceti's `SectionIndex` files. The boundary term needs a trivialization
     over the whole of `X`: with one only over `∂X` the statement is false
     (on the disc, twisting the boundary trivialization by $e^{i\theta}$
     changes the degree but not the zeros). So: let `L` be a real plane
     bundle over `X` with a frame `τ` over all of `X` (linear isomorphisms
     `τ x : L x ≃L[ℝ] ℂ`, continuous on the total space), oriented so that
     `τ` carries its orientation to `Complex.orientation`, and `t` a
     continuous section whose zeros are finitely many and lie in `ι(M)`.
     Then `TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`:
     the sum over those zeros of the `sectionIndex` of `t` restricted along
     `ι` equals `o.boundaryDegree … u`, with `u` the normalization of
     `τ t` on `∂X`. Route: by excision both sides are local homology
     computations near the zeros and near `∂X`, joined by the connecting
     morphism of `(X, ∂X)`.
   - `Geometry/Manifold/VectorBundle/Section/ArgumentPrinciple.lean`, beside
     Tau Ceti's `Section/Generic.lean`, for the smooth form:
     `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`:
     for an oriented plane bundle `L` over a closed oriented surface split by
     a regular value of `g : M → ℝ`, a frame `τ` of `L` over $\Sigma_1$
     compatible with the orientation, and a nowhere-zero section `s` over
     $\Sigma_2$, the Euler number of `L` is the boundary degree on
     $\Sigma_1$ of the normalization of
     `τ s` on `C`. Proof: extend `τ s` from `C` to a map
     $M\to\mathbb{C}$ with finitely many zeros, none on `C` (Tietze, then
     `exists_eq_on_levelSet_finite_zeros` of `RegularValue/FiniteZeros.lean`),
     so that `s` extends to a section with finitely many zeros, and combine
     `sum_sectionIndex_eq_boundaryDegree` with
     `evalFundamentalClass_eulerClass_eq_sum_sectionIndex`.
   - `Geometry/Manifold/RegularValue/FiniteZeros.lean`, used by the smooth
     form above: `SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`, on a
     compact manifold modelled on `E`, a continuous map to a space of the
     dimension of `E` that does not vanish on a level set of a continuous
     `g` agrees there with a continuous map with finitely many zeros, none on
     that level set. Route: smoothing, then subtracting a small regular value
     given by Sard's theorem (`TauCeti.dense_isRegularValue`), whose fibre
     is finite, and interpolating in `|g|` back to the original map near the
     level set.
   - `Geometry/Manifold/RegularValue/LevelCollar.lean`:
     `SymplecticGeometry.isCollared_inclusion_levelSet`, for a smooth
     `g : M → ℝ` on a compact manifold without boundary with regular value
     `0`, the inclusion of $g^{-1}(0)$ into $\{g\le0\}$ is
     `TauCeti.IsCollared`, and $\{g<0\}$ is the complement of its image.
     Compactness is the case `Splitting.lean` uses, and it makes the band
     below compact. No new flow is built: by compactness the critical values
     of `g` stay away from $0$, so for some $\varepsilon>0$ Tau Ceti's
     `TauCeti.exists_bandHomeomorph` (`Geometry/Manifold/Morse/Deformation.lean`),
     applied to `-g` on $[0,\varepsilon]$, gives
     `e : g⁻¹[-ε, 0] ≃ₜ g⁻¹{0} × Icc 0 ε` with second component `-g` and
     first component the identity on the level, and the collar is
     $(y,t)\mapsto e^{-1}(y,\varepsilon t)$. The smooth version
     `exists_bandHomeomorph_diffeomorph` is there if a smooth collar is
     needed. The smooth form of the argument principle above uses this
     lemma, and so does `Splitting.lean`.

   Done when these are proved. It can start at once.
8. **Capping a surface with boundary.**
   `Geometry/Manifold/Gluing/CapDiscs/`, a folder of its own beside Tau
   Ceti's `Geometry/Manifold/Gluing/`, whose gluing it uses, with the
   glued smooth surface in `Basic.lean` and its point-set topology
   (Hausdorff, compact, connected) in `Topology.lean`: a compact
   oriented surface with boundary, in the representation of *Symplectic
   vector bundles*, with its boundary circles parametrized by
   orientation-reversing loops, glued to discs along them, is a closed
   oriented surface. The main definition is `SymplecticGeometry.capDiscs`,
   the closed surface with its orientation, with
   `SymplecticGeometry.isOpenEmbedding_capDiscs_inl` (the interior of the
   surface sits in it as an open subset) and the data
   `SymplecticGeometry.capDiscs.coordinateDisc`, the caps as coordinate
   discs. Blocked by the issue of *Symplectic vector bundles*
   that fixes that representation, and by 5. The gluing uses polar
   coordinates on the circle,
   `AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`, in
   `Geometry/Manifold/Instances/AddCircle.lean`. That the loops are
   finitely many uses `finite_of_compactSpace_of_pairwise_disjoint`, a
   disjoint open cover of a compact space has finite index, in
   `Topology/Compactness/LocallyFinite.lean`.
9. **A map of degree one onto the sphere.**
   `Geometry/Manifold/Degree/Collapse.lean`:
   `SymplecticGeometry.exists_contMDiff_degree_eq_one`, every compact
   nonempty oriented manifold of dimension $n\ge1$ modelled on
   `EuclideanSpace ℝ (Fin n)` (a closed oriented surface when $n=2$) has a
   smooth map of degree one to the unit sphere of any oriented real inner
   product space of dimension $n+1$, by collapsing the complement of a
   coordinate ball of a chart through a cut-off, with
   `TauCeti.degree` computed at the image of the centre. For surfaces the
   sphere is `sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` with Tau Ceti's
   outward-normal orientation `o.sphereOrientation`
   (`Geometry/Manifold/Orientation/Sphere.lean`) for an orientation `o` of
   `EuclideanSpace ℝ (Fin 3)`, as in `orientable_sphere`; no new orientation
   is defined. The area form that uniqueness needs is `o.sphereVolumeForm`:
   it vanishes nowhere (`sphereVolumeForm_apply_ne_zero`), so it is
   nondegenerate by `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`,
   and the orientation it induces is `o.sphereOrientation`. That last step
   needs one small lemma: `IsNondegenerate.volumeOrientation` is `ofTopForm`
   of `(1!)⁻¹ • wedgePow σ 1` (`Geometry/Symplectic/Manifold/Volume.lean`),
   and Tau Ceti has no `wedgePow_one`. These lemmas are about Tau Ceti's
   notions only, so each goes in this library's counterpart of the Tau Ceti
   file of its subject, not in `Collapse.lean`:
   - `ContinuousAlternatingMap.wedgePow_one` (`wedgePow ω 1 = ω` for a
     continuous alternating 2-form `ω`), in
     `Topology/Algebra/Module/Alternating/Wedge/TwoForm.lean`, beside Tau
     Ceti's `wedgePow_two_eq`;
   - its smooth form `TauCeti.SmoothForm.wedgePow_one`, pointwise from the
     first, in `Geometry/Manifold/DifferentialForm/Wedge/Smooth/Pow.lean`;
   - `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_ofTopForm`
     (on a surface, the orientation of a nondegenerate `σ` is `ofTopForm`
     of `σ`), in `Geometry/Symplectic/Manifold/Volume.lean`;
   - `TauCeti.degree_eq_orientationSign_of_preimage_eq_singleton` (the
     degree of a proper smooth map whose fibre over a point is one point
     with invertible derivative is the orientation sign there), in
     `Geometry/Manifold/Degree/Global.lean`.

   With `volumeOrientation_eq_ofTopForm` the induced orientation is `o.sphereOrientation`,
   which is defined by `ofTopForm`. The genus of
   the sphere is `TauCeti.surfaceGenus_sphere` of prerequisite 2. Blocked by
   5. Done when these are proved.

### The part's own issues

10. **Chern classes and numbers.** `FirstChernClass.lean` and `Basic.lean`,
    with `FiniteRank/EulerClass.lean`, `Complex/Structure.lean` and
    `ComplexSmulI.lean`.
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
    `symplecticChernNumber_eq_boundaryMaslovIndex`, with
    `TauCeti.GLSymplectic.maslovPhase_mul_homotopic` in
    `Analysis/Matrix/SymplecticGroup/Maslov.lean`. Blocked by 7 and 12.
18. **The extension lemma.** `exists_extension_iff_boundaryMaslovIndex_eq_zero`
    in `Splitting.lean`. Blocked by 8, 14 and 17.

The first milestone needs issues 1, 2, 5–10, 12–14, 17 and 18, with the
named issues of other parts; it is done only when 14, 17 and 18 are all
merged. The Euler-number milestone needs 1, 10 and 11, and the Chern–Weil
milestone 1, 3–7, 10, 12 and 15. Issue 16 completes the comparison with Tau
Ceti.
