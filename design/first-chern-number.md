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
realification, with the complex orientation); Bott–Tu [BottTu1982], §§6, 11 and 20 (the Euler class as a count of
zeros, and the Chern–Weil description of $c_1$ for circle bundles).

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, as for `DESIGN.md`. Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`.

## The decision: a cohomological definition

The first Chern class of a complex vector bundle $E\to B$ is the Euler class of
its determinant line:

$$c_1(E) := e\bigl((\Lambda^{\mathrm{top}}_{\mathbb{C}}E)_{\mathbb{R}}\bigr)\in H^2(B;\mathbb{Z}),$$

with the canonical orientation of a complex line. In Lean this is Tau Ceti's
`TauCeti.complexEulerClass` with `r = 0`, applied to the determinant line
built from Tau Ceti's `TauCeti.FiniteRankBundleCore.det`. Over a closed oriented
surface $\Sigma$ the *first Chern number* is the pairing of this class with the
fundamental class, Tau Ceti's
`TauCeti.HomologicalOrientation.evalFundamentalClass`. A symplectic vector
bundle gets the Chern number of the complex bundle given by any compatible
complex structure.

The book defines $c_1$ through a splitting $\Sigma=\Sigma_1\cup_C\Sigma_2$,
symplectic trivializations over the two halves, and the Maslov indices of the
overlap loops. Here that description, and the description from a single
disc, are theorems (`Clutching` and `Splitting` below). Tau Ceti's
`TauCeti.clutchingNumber` is defined only on spheres $I^2/\partial I^2\to X$,
so it cannot define a number for every surface; it becomes a comparison
theorem. The reasons for this choice:

- **Functoriality is free.** $c_1(\varphi^*E)=\varphi^*c_1(E)$ is naturality
  of the Euler class (`TauCeti.complexEulerClass_pullback`) and of the
  determinant, and $\langle\varphi^*c,[\Sigma']\rangle=\deg(\varphi)\langle
  c,[\Sigma]\rangle$ is Tau Ceti's
  `TauCeti.HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul`.
  `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`
  identifies the homological degree with the signed count at a regular value,
  `TauCeti.degree`. Starting from the splitting definition, functoriality
  needs splittings adapted to the preimages of a regular value, which is
  hard.
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

## Conventions

- **Surfaces.** A closed surface is
  `[TopologicalSpace Σ] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Σ]
  [IsManifold (𝓡 2) ∞ Σ] [T2Space Σ] [CompactSpace Σ]`, with `Σ : Type`, and
  an orientation `o : TauCeti.Manifold.Orientation (𝓡 2) Σ (Fin 2)`. The
  model `𝓡 2` is the one of `TauCeti.Manifold.Orientation.degree_toHomologicalOrientation_eq_degree`
  and of Mathlib's spheres. Connectedness, `[ConnectedSpace Σ]`, is a
  hypothesis exactly where the plan or `DESIGN.md` asks for it. The
  homological orientation that the topological statements use is
  `o.toHomologicalOrientation`.
- **Universes.** Tau Ceti's fundamental class and local indices live in
  `Type`, and `complexEulerClass` asks for the base and the model fibre in
  one universe. The determinant line has model fibre `Fin 1 → ℂ`, so the
  class is defined for bases `B : Type`. Every manifold in the plan is in
  `Type`.
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
- **Orientation of the clutching circle.** A *coordinate disc* is an open
  embedding `φ : Metric.ball (0 : ℂ) 2 → Σ` that carries the standard
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

## Files

All files are under `SymplecticGeometry/`. The part's own files are in
`Geometry/Manifold/VectorBundle/ChernNumber/`, as in `DESIGN.md`. One extra
file, the topological class, goes in `Topology/VectorBundle/Complex/`,
because it uses no smooth structure and is defined over any base (a folder
here beside Tau Ceti's folder of the same name; no Tau Ceti file has the name
`Complex.lean` at that place). The prerequisites have files of their own,
listed with their issues.

### `Topology/VectorBundle/Complex/FirstChernClass.lean`

In the namespace `SymplecticGeometry.Bundle`, for a complex vector bundle
`E` with model `G` over `B : Type`:

- `firstChernClass G E`, the Euler class
  `TauCeti.complexEulerClass (Fin 1 → ℂ) (complexDet G E).core.Fiber rfl`
  (with the determinant of the prerequisite below), and `firstChernClass_def`
  by `(rfl)`.
- `firstChernClass_pullback (f : C(B', B))`: the class of `f *ᵖ E` is the
  pull-back of the class of `E`.
- `firstChernClass_congr`: complex-linear fibrewise isomorphisms that are
  continuous on total spaces (`Bundle.Trivialization`-compatible equivalences,
  in the form Tau Ceti's `TauCeti.VectorBundleOrientation.eulerClass_eq_of_fiberwise`
  takes) preserve the class.
- `firstChernClass_trivial`: zero for `Bundle.Trivial B G`, from
  `TauCeti.complexEulerClass_trivial`.
- `firstChernClass_of_finrank_eq_one`: for a line bundle it is
  `complexEulerClass G E hG`.
- `firstChernClass_conj`: the conjugate bundle (Tau Ceti's
  `Topology/VectorBundle/Conjugate.lean`) has the negated class: the
  determinant of the conjugate is the conjugate of the determinant, and the
  canonical orientation of a conjugate line is reversed, so
  `TauCeti.VectorBundleOrientation.eulerClass_neg` applies.

No Whitney sum formula is claimed over a general base; additivity is proved
over surfaces only, from clutching.

### `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean`

- `chernNumber o G E : ℤ`, for a complex vector bundle over a closed oriented
  surface: the integer under
  `(o.toHomologicalOrientation _).evalFundamentalClass _ _ (ContinuousMap.id Σ)
  (firstChernClass G E)`; with `chernNumber_def`.
- `chernNumber_neg_orientation`: reversing `o` negates it.
- `chernNumber_congr`, `chernNumber_trivial`, `chernNumber_conj`, from the
  file above.
- `chernNumber_pullback`: for `φ : Σ' → Σ` smooth between closed oriented
  surfaces, `Σ` connected, `chernNumber o' G (φ *ᵖ E) = TauCeti.degree o' o φ *
  chernNumber o G E`. The proof combines `firstChernClass_pullback`,
  `evalFundamentalClass_id_singularCohomologyMap_eq_degree_smul` and
  `degree_toHomologicalOrientation_eq_degree`.
- `symplecticChernNumber o ω : ℤ` for a symplectic vector bundle `(E, ω)` in
  the representation of *Symplectic vector bundles*: the `chernNumber` of the
  complex bundle of a compatible complex structure, chosen by the existence
  theorem of that part. `symplecticChernNumber_eq` gives the same value for
  every compatible or tame `J`. The proof: by that part's classification
  theorem (`.../Symplectic/Classification.lean`), the identity of `(E, ω)` is
  a symplectic isomorphism, so the two complex bundles are isomorphic.
- `symplecticChernNumber_neg`: `(E, -ω)` has the negated number, since `-J`
  is compatible with `-ω` and gives the conjugate bundle.
- `symplecticChernNumber_pullback` and `symplecticChernNumber_congr`, from
  the complex statements and the pullback and isomorphisms of symplectic
  bundles that *Symplectic vector bundles* defines.

### `Geometry/Manifold/VectorBundle/ChernNumber/Clutching.lean`

The disc clutching formula, in a topological form that works for a compact
topological surface with a homological orientation, and the symplectic form
the book uses.

- `sum_degree_boundary_eq_zero`: let `φ i`, `i : ι` finite, be coordinate
  discs with disjoint closed discs, and let
  `u : (Σ ∖ ⋃ i, φ i '' ball 0 1) → ℂ` be continuous and nowhere zero. Then
  the degrees (`Circle.degree`) of `u/|u|` around the circles sum to $0$. Proof:
  extend `u` radially into each disc, with one zero at each centre. This is a
  section of the trivial line bundle with finitely many zeros. Its local
  index at a centre is the winding number of its boundary loop, by
  `TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul` and
  `TauCeti.HomologicalOrientation.localDegree_eq_degree_toBasedLoop`. The
  indices sum to the Euler number of the trivial bundle, which is $0$. This
  is the half of the book's Lemma 2.7.3 that the part uses, in the case of
  discs.
- `chernNumber_eq_sum_degree_clutching`: given such discs, a frame `Φ i` of
  `E` along `φ i` on the closed unit disc and a frame `Φout` over the
  complement of the open discs (frames in the sense of Tau Ceti's
  `Clutching.lean`: continuous families of `G ≃L[ℂ] E x`), the Chern number
  is the sum over `i` of the degrees of the normalized determinant
  (`ContinuousLinearEquiv.normalizedDet`) of the loop `(Φ i)⁻¹ ∘ Φout` around the `i`-th
  circle. Proof: the section of the determinant line that is the wedge of
  `Φout` outside, extended radially in each disc as above, has one zero per
  disc, with index the degree of the determinant of the transition. One disc
  is the case `ι = Unit`.
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
  `sum_degree_boundary_eq_zero` applied to the Maslov phase. For unitary
  loops the index is the degree of the determinant,
  `Matrix.UnitaryGroup.maslovIndex_eq_degree`.

### `Geometry/Manifold/VectorBundle/ChernNumber/Gluing.lean`

Bundles from clutching data, and isomorphisms from homotopies.

- `clutchingLineBundle φ k`: over a closed surface with a coordinate disc
  `φ`, the smooth Hermitian line bundle glued from the trivial bundles over
  `φ '' ball 0 1` and over the complement of `φ '' closedBall 0 (1/2)`, with
  transition $e^{ik\theta}$ on the annulus between them. It is a
  `VectorBundleCore` with two charts and smooth unitary coordinate changes,
  so Mathlib's `VectorBundleCore` API gives its instances. With its standard
  symplectic form it is a symplectic line bundle.
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
  equality of surfaces: `structure ClosedOrientedSurface` (a type `Σ : Type`
  with the instances above, `[ConnectedSpace Σ]` and an orientation), and
  `structure SymplecticSurfaceBundle (S : ClosedOrientedSurface)` (the
  complex rank `n`, a model fibre `F : Type` with `finrank ℝ F = 2 * n`, the
  fibres `E : S → Type` with the smooth bundle instances, and the symplectic
  form `ω` in the representation of *Symplectic vector bundles*).
- `structure ChernNumberAxioms
  (c : ∀ S : ClosedOrientedSurface, SymplecticSurfaceBundle S → ℤ) : Prop`
  with four fields, as the plan states the axioms:
  - `iso_iff`: for `E E' : SymplecticSurfaceBundle S`, `Nonempty (E ≅ E')`
    (symplectic bundle isomorphism) if and only if `E.n = E'.n` and
    `c S E = c S E'`;
  - `pullback`: `c S' (φ^* E) = TauCeti.degree o' o φ * c S E` for every
    smooth `φ : S' → S`;
  - `whitneySum`: `c S (E ⊕ E') = c S E + c S E'`, with the direct sum of
    symplectic bundles from *Symplectic vector bundles* (Mathlib's
    `Bundle.Prod`);
  - `tangent`: `c S (TΣ, σ) = 2 - 2 * TauCeti.surfaceGenus S` for every area
    form `σ` that induces the orientation of `S`.
- `symplecticChernNumber_whitneySum` (from block frames and
  `TauCeti.GLSymplectic.maslovIndex_sum`, through the clutching formula with
  frames from *Symplectic vector bundles*).
- `symplecticChernNumber_tangent`: for $T\Sigma$ with an area form $\sigma$
  inducing `o`, and a $\sigma$-compatible $J$, the complex orientation of
  $(T\Sigma,J)$ is the orientation of `Σ`. So the number is the Euler number
  of $T\Sigma$. For the gradient of a Morse function (`TauCeti.exists_isMorse`,
  with a Riemannian metric), the local indices are the signs of the
  Jacobians (`sectionIndex_eq_sign_det_of_hasFDerivAt`), whose sum is
  $\chi(\Sigma)=2-b_1$ by Poincaré–Hopf and
  `TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_finrank_singularHomology_one`.
  Last, $b_1=2g$ by the prerequisite on the evenness of $b_1$.
- `symplecticChernNumber_iso_iff`: the forward direction is
  `symplecticChernNumber_congr`; the converse is
  `nonempty_iso_of_maslovIndex_eq` with the clutching formula.
- `chernNumberAxioms_symplecticChernNumber`.
- `eq_symplecticChernNumber_of_chernNumberAxioms`: uniqueness. Fix `S` and
  let `c` satisfy the axioms. By `iso_iff`, `c` is constant on isomorphism
  classes. A trivial bundle is the pull-back of itself along a constant map,
  of degree $0$ (`TauCeti.degree_const`), so `pullback` gives it `c = 0`. A
  bundle of rank `n ≥ 1` and number `k` is isomorphic to
  `clutchingLineBundle φ k` plus a trivial bundle, by
  `symplecticChernNumber_iso_iff`. So `c` is `h k` for one function
  `h : ℤ → ℤ`. Since `L_a ⊕ L_b` and `L_(a+b) ⊕ trivial` are isomorphic,
  `whitneySum` makes `h` additive, so `h k = k * h 1`. Last, pull back
  $TS^2$ along a smooth map $\Sigma\to S^2$ of degree one: `tangent` on $S^2$
  and `pullback` give `h 2 = 2`. Normalization on `S` alone would not
  suffice, since it says nothing for the torus.
- **Milestone** `existsUnique_chernNumberAxioms :
  ∃! c : ∀ S : ClosedOrientedSurface, SymplecticSurfaceBundle S → ℤ,
  ChernNumberAxioms c`, with the
  surface connected, as `DESIGN.md` and the plan say. Milestone: *First
  Chern number of symplectic vector bundles over surfaces*.
- The plan's further remark about $c_1=0$ is the case `E' = trivial` of
  `iso_iff`, and is stated as `symplecticChernNumber_eq_zero_iff`.

### `Geometry/Manifold/VectorBundle/ChernNumber/EulerNumber.lean`

- **Milestone** `chernNumber_eq_sum_sectionIndex`: let `L` be a smooth complex
  line bundle over a closed oriented surface (a smooth real rank-2 bundle with
  a complex structure, in the representation of *Symplectic vector
  bundles*), and `s` a smooth section transverse to the zero section, in Tau
  Ceti's sense (`TauCeti.sectionLinearization` surjective at every zero).
  Then the zero set is finite, and `chernNumber o ℂ L` is the sum over the
  zeros of `TauCeti.VectorBundleOrientation.sectionIndex` for the canonical
  orientation `TauCeti.VectorBundleOrientation.complex`. Each index is
  $\pm1$, the sign of the Jacobian in oriented charts
  (`sectionIndex_eq_sign_det_of_hasFDerivAt`), which is the book's
  intersection index. Milestone: *First Chern number as an Euler number*. The
  surface need not be connected.
- Finiteness: a transverse zero is isolated, by the inverse function theorem
  in a chart, and the zero set is compact.
- The proof is `firstChernClass_of_finrank_eq_one` followed by
  `evalFundamentalClass_eulerClass_eq_sum_sectionIndex`. With this
  definition the milestone does not depend on the other two.

### `Geometry/Manifold/VectorBundle/ChernNumber/ChernWeil.lean`

- Uses the circle bundle `P` of a Hermitian line bundle and its connection
  forms from the prerequisites.
- `chernNumber_eq_integral_curvature`: for every connection form `α` on `P`,
  `(chernNumber o ℂ L : ℝ) = -(2 * π)⁻¹ * TauCeti.integralTopForm o (curvature
  α)`. Proof: two connection forms differ by `π^* a`, so their curvatures
  differ by `d a`, whose integral is $0$
  (`TauCeti.integralTopForm_mextDeriv_eq_zero`; no connectedness needed). So
  it suffices to compute one connection. Choose frames as in the clutching
  formula, one disc per component of `Σ`, normalized so that each transition
  is exactly $e^{ik_j\theta}$ (`Circle.joined_iff_circleDegree_eq`, and a
  change of frame on a collar). Take the connection that is flat for the
  outer frame and equal to $k_j\beta(r)\,d\theta$ for the disc frame, with
  $\beta$ a smooth cut-off. Its curvature is supported in the discs, where
  the integral is computed in polar coordinates: $-2\pi k_j$ for each disc
  (`TauCeti.integralTopForm_eq_chartIntegral`).
- `exists_connectionForm_curvature_eq`: if `Σ` is connected, every smooth
  real 2-form `σ` with `∫ σ = -2π * chernNumber o ℂ L` is the curvature of a
  connection form. Proof: `σ - curvature α₀` has integral $0$, so it is exact
  by `TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`
  (with `TauCeti.compactlySupportedForms_eq_top`). Then add the pull-back of
  a primitive to `α₀`.
- **Milestone** `chernWeil`: the conjunction of the first statement, for
  every closed oriented surface, and the second, under `ConnectedSpace Σ`, as
  the plan and the *Milestones* table of `DESIGN.md` say. It is written with
  real forms, by the convention above. Milestone: *Chern–Weil formula for
  circle bundles over surfaces*.

### `Geometry/Manifold/VectorBundle/ChernNumber/Comparison.lean`

The comparison with Tau Ceti's `TauCeti.clutchingNumber`, which `DESIGN.md`
places in `.../Clutching.lean`. That name is taken here by the clutching
formula, so the comparison has a file of its own. For a based sphere
`p : Ω^ (Fin 2) X x` and a complex bundle `E` over `X`,
`clutchingNumber G E p` equals the Chern number of the pull-back of `E` to
$S^2$ along the map that `p` induces, for the orientation of $S^2$ for which
the collapse $I^2\to S^2$ preserves orientation in the interior. Proof: the
interior of the square is a coordinate disc, the frame along `p` is a frame
over it, and the trivialization near `x` is a frame over the complement; the
two clutching functions agree by the convention above. The theorem is
`clutchingNumber_eq_chernNumber`.

### `Geometry/Manifold/VectorBundle/ChernNumber/Splitting.lean`

The book's description and its key lemma, which no other result of the part
needs.

- A *splitting* of a closed oriented surface is given by a smooth
  `f : Σ → ℝ` with regular value `0`: $\Sigma_1=\{f\le0\}$,
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
  transition $\Phi_1^{-1}\Phi_2$ on `C`, by the splitting form of the
  argument principle (prerequisite) and the unitary reduction of
  `Clutching.lean`.
- `exists_extension_iff_boundaryMaslovIndex_eq_zero`: the book's Lemma 2.7.3,
  for a connected compact oriented surface whose boundary is not empty, in the
  representation that *Symplectic vector bundles* fixes for its last
  milestone. A continuous `Ψ` on the boundary extends continuously over the
  surface if and only if its boundary Maslov index is $0$. "Only if" is the
  argument principle. "If": cap the boundary circles with discs (prerequisite)
  and glue a bundle over the closed surface with clutching `Ψ`. Its number is
  $0$, so it is trivial by `iso_iff`. A global frame then writes `Ψ` as a map
  defined on the surface times maps defined on the discs, and the latter are
  null-homotopic on the circles, which a collar absorbs.

## What the part uses

- **From other parts.** *Symplectic vector bundles*: the representation of
  symplectic bundles, their isomorphisms, pullbacks and direct sums; the
  tangent bundle of a surface with an area form as a symplectic bundle;
  existence of compatible complex structures and the map to
  `ContinuousComplexStructure`; the classification theorem; Hermitian line
  bundles; unitary trivializations over surfaces with boundary, applied to
  the complement of open coordinate discs. *Maslov index*, symplectic loops:
  the converse of the homotopy axiom. *Standard model*: `stdForm`. If
  *Symplectic vector bundles* states its trivialization milestone for
  abstract surfaces with boundary, the issue for `Gluing.lean` derives the
  case of the complement of open discs in a closed surface (a regular
  domain, as in `Splitting.lean`).
- **From Tau Ceti.** Everything named above: `complexEulerClass`, the Euler
  class API (`Topology/VectorBundle/Orientation/`), local indices and
  their computation (`.../SectionIndex.lean`, `.../SectionIndex/Degree.lean`),
  the winding number of a plane map
  (`AlgebraicTopology/Singular/LocalHomology/Winding.lean`), fundamental
  classes and degrees (`AlgebraicTopology/Cohomology/FundamentalClass.lean`,
  `Geometry/Manifold/Degree/`), finite-rank cores and their determinant
  (`Topology/VectorBundle/FiniteRank/`, `Topology/VectorBundle/Core/Basic.lean`),
  Morse functions and Poincaré–Hopf (`Geometry/Manifold/Morse/`), generic
  sections (`Geometry/Manifold/VectorBundle/Section/Generic.lean`), the Maslov
  index of symplectic loops, frames and clutching
  (`Topology/VectorBundle/Complex/Clutching.lean`,
  `Topology/VectorBundle/Contractible.lean`), integration and Stokes on closed
  manifolds (`Geometry/Manifold/DifferentialForm/Integration/`,
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

1. **Determinant line of a complex vector bundle.**
   `Topology/VectorBundle/Complex/Determinant.lean`: the core
   `SymplecticGeometry.Bundle.complexDet G E : TauCeti.FiniteRankBundleCore ℂ B`
   of rank one, built by remodelling `TauCeti.pointIndexedCore` along a
   linear equivalence `G ≃ (Fin (finrank ℂ G) → ℂ)` and taking
   `FiniteRankBundleCore.det`. It comes with compatibility with pullback (Tau
   Ceti's `CoordinateFunctor.functor_comp_pullbackFunctor`), functoriality in
   fibrewise isomorphisms, the trivial bundle, the identification with `E` in
   rank one (`exteriorPowerOneNatIso`), and the conjugate bundle. Done when
   these are proved and build.
2. **Evenness of the first Betti number of a closed orientable surface.**
   `AlgebraicTopology/Singular/SurfaceGenus.lean` (the name of Tau Ceti's
   file, so that the two merge): for a closed connected homologically oriented
   surface, `finrank ℚ H₁(Σ; ℚ)` is even, so `χ(Σ) = 2 - 2 * surfaceGenus Σ`.
   Route: Tau Ceti's `TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`,
   given injectivity of the cap product with the fundamental class in degree
   one. That injectivity is the degree-one case of Poincaré duality, which
   Tau Ceti prepares in `AlgebraicTopology/Cohomology/CompactSupport/`
   (`HomologicalOrientation.dualityMap` and its criterion) but does not
   finish. The issue first checks whether Tau Ceti has finished it since the
   pin. If not, it proves duality for closed oriented manifolds from that
   criterion, splitting into further issues if that is more than a few
   hundred lines. Done when the evenness theorem is proved.
3. **The unit circle bundle of a Hermitian line bundle.**
   `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean`: for a smooth
   Hermitian line bundle `L`, the bundle `circleBundle L` with fibres the unit
   circles, the right action of `Circle` by scalar multiplication, and
   trivializations from local unit sections. It is a
   `TauCeti.PrincipalBundle Circle` and a smooth fibre bundle, by
   `TauCeti.PrincipalBundle.contMDiffFiberBundle_iff` (the transitions are
   smooth `Circle`-valued functions). So `TauCeti.ManifoldTotalSpace Circle
   (circleBundle L)` is a smooth manifold, and its projection is a smooth
   submersion. Blocked by the issue of *Symplectic vector bundles* that
   fixes Hermitian line bundles. Done when these instances and the
   submersion property are proved.
4. **Connection forms on principal circle bundles.**
   `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`: for a
   smooth principal `Circle`-bundle `P` over `M`, the predicate
   `IsConnectionForm α` for a smooth real 1-form on the total space,
   invariant under the action and equal to $1$ on the fundamental vector
   field of $1$ (`TauCeti.rightFundamentalVectorField` composed with
   `Circle.exp`). Its curvature `curvature α`, the 2-form on `M` whose
   pull-back is `d α`, exists and is unique by descent of basic forms
   (`TauCeti.RoughForm.IsBasic`, `TauCeti.IsSubmersion.exists_smoothForm_mpullback_eq_iff`).
   API: `α + π^* a` is a connection form for every 1-form `a` on `M`, any two
   differ by such an `a`, and `curvature (α + π^* a) = curvature α + d a`;
   existence of a connection form, by a partition of unity from the
   `TauCeti.PrincipalBundle.trivializationOfSection` charts; and the local
   form $d\theta+\pi^*s^*\alpha$ in the trivialization of a local section
   `s`. Blocked by 3 only for its example; the definitions are for any `P`.
   Done when this API is proved and applied to `circleBundle L`.
5. **Argument principle along a splitting.**
   `AlgebraicTopology/Singular/LocalHomology/ArgumentPrinciple.lean`: let
   `X` be compact with collared boundary `∂X` and oriented interior, as in
   `RelativeFundamentalClass.lean`. Let `L` be an oriented real plane bundle
   over `X`, with a nowhere-zero section `s` on `∂X` and a section `t` with
   finitely many zeros, all in the interior, and equal to `s` on `∂X`. Then
   the sum of the local indices of `t` is the degree of `s` against the
   boundary class `∂[X, ∂X]`. Route: excision and the connecting morphism of
   `(X, ∂X)`, with the pairing of the relative Thom class pulled back by `t`.
   Done when this and the corresponding Euler-number formula for a closed
   surface split along `f⁻¹(0)` are proved. Only `Splitting.lean` needs it.
6. **Capping a surface with boundary.** In the file that *Symplectic vector
   bundles* uses for surfaces with boundary: a compact oriented surface with
   boundary circles parametrized by orientation-reversing loops, glued to
   discs along them, is a closed oriented surface, by Tau Ceti's
   `Geometry/Manifold/Gluing/`. Only the converse of Lemma 2.7.3 needs it.
   Blocked by the issue that fixes that representation.
7. **A map of degree one onto the sphere.**
   `Geometry/Manifold/Degree/Collapse.lean`: every closed connected oriented
   surface has a smooth map to $S^2$ of degree one, by collapsing the
   complement of a coordinate disc through a cut-off, with `TauCeti.degree`
   computed at the image of the centre. It also gives the facts about $S^2$
   that uniqueness uses: its orientation and `surfaceGenus = 0`, from Tau
   Ceti's homology of spheres. Done when both are proved.

### The part's own issues

8. **Chern classes and numbers.** `FirstChernClass.lean` and `Basic.lean`.
   Blocked by 1, by *Symplectic vector bundles*' issues for symplectic bundles
   and complex structures, and by its classification issue for
   `symplecticChernNumber_eq`.
9. **The Euler-number milestone.** `EulerNumber.lean`. Blocked by 8.
10. **The disc clutching formula.** `Clutching.lean`. Blocked by 8.
11. **Gluing.** `Gluing.lean`. Blocked by 10, by *Maslov index*'s
    symplectic-loop issue, and by *Symplectic vector bundles*' issue for
    trivializations over surfaces with boundary.
12. **The axioms and the first milestone.** `Axioms.lean`. Blocked by 2, 7
    and 11. If it is too long, `symplecticChernNumber_tangent` goes first, on
    its own.
13. **The Chern–Weil milestone.** `ChernWeil.lean`. Blocked by 4 and 10.
14. **Comparison with clutching numbers.** `Comparison.lean`. Blocked by 10.
15. **Splittings and Lemma 2.7.3.** `Splitting.lean`. Blocked by 5, 6 and 12.
    The converse of the lemma can be a separate issue after the rest.

The milestones need issues 1–4, 7–13 and the named issues of other parts;
issues 5, 6, 14 and 15 complete the book's description and the comparison
with Tau Ceti, and can follow.
