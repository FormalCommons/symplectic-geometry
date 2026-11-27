# Symplectic h-principle

This is the detailed design of part 63 of `DESIGN.md`, *Symplectic
h-principle*. It covers the two milestones of §7.3 of
`atlas/constructing-symplectic-manifolds.md`: *Gromov's h-principle for
symplectic forms on open manifolds* (existence, path components, and the
parametric statement) and *Relative extension of exact symplectic forms over
a handle core*. The sources are McDuff–Salamon [McDuffSalamon2017], Theorem
7.3.1 and Lemma 7.3.2, and Eliashberg–Mishachev [EliashbergMishachev2002],
Theorems 4.7.4 and 10.2.1–10.2.2 (first edition).

All names below are in the namespace `SymplecticGeometry` unless written with
another one. Paths of new files are under `SymplecticGeometry/`; Tau Ceti
paths are relative to `.lake/packages/TauCeti/TauCeti/`. Manifolds, forms and
families follow *Manifolds, families and signs* of `DESIGN.md`: `M` is
modelled on `I : ModelWithCorners ℝ E H` with `[FiniteDimensional ℝ E]`,
`[I.Boundaryless]`, `[IsManifold I ∞ M]`, `[T2Space M]` and
`[SigmaCompactSpace M]`; forms are Tau Ceti's `SmoothTwoForm I M`; a smooth
family over a parameter manifold `N` is *Smooth families*'
`IsSmoothFamily J α`. *Open* means: no connected component is compact,
`∀ x : M, ¬ IsCompact (connectedComponent x)`, the page's boundary-free
formulation.

## What exists, and what the part adds

- **Forms and classes.** `TauCeti.SmoothTwoForm.IsNondegenerate`,
  `IsSymplectic` (`Geometry/Symplectic/Manifold/TwoForm.lean`), `closedForms`,
  `exactForms`, `deRhamCohomology.mk` with `mk_surjective` and
  `mk_eq_zero_iff` (`Geometry/Manifold/DeRham/Basic.lean`). Pullback along a
  diffeotopy keeps the class: `TauCeti.Diffeotopy.mpullback_final_sub_mem_exactForms`
  (`Geometry/Manifold/DeRham/Diffeotopy.lean`); along homotopic smooth maps:
  this library's `mpullback_sub_mem_exactForms_of_homotopy`
  (`Geometry/Manifold/DeRham/Map.lean`).
- **Families.** *Smooth families*' `IsSmoothFamily`
  (`Geometry/Manifold/DifferentialForm/SmoothFamily/Basic.lean`), the
  parametric Poincaré lemma
  `IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`
  (`.../SmoothFamily/Poincare.lean`), smooth primitives of exact families of
  one-forms (`Geometry/Manifold/DeRham/FamilyPrimitive.lean`), and the time
  extension and reparametrizations of `Diffeotopy/Real.lean`. Restriction to
  open subsets is `Geometry/Manifold/DifferentialForm/Opens.lean`.
- **Spaces of forms.** *Symplectic vector bundles*' `Bundle.ContMDiffTwoForm`
  with `ContMDiffSection.frameTopology` and the linear equivalence
  `Bundle.ContMDiffTwoForm.tangentEquiv` with Tau Ceti's `SmoothTwoForm`, with
  `isNondegenerate_tangentEquiv_iff`
  (`Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`). This is the bridge
  that the review of #3195 asked for: classes are taken of `tangentEquiv ω`.
- **Morse theory.** `TauCeti.exists_isMorse_isProperMap_bddBelow`
  (`Geometry/Manifold/Morse/Generic/Strong.lean`), the exhaustion
  `TauCeti.IsMorse.exists_regular_sublevel_exhaustion`
  (`Geometry/Manifold/Morse/Exhaustion.lean`), `manifoldMorseIndex`
  (`Morse/Index.lean`), the Morse lemma charts (`Morse/Lemma.lean`,
  `Morse/NormalizedChart.lean`), pseudo-gradient fields and their flows
  (`Morse/PseudoGradient/`) and the stable manifolds (`Morse/Stable/`).
  Neither library has a Morse function without critical points of top
  index, nor a core of an open manifold with a compressing isotopy.
- **Homotopy theory.** Tau Ceti's
  `ContinuousMap.IsWeakHomotopyEquivalence`
  (`Topology/Homotopy/HomotopyGroup/WeakHomotopyEquivalence.lean`) and
  Whitehead's theorem `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`
  with `homotopyEquiv_toFun` (`AlgebraicTopology/Homotopy/Whitehead.lean`),
  for spaces with `TauCeti.CWType`
  (`Topology/CWComplex/Classical/CWType.lean`), with the two halves of its
  proof for any source of CW type, `exists_comp_homotopic` and
  `homotopic_of_comp_homotopic`. CW approximation of any space:
  `TauCeti.sigmaCWApproximationMap` with
  `isWeakHomotopyEquivalence_sigmaCWApproximationMap` and
  `cwType_sigmaCWApproximation`
  (`AlgebraicTopology/Homotopy/CWApproximation/Sigma.lean`). Simplicial
  complexes: `AbstractSimplicialComplex.Realization` with the weak topology,
  `continuous_iff_faceInclusion` and `instT2SpaceRealization`
  (`AlgebraicTopology/SimplicialComplex/Realization/Basic.lean`), and
  `realizationCWComplex` (`.../Realization/CWComplex/Basic.lean`). The frame
  topology is metrizable on a Lindelöf base
  (`ContMDiffSection.isCompletelyMetrizableSpace_frameTopology`,
  `Geometry/Manifold/VectorBundle/Section/CompletelyMetrizable.lean`) and
  locally convex (`Section/Topology.lean`). Mathlib has locally finite
  partitions of unity subordinate to any open cover of a paracompact normal
  space (`PartitionOfUnity.exists_isSubordinate`), and metric spaces are
  paracompact. Neither library has absolute neighbourhood retracts or
  Milnor's or Dugundji's theorems, and neither shows that a space of smooth
  sections has CW type.
- **Holonomic approximation.** Neither library has it. Tau Ceti has jet
  bundles (`Geometry/Manifold/VectorBundle/Jet/Basic.lean`,
  `VectorBundle/FirstJet/`), which this part does not need (see
  *Decisions*).

## Decisions

1. **One route for Theorem 7.3.1: compression.** All three statements of
   the first milestone (existence, path components, parametric) come from one
   parametric, relative theorem, proved by Eliashberg–Mishachev's route:
   approximate a formal primitive of $\tau_\lambda-\alpha$ by a genuine one
   near a core, then pull everything back by an isotopy of embeddings that
   compresses $M$ into a neighbourhood of the core, one critical level at a
   time (`Morse/Core/`). The book's telescope
   over the handles of a Morse exhaustion is not used. Reasons: with
   infinitely many critical points, the book's induction needs a compatible
   choice of homotopies over the whole exhaustion, which the page flags as
   missing; and in the telescope, gluing the homotopy of a handle into the
   rest of $M$ by a cutoff breaks closedness at the parameters where the
   form is already symplectic, which the relative parametric statement
   needs. The compression route glues no forms by a cutoff except along the
   segment from a form to its approximation, inside the open set where the
   whole segment is nondegenerate; otherwise it only pulls back along
   embeddings into the neighbourhood where the approximation holds. So
   `Telescope.lean` of `DESIGN.md` is dropped, and the milestone's
   existence and path statements go in `OpenManifold.lean`, as corollaries
   (parameter spaces a point and $[0,1]$).
2. **The handle-core lemma is proved by compression**, as a milestone on
   its own (`HandleCore.lean`), not by the book's induction on $m$, which
   the source only sketches and whose direct readings fail (the
   `HandleCore.lean` section says why). For every $m$, holonomic
   approximation over the cube, relative to the part of the core near the
   attaching faces, gives an exact form close to the given one near the
   displaced core, and pulling back along a compression of the cube
   towards the core, followed by the displacing diffeotopy, ends the
   homotopy, as in Decision 1 for one cube. The case $m=1$ is also proved
   without holonomic approximation (`HandleCore/OneDimensional.lean`).
   Nothing else in the part uses the lemma. It is stated for forms on the
   whole model space, with its conditions on the cube and near the
   attaching faces, so that no form on a subset is needed.
3. **Holonomic approximation in coordinates only.** Every use happens in
   charts around the cubes of a core, so the approximation is proved for
   first jets of maps $\mathbb R^m\times\mathbb R^{d-m}\to F$ near the cube
   $I^m\times 0$, $m<d$, with Mathlib's `fderiv`, relative to a
   neighbourhood of $\partial I^m\times 0$ and to a closed set of
   parameters, for compact families. The formal datum on $M$ is a pair
   (one-form $\beta$, bilinear form $G$) in a chart with
   $G-G^{\mathsf T}=\tau-\alpha$; where $d\beta=\tau-\alpha$ already, $G$ is
   taken to be the derivative of $\beta$, so the datum is holonomic there and
   left unchanged. The result is chart-independent because only $d\beta$
   enters. Tau Ceti's jet bundles are not needed; the files are outside
   `Geometry/Symplectic/`, as general h-principle material, under
   `Analysis/Calculus/HolonomicApproximation/`.
4. **Parameters.** The engine takes a compact Hausdorff parameter space `P`
   and a closed `P₀ ⊆ P` of parameters where the form is already symplectic
   in the class, and comes in two forms with one proof: for families
   continuous into the `frameTopology` (needed by homotopy groups) and, for
   an `IsSmoothFamily` over a finite-dimensional normed space, for smooth
   families with smooth output (needed by the path statement). The closed
   representative of the class is not fixed but a family $\alpha_\lambda$ in
   the class with
   $\alpha_\lambda=\tau_\lambda$ on `P₀`, an extension of `τ` from `P₀` into
   the convex set of closed representatives of $a$. The engine takes this
   family as a hypothesis, and each use builds it by an explicit formula: a
   constant at a point, $\alpha_t=(1-t)\omega_0+t\omega_1$ on $[0,1]$, a
   radial formula on a disc or cube relative to its boundary. No extension
   theorem is used: the paragraph *The family `α` of Decision 4 is an
   input*, in the section on `HPrinciple/Relative/`, says why. On `P₀` the
   formal primitive is then zero, hence holonomic.
5. **The homotopy equivalence.** `Parametric.lean` proves that the
   inclusion of the symplectic forms in class $a$ into the nondegenerate
   forms is a `ContinuousMap.IsWeakHomotopyEquivalence`, for every open
   `M`, from the engine. To get the homotopy equivalence of the inclusion
   itself from Whitehead's theorem, `hf.homotopyEquiv` with
   `homotopyEquiv_toFun`, as the review of #3195 asked, both spaces need
   `TauCeti.CWType`. **For some open `M`, neither space has CW type.**
   - *The evidence.* Let `M` be the disjoint union of countably many copies
     of $\mathbb R^{2n}$, $n\ge1$. It is boundaryless and σ-compact, has no
     compact component, and has $H^2(M)=0$, so $a=0$. Taking the sign of
     $\omega^n$ at the origin of each copy is a continuous map $s$ from the
     nondegenerate forms onto the Cantor set $\{\pm1\}^{\mathbb N}$, since
     point evaluation is continuous. Let $\omega_0^-$ be $\omega_0$ with
     the sign of $dx_1\wedge dy_1$ reversed, so that
     $(\omega_0^-)^n=-\omega_0^n$; scaling $\omega_0$ by $-1$ would not
     do, as $(-\omega_0)^n=(-1)^n\omega_0^n$. Sending $(\varepsilon_k)$ to
     the form equal to $\omega_0$ on the $k$-th copy where
     $\varepsilon_k=1$ and to $\omega_0^-$ where $\varepsilon_k=-1$ is a
     continuous map $c$ back, since a compact set meets only finitely many
     copies. Both forms are constant, hence closed and exact on
     $\mathbb R^{2n}$, so $c$ lands in the symplectic forms of class $0$;
     and $s\circ c=\mathrm{id}$ for every $n\ge1$. If
     either space were homotopy equivalent to a CW complex $L$, there would
     be maps $u:\{\pm1\}^{\mathbb N}\to L$ and $v:L\to\{\pm1\}^{\mathbb N}$
     with $v\circ u$ homotopic to the identity, so $u$ would be injective
     on path components. But the path components of the Cantor set are
     its uncountably many points, while the compact image of $u$ lies in a
     finite subcomplex of $L$, which has finitely many path components. So
     neither space has CW type, by Milnor's theorem or by any other means.
   - *The milestone still holds for this `M`*, so this is no error of the
     plan. On each copy, $\omega\mapsto t^{-2}\,\delta_t^*\omega$ for the
     dilation $\delta_t(x)=tx$, $t\in(0,1]$, extended by the constant form
     $\omega(0)$ at $t=0$, deforms both spaces into the constant
     nondegenerate forms, compatibly with the inclusion, and continuously in
     the frame topology. Only the route through Whitehead's theorem fails.
   - *What the library proves.* The obstruction lives at infinity, so the
     library gets CW type, by domination, when `M` compresses into a
     compact set: when a `TauCeti.SmoothIsotopy` from the identity of `M`
     ends at a `j` with `IsCompact (closure (range j))`. The interior of a
     compact manifold with boundary is such an `M`, and so is
     $\mathbb R^{2n}$. Then each space `X` is dominated by a set `O`: there
     are maps `X → O → X` whose composite is homotopic to the identity.
     `O` is the set of forms that lie in a convex set `C` and are
     nondegenerate on the compact `closure (range j)`. For the
     nondegenerate forms `C` is every form; for the symplectic forms of
     class $a$ it is the forms with `tangentEquiv ω - α` exact. The maps
     are the inclusion and $\omega\mapsto j^*\omega$, and the homotopy is
     the pullback along the isotopy. An open subset of a convex subset of a
     metrizable locally convex space is dominated by the realization of the
     nerve of a partition of unity, so it has CW type. This is the argument
     behind Milnor's and Dugundji's theorems, done directly, with no
     absolute neighbourhood retracts. Last, a space dominated by a space of
     CW type has CW type, by CW approximation and the two halves of
     Whitehead's theorem.
   - *Component by component.* The homotopy equivalence is then proved
     for every open `M` each of whose connected components compresses
     into a compact set, which takes in the example above. As `M` is
     locally connected, its components are open as well as closed, so
     each is an open submanifold, Tau Ceti's `ConnectedComponents.opens`
     (`isClopen_opens`): connected, not compact, and σ-compact as a closed
     subset. Restricting to them identifies the two-forms on
     `M`, in the frame topology, with the product, over the components,
     of the two-forms on each. Restriction is continuous; conversely
     every frame domain can be shrunk into a single component, so each
     frame jet of a form on `M` is a frame jet of one of its
     restrictions. Nondegeneracy and closedness hold on `M`
     when they hold on every component, and so does exactness, since
     primitives chosen on the components glue to a primitive on `M`. So
     both spaces of forms on `M` are the products of the spaces on the
     components, for the restrictions of `α`, and the inclusion is the
     product of the inclusions. On each component the inclusion is a
     homotopy equivalence by Whitehead's theorem, as above, and Mathlib's
     `ContinuousMap.HomotopyEquiv.piCongrRight` takes the product of
     these, for any number of factors, in the product topology. If `M`
     compresses as a whole, by `h` ending at `j`, every component does:
     each slice of `h` maps a component into itself, and the closure of
     the image of a component under `j` is a closed subset of the compact
     `closure (range j)`. So this statement replaces the compressed one.
   - *The milestone's parametric statement is the weak equivalence.* The
     sources with a proof (Eliashberg–Mishachev, arXiv:math/0101196,
     Theorem 2.1.2; Bertelson, arXiv:math/0011045, Theorem 8.2) give a
     weak homotopy equivalence, and `ERRATA.md` records that the plan asks
     for more. So the milestone line goes on
     `isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`, for
     every open `M`, as well as on the existence theorem of
     `OpenManifold.lean`; the homotopy equivalence is a corollary of the
     weak one, `exists_homotopyEquiv_symplecticFormsInClass`, under the
     hypothesis above. That hypothesis holds for an `M` of finite type,
     the interior of a compact manifold with boundary, whose components
     are finitely many and each compress into a compact set along a
     collar of the boundary; the design has no lemma that derives it from
     a Morse function with finitely many critical points.
   - *Infinite type stays open.* For a connected open `M` of infinite type
     the genuine equivalence is not known, and the design does not try to
     prove it. CW type fails there too: in $\mathbb R^{2n}$, $n\ge2$, minus
     a sequence of parallel affine planes of codimension $3$, the classes
     of a form on small spheres linking the planes, in
     $\pi_2(\mathrm{GL}^+(2n)/\mathrm{Sp}(2n))\cong\mathbb Z$, give a
     retraction onto a Cantor set as in the example above. With compact
     sublevels $K_k$ of a proper Morse function, and $A_k$ the forms of
     class $a$ nondegenerate on $K_k$, the question comes down to whether
     the forms of class $a$ are homotopy equivalent, through the evident
     map, to the homotopy limit of the tower of the $A_k$; the comments on
     issue #3898 give the details.
6. **Morse input.** The existence of a proper Morse function bounded below
   without critical points of index $\dim M$ on an open manifold is
   `Geometry/Manifold/Morse/OpenManifold.lean`; the cores and their
   compressions are `Geometry/Manifold/Morse/Core/`. Both are general
   differential topology, in Tau Ceti's namespace `TauCeti` where they are
   about `TauCeti.IsMorse`; the structure `BandCore` is in
   `SymplecticGeometry`.

## Departures from `DESIGN.md`

- `Telescope.lean` is dropped (Decision 1); the milestone table and part 63
  name `OpenManifold.lean` and `Parametric.lean` for the first milestone.
- *Builds on* adds the merged *Symplectic vector bundles* (for
  `ContMDiffTwoForm`, its topology and `tangentEquiv`).
- Holonomic approximation is in coordinates (Decision 3), not on Tau Ceti's
  jet bundles.
- `Parametric.lean` proves the weak homotopy equivalence for every open
  `M`, and the homotopy equivalence only for an `M` each of whose
  components compresses into a compact set (Decision 5, `ERRATA.md`).

## Files and their contents

### `Analysis/Calculus/HolonomicApproximation/Basic.lean`

Formal sections and holonomy in coordinates, on
`D := (Fin m → ℝ) × (Fin k → ℝ)` (core directions, transverse directions,
with sup norms, so that the cube $I^m$ is
`Metric.closedBall (0 : Fin m → ℝ) 1` and no cube is defined) and a normed
space `F`:

- A formal section is a pair of smooth maps `f : D → F` and
  `G : D → D →L[ℝ] F`, holonomic on `s` when `∀ x ∈ s, fderiv ℝ f x = G x`.
  Neither gets a definition: statements carry the two maps and the
  equation.
- The one-dimensional wiggling lemma: for a segment and any $\delta>0$ there
  is a smooth diffeotopy of $D$, supported in the $\delta$-neighbourhood of
  the segment, moving points by less than $\delta$, that turns the segment
  into a curve as long in the transverse direction as wanted. This is the
  zig-zag of both sources.

### `Analysis/Calculus/HolonomicApproximation/Cube.lean`

The holonomic approximation theorem over a cube, by induction on the set of
core directions in which the datum has been made holonomic, following the
method of [EliashbergMishachev2002], Chapter 3 (zig-zags in one direction
at a time). Throughout, `D := (Fin m → ℝ) × (Fin k → ℝ)` with sup norms,
`Q := closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}` is the core cube,
and `F` is a real normed space.

**Directions and parameters.** For `J : Finset (Fin m)`, a vector `w : D`
*lies in the directions `J`* when `∀ i ∉ J, w.1 i = 0`: its core components
outside `J` vanish, its transverse part is free. The core coordinates outside
`J` play the part of parameters: the diffeotopies of a step at `J` keep them
fixed, and the approximation is only asked for derivatives in the
directions `J`. No definition is added for this: statements carry the
condition on `w`. Proofs use the projection
`P J := (ContinuousLinearMap.coordProj J).prodMap (.id ℝ _)`
of `D` onto these vectors (of norm at most `1`), as a local notation or a
`private` definition. With `J = Finset.univ` every `w` lies in the
directions `J`, and the statement is the cube theorem; with `J` a proper
subset it is the cube theorem for the cube `I^J` with the cube `I^{Jᶜ}` of
parameters, the diffeotopy being a family of diffeotopies over the
parameters.

**The inductive statement.**

```lean
theorem exists_holonomic_approximation_cube_directions {m k : ℕ} (hk : 0 < k)
    (J : Finset (Fin m)) {f : D → F} {G : D → D →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G)
    {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hJB : ∀ u ∈ closedBall (0 : Fin m → ℝ) 1, (∃ i ∈ J, |u i| = 1) → u ∈ B)
    {U : Set D} (hU : IsOpen U) (hBU : B ×ˢ {0} ⊆ U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, D) ∞ D) (f' : D → F) (V : Set D),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ Q ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      (∀ t x, ∀ i ∉ J, (h (t, x)).1 i = x.1 i) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' Q ⊆ V ∧ ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧
        ∀ w : D, (∀ i ∉ J, w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ N ∈ 𝓝ˢ B, ∀ x, x.1 ∈ N → (∀ t, h (t, x) = x) ∧ f' x = f x
```

Here `B` is a closed set of core points near which the datum is already
holonomic. It must contain the faces of the cube in the directions `J`
(`hJB`), and it may contain more: a part of the cube with interior, or the
points whose parameters lie in a closed set. The clauses are those of the
merged `exists_holonomic_approximation_segment`, with three additions: `f'`
equals `f` outside the same compact `C` as the diffeotopy, the diffeotopy
keeps the parameter coordinates, and the two relative clauses of the
segment become one clause about a neighbourhood `N` of `B` in the core:
`h` and `f'` are unchanged at every point `x` with `x.1 ∈ N`, whatever its
transverse part. The `C¹` estimate is stated vector by vector so
that it can be restricted to the directions `J`. Smoothness of `G` is
needed from `m = 2` on, since the Taylor maps of a step depend on the
parameters through `G`.

**The theorem.** `exists_holonomic_approximation_cube` is the case
`J = Finset.univ`, `B = sphere 0 1` (in the sup norm, a point of the cube
lies on the sphere exactly when one coordinate has absolute value `1`),
with `ε / 2` in place of `ε` to turn the vector estimate into
`‖fderiv ℝ f' x - G x‖ < ε`. Its statement is the inductive one with these
choices, all clauses written out:

```lean
theorem exists_holonomic_approximation_cube {m k : ℕ} (hk : 0 < k)
    {f : D → F} {G : D → D →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {U : Set D} (hU : IsOpen U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) (hU' : sphere 0 1 ×ˢ {0} ⊆ U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, D) ∞ D) (f' : D → F) (V : Set D),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ Q ∧
        (∀ t, ∀ x ∉ C, h (t, x) = x) ∧ ∀ x ∉ C, f' x = f x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      IsOpen V ∧ (fun x ↦ h (1, x)) '' Q ⊆ V ∧
      ContDiff ℝ ∞ f' ∧ (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ‖fderiv ℝ f' x - G x‖ < ε) ∧
      ∃ N ∈ 𝓝ˢ (sphere 0 1), ∀ x, x.1 ∈ N → (∀ t, h (t, x) = x) ∧ f' x = f x
```

The condition `0 < k` is the positive codimension. The relative form that
the engine needs (end of `Morse/Core/`) is the inductive statement with
`J` the core directions of the space, the parameters outside it
(`Parametric.lean`), and its larger `B`, so no subdivision of the cube is
needed for it.

**The induction**, by `Finset.induction_on` on `J`.

1. *Base case `J = ∅`* (`exists_holonomic_approximation_cube_empty`).
   Every core coordinate is a parameter, so only transverse derivatives are
   tested. Take `h := 1` and `f' := f + (λ ∘ Prod.fst) • κ' • (T - f)`,
   where `T (u, v) := f (u, 0) + G (u, 0) (0, v)` is the Taylor map in the
   transverse directions, `λ` is a smooth function of `u` that is `0` near
   `B`, `1` on the cube off a neighbourhood of `B` inside `U`, and supported
   in the `δ / 2`-neighbourhood of the cube
   (`exists_contMDiffMap_zero_one_nhds_of_isClosed`), and `κ' := κ ∘ Prod.snd` with
   `κ` a smooth bump equal to `1` for `‖v‖ ≤ ρ` and `0` for `‖v‖ ≥ 2ρ`.
   On `V := {‖v‖ < ρ}` near the cube, `κ'` is locally `1` and `λ` has no
   derivative in the tested directions, so the error is that of `T`,
   which is small for `ρ` small by uniform continuity of `G` on a compact
   neighbourhood of `Q`. The compact `C` is the product of the closed
   `δ / 2`-neighbourhood of the core cube and `closedBall 0 (2ρ)`.
2. *Step from `J'` to `insert i₀ J'`, `i₀ ∉ J'`*
   (`exists_holonomic_approximation_cube_directions_insert`, proved from the
   statement for `J'` and the lemmas of the next steps).
   - *2a. The directions `J'`.* The statement for `J'`, with the same `B`
     (it contains the faces in the directions `J'`), with `ε₁` and `δ₁ ≤
     δ / 2`, gives `h¹`, `f¹`, `V¹`, `C₁`. The datum
     `G¹ := fderiv ℝ f¹ ∘L P J' + G ∘L (1 - P J')` (pointwise in `x`) is
     smooth, holonomic in the directions `J'` everywhere, equal to `G`
     where `f¹ = f` and `(f, G)` is holonomic, and `ε₁`-close to `G` on
     `V¹`, since `‖P J'‖ ≤ 1`.
   - *2b. Straightening the displaced cube.* Let `Φ := h¹.final`. It keeps
     the coordinates outside `J'`, so `fderiv ℝ Φ x` and
     `fderiv ℝ Φ.symm y` map vectors in the directions `J'` (or `J`) to
     vectors in the same directions. The pulled-back datum
     `f² := f¹ ∘ Φ`, `G² x := G¹ (Φ x) ∘L fderiv ℝ Φ x` is smooth, and by
     the chain rule holonomic in the directions `J'` everywhere, in
     particular on the straight cube `Q`; it equals `(f, G)` near
     `B ×ˢ {0}`, where `Φ` is the identity and `f¹ = f`. This replaces the
     displaced cube `Φ '' Q` by `Q` itself, so the next step works on a
     straight cube and no graph or shear is needed: the transport is by
     the diffeomorphism the first step built.
   - *2c. The direction `i₀`.* The one-direction lemma (below) applied to
     `(f², G²)`, with `ε₂` and `δ₂`, gives `h²`, `f²'`, `V²`, `C₂`, with
     `h²` keeping every core coordinate.
   - *2d. Assembly.* The diffeotopy is
     `h := h².transDiffeomorph Φ * h¹` (Tau Ceti's conjugation
     `TauCeti.Diffeotopy.transDiffeomorph` and the product of
     `Diffeotopy/Group.lean`, `mul_apply`): first `h¹`, then `Φ h²ₜ Φ⁻¹`.
     Its final map is `Φ ∘ h².final` (`final_mul`, `final_transDiffeomorph`),
     so it sends `Q` into `Φ '' V²`. The map is `f' := f²' ∘ Φ.symm`, and
     `V := Φ '' V² ∩ V¹`. The constants: `‖fderiv ℝ Φ.symm‖ ≤ L` and `Φ`
     is `L`-Lipschitz, since `Φ - id` is smooth with compact support
     (`Diffeomorph.exists_lipschitzWith_and_norm_fderiv_symm_le`); then
     `ε₂ ≤ ε / (2 L)`, `ε₁ ≤ ε / 2`, `δ₂ ≤ δ / (2 L)`, and `δ₂` so small
     that `thickening δ₂ Q ⊆ Φ ⁻¹' V¹`
     (`IsCompact.exists_thickening_subset_open`), so that the final cube
     lies in `V¹`. Then: smallness by the triangle inequality and the
     Lipschitz bound; support in `C₁ ∪ Φ '' C₂ ⊆ thickening δ Q`; the
     coordinates outside `insert i₀ J'` are kept by `Φ` and `h²`;
     `h = id` and `f' = f` at the points over `N¹ ∩ N²`, at every height,
     since `Φ` fixes them; and for `w` in the directions `insert i₀ J'`,
     `(fderiv ℝ f' y - G¹ y) w` is
     `(fderiv ℝ f²' z - G² z) (fderiv ℝ Φ.symm y w)` with `y = Φ z`, so
     the error is at most `ε₂ L ‖w‖ + ε₁ ‖w‖`.
3. *The one-direction lemma* (`exists_holonomic_approximation_direction`,
   in `HolonomicApproximation/Direction.lean`). For a core direction `i₀`, a
   smooth `(f, G)` holonomic near `B ×ˢ {0}` as above (with the faces of
   `insert i₀ J'` in `B`) and, on `Q`, holonomic on the core vectors in the
   directions `J'` (`∀ u ∈ closedBall 0 1, ∀ v, (∀ i ∉ J', v i = 0) →
   fderiv ℝ f (u, 0) (v, 0) = G (u, 0) (v, 0)`), the
   conclusion of the inductive statement for `insert i₀ J'`, with the
   stronger clause `∀ t x, (h (t, x)).1 = x.1`. Proof:
   - the zig-zag approximation of `ZigZag.lean`, generalized from
     `Fin 1` to the direction `i₀` of `Fin m` (below), gives a height `r`,
     a profile `g₀ : ℝ → ℝ` vanishing near `± 1`, and `f₀` approximating
     `(f, G)` in the directions `insert i₀ J'` near the points
     `(u, Pi.single j (r * g₀ (u i₀)))`, `u` in the cube;
   - a smooth `ψ : (Fin m → ℝ) → [0, 1]`, `0` near `B` and `1` off a
     neighbourhood `N` of `B` with `N ×ˢ ball 0 r ⊆ U` (shrinking `r` first,
     by compactness), and a smooth `λ` on `D`, `0` over a neighbourhood of
     `B` where `ψ < 1` and off a compact neighbourhood of `Q` of height
     `2 r₀`, and `1` over the cube off a slightly larger neighbourhood of
     `B` up to the height `r₀`, which is fixed before `λ`, with `r < r₀`;
   - the diffeotopy is `exists_wiggling_diffeotopy` with the profile
     `u ↦ ψ u * g₀ (u i₀)`, over `cthickening (δ / 2) Q`: where `ψ = 1`
     it moves the cube onto the zig-zag, and near `B` it is the identity;
   - `f' := f + λ • (f₀ - f)`. Where `λ` varies, both `f₀`
     and `f` are good approximations and the gluing costs
     `‖fderiv λ‖ ‖f₀ - f‖`, so the accuracy asked of `f₀` is chosen after
     `λ`; where `λ = 0` and the cube is displaced by less than `r`, the
     point lies in `U` and `f' = f` is exact.
4. *The zig-zag in one direction of a cube.* `exists_holonomic_approximation_zigzag`
   is generalized in place from `D = (Fin 1 → ℝ) × (Fin k → ℝ)` to
   `D = (Fin m → ℝ) × (Fin k → ℝ)` and a direction `i₀`. The Taylor maps
   are taken at the points `(Function.update u i₀ (c l), 0)` of the cube,
   `S l x := f (pₗ x) + G (pₗ x) (x - pₗ x)` with
   `pₗ x := (Function.update x.1 i₀ (c l), 0)`. Their derivative in a
   direction `w` of `insert i₀ J'` is `G (pₗ x) w` up to the holonomy defect
   of `(f, G)` in the directions `J'` at `pₗ x`, which the hypothesis makes
   `0` on the cube, so that it is small near the cube, and a term bounded by
   `‖fderiv ℝ G‖ ‖x - pₗ x‖`, small with `r` and the mesh. The chain is
   `exists_zigzag_chain`, which already takes `m` and `i₀`, with `S 0 = S (n + 1) = f` near the faces `|u i₀| = 1`. The
   estimates `zigzag_section_estimate`, `zigzag_neighbour_estimate` and
   `zigzag_curve_estimate` become uniform over the other coordinates by
   compactness of the cube. Besides `Continuous G`, the hypothesis on `G` is
   that each `u ↦ G (Function.update u i₀ c, 0)` is smooth and that
   `(u, c) ↦ fderiv ℝ (fun u ↦ G (Function.update u i₀ c, 0)) u` is
   continuous, which bounds that derivative uniformly on the cube; for
   `m = 1` both hold with `G` merely continuous, since the map is constant,
   so `exists_holonomic_approximation_segment` keeps `Continuous G`. The
   holonomy in the directions `J'` is asked on the core vectors only, at
   the points of `Q`.
5. *Coordinates kept by the transverse push.* `exists_wiggling_diffeotopy`
   gains the clause `∀ t x, (h (t, x)).1 = x.1`, from a new clause of
   `exists_diffeotopy_apply_eq_add_smul` (`Diffeotopy/Translate.lean`):
   `∀ t x, h (t, x) - x ∈ ℝ ∙ e`. The field is a multiple of `e`
   everywhere, so its flow lines stay on lines `x + ℝ • e`: the quotient map
   `E → E ⧸ ℝ ∙ e` kills the field, so it is constant along integral
   curves.

**The segment.** `exists_holonomic_approximation_segment` is neither the
base case nor reproved: it stays as it is, with its proof using the
generalized zig-zag lemma at `m = 1`. The inductive base is `J = ∅`, which
costs only the transverse Taylor map, so the step from `∅` to a single
direction is the case `m = 1` with parameters.

**Parameters.** The inductive statement keeps coordinate parameters, the
core coordinates outside `J`, with the cube `[-1, 1]` as range and the
closed set `B` for the relative clause. This is what the induction needs,
and it gives directly the smooth version of `Parametric.lean` for a
parameter set in a Euclidean space: put the parameters among the core
coordinates outside `J`, rescale a compact parameter set into the cube, and
put the parameters already holonomic into `B`. A diffeotopy of `D` keeping
these coordinates is a family of diffeotopies smooth in the parameter. A
general compact parameter space, or a parameter manifold `L` that is not an
open subset of a Euclidean space, is not needed: neither the induction nor,
as the `Parametric.lean` section explains, any use of the theorem asks for
one.

**Building issues of issue 2**, in this order:

- 2a. *The push keeps the other coordinates* (step 5): `Translate.lean`
  and `Basic.lean`. Blocked by nothing.
- 2b. *The zig-zag in one direction of a cube* (step 4): `ZigZag.lean`,
  and the proof of `Segment.lean`. Blocked by nothing.
- 2c. *The one-direction lemma* (step 3): `Direction.lean`. Blocked by 2a
  and 2b.
- 2d. *Transport along a diffeomorphism* (steps 2b and 2d without the
  induction): the pulled-back datum, its holonomy in the directions kept
  by the diffeomorphism, the transported estimate and the clauses of the
  composite diffeotopy, in `HolonomicApproximation/Transport.lean`.
  Blocked by nothing.
- 2e. *The induction and the theorem*: the base case, the step, the
  inductive statement and `exists_holonomic_approximation_cube` in
  `Cube.lean`. Blocked by 2c and 2d.

### `Analysis/Calculus/HolonomicApproximation/Parametric.lean`

[EliashbergMishachev2002], Theorem 4.7.4, in coordinates, in two forms with
one proof: for smooth families over a finite-dimensional normed space, and
for families over a compact Hausdorff space that are only continuous in the
parameter. Throughout, `D := (Fin m → ℝ) × (Fin k → ℝ)` with sup norms and
`Q := closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)}`, as in `Cube.lean`.

**Parameter manifolds are not needed.** The uses are the handle-core lemma,
whose parameters lie in a finite-dimensional normed space `L` already, and
the engine, whose smooth version is used only over a point and over
`unitInterval`. A smooth family over `unitInterval` extends to a smooth
family over `ℝ` by the time extension of
`Geometry/Manifold/DifferentialForm/TimeExtension.lean`, and asking for the
conclusions only on the compact `[0, 1]` makes the values off it irrelevant.
So the smooth version takes parameters in a finite-dimensional normed space
with a compact `K` where the approximation is asked for, and the engine's
smooth version is stated the same way (its section).

**The relative clauses at every transverse height.** Both uses need `h` and
`f'` unchanged over a whole neighbourhood of `B` in the core, at every
transverse point, and not only near `B ×ˢ {0}`. In the handle-core lemma,
the region where the datum is holonomic is a slab of the cube, of every
transverse height; in the engine, it is a neighbourhood of a sublevel set,
which also meets the cube charts at every height. Points moved by the
merged theorem lie within `δ` of `Q`, but `δ` is chosen before the
neighbourhood of `B ×ˢ {0}` on which they are fixed, so nothing bounds the
moved points away from `B` at small nonzero heights. The merged proofs give
more: the cutoff of the base case (`λ ∘ Prod.fst`) and those of the one-direction
lemma (the profile `ψ` and the gluing cutoff `χ`, zero over a neighbourhood
of `B` times `univ`) all vanish on a set `N ×ˢ univ` with `N` a neighbourhood
of `B`, and in the step the final map `Φ` of the first diffeotopy fixes every
point of such a set, hence maps it onto itself, so the conjugated diffeotopy
and `f²' ∘ Φ.symm` keep that property on the intersection of the two sets.
So building issue 3a replaces, in `exists_holonomic_approximation_direction`,
`exists_holonomic_approximation_cube_empty`,
`exists_holonomic_approximation_cube_directions_insert`,
`exists_holonomic_approximation_cube_directions` and
`exists_holonomic_approximation_cube`, the two clauses
`∃ W ∈ 𝓝ˢ (B ×ˢ {0}), ∀ t, ∀ x ∈ W, h (t, x) = x` and
`∃ U' ∈ 𝓝ˢ (B ×ˢ {0}), EqOn f' f U'` by the single clause

```lean
∃ N ∈ 𝓝ˢ B, ∀ x, x.1 ∈ N → (∀ t, h (t, x) = x) ∧ f' x = f x
```

(with `sphere 0 1` for `B` in the last), and corrects the statements of the
`Cube.lean` section in the same pull request. With it, a point that some
`h t` moves, or where `f' ≠ f`, has its core coordinate outside `N` and lies
within `δ` of `Q`; this is the support that subdividing the cube was meant to
give, so no subdivision is needed.

**The smooth version.**

```lean
theorem exists_holonomic_approximation_family {L : Type*} [NormedAddCommGroup L]
    [NormedSpace ℝ L] [FiniteDimensional ℝ L] (hk : 0 < k)
    {f : L × D → F} {G : L × D → D →L[ℝ] F} (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G)
    {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {B : Set (Fin m → ℝ)} (hB : IsClosed B) (hSB : sphere 0 1 ⊆ B)
    {U : Set (L × D)} (hU : IsOpen U) (hBU : univ ×ˢ (B ×ˢ {0}) ⊆ U)
    (hP₀U : P₀ ×ˢ univ ⊆ U) (hUf : ∀ p ∈ U, fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, L × D) ∞ (L × D)) (f' : L × D → F) (V : Set (L × D)),
      (∀ t p, (h (t, p)).1 = p.1) ∧ ContDiff ℝ ∞ f' ∧
      (∃ C, IsCompact C ∧ (∀ p ∈ C, p.2 ∈ thickening δ Q) ∧
        ∀ p ∉ C, (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      (∀ t p, dist (h (t, p)) p < δ) ∧
      (∃ N ∈ 𝓝ˢ B, ∀ p : L × D, p.2.1 ∈ N → (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      (∀ p : L × D, p.1 ∈ P₀ → (∀ t, h (t, p) = p) ∧ f' p = f p) ∧
      IsOpen V ∧ (∀ l ∈ K, ∀ y ∈ Q, h (1, (l, y)) ∈ V) ∧
      ∀ p ∈ V, ‖f' p - f p‖ < ε ∧ ‖fderiv ℝ (fun x ↦ f' (p.1, x)) p.2 - G p‖ < ε
```

A diffeotopy of `L × D` that keeps the `L` coordinate is a family of
diffeotopies of `D`, smooth in `(l, t, x)`; `G` is the space part of the
datum only. The datum is holonomic near `B ×ˢ {0}` for every parameter and
everywhere for the parameters in `P₀`; the approximation is asked only for
the parameters in `K`, and nothing moves for parameters far from `K`. A use
whose datum is holonomic near `B` only for `l ∈ K` first makes it holonomic
there for every `l` by a cutoff in space, as the handle-core lemma does
below.

Proof, from the strengthened `exists_holonomic_approximation_cube_directions`:

1. *Coordinates.* With `p := Module.finrank ℝ L`, a continuous linear
   equivalence `e : L ≃L[ℝ] (Fin p → ℝ)`
   (`(Module.finBasis ℝ L).equivFun.toContinuousLinearEquiv`) and `R > 0`
   with `‖e l‖ < R` on `K` (`exists_pos_norm_finBasis_equivFun_lt`). Let
   `Ψ : L × D ≃L[ℝ] D'` (`familyCubeEquiv`),
   `D' := (Fin (p + m) → ℝ) × (Fin k → ℝ)`, send
   `(l, (u, v))` to `(A (R⁻¹ • e l, u), v)`, where
   `A : (Fin p → ℝ) × (Fin m → ℝ) ≃L[ℝ] (Fin (p + m) → ℝ)` is Tau Ceti's
   `(TauCeti.splitCoords p m).symm`, `Fin.append` on the two blocks, and is
   an isometry for the sup norms (`Fin.appendIsometry`). The
   core directions of the space are `J := Finset.univ.map (Fin.natAddEmb p)`;
   the parameters are the core coordinates outside `J`, and `Ψ` sends
   `K ×ˢ Q` into the cube `Q'` of `D'`. On the vectors `(0, w)` it is an
   isometry onto the vectors in the directions `J`.
2. *The parameter component of `G`.* On `L × D`, put
   `Ĝ p := fderiv ℝ (fun l' ↦ f (l', p.2)) p.1 ∘L ContinuousLinearMap.fst ℝ L D
   + G p ∘L ContinuousLinearMap.snd ℝ L D`, smooth by `ContDiff.fderiv`; the
   datum on `D'` is `f ∘ Ψ.symm` with `q ↦ Ĝ (Ψ.symm q) ∘L Ψ.symm`. By the
   chain rule along `hasFDerivAt_prodMk_left` and `hasFDerivAt_prodMk_right`,
   `fderiv ℝ f p` is the sum of the two partial derivatives, so this datum is
   holonomic at `Ψ p` exactly when `fderiv ℝ (fun x ↦ f (p.1, x)) p.2 = G p`,
   in particular on `Ψ '' U`. This is the definition by the parameter
   derivative of `f` that putting holonomic parameters into `B` needs.
3. *The relative set.* `B' := A '' (univ ×ˢ B ∪ (R⁻¹ • e '' P₀) ×ˢ univ)`,
   closed. It contains the faces of the cube of `D'` in the directions `J`,
   since `sphere 0 1 ⊆ B` and the sup norm of `A (s, u)` bounds `‖u‖`, and
   `B' ×ˢ {0} ⊆ Ψ '' U` by `hBU` and `hP₀U`.
4. *Approximation.* `exists_holonomic_approximation_cube_directions` with
   `J`, `B'`, `ε / 2` and `min δ 1` gives `h''`, `f''`, `V''`, `C''` and
   `N''`.
5. *Back to `L × D`.* `h := TauCeti.Diffeotopy.ofContMDiff ψ hψ h₀`
   (`Diffeotopy/OfContMDiff.lean`) for the conjugated slices
   `ψ t := Ψ.toDiffeomorph.trans ((h''.timeSlice t).trans Ψ.symm.toDiffeomorph)`
   (`ContinuousLinearEquiv.toDiffeomorph`). Tau Ceti's `transDiffeomorph`
   does not apply here, since it keeps the model and `Ψ` changes it. `hψ`
   is `Ψ.symm.toDiffeomorph.contMDiff` composed with `h''.contMDiff` and
   `Ψ` on the space factor, and `h₀` is `apply_zero`. Further,
   `f' := f'' ∘ Ψ`, `V := Ψ ⁻¹' V''` and `C := Ψ.symm '' C''`. The `L`
   coordinate is kept because `h''` keeps the coordinates outside `J`;
   displacements and the distance to `Q` are measured in the space part,
   where `Ψ` is isometric and the projection is `1`-Lipschitz; and for a
   space vector `w`, `(fderiv ℝ (fun x ↦ f' (l, x)) x - G (l, x)) w` is
   `(fderiv ℝ f'' q - G'' q) (Ψ (0, w))` at `q = Ψ (l, x)`, so it is at most
   `ε / 2 * ‖w‖`.
6. *The neighbourhood `N`.* By `generalized_tube_lemma` for the compact
   `closedBall 0 2 ×ˢ (B ∩ closedBall 0 2)` inside the open interior of
   `A ⁻¹' N''`, there is `N₁ ∈ 𝓝ˢ (B ∩ closedBall 0 2)` with
   `closedBall 0 2 ×ˢ N₁ ⊆ A ⁻¹' N''`. Take
   `N := N₁ ∪ (closedBall 0 (1 + min δ 1))ᶜ`: a point over it is either over
   `N''` or farther than `min δ 1` from `Q'`, hence outside `C''`. The
   clause for `P₀` holds because `B'` contains every core point over a
   parameter of `P₀`.

**The continuous version.**

```lean
theorem exists_holonomic_approximation_continuous_family {P : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P] (hk : 0 < k) {f : P → D → F} {G : P → D → D →L[ℝ] F}
    (hf : ∀ l, ContDiff ℝ ∞ (f l)) (hG : ∀ l, ContDiff ℝ ∞ (G l))
    (hdf : Continuous fun p : P × D ↦ fderiv ℝ (f p.1) p.2)
    (hcG : Continuous fun p : P × D ↦ G p.1 p.2)
    {P₀ : Set P} (hP₀ : IsClosed P₀) {B : Set (Fin m → ℝ)} (hB : IsClosed B)
    (hSB : sphere 0 1 ⊆ B) {U : Set (P × D)} (hU : IsOpen U)
    (hBU : univ ×ˢ (B ×ˢ {0}) ⊆ U) (hP₀U : P₀ ×ˢ univ ⊆ U)
    (hUf : ∀ p ∈ U, fderiv ℝ (f p.1) p.2 = G p.1 p.2) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (n : ℕ) (σ : P → Fin n → ℝ)
      (h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin n → ℝ) × D) ∞ ((Fin n → ℝ) × D))
      (g : (Fin n → ℝ) × D → F) (V : Set (P × D)),
      Continuous σ ∧ (∀ t q, (h (t, q)).1 = q.1) ∧ ContDiff ℝ ∞ g ∧
      (∃ C, IsCompact C ∧ (∀ q ∈ C, q.2 ∈ thickening δ Q) ∧ ∀ q ∉ C,
        (∀ t, h (t, q) = q) ∧ g q = 0) ∧
      (∀ t q, dist (h (t, q)).2 q.2 < δ) ∧
      (∃ N ∈ 𝓝ˢ B, ∀ q : (Fin n → ℝ) × D, q.2.1 ∈ N →
        (∀ t, h (t, q) = q) ∧ g q = 0) ∧
      (∀ l ∈ P₀, ∀ x, (∀ t, h (t, (σ l, x)) = (σ l, x)) ∧ g (σ l, x) = 0) ∧
      IsOpen V ∧ (∀ l, ∀ y ∈ Q, (l, (h (1, (σ l, y))).2) ∈ V) ∧
      ∀ p ∈ V, ‖g (σ p.1, p.2)‖ < ε ∧
        ‖fderiv ℝ (fun x ↦ f p.1 x + g (σ p.1, x)) p.2 - G p.1 p.2‖ < ε
```

The approximation at `l` is `f l + g (σ l, ·)` and its diffeotopy is the
slice of `h` at `σ l`. The conclusion is stated through the continuous map
`σ` into a finite-dimensional space and the smooth `g` and `h` on it, so it
asks for no new definition: every continuity in `l` that a use needs, such
as that of all space derivatives for the frame topology of the engine,
follows from continuity of `σ`, smoothness of `g` and `h`, and that of `f`.
The hypotheses ask for continuity of the first derivatives only, which is
all the proof uses. The clauses for `C`, the displacement and `N` hold at
every point of `(Fin n → ℝ) × D`, not only over the range of `σ`: the
engine carries `h` and `g` to `M` along a chart, as smooth families over
all of `Fin n → ℝ`, which needs their supports controlled at every point.

Proof, from the smooth version, by a partition of unity on `P`:

1. *Uniform control on a compact set.* Let `K_D := closedBall 0 2` and
   `e l x := G l x - fderiv ℝ (f l) x`, jointly continuous. As `P` is compact,
   the projection to `D` is closed (`isClosedMap_snd_of_compactSpace`), so there is an open
   `O ⊆ D` with `B ×ˢ {0} ⊆ O` and `univ ×ˢ O ⊆ U`, so every `e l` vanishes
   on `O`; and for the compact `K_D`, an open `O₀ ⊇ P₀` with
   `‖e l x‖ < ε / 4` for `l ∈ O₀`, `x ∈ K_D`, since `e` vanishes on
   `P₀ ×ˢ univ`.
2. *A fine partition of unity.* Curry `e`, restricted to `P × K_D`, into
   `Φ : C(P, C(K_D, D →L[ℝ] F))` (`ContinuousMap.curry`). Tau Ceti's
   `ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le` gives finitely
   many points `l i`, `i : Fin n'`, and a partition of unity `ρ` indexed by
   them with `‖∑ i, ρ i l • e (l i) x - e l x‖ ≤ ε / 8` for every `l` and
   `x ∈ K_D` (`ContinuousMap.dist_apply_le_dist`).
3. *The extra coordinate.* A continuous `τ : P → [0, 1]`, `0` on `P₀` and
   `1` off `O₀` (`exists_continuous_zero_one_of_isClosed`), and a smooth
   `χ : ℝ → [0, 1]`, `0` on `(-∞, 1/2]` and `1` on `[1, ∞)` (from
   `Real.smoothTransition`).
4. *The finite-dimensional datum.* With `n := n' + 1`,
   `σ l := Fin.cons (τ l) (fun i ↦ ρ i l)`, and for `s : Fin n → ℝ`,
   `F (s, x) := ∑ i, s i.succ • f (l i) x` and
   `G' (s, x) := ∑ i, s i.succ • (fderiv ℝ (f (l i)) x + χ (s 0) • e (l i) x)`:
   smooth, and holonomic on the open set where `s 0 < 1/2` or
   `x ∈ O`. Apply the smooth version with `L := Fin n → ℝ`,
   `K := closedBall 0 1` (it contains the range of `σ`),
   `P₀' := {s | s 0 ≤ 1/4}`, `B`, `ε / 2` and `min δ 1`; it
   gives `h`, `f''` and `V''`. Put `g := f'' - F`, and
   `V := {p | (σ p.1, p.2) ∈ V''} ∩ univ ×ˢ ball 0 2`, open as `σ` is
   continuous; it contains the images of `Q`, since they lie within `1` of
   `Q`. The clauses for `C`, the displacement and `N`, at every point of
   `(Fin n → ℝ) × D`, and for `P₀` (where `σ l ∈ P₀'`) are those of the
   smooth version.
5. *The estimate.* At `p = (l, x) ∈ V`, with `c := χ (τ l)`, the error
   `fderiv ℝ (fun x ↦ f l x + g (σ l, x)) x - G l x` is
   `(fderiv ℝ (fun y ↦ f'' (σ l, y)) x - G' (σ l, x))
   + c • (∑ i, ρ i l • e (l i) x - e l x) - (1 - c) • e l x`. The first term
   is less than `ε / 2`; the second at most `ε / 8`, by step 2;
   the third at most `ε / 4`, since `c < 1` only where
   `τ l < 1`, that is on `O₀`.

**The uses.**

- *The handle-core lemma* (step 4 of `HandleCore.lean`) uses the smooth
  version with its `L` and `K`, `P₀ := ∅`, and
  `B := {u | 1 - 2ε₀ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 + η}`, where `η > 0` is such that
  `B ×ˢ {0} ⊆ W`: the part of norm at most `1` lies in the slab of step 1,
  the rest near the compact `A` (`IsCompact.exists_thickening_subset_open`).
  It replaces `G` by `G̃ l x := G l x - χ x • J (τ l x - dβ l x)`, with `J`
  the right inverse of its step 3 and a smooth
  cutoff `χ` on `D`, `1` near `B ×ˢ {0}` and supported in `W`
  (`exists_contDiff_fderiv_eq_of_fderiv_eq_on_prod`): this datum is holonomic
  near `B ×ˢ {0}` for every `l`, and equals `G` for `l ∈ K`, since there
  `τ l = dβ l` on `W`. With `δ < min ε₀ η`, the families of step 4 are
  `H l s x := (h (s, (l, x))).2` and `β' := f'`, and every point moved, or
  where `β' l ≠ β l`, has `‖u‖ < 1 - 2ε₀` and `‖v‖ < δ`: its core
  coordinate is off `N ⊇ B`, and it lies within `δ < η` of the core cube.
- *The engine* (`HPrinciple/Relative/CoreApproximation.lean`) uses, over
  each cube of a band core in its chart, the continuous version for its
  continuous form and the smooth version for its smooth form, with the
  parameters of the engine and its `P₀`, after a cutoff in the parameter
  near `P₀`; `B` is the closed set of core points of
  `BandCore.exists_relativeSet`, containing the sphere, chosen with a
  margin so that, for `δ` small (fixed before the theorem is applied), no
  point within `δ` of the cube over a core point outside `B` lies in
  $\{g\le e_k\}$. The clause for `N` then keeps $\beta^k_l$ unchanged near
  $\{g\le e_k\}$ at every transverse height, and the clause for `P₀` keeps
  the parameters of `P₀` unchanged. The engine's datum is holonomic near
  `B ×ˢ {0}` for every parameter, so it needs no cutoff in space.

**Building issues of issue 3**, in this order:

- 3a. *The relative clauses at every transverse height*: the single clause
  above in `exists_holonomic_approximation_direction` (`Direction.lean`)
  and in the four theorems of `Cube.lean` that carry it, with the
  statements of the `Cube.lean` section. Blocked by nothing.
- 3b. *Smooth families*: `exists_holonomic_approximation_family`, steps 1 to
  6, in `Parametric.lean`. Blocked by 3a.
- 3c. *Continuous families*: `exists_holonomic_approximation_continuous_family`,
  steps 1 to 5, in `Parametric.lean`; this is issue 3 itself. Blocked by 3b.

### `Geometry/Manifold/Morse/OpenManifold.lean`

```lean
theorem TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt
    (hE : Module.finrank ℝ E ≠ 1) (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsMorse I g ∧ IsProperMap g ∧ BddBelow (Set.range g) ∧
      ∀ x ∈ criticalPoints I g, manifoldMorseIndex I g x < Module.finrank ℝ E
```

**Why the modification near the rays must create critical points.** A
function that differs from a proper Morse function `f` only near the rays
from its maxima, is proper, and has no critical point near the rays does
not exist in general. On $\mathbb R^2$ take `f` proper with exactly three
critical points, a minimum, a saddle and a maximum. A proper function with
finitely many critical points, all nondegenerate, has
$\sum_x(-1)^{\operatorname{ind}x}=\chi(\mathbb R^2)=1$, since the sublevel
above the last critical value is a deformation retract of the plane; the
minimum and the saddle alone give $0$. So the modified function has new
critical points near the ray. The route below allows them, and makes sure
that none has index $\dim M$: at each of them the Hessian takes a positive
value on some vector. A small perturbation then makes the function Morse
with all these indices below $\dim M$.

**Dimension.** In dimension one disjoint rays cannot avoid the other
critical points (a ray from a maximum on a line meets a minimum), and the
argument for that case would need the classification of noncompact
connected one-manifolds, which neither library has. The part does not need
it: the engine works in dimension $2n$, where $M$ is empty or of even
dimension (a nondegenerate two-form at a point gives
`TauCeti.SymplecticForm.even_finrank`). Hence the hypothesis `hE`. In
dimension zero `hM` makes `M` empty, and any `g` does.

Proof, in dimension at least two:

1. Take `g₀` from `exists_isMorse_isProperMap_bddBelow`. Its critical
   points form a closed discrete set
   (`IsMorse.finite_criticalPoints_inter`); let `P` be those of index $\dim M$, the strict local
   maxima (`eventually_lt_of_manifoldMorseIndex_eq_finrank`), and `Q` the
   others.
2. Rays from `P` avoiding `Q` (`ProperRay.lean`), and open neighbourhoods
   `O p` of the rays, pairwise disjoint and missing `Q`, for instance
   $\{x : d(x,R_p) < d(x,R'_p)/2\}$ for a metric `d`, with $R_p$ the ray and
   $R'_p$ the closed union of `Q` and the other rays.
3. A tube `Φ p` around each ray inside `O p` (`TubularNeighborhood/Ray.lean`),
   with the sets `Φ p '' (Ici (-2) ×ˢ closedBall 0 2)` closed and locally
   finite: take the prescribed neighbourhood `O'` of `γ p '' Ici (-2)`
   disjoint from the compact `K j` of an exhaustion for every `j` such that
   `γ p '' Ici (-2)` misses `K (j + 1)`.
4. `g₁ := g₀ + ∑ p, μ p ∘ (Φ p)⁻¹`, each term extended by zero, with `μ p`
   from `HalfCylinder.lean` applied to `g₀ ∘ Φ p`. The sum is locally
   finite, so `g₁` is smooth; `g₁ ≥ g₀`, so `g₁` is proper and bounded
   below. On `A := ⋃ p, Φ p '' (Ici (-2) ×ˢ closedBall 0 2)` every critical
   point of `g₁` has a vector on which `criticalHessian I g₁` is positive
   (at a critical point the Hessian of the chart `(Φ p)⁻¹` and of the
   preferred chart are congruent,
   `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`). Off the interior
   of `A`, `g₁ = g₀` near each point.
5. Let `c` be the control of `PositiveDirection.lean` for `g₁` and `A`, and
   `C := (⋃ p, Φ p '' (Ioi (-2) ×ˢ ball 0 2))ᶜ`, closed, on which `g₁` is
   Morse since it is `g₀` there. `ContMDiffMap.exists_isMorse_isProperMap_mem_ball`
   gives `g ∈ c.ball g₁`, Morse, proper, within `1` of `g₁` (so bounded
   below) and equal to `g₁` near `C`. A critical point of `g` in `A` has
   index below $\dim M$ by the choice of `c` and
   `manifoldMorseIndex_eq_finrank_iff`; one outside `A` lies in `C`, where
   `g = g₀` near it, so it is a point of `Q`.

#### `Geometry/Manifold/ProperRay.lean`

Rays from a closed discrete set, in the namespace `SymplecticGeometry`:

```lean
theorem exists_rays (hE : 2 ≤ Module.finrank ℝ E)
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x))
    {P Q : Set M} (hP : IsClosed P) [DiscreteTopology P] (hQ : IsClosed Q)
    [DiscreteTopology Q] (hPQ : Disjoint P Q) :
    ∃ γ : P → TauCeti.SmoothEmbedding 𝓘(ℝ) I ∞ ℝ M,
      (∀ p, γ p 0 = p) ∧ (∀ p, Filter.Tendsto (γ p) Filter.atTop (Filter.cocompact M)) ∧
      LocallyFinite (fun p ↦ γ p '' Set.Ici (-2)) ∧
      Pairwise (Disjoint on fun p ↦ Set.range (γ p)) ∧ ∀ p, Disjoint (Set.range (γ p)) Q
```

Only the half `t ≥ 0` goes to infinity; for `t ≤ 0` the ray is a short
straight segment through `p` in a chart, so that it is an embedding of all
of `ℝ`, which the tubular neighbourhood theorem needs.

Route. Fix a proper smooth `h : M → ℝ` that is bounded below, so that
each `{h ≤ c}` is compact (Tau Ceti's `Geometry/Manifold/Exhaustion.lean`
gives a nonnegative one). For a level `c` let `F c` be
`{h ≤ c}` together with the components of `{h > c}` whose closure is
compact. `F c` is compact, every component of `M \ F c` is noncompact, and
`F c ⊆ F c'` for `c ≤ c'` (a component of `M \ F c'` is connected and
noncompact, so it lies in a noncompact component of `{h > c}`). The sets
`K j := F (c j)` are chosen during the construction, with `c (j + 1)` in
`(c j + 1, c j + 2)`, so `K j ⊆ interior (K (j + 1))` and the `K j` exhaust
`M`.

Each ray is grown one arc per stage, and the construction keeps this
invariant, which fixes the problem of arcs that leave a component of
`M \ K i` and come back:

* (R) for every `i`, the part of a ray (as built so far) outside `K i` is
  empty or one connected piece containing its current endpoint.

Stage `j` starts with `K j` known. Its rays are those started before, whose
endpoints lie outside `K j`, and a new one for each `p ∈ P` outside `K j`,
not yet used, in `F (c j + 2)`, beginning with a short straight segment
through `p` outside `K j`. The arcs of the stage are built one after
another. For a ray with endpoint `x`, let `W` be the component of
`M \ K j` containing `x`, and `U` the open set left from `W` by removing
`P ∪ Q`, the closures of all rays as built so far and a small closed ball
around `x`. Take a short straight segment `σ` from `x` inside one chart `φ`
at `x`, continuing the ray, and the final diffeomorphism `Ψ` of a
compactly supported diffeotopy inside `U` that sends the far end of `σ` to
a point of `U` outside `F (c j + 2 + ε)`, for a small `ε > 0`
(`TauCeti.exists_diffeotopy_final_comp_eq_of_isPreconnected`). The arc
`α := Ψ '' σ` is straight in the chart `φ ∘ Ψ⁻¹` along its whole length,
and joins the ray smoothly at `x`.

When the stage's arcs are built, choose `c (j + 1)` in
`(c j + 1 + ε, c j + 2)` that is a regular value of `h` and of `h ∘ α` for each
arc `α` of the stage (Sard for `h`, and for the finitely many functions
`h ∘ α` of one variable `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).
Then each `α` meets `{h = c (j + 1)}` at finitely many parameters, crossing
it, so the parameters where `α` lies outside `K (j + 1)` form finitely many
intervals, the last one ending at the far end, which lies outside
`F (c j + 2 + ε) ⊇ K (j + 1)`. Cut `α` at a parameter just after the start of
the first such interval (at once, for a new ray that starts outside
`K (j + 1)`), close enough that the cut arc stays in
`interior (F (c j + 2 + ε))`. The cut end is still straight in `φ ∘ Ψ⁻¹`, so
the next arc continues it smoothly.

Why (R) holds after the stage: an arc of stage `j` lies outside `K j`,
leaves `K (j + 1)` only in its final piece, and lies in
`interior (K (j + 2))`, since `F (c j + 2 + ε) ⊆ interior (K (j + 2))`. So
outside `K i` a ray consists of its arcs of stages `≥ i`, which lie outside
`K i`, and the final piece of its arc of stage `i - 1`; arcs of stages
`≤ i - 2` lie inside `K i`.

Why `U` is connected and leaves `F (c j + 2)`: by (R) for `K j`, each ray
meets `W` in a single closed arc of `W` that ends at the ray's endpoint and
either is compact or runs out of `W` at its other end, and the ray of `x`
together with the ball is such a set with the boundary sphere as its free
end. In dimension at least two, removing finitely many disjoint such sets
and a closed discrete set from a connected manifold leaves it connected: a
path that crosses one of the arcs is rerouted around the free end, inside a
thin neighbourhood of the compact part of the arc between the crossing and
that end, which misses the other removed sets; points of `P ∪ Q` are
avoided as in
`TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`.
This is where `hE` is used. `U` leaves `F (c j + 2)`, since `W` has
noncompact closure and the removed sets have empty interior. Without (R)
this fails in dimension two: an arc of an earlier stage that leaves `W` and
returns cuts off a bounded part of `W`.

Every arc of stage `j` lies outside `K j`, and each stage adds finitely many
arcs, which gives local finiteness and the limit at infinity.

#### `Geometry/Manifold/VectorBundle/Real.lean`

A smooth vector bundle over `ℝ` is smoothly trivial: for
`[ContMDiffVectorBundle ∞ F T 𝓘(ℝ)]` with fibre `F` finite-dimensional,
`Bundle.exists_diffeomorph_prod_of_real` gives a diffeomorphism
`TotalSpace F T ≃ₘ^∞⟮𝓘(ℝ).prod 𝓘(ℝ, F), 𝓘(ℝ).prod 𝓘(ℝ, F)⟯ ℝ × F` over `ℝ`,
linear on each fibre. Tau Ceti has only the continuous statement over
contractible bases (`Topology/VectorBundle/Contractible.lean`). Route: a
global smooth frame, built from the frames of the bundle's trivializations.
Two frames glue along a smooth map into their overlap that is the identity
on one side (`IsLocalFrameOn.exists_isLocalFrameOn_union`, in
`VectorBundle/LocalFrame.lean`). Over `ℝ` this joins frames on overlapping
open intervals, and a supremum argument extends a frame on an open interval
as far as wanted to the right or the left, unchanged away from the end it
moves (`IsLocalFrameOn.exists_isLocalFrameOn_Ioo_extend_right`, `_left`).
That gives frames on `Ioo (-(k + 2)) (k + 2)`, each agreeing with the one
before on `Ioo (-(k + 1)) (k + 1)`, whose limit
(`IsLocalFrameOn.exists_isLocalFrameOn_iUnion`, in `LocalFrame.lean`) is a
global frame (`Bundle.exists_isLocalFrameOn_univ_of_real`). A global frame
of any smooth vector bundle gives the diffeomorphism with the product
(`Bundle.exists_diffeomorph_prod_of_isLocalFrameOn_univ`, in
`LocalFrame.lean`).

#### `Geometry/Manifold/TubularNeighborhood/Ray.lean`

The tube around a ray, for a fibre `V` with `Module.finrank ℝ V + 1 = Module.finrank ℝ E`, such as
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))`:

```lean
theorem TauCeti.SmoothEmbedding.exists_rayTube (γ : SmoothEmbedding 𝓘(ℝ) I ∞ ℝ M)
    (hV : Module.finrank ℝ V + 1 = Module.finrank ℝ E)
    (hγ : Filter.Tendsto γ Filter.atTop (Filter.cocompact M))
    {O O' : Set M} (hO : IsOpen O) (hγO : Set.range γ ⊆ O)
    (hO' : IsOpen O') (hγO' : γ '' Set.Ici (-2) ⊆ O') :
    ∃ Φ : SmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ, V)) I ∞ (ℝ × V) M,
      IsOpen (Set.range Φ) ∧ Set.range Φ ⊆ O ∧ (∀ t, Φ (t, 0) = γ t) ∧
      IsClosed (Φ '' (Set.Ici (-2) ×ˢ Metric.closedBall 0 2)) ∧
      Φ '' (Set.Ici (-2) ×ˢ Metric.closedBall 0 2) ⊆ O'
```

Route: Tau Ceti's `SmoothEmbedding.exists_diffeomorph_normalBundle_subset`
(`TubularNeighborhood/Existence.lean`) inside `O` identifies the total
space of the normal bundle with an open neighbourhood of the ray, and
`Bundle.exists_diffeomorph_prod_of_real` identifies that total space with
`ℝ × V`. Then `(t, y) ↦ (t, r t • y)` for a smooth `r > 0` that decreases
fast enough, by properness of `γ` on `Ici (-2)`, makes the stated set closed
and puts it inside `O'`. Over `t < -2` the tube need not be closed or lie in
`O'`.

#### `Analysis/Calculus/Morse/HalfCylinder.lean`

The Euclidean modification, in the namespace `SymplecticGeometry`, for an
inner product space `V` of finite dimension and `S := Ici (-1) ×ˢ closedBall 0 1`
in `ℝ × V`:

```lean
theorem exists_nonneg_halfCylinder_hessian_pos {f : ℝ × V → ℝ} (hf : ContDiff ℝ 2 f)
    (hcrit : ∀ x ∈ Set.Ici (-1 : ℝ) ×ˢ Metric.closedBall (0 : V) 1, fderiv ℝ f x = 0 → x = 0) :
    ∃ μ : ℝ × V → ℝ, ContDiff ℝ ∞ μ ∧ 0 ≤ μ ∧
      tsupport μ ⊆ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 ∧
      ∀ x, fderiv ℝ (f + μ) x = 0 → x ∈ Set.Ici (-1) ×ˢ Metric.closedBall 0 1 →
        ∃ v, 0 < fderiv ℝ (fderiv ℝ (f + μ)) x v v
```

The construction is `μ (t, y) = β ‖y‖ * Λ t`, where:

- `β : ℝ → [0, 1]` is smooth, `1` on `[0, 1/2]`, decreasing, `0` from `1`
  on, and `exp (-a / (1 - r))` for `r` near `1`. Then for every `K` there
  is `s > 0` with `β'' ≥ K * |β'|` on `[1 - s, 1)`, and `β ≥ β (1 - s) > 0`
  on `[0, 1 - s]`; `‖β'‖ ≤ B` everywhere.
- `Λ ≥ 0` vanishes up to some `t₀ ∈ (-1, -ρ)`, and
  `Λ' = exp (H t)` after it, with `H' ≥ L` and `H → -∞` at `t₀`, so `Λ` is
  smooth, `Λ' > 0` and `Λ'' ≥ L * Λ'` on `(t₀, ∞)`, and `Λ` is convex,
  hence `Λ' t ≥ Λ t / (t - t₀)`. Here `L` is a smooth function of `t`,
  large in terms of the bounds below, and `Λ' ≥ A` on `[-ρ, ρ]`.

Fix `ρ ≤ 1/2`, and for each `t` bounds `‖∇²f‖ ≤ C t` on the part of `S`
with first coordinate in `[t - 1, t + 1]`, and `|∂_t f| + ‖∇_y f‖ ≥ ε t > 0`
on that part outside the interior of the box `[-ρ, ρ] × closedBall 0 ρ`
(positive by `hcrit` and compactness, since `0` is inside the box). With
`F = f + μ`, at a critical point `x = (t, y)` in `S`:

- *In the box*, `β = 1`, so `∂_t F = ∂_t f + Λ' t`, and `|∂_t f| ≤ C₁` on
  `[-1, 1] × closedBall 0 1` by compactness; this is not zero once `A > C₁`.
  So there are no critical points there.
- *Elsewhere*, `Λ t > 0` or `Λ' t > 0` (else `x` is critical for `f`), and:
  - if `‖∇_y f‖ < ε/2`, then `β Λ' = -∂_t f > ε/2` (from `∂_t F = 0`), and in the direction
    `e_t` the Hessian of `F` is `∂²_t f + β Λ'' ≥ -C + L ε / 2 > 0`;
  - if `‖∇_y f‖ ≥ ε/2`, then `Λ |β'| = ‖∇_y f‖ ≥ ε/2` (from `∇_y F = 0`),
    so `Λ ≥ ε/(2B)`. Take `K = 4C/ε + 1` and its `s`. If `‖y‖ ≥ 1 - s`,
    in the radial direction `y/‖y‖` the Hessian is `∂²_r f + Λ β'' ≥ -C + K ε/2 > 0`. If
    `‖y‖ < 1 - s`, then `β ≥ β (1 - s)`, `Λ' ≥ ε / (2 B (t - t₀))`, and in
    the direction `e_t` the Hessian is at least
    `-C + β (1 - s) L ε / (2 B (t - t₀)) > 0`.

The conditions on `L` and `A` are finitely many continuous lower bounds in
`t`, so a smooth `L` meets them. The proof is long; it splits into the
cutoff `β` with its estimates, the profile `Λ` with its estimates, and the
case analysis above.

#### `Geometry/Manifold/Morse/PositiveDirection.lean`

A positive direction of the Hessian at the critical points on a closed set
survives small perturbations, in the namespace `TauCeti`:

```lean
theorem exists_strongCkControl_criticalHessian_pos (hn : 2 ≤ n) (f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯)
    {A : Set M} (hA : IsClosed A)
    (hfA : ∀ x ∈ A, x ∈ criticalPoints I f → ∃ v, 0 < criticalHessian I f x v v) :
    ∃ c : ContMDiffMap.StrongCkControl I M n, c.order = 2 ∧ ∀ g ∈ c.ball f, ∀ x ∈ A,
      x ∈ criticalPoints I g → ∃ v, 0 < criticalHessian I g x v v
```

Route: cover `A` by a locally finite family of compact sets in chart
targets. On each, in that chart, `max (‖D u‖) (sup_{‖v‖ = 1} D²u (v, v))`
is continuous and positive for `u = f ∘ φ⁻¹`, so bounded below by some
`δ`; a `C²` tolerance `δ/2` keeps it positive. At a critical point the
fixed chart and the preferred chart give congruent Hessians
(`criticalHessian_apply_eq_of_mem_maximalAtlas`). Then
`manifoldMorseIndex_eq_finrank_iff` turns the conclusion into
`manifoldMorseIndex I g x < Module.finrank ℝ E` at nondegenerate critical
points.

### `Geometry/Manifold/Morse/Core/`

**Why one critical level at a time.** A single core of all of $M$, made of
cubes each attached along earlier ones, is out of reach. Descending discs of
a pseudo-gradient attach along earlier discs only under a Morse–Smale
condition together with a structure of manifold with corners on their
closures, which neither library has, and Eliashberg–Mishachev take their core
from a triangulation, which neither library has either. The union of all
descending manifolds is the set that the downward flow compresses into, but
with infinitely many critical points it need not be locally finite: the
descending manifold of a high critical point may run down to a minimum, so
infinitely many of them can meet one compact set. So the core is cut into the
pieces that cross one critical level. Each piece is finitely many disjoint
cubes with a compression that fixes the sublevel below them, and the engine
(below) works one level at a time.

Throughout, `g : M → ℝ` is smooth and
`D m := (Fin m → ℝ) × (Fin (Module.finrank ℝ E - m) → ℝ)` with sup norms; the
cube of `D m` is `Metric.closedBall 0 1 ×ˢ {0}` and its boundary sphere
`Metric.sphere 0 1 ×ˢ {0}`, as in `HolonomicApproximation/`.

#### `Morse/Core/Basic.lean`

The structure, in the namespace `SymplecticGeometry`, for levels
`a₀ < a < b`:

```lean
structure BandCore (I : ModelWithCorners ℝ E H) (g : M → ℝ) (a₀ a b : ℝ) where
  ι : Type
  [fintype : Fintype ι]
  dim : ι → ℕ
  dim_lt (i : ι) : dim i < Module.finrank ℝ E
  chart (i : ι) : D (dim i) → M
  isSmoothEmbedding_chart (i : ι) : Manifold.IsSmoothEmbedding 𝓘(ℝ, D (dim i)) I ∞ (chart i)
  isOpen_range_chart (i : ι) : IsOpen (Set.range (chart i))
  mapsTo_cube (i : ι) : Set.MapsTo (chart i) (Metric.closedBall 0 1 ×ˢ {0}) {x | a₀ < g x}
  mapsTo_sphere (i : ι) : Set.MapsTo (chart i) (Metric.sphere 0 1 ×ˢ {0}) {x | g x < a}
  pairwise_disjoint : Pairwise fun i j ↦
    Disjoint (chart i '' Metric.closedBall 0 1 ×ˢ {0}) (chart j '' Metric.closedBall 0 1 ×ˢ {0})
  exists_compression (U : Set M) (hU : IsOpen U)
      (hsub : {x | g x ≤ a} ∪ ⋃ i, chart i '' Metric.closedBall 0 1 ×ˢ {0} ⊆ U) :
    ∃ (f : C^∞⟮I, M; I, M⟯) (F : TauCeti.SmoothIsotopy (ContMDiffMap.id) f),
      (∃ V ∈ 𝓝ˢ {x | g x ≤ a}, ∀ t, ∀ x ∈ V, F (t, x) = x) ∧ Set.MapsTo f {x | g x ≤ b} U
```

So a band core is a finite family of pairwise disjoint cubes of positive
codimension, each the image of the cube of `D m` under a smooth open
embedding of the whole of `D m` (the coordinates that
`HolonomicApproximation/` works in), lying above `a₀` with its boundary
sphere below `a`; and for every open `U` around `{g ≤ a}` and the cubes, an
isotopy of embeddings starting at the identity and fixed near `{g ≤ a}` ends
in a map sending `{g ≤ b}` into `U`. The sketch omits docstrings and the
instance attribute on `fintype`. The API: `BandCore.cubes`, the union of
the cubes, with `isCompact_cubes` and `cubes_subset` (they lie above `a₀`);
and the example `BandCore.ofNoCriticalPoint`, the band core without cubes
when `g` is smooth and the band `g⁻¹[a, b]` is compact with no critical
point (for any `a₀`). Its compression is `TauCeti.Diffeotopy.smoothIsotopy`
of the diffeotopy `TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`.

Band cores move along diffeomorphisms, which may change the model but not
the model vector space: for `I : ModelWithCorners ℝ E H` and
`J : ModelWithCorners ℝ E H'`, both boundaryless, `Φ : M ≃ₘ^∞⟮I, J⟯ N` and
a band core `c : BandCore J g a₀ a b` of `g : N → ℝ`,

```lean
def BandCore.ofDiffeomorph (Φ : M ≃ₘ^∞⟮I, J⟯ N) (c : BandCore J g a₀ a b) :
    BandCore I (g ∘ Φ) a₀ a b
```

has the charts `Φ.symm ∘ c.chart i` (smooth embeddings by Tau Ceti's
`Diffeomorph.isSmoothEmbedding_comp`, `Geometry/Manifold/SmoothEmbedding/Diffeomorph.lean`)
and, for an open `U ⊆ M`, the compression of `c` for `Φ '' U` conjugated
by `Φ`, `(t, x) ↦ Φ.symm (F (t, Φ x))`, built with this library's
`TauCeti.SmoothIsotopy.precompSmoothEmbedding` and
`postcompSmoothEmbedding` (`Geometry/Manifold/SmoothIsotopy/Basic.lean`).
The cubes keep their dimensions, since both models are on `E`. Its API is
`cubes_ofDiffeomorph : (c.ofDiffeomorph Φ).cubes = Φ.symm '' c.cubes`.

#### `Morse/Core/Cube.lean`

The cube at one critical point, in the namespace `TauCeti.MorseChart`, for
a manifold `M` modelled on `E` itself (`[ChartedSpace E M]` with
`𝓘(ℝ, E)`), the model of Tau Ceti's `MorseChart E g p` and its `field`, of
the pseudo-gradients of `Morse/PseudoGradient/Existence.lean`, and of
`TauCeti.globalFlow`; `Compression.lean` says how a general boundaryless
model comes down to it. Tau Ceti's flow
of an adapted pseudo-gradient (`Morse/PseudoGradient/Flow.lean`) needs
`[CompactSpace M]`, so this file uses a compactly supported smooth field `X`
with `dg(X) ≤ 0`, `dg(X) < 0` on the band off the critical points, and equal
near each critical point of the band to the linear field
`TauCeti.MorseChart.field` of a Morse chart: the field of
`IsCompact.exists_contMDiff_pseudoGradientOn_nhds`
(`Morse/PseudoGradient/Existence.lean`) times a cutoff. Its flow is complete
(as in `TauCeti.compactlySupportedFlowDiffeotopy`). For a nondegenerate
critical point `p` of index `m`, with `a₀ < a < g p` and no critical point
on the support with value in `[a₀, g p)` (points of the level `g p` itself
are allowed, since no flow line from `p` reaches them),
`TauCeti.MorseChart.exists_cubeChart_unstableSet` gives a smooth open embedding
`φ : D m → M` with `φ 0 = p`, sending the cube into the unstable set of `p`
for this flow and above `a₀`, and its sphere below `a`, such that every point
of that unstable set at level at least `a` is in the image of the cube.
The theorem takes the field in a more general form: any complete smooth `X`
with `dg(X) ≤ 0`, equal to the linear field on the source of a Morse chart
at `p`, with `dg(X) < 0` wherever `a₀ < g < g p` and `g⁻¹[a₀, b]` compact
for `b < g p`. A compactly supported field as above that does not vanish on
`g⁻¹[a₀, g p)` satisfies these hypotheses.

The chart is built from hitting times, not from one fixed time, since
different flow lines from `p` can take very different times to descend. Fix
`a'` with `a₀ < a' < a`, and a small round ball `B` of negative coordinates
of the Morse chart, read with its negative coordinates first, on which `X` is
the linear field, so that the flow moves points of `B` radially. Each flow
line from the sphere `∂B` meets the level `a'` exactly once and
transversally, since `dg(X) < 0` there off the critical points, so the time
`τ(u)` at which the line from `u ∈ ∂B` reaches `a'` is smooth in `u`
(implicit function theorem) and bounded. Take a smooth `θ` on `B`, constant
near `0`, equal to `τ(u)` at `r • u` for `r` near `1`, and with
`r ↦ θ (r • u) + log r` strictly increasing; a cutoff in `log r` over a
long enough interval gives one. Then `v ↦ Φ_{θ v} v`, extended to nearby
positive coordinates of the Morse chart, is an open embedding near `B`
(two points with the same image lie on one flow line, and the monotonicity
rules that out), and maps `B` onto the part of the unstable set of `p` at
level above `a'`, which lies above `a₀`. The part at level at least `a` is a
compact subset of it; a radial diffeomorphism of `ℝ^m` onto the interior of
`B`, a scaling that puts the preimage of that compact set inside the open
cube, and a coordinatewise diffeomorphism of `ℝ` onto an interval in the
positive coordinates then give the chart on all of `D m`. Tau Ceti's slice
charts `TauCeti.IsAdaptedPseudoGradient.exists_isSliceChart_unstableSet`
(`Morse/Stable/Manifold.lean`) compose a Morse chart with the flow in the
same way on compact manifolds.

#### `Morse/Core/Compression.lean`

```lean
theorem TauCeti.IsMorse.exists_bandCore (hg : IsMorse I g) (hp : IsProperMap g)
    (hbdd : BddBelow (Set.range g))
    {a₀ a v b : ℝ} (ha₀ : a₀ < a) (ha : a < v) (hb : v < b)
    (hcrit : ∀ x ∈ criticalPoints I g, a₀ ≤ g x → g x ≤ b →
      g x = v ∧ manifoldMorseIndex I g x < Module.finrank ℝ E) :
    Nonempty (BandCore I g a₀ a b)
```

**Models.** The tools below, `Cube.lean`, Tau Ceti's pseudo-gradients and
`TauCeti.globalFlow`, are stated for manifolds modelled on `E` with
`𝓘(ℝ, E)`. So the file first proves the theorem for such an `M`, with
`I := 𝓘(ℝ, E)`, as a lemma of its own, and gets the general statement
from it through Tau Ceti's `BoundarylessModel I M`
(`Geometry/Manifold/ModelTransport/Boundaryless.lean`): `M` with the same
topology and the charts composed with `I`, a manifold modelled on `E`,
with the diffeomorphism
`BoundarylessModel.diffeomorph I ∞ : M ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ BoundarylessModel I M`
whose underlying map is the identity (`coe_diffeomorph`). The lemma is
applied to `g' := g ∘ (BoundarylessModel.homeomorph I M).symm`:

- `IsMorse`, `criticalPoints` and `manifoldMorseIndex` are carried by
  `BoundarylessModel.isMorse_iff`, `criticalPoints_eq` and
  `manifoldMorseIndex_eq` (`Geometry/Manifold/Morse/ModelTransport.lean`),
  which give `hg` and `hcrit` for `g'`;
- `IsProperMap g'` and `BddBelow (Set.range g')` hold since `g'` is `g`
  composed with a homeomorphism; `T2Space` has an instance on
  `BoundarylessModel I M`, and `SigmaCompactSpace`, which the
  pseudo-gradients need, is the library's
  `BoundarylessModel.instSigmaCompactSpace`;
- the band core of `g'` comes back to `M` as
  `BandCore.ofDiffeomorph (BoundarylessModel.diffeomorph I ∞)` of it
  (`Basic.lean`), a band core of `g' ∘ diffeomorph I ∞ = g`, and that
  definition carries its smooth embeddings and smooth isotopies.

The cubes are those of `Cube.lean` at the finitely many critical points of
the level `v` (`TauCeti.IsMorse.finite_criticalPoints_inter`), all for the
one field `X`: by `hcrit` no critical value lies in `[a₀, v)`, which is the
hypothesis of `TauCeti.MorseChart.exists_cubeChart_unstableSet` at each of them, the
other points of the level `v` being allowed. They are disjoint since
unstable sets of distinct critical points are. The compression is the time-`T`
map of the flow of `ρ • X`, with `ρ` zero near `{g ≤ a}` and one from just
above `a` up to `b`; time slices of a flow are open embeddings. That
`{g ≤ b}` is carried into `U` for large `T` is Mathlib's
`eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`
(`Mathlib/Dynamics/OmegaLimit.lean`) for the forward invariant set
`{g ≤ b}`, compact because `g` is proper and bounded below (`hbdd`; for
`g = id` on `ℝ` the sublevel is `(-∞, b]`), once its ω-limit is in `U`.
A point of the ω-limit has its whole backward orbit in `{g ≤ b}`, along
which `g` increases to a limit; its α-limit lies where `ρ • X` vanishes.
Either that is the zero set of `ρ`, and then the point is no higher than
it, so in `U` when that zero set is chosen
close to `{g ≤ a}` (properness); or it is a critical point of the level `v`,
and the point lies in its unstable set at level at least `a`, hence in a
cube. If this ω-limit argument is long, it is a
public lemma of its own in this file.

#### `Morse/Core/Exhaustion.lean`

The band cores of an open manifold, from issue 4:

```lean
theorem SymplecticGeometry.exists_isMorse_bandCore_seq (hE : Module.finrank ℝ E ≠ 1)
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (d e : ℕ → ℝ), IsMorse I g ∧ IsProperMap g ∧
      (∀ x, e 0 < g x) ∧ (∀ k, d k < e k ∧ e k < d (k + 1)) ∧
      Filter.Tendsto d Filter.atTop Filter.atTop ∧
      ∀ k, Nonempty (BandCore I g (d k) (e k) (e (k + 1)))
```

`g` comes from `TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt`. The engine
supplies `hE` as that theorem's section explains.
Its critical values form a discrete set, so the levels can be chosen with all
critical values in the intervals `(e k, d (k + 1))`, at most one in each;
`exists_bandCore` then applies to `(d k, e k, e (k + 1))`, with `hbdd`
from `BddBelow (Set.range g)` in that theorem, also where the interval
holds none, since its hypothesis on critical points then holds vacuously.

**What the engine needs beyond the sketch of `Cube.lean`.** The engine
approximates over each cube of a band core relative to the open set where
its form is already good. That set contains the part of the cube below `a`,
which has interior in the cube, and not only a neighbourhood of the boundary
sphere, to which the sketch of `exists_holonomic_approximation_cube` is
relative. Eliashberg–Mishachev's relative form, relative to a closed set near
which the datum is holonomic, is what the engine uses; it is
`exists_holonomic_approximation_cube_directions`, applied through
`HolonomicApproximation/Parametric.lean` with the parameters as the core
coordinates outside `J`.

### `Geometry/Symplectic/HPrinciple/HandleCore.lean`

The second milestone. With $m+k=2n$, $1\le m$, $1\le k$ (so $m<2n$),
`D := (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, the cube
`Q := Metric.closedBall (0 : D) 1`, the attaching faces
`A := Metric.sphere (0 : Fin m → ℝ) 1 ×ˢ Metric.closedBall 0 1`, and a parameter space a finite-dimensional
normed space `L` with a compact `K ⊆ L`:

```lean
theorem exists_homotopy_exact_of_exact_near_attaching (hK : IsCompact K)
    {τ : L → SmoothTwoForm 𝓘(ℝ, D) D} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ Q, ((τ l).bilinFormAt x).Nondegenerate)  -- on the cube
    {β : L → SmoothForm 𝓘(ℝ, D) D ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {W : Set D} (hW : IsOpen W) (hAW : A ⊆ W)
    (hτβ : ∀ l ∈ K, ∀ x ∈ W, mextDerivₗ 1 (β l) x = τ l x) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, D) D,
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ Q, ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ A, ∀ l ∈ K, ∀ t, ∀ x ∈ W', σ (l, t) x = τ l x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, D) D ℝ 1, mextDerivₗ 1 γ = σ (l, 1)) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ Q, ∃ γ, ∀ x ∈ V, mextDerivₗ 1 γ x = τ l x) →
        ∀ t, ∃ V ∈ 𝓝ˢ Q, ∃ γ, ∀ x ∈ V, mextDerivₗ 1 γ x = σ (l, t) x
```

This is the shape of the working lemma, not the final text. Its collar `W`
is one open set for all of `K`, and its primitives `β` depend smoothly on
`λ`. The milestone asks for neither, and in its conclusion the homotopy
need only be fixed near `A` for each `λ` separately:

```lean
theorem exists_homotopy_exact_of_forall_exact_near_attaching (hK : IsCompact K)
    {τ : L → SmoothTwoForm 𝓘(ℝ, D) D} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ Q, ((τ l).bilinFormAt x).Nondegenerate)
    (hex : ∀ l ∈ K, ∃ W ∈ 𝓝ˢ A, ∃ β : SmoothForm 𝓘(ℝ, D) D ℝ 1,
      ∀ x ∈ W, mextDerivₗ 1 β x = τ l x) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, D) D,
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ Q, ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∀ l ∈ K, ∃ W' ∈ 𝓝ˢ A, ∀ t, ∀ x ∈ W', σ (l, t) x = τ l x) ∧
      -- the last two clauses as in the working lemma, the relative one only for `l ∈ K`
      ...
```

The neighbourhoods in `hex` may shrink to `A` as `λ` converges in `K`, so
they give no common collar directly. The proof first removes that
difference (step 0), then builds a smooth family of primitives on the
common collar (steps 1 to 3), and applies the working lemma.

0. **A common collar.** Fix a thin product collar `W₀ ⊇ A` (as in step 1).
   Correct `τ` by a smooth family of two-forms `η λ` that, for each
   `λ ∈ K`, vanishes near `A`, is small enough on `Q` that
   `τ λ - s • η λ` stays nondegenerate for `s ∈ [0, 1]`, and makes
   `τ λ - η λ` closed on `W₀`. The straight line from `τ` to `τ - η`,
   joined smoothly in `t` to the homotopy of the working lemma, then gives
   the milestone. Each `τ λ - η λ`, `λ ∈ K`, is closed on `W₀` and exact on
   a thinner product collar inside the `W` of `hex`, so it is exact on
   `W₀`, since that inclusion is a homotopy equivalence. The candidate
   for `η λ` is a homotopy operator applied to `d (τ λ)` along segments
   into the faces: it vanishes wherever `d (τ λ)` vanishes along those
   segments, and is bounded by the width of `W₀` times the size of
   `d (τ λ)`, uniformly over the compact `K`. For `λ ∈ K` that is the
   case near `A`, since `τ λ` is closed there. The sup norm is not smooth
   at the corners of `A`, so the operator must be built with care there.
   The building issue settles this step first. If it fails, the issue
   records the difference between the two statements in `ERRATA.md`, with
   a counterexample, before it proves the milestone with one collar.

On the common collar, with `τ` now the corrected family `τ - η`, the
smooth family `β` of primitives that the working lemma takes comes in
three steps:

1. The product collar `W₀ ⊇ A` is the set of `(u, v)` with
   `|‖u‖ - 1| < ε` and `‖v‖ < 1 + ε`, for a small `ε > 0`. It has a finite
   good cover by convex slabs, so it has a `SmoothCohomologySplitting`
   (`HasFiniteGoodCover.smoothCohomologySplitting`) and a linear
   primitive map on exact three-forms, that splitting's `exactPrimitive`.
2. Off `K` the forms `τ λ` need not be closed on `W₀`. So subtract from each
   restriction `τ λ|W₀` the primitive given by step 1 of `d (τ λ|W₀)`. The
   difference is closed for every `λ`, depends smoothly on `λ`, and is
   `τ λ|W₀` for `λ ∈ K`, because the primitive map is linear.
3. Apply the splitting's `primitive` to that difference. By
   `mextDerivₗ_primitive` and `proj_eq_zero_iff`, its differential is
   `τ λ` on `W₀` for `λ ∈ K`. A cutoff that is `1` on a smaller collar then
   makes it a form on `D`.

Steps 2 and 3 need the splitting's maps to take smooth families over `L` to
smooth families. `PreservesSmoothFamilies`, which issue 6 below generalizes
from `unitInterval` to any parameter manifold, gives this.

**Shape of the conclusion.** The hypotheses on the collar are an open `W`
with `A ⊆ W`, as in the case $m=1$
(`exists_homotopy_exact_of_closed_near_attaching_fin_one`). The last two
clauses are those of the case $m=1$ too: for every `l` the end `σ (l, 1)` is
exact on all of `D`, and for every `l` at which `τ l` is exact on a
neighbourhood of `Q` every `σ (l, t)` is exact on one. The proof below gives
a primitive of `σ (l, 1)` that depends smoothly on `l`; the statement does not
record it, since neither the milestone nor the engine uses it.

**The proof, for every $m\ge1$: approximation and compression.** The source
proves the case $m=1$ and only sketches an induction on $m$, and two readings
of it fail. A lower case applied to a splitting
`D = (Fin (m-1) → ℝ) × (ℝ × (Fin k → ℝ))` of the core gives a homotopy that
is fixed only near the faces of the smaller core, so it moves the form near
the other faces of `A`; and the identity
$\tau=\pi^*\iota^*\tau+d\,h(\Phi^*\tau)+h(\Phi^*d\tau)$ for the contraction
`Φ` along the fibres, which proves the case $m=1$, keeps the term
$\pi^*\iota^*\tau$, the restriction of `τ` to the core pulled back by the
projection, which vanishes for a one-dimensional core but in general is not
small. So the working lemma is proved for all $m$ at once by Decision 1's
argument, on one cube instead of a band core. With `u` the core coordinate
and `v` the transverse one, the choices, each uniform over `K`, are made in
this order.

1. *A slab inside the collar.* By compactness of `A` there is
   `0 < ε₀ ≤ 1/4` with every point of `Q` where `1 - 2ε₀ ≤ ‖u‖` in `W`
   (`IsCompact.exists_thickening_subset_open`).
2. *A margin.* `r > 0` from `IsSmoothFamily.exists_pos_forall_nondegenerate`
   over `K × Q`: a two-form within `r` of `τ l` at a point `x ∈ Q`,
   `l ∈ K`, is nondegenerate at `x`.
3. *The formal primitive.* The datum is `f l := β l`, as a map
   `D → D [⋀^Fin 1]→L[ℝ] ℝ`, and
   `G l x := fderiv ℝ (f l) x + J (τ l x - dβ l x)`, where `J` is a linear
   right inverse of the alternation of a bilinear map (half the curried
   form). By `TauCeti.mextDeriv_eq_extDeriv` the alternation of `G l x` is
   `τ l x`, and `G l = fderiv ℝ (f l)` wherever `dβ l = τ l`, so for
   `l ∈ K` the datum is holonomic on `W`. If `fderiv ℝ f' x` is within `ε`
   of `G l x`, then `d f'` is within `2ε` of `τ l` at `x`.
4. *Holonomic approximation.* Parametric relative holonomic approximation
   (`HolonomicApproximation/Parametric.lean`, in the form given there for
   this use: `exists_holonomic_approximation_family`) over the cube
   `closedBall 0 1 ×ˢ {0}`, relative to the closed
   `B := {1 - 2ε₀ ≤ ‖u‖ ≤ 1 + η}` with `B ×ˢ {0} ⊆ W`, after a cutoff in
   space makes the datum holonomic near `B ×ˢ {0}` for every `l`, with
   accuracy `r / 4` and a width `δ < min ε₀ η`. It gives a smooth
   family of diffeotopies `H l`, smooth in `(l, s, x)`, and a smooth family
   `β' l` of one-forms, such that for every `l` and `s`, `H l s` is the
   identity and `β' l = β l` outside the `δ`-neighbourhood of
   `{‖u‖ ≤ 1 - 2ε₀} ×ˢ {0}`, and an open `V ⊆ L × D` containing
   `(l, H l 1 y)` for `l ∈ K` and `y` in the core, at whose points over `K`
   the derivative of `β' l` is within `r / 4` of `G l`. That
   support lies in a compact subset of the interior of `Q` and misses the
   slab `S := {‖u‖ > 1 - ε₀}`, so every `H l s` maps `Q` onto `Q` and is the
   identity on `S`, and `β' l = β l` on `S`.
5. *A thin tube.* By compactness of `K` and of the core, there is `δ' > 0`
   with `(l, H l 1 x) ∈ V` for `l ∈ K` and `x ∈ Q` with `‖v‖ ≤ δ'`.
6. *The compression.* `exists_cubeCompression`, for the core `E := ι → ℝ`
   instead of `Fin 1 → ℝ`, with `ε₀` and `δ'`, gives fibre scalings `c s`, the
   identity where `1 - ε₀ / 2 < ‖u‖`, preserving `Q`, with `c 1` mapping `Q`
   into `{‖v‖ < δ'} ∪ S`. Put `e l s := H l s ∘ c s`: an isotopy of
   diffeomorphisms from the identity, smooth in `(l, s, x)`, preserving
   `Q`, the identity where `1 - ε₀ / 2 < ‖u‖`, and with `e l 1` mapping `Q`
   into the set where `d (β' l)` is within `r / 2` of `τ l`, for `l ∈ K`:
   on the tube by 5 and 3, and on `S ∩ Q` because there
   `d (β' l) = dβ l = τ l`, by 1 and 4.

The homotopy, with the smooth steps `a` and `b` of the case $m=1$ (`b`
starts once `a` has reached `1`), is
`σ (l, t) := (e l (a t))^* ((1 - b t) • τ l + b t • d (β' l))`, a smooth
family by `IsSmoothFamily.mpullback_family`. The clauses:

- *Nondegenerate on `Q`* for `l ∈ K`: while `b t = 0` it is a pullback of
  `τ l` along a diffeomorphism preserving `Q`
  (`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`);
  once `a t = 1` every point of `e l 1 '' Q` has the segment within the
  margin `r` of step 2.
- *Fixed near `A`* for `l ∈ K`: on the open set where `1 - ε₀ / 2 < ‖u‖`
  and `x ∈ W`, `e l s` is the identity and `d (β' l) = dβ l = τ l`.
- *Exact at the end*, for every `l`: `σ (l, 1) = d ((e l 1)^* (β' l))`.
- *Relative clause*, for every `l`: if `τ l` is exact on a neighbourhood of
  `Q`, so is every `(1 - b) • τ l + b • d (β' l)`, and a pullback along a
  map that sends `Q` into `Q` stays exact near `Q`
  (`TauCeti.SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq`).

Beyond the cutoff of step 4, which makes the datum holonomic near
`B ×ˢ {0}` for every `l` as `exists_holonomic_approximation_family` asks,
no cutoff in space is needed: only `Q` and the neighbourhood of `A` are
constrained, and `e l 1` sends `Q` into the region of approximation. The merged case $m=1$
(`HandleCore/OneDimensional.lean`) needs neither holonomic approximation
nor a primitive near `A`; the working lemma does not use it.

**New lemmas and their files.**

- `exists_cubeCompression` generalized from the core `Fin 1 → ℝ` to a core
  `E` with `[HasContDiffBump E]`, used with `E := ι → ℝ` for a `Fintype ι`
  (`CubeCompression.lean`); its proof uses only `‖u‖`.
- The formal primitive of step 3 and its two facts (holonomic where
  `dβ = τ`, and the bound by `2ε`), with smoothness in the parameter, in
  `FormalPrimitive.lean`.
- The working lemma, from steps 1 to 6, in this file.

**Order of the building issues of issue 7.** The generalized compression
and the formal primitive, blocked by nothing; then the working lemma,
blocked by both and by issue 3; then the milestone, from the working lemma
with steps 0 to 3 above, blocked by the working lemma and by issue 6.

The docstring of
`exists_homotopy_exact_of_forall_exact_near_attaching` ends with "Milestone:
*Relative extension of exact symplectic forms over a handle core*."

### `Geometry/Symplectic/HPrinciple/Relative/`

The parametric relative theorem, by Decision 1, for an open `M` of
dimension $2n$, one band core of `SymplecticGeometry.exists_isMorse_bandCore_seq`
at a time (`Morse/Core/`). Issue 8 is one stage, in the four files
`CubeCoordinates.lean`, `CoreApproximation.lean`, `StagePath.lean` and
`Stage.lean`; issue 9 composes the stages, in `Relative/Basic.lean`.
Throughout, `c : BandCore I g a₀ a b` with `g : M → ℝ` continuous,
`D i := (Fin (c.dim i) → ℝ) × (Fin (Module.finrank ℝ E - c.dim i) → ℝ)`
with sup norms, `Q i := closedBall 0 1 ×ˢ {0} ⊆ D i` its cube, and
`k i := Module.finrank ℝ E - c.dim i`, positive by `c.dim_lt i`. The stage
uses neither `a₀` nor the level structure below `a`, only that the boundary
sphere of each cube lies in `{g < a}` (`c.mapsTo_sphere`), that the cubes
are disjoint, and the compression.

**The invariant.** Stage $k$ starts from families over the parameters of

- two-forms $\omega_l$, nondegenerate for the parameters `l ∈ K`;
- closed two-forms $\alpha_l$ (Decision 4: at the first stage, the family
  in the class with $\alpha_l=\tau_l$ for `l ∈ P₀`);
- one-forms $\beta_l$;

and an open `N ⊇ {g ≤ a}` with $\omega_l=\alpha_l+d\beta_l$ on `N` for
**every** parameter `l`, and on all of `M` for every `l ∈ P₀`. At the first
stage $\beta=0$ and `N = ∅`, since `g > e 0` everywhere. The stage returns
the same data for `b` in place of `a`, with
$\alpha'_l=e_{l,1}^*\alpha_l$ for the end $e_{l,1}$ of an isotopy of
embeddings $e_{l,t}$ from the identity, together with a primitive $\gamma_l$
of $\alpha'_l-\alpha_l$ that vanishes near `{g ≤ a}`; and the path
from $\omega_l$ to $\omega'_l$, constant near `{g ≤ a}` and, for
`l ∈ P₀`, through closed forms cohomologous to $\alpha_l$.

Two choices make this invariant easy to keep.

- *The identities hold for every parameter*, and only nondegeneracy is
  restricted to `K`. The stage keeps them for every parameter, since the
  end of its path is $e_{l,1}^*\sigma_l$ near `{g ≤ b}` by an algebraic identity
  that does not use `l ∈ K` (`StagePath.lean`). So the datum of each cube
  is holonomic near the relative set for every `l`, and the stage needs no
  cutoff in space to make it so (the remark under
  `exists_holonomic_approximation_family`): `B` is a set of core points
  for all parameters at once.
- *The closed family moves*, $\alpha'_l=e_{l,1}^*\alpha_l$, instead of staying
  fixed with the primitive of $e_{l,1}^*\alpha_l-\alpha_l$ added to $\beta$. The primitive
  given by the homotopy formula depends on `l` through `α` and the
  isotopy, and keeping it in $\beta$ would ask for its regularity in `l`
  in both forms. With $\alpha$ moving, the new one-forms are
  $e_{l,1}^*\beta'_l$, pulled back along a family of embeddings that is smooth in
  the parameter, and the primitives $\gamma_l$ are only needed one `l` at a
  time, by issue 9, which sums them (a locally finite sum, since
  $\gamma^{(k)}$ vanishes near $\{g\le e_k\}$) to show that the limit of
  the $\alpha^{(k)}$ is cohomologous to $\alpha^{(0)}$. For the isotopy
  $e_l(x,t)=e_{l,t}(x)$ from the identity to $e_{l,1}$,
  `TauCeti.SmoothForm.exists_mextDerivₗ_eq_mpullback_sub_of_homotopy`
  (`DifferentialForm/HomotopyOperator.lean`) gives a primitive $\gamma_l$
  of $e_{l,1}^*\alpha_l-\alpha_l$ that vanishes where the isotopy is the
  identity; its proof takes $\gamma_l=h\bigl(e_l^*\alpha_l\bigr)$ for the
  homotopy operator `h`.

**Parameters.** The two forms of Decision 4 share all of the stage except
the call to holonomic approximation, which differs in its two versions.

- *Smooth form*: parameters in a finite-dimensional normed space `L`, a
  compact `K ⊆ L` and a closed `P₀ ⊆ L`; all families are
  `IsSmoothFamily 𝓘(ℝ, L)`; the path is an
  `IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1))`. Nondegeneracy, of the data and
  of the path, is asked only over `K`.
- *Continuous form*: a compact Hausdorff `P` (so `K = univ`) and a closed
  `P₀ ⊆ P`; the two-forms are continuous into the frame topology of a
  covering frame system, read through `tangentEquiv.symm` as in
  `FormSpaces.lean`; the one-forms factor as $\beta_l=B(s\,l)$ through a
  continuous `s : P → S` into a finite-dimensional normed space `S` and an
  `IsSmoothFamily 𝓘(ℝ, S) B`. This factorization is the form in which the
  continuous version of holonomic approximation returns its output, and the
  stage returns it again (with a larger `S`), so no topology on one-forms
  is needed. At the first stage `B = 0` over `S = Fin 0 → ℝ`.

The shared part is stated over a topological parameter space `Λ` with a
compact `K ⊆ Λ`, a continuous `s : Λ → S` into a finite-dimensional
normed space, two-forms `ω α : Λ → SmoothTwoForm I M` given one `l` at a
time, and the smooth data of the approximation over `S`
(`StagePath.lean`). The smooth form takes `Λ = S = L` and `s = id`; the
continuous form takes `Λ = P`. Its conclusion gives the path by an
explicit formula, from which each form proves the regularity it needs
(`Stage.lean`).

**The family `α` of Decision 4 is an input.** Dugundji's extension
theorem, which gives `α` for a general compact Hausdorff `P`, is in neither
library, and it needs a metrizable domain; a finite partition of unity on
`P` gives a family that agrees with `τ` on `P₀` only up to a small error,
while the stage needs equality there. So the stage and the theorem of
issue 9 take the family `α` as a hypothesis (closed for every parameter,
`α l - α₀` exact, and `α l = τ l` for `l ∈ P₀`), and each use builds it explicitly:

- a point, with `P₀ = ∅` or `P₀ = univ`: the constant `α₀` or `τ` itself;
- `unitInterval`, extended to `ℝ`, with `P₀ = {0, 1}`:
  $\alpha_t=(1-t)\,\omega_0+t\,\omega_1$, smooth on `ℝ` and closed for
  every `t`;
- a disc or the cube `I^n` with `P₀` its boundary, for homotopy groups
  (`Parametric.lean`): $\alpha_x=\psi(x)\,\tau_{r(x)}+(1-\psi(x))\,\alpha_0$,
  with `r` the radial retraction from the centre onto the boundary and `ψ`
  continuous, `1` on the boundary and `0` near the centre; continuous into
  the frame topology since the frame topology makes addition and scalar
  multiplication continuous (`continuousSMul_frameTopology`).

#### `Relative/CubeCoordinates.lean`

The cube charts as coordinates for forms, in the namespace
`SymplecticGeometry.BandCore`.

- `isLocalDiffeomorph_chart`: each `c.chart i` is a local diffeomorphism,
  by Tau Ceti's `Manifold.IsImmersion.isLocalDiffeomorph`, since
  `c.dim i + k i = Module.finrank ℝ E`.
- `chartPartialDiffeomorph c i : PartialDiffeomorph I 𝓘(ℝ, D i) M (D i) ∞`,
  the symm of this library's `IsLocalDiffeomorph.partialDiffeomorphOfInjective`
  (`LocalDiffeomorph/Injective.lean`), with source `range (c.chart i)` and
  target `univ`, and `chartPartialDiffeomorph_symm_apply` (it is
  `c.chart i`).
- *Readings.* A form on `M` is read in the chart by
  `TauCeti.SmoothForm.mpullback` along `c.chart i`. The formal datum of the
  cube is `f l x := (mpullback (c.chart i) (β l)).val x` and
  `G l x := formalPrimitive (mpullback (c.chart i) (ω l - α l)).val
  (mpullback (c.chart i) (β l)).val x` (`FormalPrimitive.lean`, whose `J`
  is built from `ContinuousAlternatingMap.curryLeft`). It is holonomic at
  every point of `(c.chart i) ⁻¹' N`, by `formalPrimitive_eq_fderiv` and
  Tau Ceti's `SmoothForm.mextDerivₗ_mpullback`, for every `l`, and on all
  of `D i` for `l ∈ P₀`. Smoothness in the smooth form is
  `contMDiff_formalPrimitive`. In the continuous form, the joint continuity
  of `(l, x) ↦ G l x` comes from `continuous_tangentEquiv_symm_mpullback_of_contMDiff`
  (to the two-forms on `D i`) and `ContMDiffSection.continuous_totalSpace_eval`,
  and that of `(l, x) ↦ fderiv ℝ (f l) x` from the smoothness of `B` and
  the continuity of `s`.
- *Back to `M`.* For a smooth `a : S × D i → D i [⋀^Fin 1]→L[ℝ] ℝ` whose
  slices vanish off a fixed compact set, the forms
  `TauCeti.SmoothForm.extendByZeroAlong (c.chartPartialDiffeomorph i) (a (q, ·))`
  (`DifferentialForm/PartialDiffeomorph.lean`) are an `IsSmoothFamily 𝓘(ℝ, S)`:
  the new lemma `IsSmoothFamily.extendByZeroAlong`, in
  `DifferentialForm/SmoothFamily/PartialDiffeomorph.lean`. Since
  `mpullback_symm_extendByZeroAlong` reads the extension back as `a` on the
  chart, the corrected one-forms
  `B' q := B q + ∑ i, extendByZeroAlong (c.chartPartialDiffeomorph i) (a i (q, ·))`
  read as `f + a i` in the chart of `i`, wherever the other corrections
  vanish.
- *Diffeotopies back to `M`.* `TauCeti.extendDiffeotopyAlong`: for a smooth
  open embedding `φ : N → M` into a Hausdorff manifold and a diffeotopy `h`
  of `S × N` that fixes every `(q, z)` with `z` off a compact `C ⊆ N`, the
  diffeotopy of `S × M` that moves `(q, φ z)` as `h` moves `(q, z)` and
  fixes every `(q, y)` with `y ∉ φ '' C`; it keeps the parameter when `h`
  does. It goes in `Geometry/Diffeomorphism/Diffeotopy/Extend.lean`, in the
  namespace `TauCeti`. The cubes' diffeotopies have disjoint
  supports, so the stage composes their extensions in the order of
  `(Finset.univ : Finset c.ι).toList`, and each point of a cube is moved
  only by the extension of its own cube.
- *The relative set and the margin* (the review of #6134 asked to check it
  against the band-core faces). `exists_relativeSet`: for an open
  `N ⊇ {g ≤ a}` and a cube `i`, let `T := closedBall (0 : D i) 2` and
  `Y := (c.chart i) ⁻¹' {x | g x ≤ a} ∩ T`, compact. There are
  `0 < η < 1` and the closed
  `B := {u | ‖u‖ ≤ 1 + η ∧ (u, 0) ∈ cthickening η Y}` such that
  1. `sphere 0 1 ⊆ B`, since `c.mapsTo_sphere` puts `(u, 0)` in `Y` for
     `‖u‖ = 1`;
  2. `B ×ˢ {0} ⊆ (c.chart i) ⁻¹' N`, for `η` with
     `cthickening (2 * η) Y ⊆ (c.chart i) ⁻¹' N`
     (`Metric.eventually_image_cthickening_subset`);
  3. for `0 < δ ≤ η / 2`, no `p ∈ thickening δ (Q i)` with `p.1 ∉ B`
     is in `cthickening (η / 2) Y`; in particular `c.chart i p ∉ {g ≤ a}`.
     Indeed `‖p.1‖ < 1 + δ`, so `(p.1, 0) ∉ cthickening η Y`, and
     `‖p - (p.1, 0)‖ = ‖p.2‖ < δ`; and `p ∈ T`.

  `cthickening` and not `infDist` is used because a cube of dimension `0`
  has an empty sphere and possibly an empty `Y`, for which `infDist` is
  `0`; then `B = ∅`. Only `c.mapsTo_sphere` and the charts being defined on
  all of `D i` enter; where the cubes lie relative to `a₀` does not.

#### `Relative/CoreApproximation.lean`

Holonomic approximation over all cubes of a band core, relative to `N` and
to `P₀`, in a smooth and a continuous form,
`BandCore.exists_approximation_family` and
`BandCore.exists_approximation_continuous_family`. Both return the
hypotheses of `exists_stagePath` and of the lemmas on `stagePath` (next file):

- `S`, a continuous `s : Λ → S` (`S = L` and `s = id` in the smooth form,
  `S = S₀ × ((i : c.ι) → Fin (n i) → ℝ)` and `s l = (s₀ l, fun i ↦ σ i l)`
  in the continuous form, with the `σ i` of the continuous version), and
  `B` over `S` with `β l = B (s l)` (`B q = B₀ q.1` in the continuous form);
- a smooth `Φ : (S × unitInterval) × M → M` with diffeomorphisms as slices,
  `Φ ((q, 0), ·) = id`, and corrected one-forms `B'`, an
  `IsSmoothFamily 𝓘(ℝ, S)`;
- an open `N₁` with `{g ≤ a} ⊆ N₁ ⊆ N`, on which every slice of `Φ` is the
  identity and `B' q = B q`, for every `q`;
- for `l ∈ P₀`: `Φ ((s l, t), ·) = id` and `B' (s l) = B (s l)`;
- an open `U ⊆ Λ × M` with `K ×ˢ N₁ ⊆ U` and
  `(l, Φ ((s l, 1), y)) ∈ U` for `l ∈ K` and `y ∈ c.cubes`, at whose
  points `(l, y)` with `l ∈ K` every
  `ω l + r • (α l + mextDerivₗ I 1 (B' (s l)) - ω l)`, `r ∈ [0, 1]`, is
  nondegenerate at `y`.

Proof, the same in both forms except in step 4:

1. *Readings and margins.* For each cube the readings of
   `CubeCoordinates.lean`, and `η i`, `B i` of `exists_relativeSet`.
   A `δ' > 0` with the sets `c.chart i '' cthickening δ' (Q i)` pairwise
   disjoint (`c.pairwise_disjoint`, compactness), and
   `0 < δ ≤ min (min_i η i / 2) (min δ' (1 / 2))`.
2. *Nondegeneracy margin.* `r > 0` with: for `l ∈ K` and
   `x ∈ closedBall 0 2`, every two-form within `r` of the reading of
   `ω l` at `x`, and every point of the segment towards it, is
   nondegenerate at `x`. In the smooth form this is
   `IsSmoothFamily.exists_pos_forall_nondegenerate_sub_smul`; in the
   continuous form the same statement for a family whose values are only
   jointly continuous, `exists_pos_forall_nondegenerate_sub_smul_of_continuousOn`,
   a new lemma in `SmoothFamily/NormedSpace.lean` from which the merged
   one follows, since its proof uses only that continuity. Put
   `ε₁ := r / 5`.
3. *A cutoff in the parameter near `P₀`.* The holonomic approximation
   theorems ask the datum to be holonomic on an open set containing
   `P₀ ×ˢ univ`; the invariant gives it on `P₀ ×ˢ univ` only. With
   `T := closedBall 0 2`, the set
   `O := {l | ∀ i, ∀ x ∈ T, ‖fderiv ℝ (f i l) x - G i l x‖ < ε₁}` is open
   and contains `P₀`: `IsCompact.isOpen_setOfPred_forall_norm_sub_lt`, in
   `Topology/Compactness/Normed.lean`, for jointly continuous
   `f g : Λ × D → F'` and a compact `T`
   (`IsCompact.eventually_forall_of_forall_eventually`); step 1 of the
   continuous version uses it too. Take `χ : Λ → [0, 1]`, `1`
   on an open `O' ⊇ P₀` and `0` off `O` (smooth on `L` by
   `exists_contMDiffMap_zero_one_nhds_of_isClosed`, continuous on `P` by
   `exists_continuous_zero_one_of_isClosed`), and replace `G i` by
   `G' i l x := G i l x + χ l • (fderiv ℝ (f i l) x - G i l x)`. It is
   holonomic on the open
   `(univ ×ˢ (c.chart i) ⁻¹' N) ∪ (O' ×ˢ univ)`, which contains
   `univ ×ˢ (B i ×ˢ {0})` (item 2 of `exists_relativeSet`) and
   `P₀ ×ˢ univ`, and `‖G' i - G i‖ < ε₁` on `Λ × T`.
4. *Approximation.* For each cube, `exists_holonomic_approximation_family`
   (smooth form) or `exists_holonomic_approximation_continuous_family`
   (continuous form; building issue 8c states its support clauses at every
   point, as its proof gives) with `K`, `P₀`, `B i`, `ε₁` and `δ`. It gives
   the diffeotopy `h i`, the approximation, `V i`, `C i` and `N i`. On
   `V i` the derivative of the approximation is within `2 * ε₁` of `G i`
   at points of `T`, so its exterior derivative is within `4 * ε₁ < r` of
   the reading of `ω l - α l`
   (`norm_extDeriv_sub_le_of_norm_fderiv_sub_formalPrimitive_le`).
5. *Back to `M`.* `a i` is the approximation minus `f i` (in the continuous
   form `g i (q.2 i, x)`), which vanishes off the compact `C i`. Then `B'`
   as in `CubeCoordinates.lean`, and `Φ` the composite of the extensions
   of the `h i` (`extendDiffeotopyAlong`).
6. *The set `N₁`.* Let `Z i := Prod.snd '' C i ∩ {x | x.1 ∉ interior (N i)}`,
   compact. Every point that `h i` moves, or where `a i ≠ 0`, lies in
   `Z i`, by the `C` and `N` clauses, and `Z i` misses
   `(c.chart i) ⁻¹' {g ≤ a}` by item 3 of `exists_relativeSet`, since
   `B i ⊆ interior (N i)`. So `N₁ := N ∩ ⋂ i, (c.chart i '' Z i)ᶜ` is open
   and contains `{g ≤ a}`.
7. *The set `U`.* The union of `univ ×ˢ N₁` and, for each `i`, the open
   set of `(l, c.chart i x)` with `x ∈ thickening δ' (Q i) ∩ ball 0 2` and
   `(l, x) ∈ V i`. On
   `univ ×ˢ N₁` the segment is constant, `B' = B` there and
   `ω l = α l + dβ l` on `N`; at a point of the second set the
   corrections of the other cubes vanish (step 1), so the segment's
   reading is within `r` of that of `ω l`, by steps 2 and 4, and
   nondegeneracy carries back to `M` by
   `SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`
   along the chart. The displaced cube points lie in it since `h i` moves
   points by less than `δ < δ'`.

#### `Relative/StagePath.lean`

The shared part of the two forms.

```lean
theorem exists_stagePath {Λ S : Type*} [TopologicalSpace Λ] [NormedAddCommGroup S]
    [NormedSpace ℝ S] (c : BandCore I g a₀ a b) (hg : Continuous g)
    {K : Set Λ} (hK : IsCompact K) {s : Λ → S} (hs : Continuous s)
    {ω α : Λ → SmoothTwoForm I M} (hnd : ∀ l ∈ K, (ω l).IsNondegenerate)
    {B' : S → SmoothForm I M ℝ 1}
    {Φ : (S × unitInterval) × M → M} (hΦ : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ Φ)
    (hΦd : ∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ Φ (p, x)) (hΦ₀ : ∀ q x, Φ ((q, 0), x) = x)
    {N₁ : Set M} (hN₁ : IsOpen N₁) (haN₁ : {x | g x ≤ a} ⊆ N₁)
    (hΦN₁ : ∀ p, ∀ x ∈ N₁, Φ (p, x) = x)
    {U : Set (Λ × M)} (hU : IsOpen U) (hKN₁ : K ×ˢ N₁ ⊆ U)
    (hUc : ∀ l ∈ K, ∀ y ∈ c.cubes, (l, Φ ((s l, 1), y)) ∈ U)
    (hUnd : ∀ p ∈ U, p.1 ∈ K → ∀ r ∈ Icc (0 : ℝ) 1,
      ((ω p.1 + r • (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - ω p.1)).bilinFormAt
        p.2).Nondegenerate) :
    ∃ (e : (S × unitInterval) × M → M) (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e)
      (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (V N' : Set M),
      (∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ e (p, x)) ∧ (∀ q x, e ((q, 0), x) = x) ∧
      IsOpen V ∧ V ∈ 𝓝ˢ {x | g x ≤ a} ∧ V ⊆ N₁ ∧ (∀ p, ∀ x ∈ V, e (p, x) = x) ∧
      IsOpen N' ∧ {x | g x ≤ b} ⊆ N' ∧ (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ N', ρ x = 1) ∧
      ∀ l ∈ K, ∀ t, (stagePath he hρ s ω α B' (l, t)).IsNondegenerate
```

The path is a definition of this file, with `stagePath_def`, given by its
formula, for the smooth steps `A := TauCeti.collaredFirstHalf` and
`C := TauCeti.collaredSecondHalf` of `HandleCore/Homotopy.lean` (`C` leaves
`0` only once `A` has reached `1`) and $e_{l,t}:=e((s\,l,t),\cdot)$:

$$\mathrm{stagePath}(l,t)=e_{l,A(t)}^{\,*}\,\omega_l
  +C(t)\,\rho\cdot e_{l,1}^{\,*}\bigl(\alpha_l+d\beta'_l-\omega_l\bigr),
  \qquad \beta'_l=B'(s\,l),$$

with pullbacks by `TauCeti.SmoothForm.mpullback` and the product with `ρ`
of Tau Ceti's `IsSmoothForm.fun_smul`. The new data are
`α' l := e_{l,1}^* α l` and the one-forms `β'' (s l)`, with
`β'' q := (e ((q, 1), ·))^* B' q`, an `IsSmoothFamily 𝓘(ℝ, S)` by
`IsSmoothFamily.mpullback_family`. The lemmas below read the stage's other
conclusions off the formula, one `l` at a time, each with the hypotheses
on `e`, `ρ`, `V` and `N'` that the theorem provides, so that both forms of
`Stage.lean` use them:

- `stagePath_zero`: at `t = 0` the path is `ω l`.
- `stagePath_one_eqOn`: on `N'`, `stagePath (l, 1)` equals
  `α' l + d (β'' (s l))`, for every `l`, since pullback commutes with `d`
  (Tau Ceti's `SmoothForm.mextDerivₗ_mpullback`).
- `stagePath_eqOn_nhdsSet`: on `V`, `stagePath (l, t) = ω l`,
  `α' l = α l` and `β'' (s l) = B (s l)`, since the slices of `e` are the
  identity there and `α l + dβ'_l = ω l` on `N₁` (hypotheses of the lemma).
- `stagePath_of_mem`: for `l ∈ P₀` the second term vanishes, since
  `α l + dβ'_l = ω l` on all of `M`; so `stagePath (l, t)` is
  `e_{l,A t}^* ω l`, closed, with `stagePath (l, t) - α l` exact
  (`ω l - α l` is exact, and `mpullback_sub_mem_exactForms_of_homotopy`
  along the isotopy), and `stagePath (l, 1) = α' l + d (β'' (s l))` on all
  of `M`.
- `exists_mextDerivₗ_eq_endPullback_sub`: for every `l`, a form `γ l` of
  the invariant, with `α' l = α l + d (γ l)` and `γ l = 0` on `V` (its
  proof takes `γ l := homotopyOperator (e_l^* α l)`).


Proof of `exists_stagePath`:

1. *The open set to compress into.*
   `W := {x | ∀ l ∈ K, (l, Φ ((s l, 1), x)) ∈ U}` is open, by compactness of
   `K` (`IsCompact.eventually_forall_of_forall_eventually`), and contains
   `{g ≤ a}` (by `hKN₁` and `hΦN₁`) and the cubes (by `hUc`).
2. *The compression.* `c.exists_compression_of_subset` for `W` gives `f`,
   the isotopy `F` from the identity to `f`, fixed on a neighbourhood
   `V₀` of `{g ≤ a}`, with `f '' {g ≤ b} ⊆ W`.
3. *The isotopy of the stage* is `e ((q, t), x) := Φ ((q, t), F (t, x))`:
   smooth, the identity at `t = 0` and on `V := interior V₀ ∩ N₁`, with slices
   local diffeomorphisms (a slice of `F` is a smooth embedding of `M` into
   itself, a local diffeomorphism by Tau Ceti's
   `Manifold.IsImmersion.isLocalDiffeomorph`), and
   `e ((s l, 1), ·) = Φ ((s l, 1), ·) ∘ f`. This is the compression
   conjugated by the displacement: compressing first and displacing after
   sends `{g ≤ b}` to points `y` with `(l, y) ∈ U`.
4. *The cutoff.* `W₁ := {x | ∀ l ∈ K, (l, e ((s l, 1), x)) ∈ U}` is open
   and contains `{g ≤ b}`. `ρ` is smooth, `1` on an open `N' ⊇ {g ≤ b}` and
   `0` off `W₁` (`exists_contMDiffMap_zero_one_nhds_of_isClosed`, for the
   closed sets `{g ≤ b}` and `W₁ᶜ`). The cutoff is on `M`, outside the
   pullback, so that it does not depend on `l`.
5. *Nondegeneracy.* While `C t = 0` the path is the pullback of `ω l` along
   a local diffeomorphism; once `C t ≠ 0`, `A t = 1`, and at a point `x` the value
   is the pullback along the differential of `e_{l,1}` at `x` of
   `ω l + (C t * ρ x) • (α l + dβ'_l - ω l)` at `e_{l,1} x`, which is nondegenerate
   by `hUnd` when `ρ x ≠ 0`, as then `x ∈ W₁`. Both cases use
   `SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv`.

#### `Relative/Stage.lean`

The stage in its two forms, each from `exists_approximation_family` or
`exists_approximation_continuous_family` followed by `exists_stagePath`.
The smooth form:

```lean
theorem BandCore.exists_stage_family (c : BandCore I g a₀ a b) (hg : Continuous g)
    {K P₀ : Set L} (hK : IsCompact K) (hP₀ : IsClosed P₀)
    {ω α : L → SmoothTwoForm I M} (hω : IsSmoothFamily 𝓘(ℝ, L) ω)
    (hα : IsSmoothFamily 𝓘(ℝ, L) α) (hαc : ∀ l, mextDerivₗ I 2 (α l) = 0)
    (hnd : ∀ l ∈ K, (ω l).IsNondegenerate)
    {β : L → SmoothForm I M ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {N : Set M} (hN : IsOpen N) (haN : {x | g x ≤ a} ⊆ N)
    (hωN : ∀ l, ∀ x ∈ N, (ω l).val x = (α l + mextDerivₗ I 1 (β l)).val x)
    (hωP₀ : ∀ l ∈ P₀, ω l = α l + mextDerivₗ I 1 (β l)) :
    ∃ (H : L × unitInterval → SmoothTwoForm I M) (α' : L → SmoothTwoForm I M)
      (β' : L → SmoothForm I M ℝ 1) (V N' : Set M),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) H ∧ IsSmoothFamily 𝓘(ℝ, L) α' ∧
      IsSmoothFamily 𝓘(ℝ, L) β' ∧ (∀ l, H (l, 0) = ω l) ∧
      (∀ l ∈ K, ∀ t, (H (l, t)).IsNondegenerate) ∧
      V ∈ 𝓝ˢ {x | g x ≤ a} ∧ (∀ l t, ∀ x ∈ V, (H (l, t)).val x = (ω l).val x ∧
        (α' l).val x = (α l).val x ∧ (β' l).val x = (β l).val x) ∧
      (∀ l, mextDerivₗ I 2 (α' l) = 0 ∧
        ∃ γ : SmoothForm I M ℝ 1, α' l = α l + mextDerivₗ I 1 γ ∧ ∀ x ∈ V, γ.val x = 0) ∧
      IsOpen N' ∧ {x | g x ≤ b} ⊆ N' ∧
      (∀ l, ∀ x ∈ N', (H (l, 1)).val x = (α' l + mextDerivₗ I 1 (β' l)).val x) ∧
      ∀ l ∈ P₀, H (l, 1) = α' l + mextDerivₗ I 1 (β' l) ∧
        ∀ t, mextDerivₗ I 2 (H (l, t)) = 0 ∧ H (l, t) - α l ∈ exactForms I M 2
```

`H := stagePath …`, an `IsSmoothFamily` by
`IsSmoothFamily.mpullback_family`, `fun_smul` and `add`, as in
`HandleCore/Homotopy.lean`. The data unchanged near `{g ≤ a}` are in
particular unchanged near `{g ≤ d k}` for the levels of
`exists_isMorse_bandCore_seq`, as issue 9 needs.

The continuous form, `BandCore.exists_stage_continuous_family`, has the
same conclusions for `l ∈ P` (with `K = univ`), with
`hω : Continuous fun l ↦ tangentEquiv.symm (ω l)` and the same for `α`
into the frame topology of a covering frame system
(`letI := ContMDiffSection.frameTopology …`, `hcover`), `β l = B (s l)`
as in *Parameters*, and in the conclusion `H` continuous on
`P × unitInterval` and `α'` continuous in the same sense, and
`β' l = B'' (s' l)` for a continuous `s' : P → S'` into a
finite-dimensional normed space and an `IsSmoothFamily 𝓘(ℝ, S') B''`.
The continuity of `H`, term by term in the formula:

- `e_{l,A t}^* ω l` and `e_{l,1}^* (α l - ω l)`: Tau Ceti's frame topology
  through this library's `continuous_tangentEquiv_symm_mpullback_prod`
  (`VectorBundle/Symplectic/Topology.lean`), with parameter manifold
  `S × unitInterval` and the smooth `e`, composed with
  `(l, t) ↦ (ω l, (s l, A t))`;
- `e_{l,1}^* (d β'_l)`, a smooth family over `S` composed with `s`: the
  new lemma `IsSmoothFamily.continuous_tangentEquiv_symm` in
  `VectorBundle/Symplectic/Topology.lean`, that a smooth family of
  two-forms over a manifold is continuous into the frame topology (its
  frame jets are jointly smooth in the parameter and the point);
- the products with `C t` and `ρ`: `continuousSMul_frameTopology` for the
  scalar, and, for the fixed function `ρ`, the new lemma
  `continuous_tangentEquiv_symm_smul` in the same file, multiplication by
  a fixed smooth function being continuous for the frame topology
  (Tau Ceti's `ContMDiffSection.continuous_smul_function_frameTopology`).

`α' l = e_{l,1}^* α l` is continuous by the first item.

#### `Relative/Basic.lean`

The parametric relative theorem, from the stages, in two forms:

- *Continuous version.* Given a compact Hausdorff `P`, closed `P₀ ⊆ P`,
  `τ : C(P, X)` where
  `X := {ω : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I) // ω.IsNondegenerate}`
  with the topology of a covering frame system (as *Symplectic vector
  bundles* installs it, `letI` and `hcover`), and a family `α` continuous
  into the frame topology with `α l` closed, `α l - α₀ ∈ exactForms I M 2`,
  and `α l = tangentEquiv (τ l)` for `l ∈ P₀`: there is
  `H : C(P × unitInterval, X)` with `H (l, 0) = τ l`, `H (l, t)` symplectic
  in the class of `α₀` for `l ∈ P₀` and all `t`, and `H (l, 1)` symplectic
  in that class for all `l`.
- *Smooth version.* The same for `τ : L → SmoothTwoForm I M` an
  `IsSmoothFamily` over a finite-dimensional normed space `L`, with a
  compact `K ⊆ L`, a closed `P₀ ⊆ L` and a smooth family `α` as above, the
  nondegeneracy of `τ` and the conclusions asked only for `l ∈ K`, and `H`
  an `IsSmoothFamily` over `L × unitInterval`. The uses are a point and
  `unitInterval`, a family over which is first extended to `ℝ` by the time
  extension of `DifferentialForm/TimeExtension.lean`, with `K = [0, 1]` (the
  `Parametric.lean` section of holonomic approximation says why no
  parameter manifold is needed). The family `α` of each use is given under
  *The family `α` of Decision 4 is an input* above. A corollary for a
  family over `unitInterval` does that extension and restricts `H` from
  `ℝ × unitInterval` back by `isSmoothFamily_iff_contMDiff`, so that
  `OpenManifold.lean` does not extend by hand.

Proof. `SymplecticGeometry.exists_isMorse_bandCore_seq` gives `g`, `d`,
`e` and the band cores; its hypothesis `hE : Module.finrank ℝ E ≠ 1` needs
a case split, since `TauCeti.SymplecticForm.even_finrank` gives nothing when
`M` is empty, and an empty `M` is a trivial case. Stage `k` is the stage of
`Stage.lean` for the band core of `(d k, e k, e (k + 1))`, from the data of
stage `k - 1` (at `k = 0`: `ω = τ`, the given `α`, `β = 0`, `N = ∅`).
A stage changes nothing near $\{g\le e_k\}$, and $e_k\to\infty$ with `g`
proper, so the stages, run on the times $[1-2^{-k},1-2^{-k-1}]$, are
constant near each compact set for times close to `1`; they compose to the
homotopy `H`. Its end is $\alpha^{(\infty)}_l+d\beta^{(\infty)}_l$, the
limits being eventually constant near each compact set, and
$\alpha^{(\infty)}_l-\alpha^{(0)}_l=d\sum_k\gamma^{(k)}_l$, a locally
finite sum; so the end is closed in the class, and nondegenerate. On `P₀`
every stage is through closed forms in the class (`stagePath_of_mem`).

### `Geometry/Symplectic/HPrinciple/OpenManifold.lean`

Theorem 7.3.1, both assertions, from the smooth engine:

```lean
theorem SmoothTwoForm.IsNondegenerate.exists_homotopy_isSymplectic
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) {α : SmoothTwoForm I M}
    (hα : α ∈ closedForms I M 2) {τ : SmoothTwoForm I M} (hτ : τ.IsNondegenerate) :
    ∃ σ : unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓡∂ 1) σ ∧ σ 0 = τ ∧
      (∀ t, (σ t).IsNondegenerate) ∧ (σ 1).IsSymplectic ∧ σ 1 - α ∈ exactForms I M 2

theorem SmoothTwoForm.IsSymplectic.exists_isSmoothFamily_isSymplectic_of_homotopy
    (hM : …) (hα : α ∈ closedForms I M 2) {ω₀ ω₁ : SmoothTwoForm I M}
    (h₀ : ω₀.IsSymplectic) (h₁ : ω₁.IsSymplectic)
    (h₀α : ω₀ - α ∈ exactForms I M 2) (h₁α : ω₁ - α ∈ exactForms I M 2)
    {τ : unitInterval → SmoothTwoForm I M} (hτ : IsSmoothFamily (𝓡∂ 1) τ)
    (hτ₀ : τ 0 = ω₀) (hτ₁ : τ 1 = ω₁) (hτnd : ∀ t, (τ t).IsNondegenerate) :
    ∃ σ : unitInterval → SmoothTwoForm I M, IsSmoothFamily (𝓡∂ 1) σ ∧
      σ 0 = ω₀ ∧ σ 1 = ω₁ ∧ ∀ t, (σ t).IsSymplectic ∧ σ t - α ∈ exactForms I M 2
```

The class $a$ is given by a closed representative `α`; the docstrings say
that by `deRhamCohomology.mk_surjective` and `mk_eq_zero_iff` this is the
statement for every `a : deRhamCohomology I M 2`. The first theorem's
docstring ends with the milestone line of *Gromov's h-principle for
symplectic forms on open manifolds*.

### `AlgebraicTopology/Homotopy/Domination.lean`

CW type by domination (Decision 5), about Tau Ceti's notion, so in its
namespace:

```lean
theorem TauCeti.CWType.of_comp_homotopic_id {X : Type u} {K : Type*} [TopologicalSpace X]
    [TopologicalSpace K] [TauCeti.CWType K] {i : C(X, K)} {r : C(K, X)}
    (h : (r.comp i).Homotopic (ContinuousMap.id X)) : TauCeti.CWType X
```

Proof: `f := sigmaCWApproximationMap (TopCat.of X)` is a weak homotopy
equivalence from a space of CW type. Lift `r` through it,
`f ∘ r' ≃ r` (`exists_comp_homotopic`), and put `g := r' ∘ i`. Then
`f ∘ g ≃ r ∘ i ≃ id`, so `f ∘ (g ∘ f) ≃ f`, and `g ∘ f ≃ id` by
`homotopic_of_comp_homotopic`. So `f` is a homotopy equivalence, and `X`
has CW type by `ContinuousMap.HomotopyEquiv.cwType`. `K` may live in any
universe, since the approximation is in the universe of `X`. This is the
classical fact that a space dominated by a CW
complex has CW type, proved here without mapping telescopes.

### `AlgebraicTopology/SimplicialComplex/Realization/PartitionOfUnity.lean`

The nerve of a partition of unity and its canonical map, for
`ρ : PartitionOfUnity ι X`:

- `PartitionOfUnity.nerve ρ : AbstractSimplicialComplex ι`, whose
  faces are the nonempty finite `s` with `∃ x, ∀ i ∈ s, ρ i x ≠ 0` and the
  singletons, with `mem_nerve_iff`;
- `PartitionOfUnity.toNerve ρ : C(X, ρ.nerve.Realization)`, sending `x` to
  the point with barycentric coordinates `ρ i x`, with `toNerve_apply_coe`
  (its coordinates). Its continuity for the weak topology uses local
  finiteness: near each point it lands in the realization of finitely many
  vertices, where the weak topology is the Euclidean one.

### `Analysis/LocallyConvex/CWType.lean`

```lean
theorem Convex.cwType_inter {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [MetrizableSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hU : IsOpen U) : TauCeti.CWType ↥(C ∩ U)
```

Proof, by the nerve argument of Milnor and of Dugundji (*References*)
made direct: put `O := C ∩ U` with a metric. Each `y ∈ O` has a convex
relatively open neighbourhood `C ∩ (y + V) ⊆ O` (local convexity). Tau
Ceti's `Topology.IsInducing.exists_continuous_radius_subordinate` gives a
positive continuous `r` on `O` such that each ball `B(y, 2 r y)` lies in one
of these convex sets. Take a partition of unity `ρ`, indexed by `O`,
subordinate to the cover by the balls `B(y, r y)`
(`PartitionOfUnity.exists_isSubordinate`, as `O` is metrizable, so
paracompact and normal). If `x` lies in the supports of `ρ y₀, …, ρ yₖ` and
`r yⱼ` is the largest of the `r yᵢ`, then `x` and all `yᵢ` lie in
`B(yⱼ, 2 r yⱼ)`, so in one convex subset of `O`. Hence the map `ψ` from the realization of
`ρ.nerve` to `O`, affine on each simplex with vertex `y` sent to `y`, is
well defined, continuous by `continuous_iff_faceInclusion`, and the
straight segment from `x` to `ψ (ρ.toNerve x)` stays in `O`. So `O` is
dominated by a CW complex (`realizationCWComplex`, `instT2SpaceRealization`,
`TauCeti.CWType.of_cwComplex_univ`), and `TauCeti.CWType.of_comp_homotopic_id`
gives the theorem.

### `Geometry/Manifold/VectorBundle/Symplectic/Topology.lean`

Facts about two-forms in the frame topology of a covering frame system
(`letI := frameTopology …`, `hcover`), on a finite-dimensional base:

- `Bundle.ContMDiffTwoForm.isOpen_setOfPred_forall_mem_nondegenerate`: for a
  compact `K ⊆ M`, the forms `ω` with `(ω.bilinFormAt x).Nondegenerate` for
  all `x ∈ K` are an open set. Nondegeneracy is open in each fibre, and
  evaluation is jointly continuous in the form and the point
  (`Section/Topology.lean`).
- `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback`: for a
  `TauCeti.SmoothIsotopy` `h` of `M`, the map
  `(ω, t) ↦ tangentEquiv.symm ((tangentEquiv ω).mpullback (h.timeSlice t))`
  is continuous on `ContMDiffTwoForm … × unitInterval`. Its frame jets are
  polynomials in the jets of `ω` and of the slices of `h`, so this follows
  from the continuity of composition and pairing in the weak Whitney
  topology (`ContMDiffMap.continuous_comp_manifoldWeakWhitney`,
  `continuous_prodMk_manifoldWeakWhitney`), as for Tau Ceti's
  `ContMDiffSection.continuous_map_frameTopology`. The issue fixes the
  exact form of the pullback here.
- `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal`:
  for `U : Opens M`, covering frames on `M` and any frames on `U`,
  restriction, `ω ↦ tangentEquiv.symm (SmoothForm.mpullback Subtype.val
  contMDiff_subtypeVal (tangentEquiv ω))`, is continuous from the two-forms
  on `M` to those on `U`. Tau Ceti's
  `ContMDiffSection.continuous_restrict_frameTopology` lands in the
  pulled-back bundle over `U`, not in the tangent bundle of `U`, which is
  why the statement here is needed. It is the slice at `0` of the constant
  family `(p, x) ↦ x : ℝ × U → M` in
  `Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_prod`.

### `Geometry/Symplectic/HPrinciple/FormSpaces.lean`

The spaces, in the topology of the departure *Spaces of forms*:

- `nondegenerateForms I M : Set (Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I))`,
  `{ω | ω.IsNondegenerate}`, with `mem_nondegenerateForms`.
- `symplecticFormsInClass α`, `{ω | (tangentEquiv ω).IsSymplectic ∧
  tangentEquiv ω - α ∈ exactForms I M 2}`, with
  `mem_symplecticFormsInClass`, `symplecticFormsInClass_subset_nondegenerateForms`
  (by `isNondegenerate_tangentEquiv_iff`) and
  `symplecticFormsInClass_congr` (it depends on `α` only through its class).
- `cwType_nondegenerateForms` and `cwType_symplecticFormsInClass`
  (`hα : α ∈ closedForms I M 2`): for covering frames, a smooth isotopy
  `h : TauCeti.SmoothIsotopy (ContMDiffMap.id) j` and
  `IsCompact (closure (Set.range j))`, the space has `TauCeti.CWType`.
  Proof as in Decision 5: `Convex.cwType_inter` for the convex set (all
  forms, or the preimage under `tangentEquiv` of the coset
  `α + exactForms I M 2`) and the open set of
  `isOpen_setOfPred_forall_mem_nondegenerate` for `closure (Set.range j)`; then
  `TauCeti.CWType.of_comp_homotopic_id` with the inclusion,
  $\omega\mapsto j^*\omega$ (nondegenerate since the slices of `h` are
  embeddings between manifolds of one dimension; in the class by
  `mpullback_sub_mem_exactForms_of_homotopy`), and the homotopy of
  `continuous_tangentEquiv_symm_mpullback`. Metrizability is
  `metrizableSpace_frameTopology`, as `M` is second countable: `j`
  embeds it into the compact `closure (Set.range j)`.
- The docstrings say why the hypothesis on `j` is there: without it the
  spaces need not have CW type (Decision 5).

### `Geometry/Manifold/DifferentialForm/Components.lean`

Smooth forms of any degree on a manifold `M` and on its components, in
Tau Ceti's namespace like `DifferentialForm/Opens.lean`, whose restriction
along `Subtype.val` it uses:

- `ConnectedComponents.isConnected_opens`: each `c.opens` is connected,
  from Tau Ceti's `coe_opens_mk` and `isConnected_connectedComponent`. The
  rest of the API of the components as open sets is Tau Ceti's, in
  `TauCeti/Topology/ConnectedComponents.lean`: `mem_opens`, `coe_opens`,
  `coe_opens_mk`, `isClopen_opens`, `pairwise_disjoint_opens` and
  `iSup_opens`.
- `TauCeti.SmoothForm.ofDisjointCover`: for pairwise disjoint open sets
  `U i` with `IsOpenCover U` (for the components,
  `pairwise_disjoint_opens` and `IsOpenCover.mk iSup_opens`), a family of
  smooth `k`-forms on the open submanifolds `U i` glues to one on `M`. With
  `mpullback_subtype_val_ofDisjointCover` (its restriction to `U i` is
  the `i`-th form) and `ext_of_mpullback_subtype_val` (forms with the same
  restrictions to all members of an open cover are equal), this gives the
  linear equivalence `TauCeti.SmoothForm.disjointCoverEquiv` with the
  product over the `U i`.
- `TauCeti.SmoothForm.mem_closedForms_iff_forall_mpullback_subtype_val`
  and `mem_exactForms_iff_forall_mpullback_subtype_val`: a form is closed,
  or exact, exactly when each restriction to a `U i` is. Forward, as
  restriction commutes with `mextDerivₗ` (Tau Ceti's
  `SmoothForm.mextDerivₗ_mpullback`); back, for exactness, glue chosen
  primitives by `ofDisjointCover`.

### `Geometry/Symplectic/HPrinciple/Components.lean`

The spaces of `FormSpaces.lean` split over the components (Decision 5).
On each `c.opens` the frames are the `trivializationAt` of the bundle
of two-forms at its points, with their base sets; any covering frames
give the same topology.

- `restrictComponentsHomeomorph`: for covering frames on `M`, the map
  sending `ω` to the family of its restrictions to the components, as in
  `continuous_tangentEquiv_symm_mpullback_subtypeVal`, is a homeomorphism
  from the two-forms on `M` onto the product of the two-forms on the
  components. Its inverse is `tangentEquiv.symm ∘ ofDisjointCover` on the
  `tangentEquiv` forms. Continuity of the inverse: by
  `frameTopology_le_of_cover` it can be tested on frames of `M` whose
  domains each lie in one component, and each frame jet of a form on
  `M` on such a domain is a frame jet of its restriction to that
  component.
- `mem_nondegenerateForms_iff_forall_restrict` and
  `mem_symplecticFormsInClass_iff_forall_restrict`: `ω` is in the space on
  `M` (for `α`) exactly when each restriction is in the space on the
  component (for the restriction of `α`), stated for any open cover, pairwise
  disjoint for the second; nondegeneracy is pointwise, and
  closedness and exactness are the lemmas of
  `DifferentialForm/Components.lean`.
- `nondegenerateFormsHomeomorphPi` and `symplecticFormsInClassHomeomorphPi`:
  the restrictions of `restrictComponentsHomeomorph` to the two spaces,
  onto the products of the spaces on the components (with
  Tau Ceti's `Homeomorph.Set.univPi`), with the lemma that they carry
  `Set.inclusion` on `M` to the product of the inclusions on the
  components.

### `Geometry/Symplectic/HPrinciple/Parametric.lean`

For the spaces of `FormSpaces.lean`:

- `isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`: for
  covering frames `e U hU` and open `M`, the inclusion is a
  `ContinuousMap.IsWeakHomotopyEquivalence`, from the continuous engine
  with `P` a disc and `P₀` its boundary sphere, and `P` a point. Its
  docstring ends with the milestone line (Decision 5, `ERRATA.md`).
- `exists_homotopyEquiv_symplecticFormsInClass`: for covering frames, open
  `M`, `hα : α ∈ closedForms I M 2`, and, for every
  `c : ConnectedComponents M`, some `j : C^∞⟮I, c.opens; I, c.opens⟯`
  with `Nonempty (TauCeti.SmoothIsotopy (ContMDiffMap.id) j)` and
  `IsCompact (closure (Set.range j))`, `∃ e : symplecticFormsInClass α ≃ₕ
  nondegenerateForms I M, ⇑e.toFun = Set.inclusion
  (symplecticFormsInClass_subset_nondegenerateForms α)`. On each
  component, `isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`
  and the CW type of both spaces (`cwType_nondegenerateForms`,
  `cwType_symplecticFormsInClass`) give a homotopy equivalence by
  Whitehead's theorem, `hf.homotopyEquiv` with `homotopyEquiv_toFun`;
  then `ContinuousMap.HomotopyEquiv.piCongrRight`, conjugated by the
  homeomorphisms of `HPrinciple/Components.lean`
  (`Homeomorph.toHomotopyEquiv`, `ContinuousMap.HomotopyEquiv.trans`).
  The docstring says that an `M` that compresses as a whole satisfies the
  hypothesis (Decision 5). It carries no milestone line: for every open
  `M` the milestone is the weak equivalence above (Decision 5).

## What the part uses

*Smooth families* (merged files: `SmoothFamily/Basic.lean`,
`SmoothFamily/Poincare.lean`, `DeRham/FamilyPrimitive.lean`,
`Diffeotopy/Real.lean`), *Moser isotopy* (pullbacks of families,
`Geometry/Manifold/DifferentialForm/Pullback/Family.lean`), *Symplectic
vector bundles* (`VectorBundle/Symplectic/Basic.lean`, merged); Tau Ceti's
de Rham cohomology, Morse theory, diffeotopies and smooth isotopies, homotopy
groups, Whitehead's theorem, CW approximation and realizations of
simplicial complexes; Mathlib's calculus on normed spaces and partitions of
unity.

## Issues

Each is a few hundred lines; each issue's blockers come before it.

1. **Formal sections and wiggling.**
   `Analysis/Calculus/HolonomicApproximation/Basic.lean`.
2. **Holonomic approximation over a cube.**
   `Analysis/Calculus/HolonomicApproximation/Cube.lean`. Blocked by 1.
   The case $m=1$ is merged (`Segment.lean`); the induction is in the five
   building issues 2a to 2e that the file's section gives, in that order.
3. **Parametric relative holonomic approximation.**
   `Analysis/Calculus/HolonomicApproximation/Parametric.lean`. Blocked by 2.
   In the three building issues 3a to 3c that the file's section gives, in
   that order; the last, the continuous version, is issue 3 itself.
4. **Morse functions without top-index critical points**, in six building
   issues, in this order:
   - 4a. **Rays.** `Geometry/Manifold/ProperRay.lean`: `exists_rays`.
     Blocked by nothing.
   - 4b. **Vector bundles over the line are trivial.**
     `Geometry/Manifold/VectorBundle/Real.lean`:
     `Bundle.exists_diffeomorph_prod_of_real`. Blocked by nothing.
   - 4c. **Tubes around rays.** `Geometry/Manifold/TubularNeighborhood/Ray.lean`:
     `TauCeti.SmoothEmbedding.exists_rayTube`. Blocked by 4b.
   - 4d. **The model modification.** `Analysis/Calculus/Morse/HalfCylinder.lean`:
     `exists_nonneg_halfCylinder_hessian_pos`. Blocked by nothing. If it
     exceeds the size limit, the cutoff `β` and the profile `Λ` with their
     estimates become an issue of their own before it.
   - 4e. **Positive directions survive perturbation.**
     `Geometry/Manifold/Morse/PositiveDirection.lean`:
     `TauCeti.exists_strongCkControl_criticalHessian_pos`. Blocked by nothing.
   - 4f. **The theorem.** `Geometry/Manifold/Morse/OpenManifold.lean`:
     `TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt`. Blocked by
     4a, 4c, 4d and 4e.
5. **The band cores**, `Geometry/Manifold/Morse/Core/`, in these building
   issues, in this order:
   - 5a. **The structure.** `Morse/Core/Basic.lean`: `BandCore`, its API
     and `BandCore.ofNoCriticalPoint`. Blocked by nothing.
   - 5a′. **Band cores along diffeomorphisms.** `Morse/Core/Basic.lean`:
     `BandCore.ofDiffeomorph` and `cubes_ofDiffeomorph`. Blocked by 5a.
   - 5b. **The cube at a critical point.** `Morse/Core/Cube.lean`:
     `TauCeti.MorseChart.exists_cubeChart_unstableSet`. Blocked by nothing.
   - 5c. **Compression across one critical level.**
     `Morse/Core/Compression.lean`: `TauCeti.IsMorse.exists_bandCore`.
     Blocked by 5a, 5a′ and 5b.
   - 5d. **The band cores of an open manifold.** `Morse/Core/Exhaustion.lean`:
     `SymplecticGeometry.exists_isMorse_bandCore_seq`. Blocked by 4 and 5c.
6. **Smooth families of primitives over a manifold parameter**
   (`DifferentialForm/SmoothFamily/Map.lean`, `DeRham/SmoothFamily/`).
   This is the refactor that `design/compatible-symplectic-forms.md` plans
   as its issue 9: `PreservesSmoothFamilies` and
   `exists_isSmoothFamily_mextDerivₗ_eq` over any parameter manifold. It is
   one issue for both parts. Whichever building issue is split first
   creates it, and the other part uses that issue. Blocked by nothing.
7. **The handle-core lemma.** `Geometry/Symplectic/HPrinciple/HandleCore.lean`.
   Blocked by 6, for the family `β` of primitives, and by 3, for the
   working lemma; its building issues are in the order that the file's
   section gives. It settles step 0, the common collar, first. If it
   exceeds the size limit, the case $m=1$ becomes an issue of its own.
8. **The engine: one stage.** The approximation near a band core and the
   compressed path of one stage, in the first four files of
   `Geometry/Symplectic/HPrinciple/Relative/`, in these building issues,
   in this order:
   - 8a. **Cube coordinates and the relative set.**
     `Relative/CubeCoordinates.lean` without the diffeotopies:
     `BandCore.isLocalDiffeomorph_chart`, `BandCore.chartPartialDiffeomorph`,
     the readings of the formal datum and `BandCore.exists_relativeSet`;
     and `IsSmoothFamily.extendByZeroAlong` in
     `DifferentialForm/SmoothFamily/PartialDiffeomorph.lean`. Blocked by
     nothing.
   - 8b. **Diffeotopies along a chart.** `Diffeotopy/Extend.lean`:
     `TauCeti.extendDiffeotopyAlong`. Blocked by nothing.
   - 8c. **The continuous version's clauses at every point.** The `C`, `N`
     and displacement clauses of
     `exists_holonomic_approximation_continuous_family` for every point of
     `(Fin n → ℝ) × D`, as in the statement of its section, and
     `IsCompact.isOpen_setOfPred_forall_norm_sub_lt`, in
     `Topology/Compactness/Normed.lean`. Blocked by
     nothing.
   - 8d. **Approximation over a band core.** `Relative/CoreApproximation.lean`,
     both forms, with
     `exists_pos_forall_nondegenerate_sub_smul_of_continuousOn`.
     Blocked by 8a, 8b and 8c. If it exceeds the size limit, the
     continuous form becomes an issue of its own after it.
   - 8e. **The path of a stage.** `Relative/StagePath.lean`. Blocked by
     nothing.
   - 8f. **Smooth families and products in the frame topology.**
     `IsSmoothFamily.continuous_tangentEquiv_symm` and
     `continuous_tangentEquiv_symm_smul` in
     `VectorBundle/Symplectic/Topology.lean`. Blocked by nothing.
   - 8g. **The stage.** `Relative/Stage.lean`, both forms; this is issue 8
     itself. Blocked by 8d, 8e and 8f.
9. **The engine: the stages composed.** `Relative/Basic.lean`. Blocked by
   8.
10. **Existence and path components.**
    `Geometry/Symplectic/HPrinciple/OpenManifold.lean`. Blocked by 9.
11. **Design the CW type of spaces of forms** (a design issue, Decision 5).
    Blocked by nothing. Its building issues are 13 to 17.
12. **The parametric statement.**
    `Geometry/Symplectic/HPrinciple/Parametric.lean`. Blocked by 9 and by
    the building issues of 11 and of 18.
13. **CW type by domination.** `AlgebraicTopology/Homotopy/Domination.lean`.
    Blocked by nothing.
14. **The nerve of a partition of unity.**
    `AlgebraicTopology/SimplicialComplex/Realization/PartitionOfUnity.lean`.
    Blocked by nothing.
15. **Open subsets of convex sets have CW type.**
    `Analysis/LocallyConvex/CWType.lean`. Blocked by 13 and 14.
16. **Nondegeneracy on compact sets and pullback along isotopies in the
    frame topology.** `Geometry/Manifold/VectorBundle/Symplectic/Topology.lean`.
    Blocked by nothing.
17. **CW type of the spaces of forms.**
    `Geometry/Symplectic/HPrinciple/FormSpaces.lean`. Blocked by 15 and 16.
    Issue 12 is then blocked by it, as a building issue of 11.
18. **Design the homotopy equivalence component by component** (a design
    issue, Decision 5). Blocked by nothing. Its building issues
    are 19 to 21.
19. **Forms on the components.**
    `Geometry/Manifold/DifferentialForm/Components.lean`. Blocked by
    nothing.
20. **Restriction to an open subset in the frame topology.** The third
    lemma of `Geometry/Manifold/VectorBundle/Symplectic/Topology.lean`.
    Blocked by the building issue of 16 that creates the file.
21. **The spaces of forms split over the components.**
    `Geometry/Symplectic/HPrinciple/Components.lean`. Blocked by 17, 19
    and 20. Issue 12 is then blocked by it, as a building issue of 18.


## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.3.1 and Lemma 7.3.2, pp. 322–326.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002],
  Chapter 3, Theorem 4.7.4 and Theorems 10.2.1–10.2.2 (first edition).
* J. Milnor, *On spaces having the homotopy type of a CW-complex*,
  Trans. Amer. Math. Soc. 90 (1959), 272–280 (cited in full, as the plan's
  `references.bib` does not list it).
* J. Dugundji, *An extension of Tietze's theorem*, Pacific J. Math. 1
  (1951), 353–367 (cited in full, as above).
