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
2. **The handle-core lemma is proved by the book's argument**, as a
   milestone on its own (`HandleCore.lean`), except for $m=1$, where the
   cube is compressed towards the core and the contraction along the fibres
   gives the primitive, in place of the book's patching and zig-zag
   (`HandleCore/OneDimensional.lean`). Nothing else in the part uses
   it. It is stated for forms on the whole model space, with its conditions
   on the cube and near the attaching faces, so that no form on a subset is
   needed.
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
   continuous into the `frameTopology` (needed by homotopy groups) and, when
   `P` is a manifold and the family is an `IsSmoothFamily`, for smooth
   families with smooth output (needed by the path statement). The closed
   representative of the class is not fixed but a family $\alpha_\lambda$ in
   the class with
   $\alpha_\lambda=\tau_\lambda$ on `P₀`, an extension of `τ` from `P₀` into
   the convex set of closed representatives of $a$: by an explicit formula
   for the parameter spaces used ($\alpha_t=(1-t)\omega_0+t\omega_1$ on
   $[0,1]$, a radial formula on a disc relative to its boundary sphere), or
   by Dugundji's extension theorem in general. On `P₀` the formal primitive
   is then zero, hence holonomic.
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
     point evaluation is continuous. Sending $(\varepsilon_k)$ to the form
     equal to $\varepsilon_k\omega_0$ on the $k$-th copy is a continuous
     map $c$ back, since a compact set meets only finitely many copies, and
     it lands
     in the symplectic forms of class $0$; and $s\circ c=\mathrm{id}$. If
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
     restrictions. (This is where a compact set meeting only finitely
     many components enters.) Nondegeneracy and closedness hold on `M`
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

The holonomic approximation theorem over a cube, by induction on `m`, as in
[EliashbergMishachev2002], Chapter 3:

```lean
theorem exists_holonomic_approximation_cube {m k : ℕ} (hk : 0 < k)
    {f : D → F} {G : D → D →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : ContDiff ℝ ∞ G) {U : Set D} (hU : IsOpen U)
    (hUf : ∀ x ∈ U, fderiv ℝ f x = G x) (hU' : Metric.sphere 0 1 ×ˢ {0} ⊆ U)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (h : TauCeti.Diffeotopy 𝓘(ℝ, D) ∞ D) (f' : D → F) (V : Set D),
      -- h is δ-small and fixed near Metric.sphere 0 1 ×ˢ {0}
      IsOpen V ∧ h.timeSlice 1 '' (Metric.closedBall 0 1 ×ˢ {0}) ⊆ V ∧
      ContDiff ℝ ∞ f' ∧ (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ‖fderiv ℝ f' x - G x‖ < ε) ∧
      ∃ U' ∈ 𝓝ˢ (Metric.sphere 0 1 ×ˢ {0}), EqOn f' f U'
```

The sketch abbreviates the smallness and support clauses of the
diffeotopy, which the issue
writes out. The condition `0 < k` is the positive codimension.

### `Analysis/Calculus/HolonomicApproximation/Parametric.lean`

[EliashbergMishachev2002], Theorem 4.7.4, in coordinates: the same for a
family $(f_\lambda,G_\lambda)$ over a compact parameter space `P`, continuous
in `P` with all space derivatives (and, in the smooth version, smooth on
`P × D` for a parameter manifold `P`), with a diffeotopy and approximation
depending in the same way on $\lambda$, and with $h_\lambda=\mathrm{id}$,
$f'_\lambda=f_\lambda$ for $\lambda$ in a closed `P₀` on which
$(f_\lambda,G_\lambda)$ is holonomic on a neighbourhood of the cube.

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
a point of `U` outside `F (c j + 2)`
(`TauCeti.exists_diffeotopy_final_comp_eq_of_isPreconnected`). The arc
`α := Ψ '' σ` is straight in the chart `φ ∘ Ψ⁻¹` along its whole length,
and joins the ray smoothly at `x`.

When the stage's arcs are built, choose `c (j + 1)` in
`(c j + 1, c j + 2)` that is a regular value of `h` and of `h ∘ α` for each
arc `α` of the stage (Sard for `h`, and for the finitely many functions
`h ∘ α` of one variable `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).
Then each `α` meets `{h = c (j + 1)}` at finitely many parameters, crossing
it, so the parameters where `α` lies outside `K (j + 1)` form finitely many
intervals, the last one ending at the far end, which lies outside
`F (c j + 2) ⊇ K (j + 1)`. Cut `α` at a parameter just after the start of
the first such interval (at once, for a new ray that starts outside
`K (j + 1)`), close enough that the cut arc stays in
`interior (F (c j + 2))`. The cut end is still straight in `φ ∘ Ψ⁻¹`, so
the next arc continues it smoothly.

Why (R) holds after the stage: an arc of stage `j` lies outside `K j`,
leaves `K (j + 1)` only in its final piece, and lies in
`interior (K (j + 2))`, since `F (c j + 2) ⊆ interior (K (j + 2))`. So
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
structure BandCore (g : M → ℝ) (a₀ a b : ℝ) where
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
when `g` is proper with no critical value in `[a₀, b]`. Its compression is
the flow of a field that vanishes near `{g ≤ a}`, lowers `g` at unit speed
through the rest of the band and is cut off above `b`, built as in Tau Ceti's
`exists_flow_apply_eq_sub` (`Geometry/Manifold/Morse/Deformation.lean`).

#### `Morse/Core/Cube.lean`

The cube at one critical point, in the namespace `TauCeti`. Tau Ceti's flow
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
`TauCeti.exists_cubeChart_unstableSet` gives a smooth open embedding
`φ : D m → M` with `φ 0 = p`, sending the cube into the unstable set of `p`
for this flow and above `a₀`, and its sphere below `a`, such that every point
of that unstable set at level at least `a` is in the image of the cube.

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

The cubes are those of `Cube.lean` at the finitely many critical points of
the level `v` (`TauCeti.IsMorse.finite_criticalPoints_inter`), all for the
one field `X`: by `hcrit` no critical value lies in `[a₀, v)`, which is the
hypothesis of `TauCeti.exists_cubeChart_unstableSet` at each of them, the
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
theorem TauCeti.exists_isMorse_bandCore_seq (hE : Module.finrank ℝ E ≠ 1)
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
from `BddBelow (Set.range g)` in that theorem, or
`BandCore.ofNoCriticalPoint` where the interval holds none.

**What the engine needs beyond the sketch of `Cube.lean`.** The engine
approximates over each cube of a band core relative to the open set where
its form is already good. That set contains the part of the cube below `a`,
which has interior in the cube, and not only a neighbourhood of the boundary
sphere, to which the sketch of `exists_holonomic_approximation_cube` is
relative. Eliashberg–Mishachev's relative form, relative to a closed set near
which the datum is holonomic, is what the engine uses; it follows from the
sketched one by subdividing the cube finely.

### `Geometry/Symplectic/HPrinciple/HandleCore.lean`

The second milestone. With $m+k=2n$, $1\le m$, $1\le k$ (so $m<2n$),
`D := (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, the cube
`Q := Metric.closedBall (0 : D) 1`, the attaching faces
`A := Metric.sphere (0 : Fin m → ℝ) 1 ×ˢ Metric.closedBall 0 1`, and a parameter space a finite-dimensional
normed space `L` with a compact `K ⊆ L`:

```lean
theorem exists_homotopy_exact_of_exact_near_attaching
    {τ : L → SmoothTwoForm 𝓘(ℝ, D) D} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ λ ∈ K, ∀ x ∈ Q, ((τ λ).bilinFormAt x).Nondegenerate)  -- on the cube
    {β : L → SmoothForm 𝓘(ℝ, D) D ℝ 1} (hβ : IsSmoothFamily 𝓘(ℝ, L) β)
    {W : Set D} (hW : IsOpen W) (hAW : A ⊆ W)
    (hτβ : ∀ λ ∈ K, ∀ x ∈ W, mextDerivₗ 1 (β λ) x = τ λ x) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, D) D,
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ λ, σ (λ, 0) = τ λ) ∧
      (∀ λ ∈ K, ∀ t, ∀ x ∈ Q, ((σ (λ, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ A, ∀ λ ∈ K, ∀ t, ∀ x ∈ W', σ (λ, t) x = τ λ x) ∧
      (∃ V ∈ 𝓝ˢ Q, ∀ λ ∈ K, ∃ γ : SmoothForm 𝓘(ℝ, D) D ℝ 1,
        ∀ x ∈ V, mextDerivₗ 1 γ x = σ (λ, 1) x) ∧
      ∀ λ ∈ K, (∃ V ∈ 𝓝ˢ Q, ∃ γ, ∀ x ∈ V, mextDerivₗ 1 γ x = τ λ x) →
        ∀ t, ∃ V ∈ 𝓝ˢ Q, ∃ γ, ∀ x ∈ V, mextDerivₗ 1 γ x = σ (λ, t) x
```

This is the shape of the working lemma, not the final text. Its collar `W`
is one open set for all of `K`, and its primitives `β` depend smoothly on
`λ`. The milestone asks for neither, and in its conclusion the homotopy
need only be fixed near `A` for each `λ` separately:

```lean
theorem exists_homotopy_exact_of_forall_exact_near_attaching
    {τ : L → SmoothTwoForm 𝓘(ℝ, D) D} (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ λ ∈ K, ∀ x ∈ Q, ((τ λ).bilinFormAt x).Nondegenerate)
    (hex : ∀ λ ∈ K, ∃ W ∈ 𝓝ˢ A, ∃ β : SmoothForm 𝓘(ℝ, D) D ℝ 1,
      ∀ x ∈ W, mextDerivₗ 1 β x = τ λ x) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, D) D,
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ λ, σ (λ, 0) = τ λ) ∧
      (∀ λ ∈ K, ∀ t, ∀ x ∈ Q, ((σ (λ, t)).bilinFormAt x).Nondegenerate) ∧
      (∀ λ ∈ K, ∃ W' ∈ 𝓝ˢ A, ∀ t, ∀ x ∈ W', σ (λ, t) x = τ λ x) ∧
      -- the last two clauses as in the working lemma
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
For $m=1$ the proof differs from the book's: the cube is compressed
towards the core, near which the contraction along the fibres gives one
primitive of a form close to `τ`, so no patching and no zig-zag are needed
(`HandleCore/OneDimensional.lean`); then induction on $m$, with
the cutoffs and the nondegeneracy bounds chosen uniformly over `K` by
compactness, and the attaching collars fixed once in the working lemma
(the neighbourhoods `W` and `W'`). The docstring of
`exists_homotopy_exact_of_forall_exact_near_attaching` ends with "Milestone:
*Relative extension of exact symplectic forms over a handle core*."

### `Geometry/Symplectic/HPrinciple/Engine.lean`

The parametric relative theorem, by Decision 1, for an open `M` of
dimension $2n$:

- *Continuous version.* Given a compact Hausdorff `P`, closed `P₀ ⊆ P`, a
  closed representative `α` of `a`, and `τ : C(P, X)` where
  `X := {ω : Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I) // ω.IsNondegenerate}`
  with the topology of a covering frame system (as *Symplectic vector
  bundles* installs it, `letI` and `hcover`), with `tangentEquiv (τ λ)`
  symplectic and `tangentEquiv (τ λ) - α ∈ exactForms I M 2` for `λ ∈ P₀`:
  there is `H : C(P × unitInterval, X)` with `H (λ, 0) = τ λ`, `H (λ, t)`
  symplectic in the class for `λ ∈ P₀` and all `t`, and `H (λ, 1)`
  symplectic in the class for all `λ`.
- *Smooth version.* The same for `τ : P → SmoothTwoForm I M` an
  `IsSmoothFamily` over a compact parameter manifold `P` (the uses are a
  point and `unitInterval`), with `H` an `IsSmoothFamily` over
  `P × unitInterval`.

Proof, one band core of `TauCeti.exists_isMorse_bandCore_seq` at a time
(`Morse/Core/`), with the family $\alpha_\lambda$ of Decision 4. Stage $k$
starts from nondegenerate $\omega^k_\lambda$ ($\omega^0=\tau$) and one-forms
$\beta^k_\lambda$ with $\omega^k_\lambda=\alpha_\lambda+d\beta^k_\lambda$ on a
neighbourhood $N_k$ of $\{g\le e_k\}$, and on all of $M$ for $\lambda\in P_0$.
The formal primitive of $\omega^k_\lambda-\alpha_\lambda$ in the cube charts is
then holonomic on $N_k$ and on `P₀`. Parametric holonomic approximation over
each cube of the band core in turn (they are disjoint), relative to $N_k$, as
noted at the end of `Morse/Core/`, and to `P₀`, gives $\beta'_\lambda$, equal
to $\beta^k_\lambda$ away from a neighbourhood of the cubes that lies above
$d_k$, and an open $U$ around $\{g\le e_k\}$ and the displaced cubes on which
every $(1-s)\omega^k_\lambda+s\sigma_\lambda$ is nondegenerate, where
$\sigma_\lambda=\alpha_\lambda+d\beta'_\lambda$ is closed in the class. The
band core's compression, conjugated by the displacing diffeotopy, gives an
isotopy $h_s$ fixed near $\{g\le e_k\}$ with $h_1(\{g\le e_{k+1}\})\subseteq U$.
For a cutoff $\chi$ supported in $U$ and equal to $1$ near
$h_1(\{g\le e_{k+1}\})$, the stage is the path $h_s^*\omega^k_\lambda$
followed by $h_1^*(\omega^k_\lambda+s\chi(\sigma_\lambda-\omega^k_\lambda))$,
nondegenerate since embeddings are local diffeomorphisms
(`IsNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph`). Its end
$\omega^{k+1}_\lambda$ is $\alpha_\lambda+d\beta^{k+1}_\lambda$ near
$\{g\le e_{k+1}\}$, with $\beta^{k+1}_\lambda$ the sum of
$h_1^*\beta'_\lambda$ and the primitive of
$h_1^*\alpha_\lambda-\alpha_\lambda$ given by the isotopy, which vanishes
where $h_s$ is the identity (the class is kept as in
`mpullback_sub_mem_exactForms_of_homotopy`). A stage changes nothing near
$\{g\le d_k\}$, and $d_k\to\infty$, so the stages, run on the times
$[1-2^{-k},1-2^{-k-1}]$, are constant near each compact set for times close
to $1$; they compose to the homotopy $H$, whose end is closed in the class
and nondegenerate. On `P₀` the approximation is the identity, so the second
half of each stage is constant and the first stays symplectic in the class.
Since this is long, the issue splits it into one stage and the composition
of the stages.

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

- `Bundle.ContMDiffTwoForm.isOpen_setOf_forall_mem_nondegenerate`: for a
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
  `isOpen_setOf_forall_mem_nondegenerate` for `closure (Set.range j)`; then
  `TauCeti.CWType.of_comp_homotopic_id` with the inclusion,
  $\omega\mapsto j^*\omega$ (nondegenerate since the slices of `h` are
  embeddings between manifolds of one dimension; in the class by
  `mpullback_sub_mem_exactForms_of_homotopy`), and the homotopy of
  `continuous_tangentEquiv_symm_mpullback`. Metrizability is
  `isCompletelyMetrizableSpace_frameTopology`, as `M` is σ-compact, hence
  Lindelöf.
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
  `frameTopology_eq_of_covers` the frame domains on `M` can be cut down
  to their intersections with the components, and each frame jet of a
  form on `M` on such a domain is a frame jet of its restriction to that
  component.
- `mem_nondegenerateForms_iff_forall_restrict` and
  `mem_symplecticFormsInClass_iff_forall_restrict`: `ω` is in the space on
  `M` (for `α`) exactly when each restriction is in the space on the
  component (for the restriction of `α`); nondegeneracy is pointwise, and
  closedness and exactness are the lemmas of
  `DifferentialForm/Components.lean`.
- `nondegenerateFormsHomeomorphPi` and `symplecticFormsInClassHomeomorphPi`:
  the restrictions of `restrictComponentsHomeomorph` to the two spaces,
  onto the products of the spaces on the components (with
  `Equiv.subtypePiEquivPi`), with the lemma that they carry
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
   If it exceeds the size limit, the case $m=1$ becomes an issue of its own
   before the induction.
3. **Parametric relative holonomic approximation.**
   `Analysis/Calculus/HolonomicApproximation/Parametric.lean`. Blocked by 2.
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
5. **The band cores**, `Geometry/Manifold/Morse/Core/`, in four building
   issues, in this order:
   - 5a. **The structure.** `Morse/Core/Basic.lean`: `BandCore`, its API
     and `BandCore.ofNoCriticalPoint`. Blocked by nothing.
   - 5b. **The cube at a critical point.** `Morse/Core/Cube.lean`:
     `TauCeti.exists_cubeChart_unstableSet`. Blocked by nothing.
   - 5c. **Compression across one critical level.**
     `Morse/Core/Compression.lean`: `TauCeti.IsMorse.exists_bandCore`.
     Blocked by 5a and 5b.
   - 5d. **The band cores of an open manifold.** `Morse/Core/Exhaustion.lean`:
     `TauCeti.exists_isMorse_bandCore_seq`. Blocked by 4 and 5c.
6. **Smooth families of primitives over a manifold parameter**
   (`DifferentialForm/SmoothFamily/Map.lean`, `DeRham/SmoothFamily/`).
   This is the refactor that `design/compatible-symplectic-forms.md` plans
   as its issue 9: `PreservesSmoothFamilies` and
   `exists_isSmoothFamily_mextDerivₗ_eq` over any parameter manifold. It is
   one issue for both parts. Whichever building issue is split first
   creates it, and the other part uses that issue. Blocked by nothing.
7. **The handle-core lemma.** `Geometry/Symplectic/HPrinciple/HandleCore.lean`.
   Blocked by 6, for the family `β` of primitives. It settles step 0, the
   common collar, first. If it exceeds the size limit, the case $m=1$
   becomes an issue of its own.
8. **The engine: one stage.** The approximation near a band core and the
   compressed path of one stage, in
   `Geometry/Symplectic/HPrinciple/Engine.lean`, with the relative form of
   holonomic approximation noted at the end of `Morse/Core/`. Blocked by 3
   and by the building issues of 5.
9. **The engine: the stages composed.** The rest of `Engine.lean`. Blocked
   by 8.
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
