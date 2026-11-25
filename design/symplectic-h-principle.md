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
  (`Topology/CWComplex/Classical/CWType.lean`). Neither library shows that a
  space of smooth sections has CW type.
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
   compresses $M$ into a neighbourhood of the core. The book's telescope
   over the handles of a Morse exhaustion is not used. Reasons: with
   infinitely many critical points, the book's induction needs a compatible
   choice of homotopies over the whole exhaustion, which the page flags as
   missing; and in the telescope, gluing the homotopy of a handle into the
   rest of $M$ by a cutoff breaks closedness at the parameters where the
   form is already symplectic, which the relative parametric statement
   needs. The compression route never glues forms: it only pulls back along
   embeddings into the neighbourhood where the approximation holds. So
   `Telescope.lean` of `DESIGN.md` is dropped, and the milestone's
   existence and path statements go in `OpenManifold.lean`, as corollaries
   (parameter spaces a point and $[0,1]$).
2. **The handle-core lemma is proved by the book's argument**, as a
   milestone on its own (`HandleCore.lean`). Nothing else in the part uses
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
   forms is a `ContinuousMap.IsWeakHomotopyEquivalence`, from the engine,
   and then the homotopy equivalence of the inclusion itself by Whitehead's
   theorem, `hf.homotopyEquiv` with `homotopyEquiv_toFun`, as the review of
   #3195 asked. That needs `TauCeti.CWType` for both spaces, which neither
   library has (Milnor's theorem that metrizable ANRs have CW type, and
   Dugundji's extension theorem for convex sets of metrizable locally convex
   spaces). It gets a design issue of its own, which the split of the
   building issue creates; if the nondegenerate forms, which are not open in
   the compact-open $C^\infty$ topology over a noncompact base, turn out not
   to have CW type by these means, that issue says so, and the milestone's
   last statement waits for it.
6. **Morse input.** The existence of a proper Morse function bounded below
   without critical points of index $\dim M$ on an open manifold is
   `Geometry/Manifold/Morse/OpenManifold.lean`; the core and its
   compression are `Geometry/Manifold/Morse/Core.lean`. Both are general
   differential topology, in Tau Ceti's namespace `TauCeti` where they are
   about `TauCeti.IsMorse`.

## Departures from `DESIGN.md`

- `Telescope.lean` is dropped (Decision 1); the milestone table and part 63
  name `OpenManifold.lean` and `Parametric.lean` for the first milestone.
- *Builds on* adds the merged *Symplectic vector bundles* (for
  `ContMDiffTwoForm`, its topology and `tangentEquiv`).
- Holonomic approximation is in coordinates (Decision 3), not on Tau Ceti's
  jet bundles.

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
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, IsMorse I g ∧ IsProperMap g ∧ BddBelow (Set.range g) ∧
      ∀ x ∈ criticalPoints I g, manifoldMorseIndex I g x < Module.finrank ℝ E
```

Route: start from `exists_isMorse_isProperMap_bddBelow`; the local maxima
form a closed discrete set; in each noncompact component join each of them
by a proper smooth ray to infinity, the rays disjoint and missing the other
critical points (locally finitely many choices in an exhaustion); in a
tubular neighbourhood of each ray, modify the function to one without
critical points that increases along the ray, keeping properness.

### `Geometry/Manifold/Morse/Core.lean`

A core of an open manifold, for the engine: a countable, locally finite
family of smooth open embeddings $\varphi_i$ of a neighbourhood of
$I^{m_i}\times I^{d-m_i}$ into $M$, $m_i<d=\dim M$, well-ordered so that
$\varphi_i(\partial I^{m_i}\times 0)$ lies in the union $A_{<i}$ of the
earlier cores $\varphi_j(I^{m_j}\times0)$, and, for every open
$U\supseteq A=\bigcup_iA_i$, a Tau Ceti `TauCeti.SmoothIsotopy` of
embeddings $M\to M$ from the identity to an embedding with image in $U$.
Its existence comes from the Morse function of `OpenManifold.lean` and a
pseudo-gradient flow. The precise structure (whether a `structure` with
these fields or a statement with them as an existential) and the
construction of the cores from the descending discs are not fixed here:
the split of the building issue creates a design issue for this file
before its building issue, because the descending discs of a pseudo-gradient
need not attach along earlier discs without a Morse–Smale condition, and
Eliashberg–Mishachev obtain their core from a triangulation, which neither
library has.

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
   (`HasFiniteGoodCover.nonempty_smoothCohomologySplitting`) and a linear
   primitive map on exact three-forms (`exists_primitiveMap_of_hasFiniteGoodCover`).
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
The proof is the book's: for $m=1$, the primitives
given near the two ends of the core are patched across a narrow band around
it with cutoff functions, the zig-zag immersion giving the band enough
length to keep the error small; then induction on $m$, with
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

Proof: the family $\alpha_\lambda$ of Decision 4; the formal primitive in
the charts of the core; parametric holonomic approximation over each cube in
the order of the core, relative to the earlier ones and to `P₀`, giving
closed $\sigma_\lambda$ in the class on a neighbourhood $U$ of the displaced
core with the straight segment from $\tau_\lambda$ to $\sigma_\lambda$
nondegenerate on $U$; the compression $h_s$ of `Core.lean` into $U$, after
conjugating by the displacing diffeotopy; the path $h_s^*\tau_\lambda$
followed by $h_1^*((1-s)\tau_\lambda+s\sigma_\lambda)$, nondegenerate since
embeddings are local diffeomorphisms
(`IsNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph`); the
class is kept by `mpullback_sub_mem_exactForms_of_homotopy`. On `P₀` the approximation is
the identity, so the second half of the path is constant and the first
stays symplectic. Since this is long, the issue splits it into the
construction of $\sigma$ near the core and the compression step.

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

### `Geometry/Symplectic/HPrinciple/Parametric.lean`

The spaces, in the topology of the departure *Spaces of forms*:

- `nondegenerateForms I M : Set (Bundle.ContMDiffTwoForm I ⊤ E (TangentSpace I))`,
  `{ω | ω.IsNondegenerate}`, with `mem_nondegenerateForms`.
- `symplecticFormsInClass α`, `{ω | (tangentEquiv ω).IsSymplectic ∧
  tangentEquiv ω - α ∈ exactForms I M 2}`, with
  `mem_symplecticFormsInClass`, `symplecticFormsInClass_subset_nondegenerateForms`
  (by `isNondegenerate_tangentEquiv_iff`) and
  `symplecticFormsInClass_congr` (it depends on `α` only through its class).
- `isWeakHomotopyEquivalence_inclusion_symplecticFormsInClass`: for
  covering frames `e U hU` and open `M`, the inclusion is a
  `ContinuousMap.IsWeakHomotopyEquivalence`, from the continuous engine
  with `P` a disc and `P₀` its boundary sphere, and `P` a point.
- The milestone: `∃ e : symplecticFormsInClass α ≃ₕ nondegenerateForms I M,
  ⇑e.toFun = Set.inclusion (symplecticFormsInClass_subset_nondegenerateForms α)`,
  from Whitehead's theorem once both spaces have `TauCeti.CWType`
  (Decision 5). Its docstring ends with the milestone line.

## What the part uses

*Smooth families* (merged files: `SmoothFamily/Basic.lean`,
`SmoothFamily/Poincare.lean`, `DeRham/FamilyPrimitive.lean`,
`Diffeotopy/Real.lean`), *Moser isotopy* (pullbacks of families,
`Geometry/Manifold/DifferentialForm/Pullback/Family.lean`), *Symplectic
vector bundles* (`VectorBundle/Symplectic/Basic.lean`, merged); Tau Ceti's
de Rham cohomology, Morse theory, diffeotopies and smooth isotopies, homotopy
groups and Whitehead's theorem; Mathlib's calculus on normed spaces.

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
4. **Morse functions without top-index critical points.**
   `Geometry/Manifold/Morse/OpenManifold.lean`.
5. **Design the core of an open manifold** (a design issue: the structure of
   `Geometry/Manifold/Morse/Core.lean` and its issues). Blocked by nothing;
   its building issues are blocked by 4.
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
8. **The engine near the core.** The construction of $\sigma_\lambda$ in
   `Geometry/Symplectic/HPrinciple/Engine.lean`. Blocked by 3 and by the
   building issues of 5.
9. **The engine: compression.** The rest of `Engine.lean`. Blocked by 8.
10. **Existence and path components.**
    `Geometry/Symplectic/HPrinciple/OpenManifold.lean`. Blocked by 9.
11. **Design the CW type of spaces of forms** (a design issue, Decision 5).
    Blocked by nothing.
12. **The parametric statement.**
    `Geometry/Symplectic/HPrinciple/Parametric.lean`. Blocked by 9 and by
    the building issues of 11.


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
