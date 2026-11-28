# Coupling forms

This is the detailed design of part 53 of `DESIGN.md`, *Coupling forms*. It
covers three milestones of `atlas/symplectic-fibrations.md`, §6.4: *Coupling
form of a symplectic connection*, *Compatible symplectic forms for fibrations
with simply connected fibre* and *Curvature identity for symplectic
connections*. They follow McDuff–Salamon [McDuffSalamon2017], §6.4 (Theorem
6.4.1, Remark 6.4.2, Corollary 6.4.3, Lemma 6.4.8, Exercise 6.4.9 and
equations (6.4.3)–(6.4.5)) with the authors' errata [McDuffSalamon2019Errata],
and Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], §§1.3–1.5
(equations (1.11)–(1.14), Theorems 1.4.1 and 1.4.3), whose sign conventions
the page uses.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. Statements about Mathlib, Tau Ceti and the library were checked
against the versions pinned when this file was written (Tau Ceti
`c9d170eed5a8`).

## What other parts give, and under which names

The parts this one builds on have design files: *Parallel transport*
(`design/parallel-transport.md`) and *Flux homomorphism*
(`design/flux-homomorphism.md`), merged, and *Symplectic fibrations*
(#2445) and *Integration over the fibre* (#2441), under review when this
file was written. This file uses the names that those designs give, listed
here, and
its building issues use the names of the merged designs and code where they
differ.

- *Symplectic fibrations*: a smooth atlas `A` of `π : M → B` with fibre `F`
  and charts `A.trivAt b`, smooth with smooth inverses (`hA`); symplectic
  atlases, `A.HasStructureGroup (TauCeti.SmoothForm.diffeomorphStabilizer σ)`;
  fibre inclusions `Bundle.Trivialization.fiberInclusionMap e hb`,
  $v\mapsto e^{-1}(b,v)$; the predicates `A.RestrictsTo σ τ` ($\iota_b^*\tau=\sigma_b$),
  `τ.IsVerticallyNondegenerate IB π` and `τ.IsVerticallyClosed π`; the connection
  `τ.horizontalDistribution π` ($\mathrm{Ver}^\tau$), an Ehresmann connection
  by `IsVerticallyNondegenerate.isEhresmannConnection`, with
  `horizontalDistribution_eq_iff`; symplectic connections
  `hD.IsSymplectic A σ`; connection two-forms and their existence,
  `exists_restrictsTo_isVerticallyClosed` and
  `IsSymplectic.exists_restrictsTo_isVerticallyClosed`; and the local form
  of `LocalForm.lean` (`eq_verticalForm_add_sum`, `isVerticallyClosed_iff_local`,
  `horizontalLift_local`).
- *Parallel transport*: Tau Ceti's `TauCeti.IsEhresmannConnection` with
  `horizontalLift`; `hD.horizontalLiftField`; `hD.parallelTransport γ s t`
  along smooth curves `γ : ℝ → B`; its reading in charts
  `hD.parallelTransportIn e e' γ s t` with `parallelTransportInDiffeomorph`
  and `parallelTransportIn_coordChange`; smoothness in a family of curves,
  `exists_contMDiff_parallelTransport_param`; and the curvature
  `hD.curvature v₁ v₂` $=[v_1^\sharp,v_2^\sharp]-[v_1,v_2]^\sharp$ with
  `curvature_mem_ker` and `curvature_congr`.
- *Integration over the fibre*: for an atlas with an oriented structure
  group (`hA' : A.IsOriented o`), the operator `A.fiberIntegral hA'` from
  forms of degree `r + m` on `M` to forms of degree `r` on `B`, with
  `fiberIntegral_apply_of_lift` (the value at `b` computed from any lifts of
  the base vectors), `fiberIntegral_mextDeriv`, and the product operator
  `prodFiberIntegral` with `mpullback_subtypeVal_fiberIntegral`.
- *Flux homomorphism*: `Family.lean`,
  `TauCeti.Diffeotopy.isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup`
  (McDuff–Salamon, Proposition 10.2.12).

## Setting and notation

- **Manifolds.** As in *Symplectic fibrations*: `B`, `M` and `F` modelled
  by `IB`, `IM` and `IF` on finite-dimensional spaces, boundaryless and
  Hausdorff, with `[IsManifold _ ∞ _]`. The fibre has dimension `2 * k`
  (`finrank ℝ EF = 2 * k`), carries `σ : SmoothTwoForm IF F` with
  `σ.IsSymplectic`, and the atlas is symplectic. The page's standing
  hypotheses are `[CompactSpace M]` and `[ConnectedSpace F]`.
- **Compact fibre.** Parallel transport and the fibre integral need a
  compact `F`. When `B` is nonempty this follows from a compact `M`, since a
  fibre inclusion is a closed embedding onto a fibre; when `B` is empty,
  `M` is empty and every statement below holds trivially. So the milestones
  take no hypothesis on `F` beyond the page's.
- **Orientation.** The fibre integral uses the symplectic orientation
  `o := hσ.isNondegenerate.volumeOrientation` of `F`. A symplectic atlas is
  oriented for it, since a diffeomorphism that preserves `σ` preserves its
  volume form; this is a new lemma
  `TauCeti.SmoothForm.diffeomorphStabilizer_le_orientationPreservingSubgroup`
  in the library's `Geometry/Symplectic/Manifold/Volume.lean`.
- **Holonomy.** As *Parallel transport* decides, the holonomy around a loop
  `γ` at `b`, read in a chart `e` of `A` at `b`, is
  `hD.parallelTransportInDiffeomorph e e γ 0 1`, a diffeomorphism of `F`; no
  definition is added for it.
- **Signs.** The bracket is Mathlib's `VectorField.mlieBracket`, the page's.
  Tau Ceti's `TauCeti.SmoothTwoForm.IsHamiltonianVectorField σ f X` is
  $\iota_X\sigma=df$, the book's sign, so the page's $X_H$ is Tau Ceti's
  field of $-H$. The page's statement that $\Omega_\Gamma(v_1,v_2)$ is the
  Hamiltonian field of $-\tau(v_1^\sharp,v_2^\sharp)$ reads, in Tau Ceti's
  terms, that on each fibre the restriction of $\tau(v_1^\sharp,v_2^\sharp)$
  generates $\Omega_\Gamma(v_1,v_2)$ in Tau Ceti's sign. Statements below
  use Tau Ceti's predicate, so no sign is changed by hand.

## Decisions

These settle the points that part 53 of `DESIGN.md` leaves to this file.

- **The proof of 2 ⇒ 1 is local, with the page's corrected normalization
  applied globally.** In a symplectic chart over a coordinate patch, the
  closed form is built from the local form of a connection two-form: the
  one-forms $\alpha_i$ are fixed by the connection, and the functions
  $f_{ij}$ are primitives along the fibre of the one-forms that closedness
  prescribes, which exist because the curvature is Hamiltonian. The
  normalization is not imposed on the $f_{ij}$, which is the error the page
  notes in the book's first proof; it is imposed afterwards on each local
  form, as fibrewise mean value zero of $\tau(v_1^\sharp,v_2^\sharp)$, which
  is equivalent to $\int_F\tau^{k+1}=0$ and does not depend on the chart.
  Normalized local forms agree on overlaps by uniqueness, so they glue.
  The second route, Guillemin–Lerman–Sternberg's and the book's second
  proof, which works with vector fields whose flows preserve the fibre
  forms, is not taken.
- **Exercises 6.4.4, 6.4.5 and 6.4.7 are not needed.** They serve only the
  second proof, which is not taken. What the chosen route needs from the
  curvature is the identity of Lemma 6.4.8 (in the page's form) and the
  equivalence of Exercise 6.4.9, both proved here.
- **Uniqueness is pointwise.** Two closed connection two-forms with the
  same connection differ by a closed form $\delta$ that vanishes on vertical
  vectors. The invariant formula for $d\delta$ on two horizontal lifts and a
  vertical field shows that $\delta(v_1^\sharp,v_2^\sharp)$ is constant
  along each fibre; since fibres are connected, $\delta$ is basic, and
  $\beta$ is its descent `TauCeti.SmoothForm.descendedForm` along the
  surjective submersion $\pi$, smooth by construction and closed because
  $\delta$ is.
- **Holonomy along a disc is an isotopy, without a trivialization over the
  disc.** A loop that bounds a disc is the end of Tau Ceti's smooth disc
  `TauCeti.IsSmoothDisc IB γ D` (`Geometry/Manifold/DifferentialForm/Integration/Disc.lean`):
  $D(0,\cdot)$ is constant, $D(1,\cdot)=\gamma$, and $D(s,0)=b$. The
  holonomies of the loops $D(s,\cdot)$, read in one chart at $b$, form a
  symplectic isotopy of $F$ from the identity to the holonomy of $\gamma$.
  The periods of its velocity are integrals of $d\tau$ over the swept
  cylinders, from Tau Ceti's rectangle integrals. No pull-back fibration
  over the disc and no symplectic trivialization over it are built, so
  `Holonomy.lean` departs from the wording of part 53 of `DESIGN.md`, which
  is corrected in the same pull request.
- **Theorem 10.2.5 is replaced by Proposition 10.2.12.** If the curvature
  is Hamiltonian, the velocity of that isotopy is Hamiltonian at every time,
  so the isotopy is Hamiltonian by the library's criterion
  `TauCeti.Diffeotopy.isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`
  and the holonomy lies in `TauCeti.SmoothForm.hamiltonianGroup σ`; a
  zero-flux theorem is not needed. Conversely, if every holonomy around a
  disc is Hamiltonian, the isotopy is a path in $\mathrm{Ham}$, hence
  Hamiltonian by Proposition 10.2.12 (*Flux homomorphism*, `Family.lean`,
  whose proof uses that the flux group is countable, as the page's route
  does). So the part uses `Family.lean` of *Flux homomorphism*, and
  `Kernel.lean` and `Countable.lean` only through it; `DESIGN.md` is
  corrected.
- **Contractible loops.** The page calls a loop contractible when it
  bounds a smooth map of the closed disc. That is the predicate
  `BoundsSmoothDisc` below; the proofs pass to Tau Ceti's `IsSmoothDisc`
  by `BoundsSmoothDisc.exists_isSmoothDisc`.
- **Names.** `IsCouplingForm` is taken by *Minimal coupling*; the coupling
  form of a connection is characterized by the predicate
  `TauCeti.IsEhresmannConnection.IsCouplingTwoForm`. No definition chooses
  it: the milestone gives existence and uniqueness, and later parts use
  them.
- **Flatness and foliations.** Nothing here needs flat connections, so
  neither `TauCeti.IsInvolutiveDistribution` nor the foliation API of
  *Coisotropic reduction* is used; *Parallel transport* states flatness.
  No circle action occurs, so `circlePeriodOneGenerator` is not used.

## Files

### `Geometry/Symplectic/Fibration/Holonomy.lean`

Holonomy around loops that bound discs. About 450 lines.

- `BoundsSmoothDisc IB γ`, for `γ : ℝ → B`: some `w : ℂ → B` with
  `ContMDiffOn 𝓘(ℝ, ℂ) IB ∞ w (Metric.closedBall 0 1)` has
  `w (Circle.exp (2 * π * t)) = γ t` for every `t`. With
  `boundsSmoothDisc_const`, and `BoundsSmoothDisc.exists_isSmoothDisc`: for
  `h : BoundsSmoothDisc IB γ`, some `D` has `TauCeti.IsSmoothDisc IB h.path D`,
  where `h.path` is `γ` as a `Path (γ 0) (γ 0)`; take
  $D(s,t)=w\big((1-\varphi(s))+\varphi(s)e^{2\pi it}\big)$ for a smooth
  $\varphi\colon\mathbb R\to[0,1]$ with $\varphi(0)=0$ and $\varphi(1)=1$.
  Each loop $D(s,\cdot)$ of any smooth disc again bounds a disc
  ($z\mapsto D(s\,\psi(|z|),\arg z/2\pi)$ with $\psi=0$ near $0$ and
  $\psi(1)=1$), `BoundsSmoothDisc.of_isSmoothDisc_slice`.
- `TauCeti.IsEhresmannConnection.HasHamiltonianDiscHolonomy hD A σ`: for
  every `γ` with `BoundsSmoothDisc IB γ` and every chart `e = A.trivAt b`
  with `γ 0 ∈ e.baseSet`, some `φ ∈ TauCeti.SmoothForm.hamiltonianGroup σ`
  has `⇑φ = hD.parallelTransportIn e e γ 0 1`; for `π` proper and a smooth
  atlas, `hasHamiltonianDiscHolonomy_iff` states it as
  `hD.parallelTransportInDiffeomorph e e γ 0 1 ∈ hamiltonianGroup σ`. With
  `hasHamiltonianDiscHolonomy_iff_forall_exists`: for a symplectic atlas
  one chart per loop suffices, by `parallelTransportIn_coordChange` and Tau
  Ceti's `TauCeti.SmoothForm.mul_mul_inv_mem_hamiltonianGroup`.
- `TauCeti.IsEhresmannConnection.holonomyDiffeotopy hD hf hfp he he_symm hΔ hx`,
  for `π` smooth and proper, a smooth disc `Δ` with centre `x` and a smooth
  trivialization `e` with `x ∈ e.baseSet`: the
  diffeotopy `TauCeti.Diffeotopy IF ∞ F` whose slice at `s` is
  `hD.parallelTransportIn e e (fun t ↦ Δ (s, t)) 0 1`. It starts at the
  identity since $\Delta(0,\cdot)$ is constant (`parallelTransport_const`), and is
  jointly smooth by `contMDiffOn_parallelTransportIn_param`. API:
  `holonomyDiffeotopy_apply`, `final_holonomyDiffeotopy` (the holonomy of
  the boundary loop `t ↦ Δ (1, t)`), `timeSlice_holonomyDiffeotopy`, and,
  for a symplectic connection and `e = A.trivAt b`,
  `IsSymplectic.timeSlice_holonomyDiffeotopy_mem_diffeomorphStabilizer`
  (every slice preserves `σ`).
- `period_interior_velocity_holonomyDiffeotopy` (the variation of holonomy):
  let `τ` restrict to a closed `σ` and define the connection, and let every
  slice of the diffeotopy preserve `σ`. Let `c : ℝ → F` be a smooth loop of
  period one, and $C(s,t,\theta)$ the transport along $D(s,\cdot)$ from $0$
  to $t$ of $e^{-1}(x,c(\theta))$. Then the line integral over $c$ of
  $\iota(X_s)\sigma$, with $X_s$ the velocity of the diffeotopy at `s`, is
  $-\int_0^1\!\int_0^1 d\tau(\partial_sC,\partial_tC,\partial_\theta C)\,d\theta\,dt$.
  Proof: $\partial_tC$ is horizontal and $\partial_\theta C$ vertical, so
  $\tau(\partial_tC,\partial_\theta C)=0$ and the $\tau$-area of each
  cylinder $C(s,\cdot,\cdot)$ vanishes. Its derivative in $s$ is computed
  pointwise by Tau Ceti's invariant formula `TauCeti.mextDeriv_apply_two`
  for commuting coordinate fields. The term in $t$ integrates to the
  boundary values: at $t=0$ the point does not move in $s$, and at $t=1$ it
  is $\sigma(X_s,\cdot)$ on the moved loop, read through the chart since
  `τ` restricts to `σ`. The term in $\theta$ integrates to zero by
  periodicity. The moved loop is homotopic to $c$ through the slices, so the
  closed form $\iota(X_s)\sigma$ has the same integral on both.

### `Geometry/Symplectic/Fibration/Curvature.lean`

The curvature identity and the local curvature formula.
About 500 lines.

- `TauCeti.IsEhresmannConnection.apply_curvature_eq_mvfderiv_sub_mextDeriv`,
  the first statement of the milestone: for `hD` a `C^n` Ehresmann connection
  (`1 ≤ n`) on a `C^2` map `π` with spaces `τ.horizontalDistribution π` (as for
  `τ` vertically nondegenerate, by `IsVerticallyNondegenerate.isEhresmannConnection`),
  fields `v₁ v₂` on `B` that are `C^1` at `π x`, and a vertical vector `η` at `x`,
  `τ.val x ![hD.curvature v₁ v₂ x, η] =
  mvfderiv IM (fun y ↦ τ.val y ![v₁♯ y, v₂♯ y]) x η - mextDeriv τ.val x ![v₁♯ x, v₂♯ x, η]`,
  with `v♯ = hD.horizontalLiftField v`. This is the page's identity, the
  restriction of both one-forms to each fibre. Its docstring ends with
  "Milestone: *Curvature identity for symplectic connections*." Proof
  ([GuilleminLermanSternberg1996], pp. 6–7): extend `η` to a vertical field
  near `x`; in `TauCeti.mextDeriv_apply_two` for $v_1^\sharp,v_2^\sharp,\eta$,
  the terms $\tau(v_i^\sharp,\eta)$ vanish identically, the brackets
  $[v_i^\sharp,\eta]$ are vertical (the lift is related to $v_i$ and $\eta$
  to $0$, Tau Ceti's `ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`),
  so $\tau([v_i^\sharp,\eta],v_j^\sharp)=0$, and
  $\tau([v_1^\sharp,v_2^\sharp],\eta)=\tau(\Omega_\Gamma(v_1,v_2),\eta)$
  because $[v_1,v_2]^\sharp$ is horizontal. Neither closedness nor vertical
  closedness is used, so the statement is more general than the page's.
- `TauCeti.IsEhresmannConnection.curvatureIn hD IF e b v₁ v₂ : Π y : F, TangentSpace IF y`,
  the curvature on the fibre over `b` read in the chart `e`: the image of
  `hD.curvature v₁ v₂ (e.symm (b, y))` under the derivative of
  `fun x ↦ (e x).2`. With `curvatureIn_def` and `curvatureIn_coordChange`.
- `TauCeti.IsEhresmannConnection.HasHamiltonianCurvature hD A σ`: for every
  chart `e = A.trivAt b'`, every `b ∈ e.baseSet` and smooth `v₁ v₂`, some
  smooth `f : F → ℝ` has `σ.IsHamiltonianVectorField f (hD.curvatureIn IF e b v₁ v₂)`.
  This is the page's condition 2 of the equivalence in Tau Ceti's sign (see
  *Signs*). With `hasHamiltonianCurvature_iff_forall_exists` (one chart per
  point suffices: symplectomorphisms carry Hamiltonian fields to
  Hamiltonian fields).
- `hasHamiltonianCurvature_of_isClosed`: for a closed `τ` that restricts to
  `σ` and defines `hD`, the curvature is Hamiltonian, with Hamiltonian the
  restriction of $\tau(v_1^\sharp,v_2^\sharp)$ to the fibre (from the
  identity with $d\tau=0$).
  This is the page's equation (1.12) of [GuilleminLermanSternberg1996].
- `curvatureIn_local` (the local formula): in the setting of
  `LocalForm.lean`, with $X_i$ the fields of `horizontalLift_local`, the
  curvature of the coordinate fields $\partial_i,\partial_j$ at $(x,v)$ is
  the field $V_{ij}$ on `F` with
  $\iota(V_{ij})\sigma=\partial_i\alpha_j-\partial_j\alpha_i-d\big(\sigma(X_i,X_j)\big)$,
  the formula of the page's corrected hint to Exercise 6.4.9. Then
  `hasHamiltonianCurvature_iff_local`, in `Fibration/HamiltonianCurvature.lean`
  (it uses `PatchForm.lean`, which imports this file): the curvature is
  Hamiltonian exactly
  when, in every symplectic chart over a coordinate patch,
  every $\partial_i\alpha_j-\partial_j\alpha_i$ has a primitive on `F`, at
  every `x` (the page's 2 ⇔ 3).

### `Geometry/Symplectic/Fibration/HamiltonianHolonomy.lean`

Hamiltonian holonomy and Hamiltonian curvature. It imports `Holonomy.lean`
and `HamiltonianCurvature.lean`; the latter imports `Curvature.lean` through
`PatchForm.lean`, so the equivalence, which uses
`hasHamiltonianCurvature_iff_local`, cannot sit in `Curvature.lean`.

- `hasHamiltonianDiscHolonomy_of_hasHamiltonianCurvature` (2 ⇒ 1): for a
  symplectic connection with `π` proper, take a connection two-form `τ` for
  it (`IsSymplectic.exists_restrictsTo_isVerticallyClosed`). In
  `period_interior_velocity_holonomyDiffeotopy`, drop the vertical part of
  $\partial_sC$ by vertical closedness and apply the identity
  `apply_curvature_eq_mvfderiv_sub_mextDeriv`:
  the integrand becomes the curvature of $\partial_sD,\partial_tD$ on the
  loop $\theta\mapsto C(s,t,\theta)$ in one fibre, plus a $\theta$-derivative
  that integrates to zero. If the curvature is Hamiltonian, every period of
  $\iota(X_s)\sigma$ vanishes, so it is exact on the connected `F`
  (Tau Ceti's `deRhamCohomology.period_injective`), the diffeotopy is
  Hamiltonian by `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`,
  and its end, the holonomy, lies in `hamiltonianGroup`.
- `hasHamiltonianCurvature_of_hasHamiltonianDiscHolonomy` (1 ⇒ 2): fix `b`,
  a chart at `b` and tangent vectors $w_1,w_2$, and take the discs
  $D_r(s,t)$ that run around the circle of radius $r\varphi(s)$ through `b`
  in the plane of $w_1,w_2$ in a chart of `B`. Every slice of the holonomy
  diffeotopy is the holonomy of a loop that bounds a disc, so the diffeotopy
  is Hamiltonian by `TauCeti.Diffeotopy.isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup`
  and all periods of its velocity vanish. By the computation of the
  previous item, at a time `s` with $\varphi(s)\varphi'(s)\ne0$, the period
  on `c` is $r^2\varphi(s)\varphi'(s)$ times an integral, over the circle, of the period of
  $\iota(\Omega_\Gamma(w_1,w_2))\sigma$ moved along $C$, which is continuous
  in $r$; dividing by $r^2$ and letting $r\to0$ shows that the period of
  $\iota(\Omega_\Gamma(w_1,w_2))\sigma$ on `c` vanishes. So
  $\iota(\Omega_\Gamma(w_1,w_2))\sigma$ is exact, which gives the
  Hamiltonian.
- The equivalence, `hasHamiltonianDiscHolonomy_tfae`: for `[CompactSpace M]`,
  `[ConnectedSpace F]` and a symplectic connection, `List.TFAE` of
  `HasHamiltonianDiscHolonomy`, `HasHamiltonianCurvature` and the local
  condition of `hasHamiltonianCurvature_iff_local`. Its docstring ends with
  "Milestone: *Curvature identity for symplectic connections*."

### `Geometry/Symplectic/Fibration/Coupling.lean`

The coupling form. About 700 lines, written by three building issues in
turn.

- Linear algebra, in the library's
  `Topology/Algebra/Module/Alternating/Wedge/Pow.lean`, about Tau Ceti's
  `ContinuousAlternatingMap.wedgePow`:
  `ContinuousAlternatingMap.wedgePow_succ_apply_append_of_eq_zero`: for a
  two-form `φ` and vectors `u : Fin 2 → E`, `w : Fin (2 * k) → E` with
  `φ ![u 0, w j] = 0` for all `j`, the value of `φ.wedgePow (k + 1)` on
  `Fin.append u w` (cast along `2 * (k + 1) = 2 + 2 * k`) is
  `(k + 1) * φ u * φ.wedgePow k w`. Only the shuffles that give both `u i`
  to one factor survive.
- `TauCeti.IsEhresmannConnection.fiberMean hD A hσ hk τ b w₁ w₂`, for
  `hσ : σ.IsNondegenerate`, `hk : finrank ℝ EF = 2 * k` and
  `w₁ w₂ : TangentSpace IB b`: the integral over `F` of
  $\tau(w_1^\sharp,w_2^\sharp)$ read through the chart `A.trivAt b`,
  against `σ.volumeForm k` and the orientation `o`; with `fiberMean_def`,
  `fiberMean_coordChange` (any chart of the symplectic atlas gives the same
  value, by Tau Ceti's change of variables
  `Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`),
  `fiberMean_add`, and `fiberMean_add_mpullback`
  (`fiberMean (τ + π^*β) = fiberMean τ + V • β`, with $V$ the symplectic
  volume of `F`, positive by Tau Ceti's `TauCeti.integralTopForm_pos`; for
  `k = 0` the fibre is a point and $V=1$).
- `fiberIntegral_wedgePow_apply`: for `τ` restricting to `σ` and defining
  `hD`, the value of `A.fiberIntegral (τ.wedgePow (k + 1))` at `b` on
  `w₁ w₂` is `(k + 1) * k.factorial * fiberMean τ b w₁ w₂`, from
  `fiberIntegral_apply_of_lift` with horizontal lifts and the linear
  algebra above. So `fiberIntegral_wedgePow_eq_zero_iff`: the page's
  normalization $\int_F\tau^{k+1}=0$ holds exactly when `fiberMean τ`
  vanishes, which is [McDuffSalamon2017], equations (6.4.3) and (6.4.4).
- `TauCeti.IsEhresmannConnection.IsCouplingTwoForm hD A σ τ`: a structure
  with fields `isClosed : τ.IsClosed`, `restrictsTo : A.RestrictsTo σ τ`,
  `horizontalDistribution_eq : τ.horizontalDistribution π = D` and
  `fiberIntegral_eq_zero` (the normalization, as the page states it,
  with the degree cast of *Integration over the fibre*). With
  `isCouplingTwoForm_iff_fiberMean`, which replaces the last field by
  `fiberMean τ = 0`.
- `eq_add_mpullback_of_isClosed` (uniqueness up to the base): for
  `[ConnectedSpace F]` and two closed forms `τ τ'` that restrict to `σ` and
  define the same connection, there is a unique closed `β : SmoothTwoForm IB B`
  with `τ' = τ + π^*β`; `β` at `b` is $(\tau'-\tau)(w_1^\sharp,w_2^\sharp)$
  at any point over `b` (see *Decisions*), and it is unique because `π` is a
  surjective submersion when `F` is nonempty.
- `IsCouplingTwoForm.unique`: two coupling two-forms of one connection are
  equal (the `β` of the previous item has `V • β = 0`).
- `exists_isClosed_local` (local existence): in the setting of
  `LocalForm.lean`, over a coordinate patch `U` and with `σ` constant in
  the chart, if each $\partial_i\alpha_j-\partial_j\alpha_i$ has a primitive
  on `F` at every `x`, there is a closed form on `U ×ˢ univ` with the same $\sigma$
  and $\alpha_i$. The functions $f_{ij}$ are jointly smooth primitives
  from the library's `exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`
  (`Geometry/Manifold/DeRham/FamilyPrimitive.lean`), with the patch as
  parameter manifold, made to vanish at a base point $y_0$ by passing to
  $f(x,y)-f(x,y_0)$. Closedness in the directions (fibre, fibre, base) is
  vertical closedness; in (fibre, base, base) it is the choice of $f_{ij}$;
  and in (base, base, base) the cyclic sum of $\partial_kf_{ij}$ has zero
  derivative along `F`, so it is constant on the connected `F`, and it
  vanishes at $y_0$.
- `exists_isCouplingTwoForm_of_hasHamiltonianCurvature`: for a symplectic
  connection with Hamiltonian curvature, `[CompactSpace M]` and
  `[ConnectedSpace F]`, a coupling two-form exists. Local closed forms
  from `exists_isClosed_local` and `hasHamiltonianCurvature_iff_local`,
  transported to `M` by the charts, are normalized by subtracting the
  pull-back of their mean (`fiberMean_add_mpullback`, smooth by
  `fiberIntegral_wedgePow_apply` on the product, `prodFiberIntegral`); the
  normalized forms agree on overlaps by the pointwise argument of
  `IsCouplingTwoForm.unique`, and the form defined pointwise by them is
  smooth and closed, being so near every point.
- The milestone,
  `TauCeti.IsEhresmannConnection.exists_isClosed_iff_and_existsUnique_isCouplingTwoForm`:
  for `[CompactSpace M]`, `[ConnectedSpace F]`, a symplectic atlas and a
  symplectic connection `hD`, the conjunction of
  - `(∃ τ, τ.IsClosed ∧ A.RestrictsTo σ τ ∧ τ.horizontalDistribution π = D) ↔
    hD.HasHamiltonianDiscHolonomy A σ`;
  - `hD.HasHamiltonianDiscHolonomy A σ → ∃! τ, hD.IsCouplingTwoForm A σ τ`
    (by the first conjunct, a closed `τ` as there gives the hypothesis too);
  - for every `τ` with `hD.IsCouplingTwoForm A σ τ` and every closed `τ'`
    with `A.RestrictsTo σ τ'` and `τ'.horizontalDistribution π = D`,
    `∃! β : SmoothTwoForm IB B, β.IsClosed ∧ τ' = τ + π^*β`.

  The direction ⇒ of the first conjunct is
  `hasHamiltonianCurvature_of_isClosed` and
  `hasHamiltonianDiscHolonomy_of_hasHamiltonianCurvature`; the direction ⇐
  and the existence in the second are
  `hasHamiltonianCurvature_of_hasHamiltonianDiscHolonomy` and
  `exists_isCouplingTwoForm_of_hasHamiltonianCurvature`; the uniqueness in
  the second is `IsCouplingTwoForm.unique`, and the third is
  `eq_add_mpullback_of_isClosed`. Its docstring ends with "Milestone:
  *Coupling form of a symplectic connection*."

### `Geometry/Symplectic/Fibration/SimplyConnected.lean`

The corollary. About 150 lines.

- `exists_isClosed_restrictsTo_of_subsingleton_deRhamCohomology`: for
  `[CompactSpace M]`, `[ConnectedSpace F]`,
  `Subsingleton (deRhamCohomology IF F 1)` and a symplectic atlas, some
  closed `τ` has `A.RestrictsTo σ τ`. Take a connection two-form
  (`exists_restrictsTo_isVerticallyClosed`); its connection is symplectic,
  and since every closed one-form on `F` is exact its curvature is
  Hamiltonian: by the identity, $\iota(\Omega)\sigma$ on a fibre is $d$ of
  a function minus the restriction of $\iota(v_2^\sharp)\iota(v_1^\sharp)d\tau$,
  and that restriction is closed, by Cartan's formula for the closed form
  $d\tau$, vertical closedness, and the verticality of $[v_i^\sharp,\eta]$
  for vertical $\eta$. Then
  `exists_isCouplingTwoForm_of_hasHamiltonianCurvature`. The holonomy is
  not needed, as the page's note says.
- The milestone, `exists_isClosed_restrictsTo_of_simplyConnectedSpace`, the
  same with `[SimplyConnectedSpace F]` through Tau Ceti's
  `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`,
  and `exists_isSymplectic_restrictsTo_of_simplyConnectedSpace`: if
  moreover `B` is compact and connected with a symplectic form, some
  symplectic `ω` has `A.RestrictsTo σ ω`, by step 2 of Thurston's theorem
  in *Compatible symplectic forms* (`Thurston.lean`,
  `exists_forall_ge_isSymplectic_add_smul_mpullback` in its design). The
  docstrings of both end with "Milestone: *Compatible symplectic forms for
  fibrations with simply connected fibre*." The page's compact fibre
  follows from the compact total space (see *Setting*).

## What the part uses

- Tau Ceti: `IsSmoothDisc`, `rectangleIntegral` and its calculus,
  `pathIntegral`, `mextDeriv_apply_two`,
  `ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`,
  `IsHamiltonianVectorField`, `hamiltonianGroup` with its normality,
  `diffeomorphStabilizer`, `isotopyStabilizer`, `Diffeotopy`,
  `deRhamCohomology.period_injective`, `SmoothForm.wedgePow`,
  `SmoothTwoForm.volumeForm`, `integralTopForm` with `integralTopForm_pos`
  and its change of variables, and
  `subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`.
- The library, merged: `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`
  and `exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`
  (*Hamiltonian flows*), and smooth families of forms (*Smooth families*).
- Other parts: *Symplectic fibrations* (`Basic.lean`,
  `HorizontalDistribution.lean`, `Connection.lean`, `LocalForm.lean`),
  *Parallel transport* (`HorizontalLiftField.lean`,
  `ParallelTransport/Basic.lean`, `ParallelTransport/Smooth.lean`,
  `Curvature.lean`), *Integration over the fibre* (`FiberIntegral/Basic.lean`
  and its product files), *Flux homomorphism* (`Family.lean`), and
  *Compatible symplectic forms* (`Thurston.lean`, for the corollary only).
- Used by *Hamiltonian fibrations*: `IsCouplingTwoForm` and the milestone,
  `holonomyDiffeotopy`, `curvatureIn`, `HasHamiltonianCurvature`.

## Building issues

In the order they can be done; each is one pull request of a few hundred
lines, and waits only for what it names.

1. **The curvature identity and the local formula.** The first items
   of `Fibration/Curvature.lean`:
   `apply_curvature_eq_mvfderiv_sub_mextDeriv` (milestone line),
   `curvatureIn`, `HasHamiltonianCurvature`,
   `hasHamiltonianCurvature_of_isClosed`, `curvatureIn_local`; and
   `hasHamiltonianCurvature_iff_local`, in
   `Fibration/HamiltonianCurvature.lean`. Waits for *Symplectic fibrations*
   (`HorizontalDistribution.lean`, `LocalForm.lean`) and *Parallel
   transport* (`Curvature.lean`).
2. **Holonomy around discs.** `Fibration/Holonomy.lean`. Waits for
   *Symplectic fibrations* (`Connection.lean`) and *Parallel transport*
   (`ParallelTransport/Smooth.lean`).
3. **Hamiltonian holonomy and Hamiltonian curvature.**
   `Fibration/HamiltonianHolonomy.lean`: both directions and
   `hasHamiltonianDiscHolonomy_tfae` (milestone line). Waits for 1, 2 and
   *Flux homomorphism* (`Family.lean`).
4. **Normalization and uniqueness.** In `Fibration/Coupling.lean`: the
   wedge-power lemma, the orientation lemma of *Setting*, `fiberMean`,
   `fiberIntegral_wedgePow_apply`, `IsCouplingTwoForm`,
   `eq_add_mpullback_of_isClosed` and `IsCouplingTwoForm.unique`. Waits for
   *Integration over the fibre* (`FiberIntegral/Basic.lean`) and
   *Symplectic fibrations* (`HorizontalDistribution.lean`).
5. **Existence of the coupling form.** In `Fibration/Coupling.lean`:
   `exists_isClosed_local` and
   `exists_isCouplingTwoForm_of_hasHamiltonianCurvature`. Waits for 1 and 4.
6. **The coupling form theorem.** The milestone in
   `Fibration/Coupling.lean`. Waits for 3 and 5.
7. **Simply connected fibres.** `Fibration/SimplyConnected.lean`. Waits for
   5 and *Compatible symplectic forms* (`Thurston.lean`).

Issues 1, 2 and 4 can start as soon as the files they wait for are
merged; 7 does not wait for the holonomy issues.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4 (Theorem 6.4.1, Remark 6.4.2, Corollary 6.4.3, Lemma 6.4.8,
  Exercise 6.4.9, equations (6.4.3)–(6.4.5)) and §10.2 (Proposition
  10.2.12).
* [D. McDuff, D. Salamon, errata to the third edition][McDuffSalamon2019Errata],
  the entries for §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity Diagrams*][GuilleminLermanSternberg1996],
  §§1.3–1.5 (equations (1.11)–(1.14), Theorems 1.4.1 and 1.4.3).
