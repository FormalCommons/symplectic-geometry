# Isothermal coordinates

This is the detailed design of part 24 of `DESIGN.md`, *Isothermal
coordinates*. It proves the milestone *Integrability of almost complex
structures on surfaces* of `atlas/almost-complex-structures.md` by the
Beltrami route (see *Departures*, *Surfaces*, in `DESIGN.md`), following
McDuff–Salamon [McDuffSalamon2017], Theorem 4.2.6, for the reduction to the
Beltrami equation, and the Hölder theory of the Cauchy and Beurling transforms
of McDuff–Salamon [McDuffSalamon2012], Appendix B, and Ahlfors, *Lectures on
Quasiconformal Mappings*, Chapter V, for the solution and its regularity.

Paths of new files are under `SymplecticGeometry/`. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`. All Tau Ceti declarations named
below were checked against the pinned version. The planar statements are in
the namespace `TauCeti.Beltrami`, beside Tau Ceti's; the statements on
manifolds are in the namespaces of the Tau Ceti types they are about
(`TauCeti.SmoothAlmostComplexStructure`, `TauCeti.Manifold.Orientation`), as
`AGENTS.md` asks for declarations about Tau Ceti notions.

## What there is, and what is missing

Tau Ceti has the $C^1$ half of the Beltrami route and most of the analysis
for the higher orders.

- **Planar charts of class $C^1$.**
  `TauCeti.Beltrami.exists_isothermal_chart` and
  `exists_isothermal_chart_of_contDiffAt` (`Analysis/Complex/Beltrami/Isothermal.lean`):
  a field `J : ℂ → AlmostComplexStructure ℂ`, tame for
  `stdComplexSymplecticForm` near `c` with Hölder coefficient (or $C^1$ at
  `c` and tame at `c`), has an open partial homeomorphism `e` with
  `c ∈ e.source`, `C¹` on its source with Hölder and invertible derivative,
  and `fderiv ℝ e z (J z v) = I * fderiv ℝ e z v`. The proof normalizes the
  coefficient at `c` with `TauCeti.Beltrami.linearEquiv` and
  `isComplexLinear_comp_linearMap_iff`, rescales it with
  `TauCeti.eventually_exists_holderSpace_cutoff_rescale`, and solves
  $h=\mu(1+Bh)$ by a contraction in $C^{0,\alpha}$
  (`TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`,
  `Analysis/Complex/Beltrami/Holder.lean`; `exists_isComplexLinear_chart`,
  `Chart.lean`). Its steps `exists_rescaled_coefficient`,
  `exists_chart_of_norm_lt` and `exists_chart_comp_affine` are `private`.
- **The bootstrap.** `TauCeti.Beltrami.contDiffOn_infty_of_fderiv_comp`
  (`Analysis/Complex/Beltrami/Transition.lean`): an isothermal chart `e` is
  smooth on its source if around each point of the source there is, for
  every `m : ℕ`, an isothermal chart of class `C^m` with invertible
  derivative. `contDiffOn_inter_of_fderiv_comp` is the step behind it.
- **Higher Hölder spaces.** `TauCeti.CkHolderSpace k α E F` and
  `supportedCkHolderSubmodule` (`Analysis/Holder/Iterated.lean`), with
  `CkHolderSpace.ofContDiff`, `norm_eq` and completeness; products
  `ContinuousLinearMap.compCkHolder₂` with `norm_compCkHolder₂_le`
  (`Analysis/Holder/Product.lean`); globalization by a cutoff,
  `CkHolderSpace.cutoff` with `norm_cutoff_le` and `cutoff_mem_supported`
  (`Analysis/Holder/Localization.lean`); rescaling to small norm,
  `eventually_exists_ckHolderSpace_cutoff_rescale` and
  `exists_pos_cutoff_rescale_mem_supportedCkHolderSubmodule`
  (`Analysis/Holder/Rescaling.lean`).
- **The operators of order $k$.** `TauCeti.cauchyTransformCkCLM` with
  `cauchyTransformCkCLM_apply_fst`, `_apply_snd`, and
  `HasCompactSupport.contDiff_cauchyTransform_of_holderWith_iteratedFDeriv`
  (`Analysis/Complex/Pompeiu/Holder/Higher.lean`): $T$ maps $C^{k,\alpha}$
  data supported in `closedBall c r` boundedly to the fields of orders
  $\le k+1$ on `closedBall c R`, and the transform is globally `C^{k+1}`;
  `TauCeti.beurlingCkCLM` with `beurlingCkCLM_apply_fst`, `_apply_snd` and
  `norm_beurlingCkCLM_apply_le`, and
  `HasCompactSupport.contDiff_wirtingerDeriv_cauchyTransform_of_holderWith`
  (`Analysis/Complex/Pompeiu/Holder/Beurling.lean`): the same for $B=\partial T$
  at order $k$. `HasCompactSupport.conjWirtingerDeriv_cauchyTransform`
  (`Analysis/Complex/Pompeiu/Basic.lean`, `C¹` data) and
  `conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule`
  (`Pompeiu/Holder/Operator.lean`, Hölder data) give $\bar\partial T h=h$.
- **Surfaces.** `TauCeti.IsIsothermalChart`, the class
  `TauCeti.SmoothAlmostComplexStructure.HasIsothermalCharts` and the complex
  curve `TauCeti.IsothermalSurface` (`Geometry/Manifold/Complex/Isothermal.lean`),
  with the instance only for complex curves. An isothermal chart there needs
  only to lie in the `C¹` maximal atlas. Tau Ceti's main branch (commit
  `659fa713d6`) removes the class and proves instead
  `TauCeti.SmoothAlmostComplexStructure.exists_isIsothermalChart`: every
  smooth structure on a surface modelled on `𝓘(ℝ, ℂ)` has isothermal charts,
  of class `C¹` (Decision 8).
- **Charts and structures.** `SmoothAlmostComplexStructure.chartPushforward`,
  `mfderiv_comp_toEndomorphism`, `chartPushforward_apply_chartPushforward_apply`
  and `SmoothAlmostComplexStructure.contDiffOn_chartPushforward`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean`);
  `TauCeti.stdComplexSymplecticForm_tames_or_tames_transport_conj` and
  `stdComplexSymplecticForm_tames_iff_im_pos`
  (`Geometry/Symplectic/Complex/Line.lean`); `SymplecticForm.Tames.contMDiffAt_cayley`
  (`Geometry/Symplectic/Cayley/Smooth.lean`), for any order.
- **Rotation.** `TauCeti.Manifold.Orientation.contMDiff_rightAngleRotation`
  (`Geometry/Manifold/Riemannian/Orientation/Rotation.lean`) and
  `TauCeti.Manifold.contMDiff_hom_iff` (`Geometry/Manifold/VectorBundle/Hom.lean`);
  Mathlib's `Orientation.rightAngleRotation`,
  `Orientation.rightAngleRotation_map_complex` and
  `isConformalMap_complex_linear`.

Missing, and built here: the fixed point in $C^{k,\alpha}$, the planar charts
of class `C^m` and the smooth planar charts built from it, the same charts
read on a surface, `IsIntegrable` in real
dimension two, the rotation structure of an oriented Riemannian surface, and
its isothermal coordinates.

## Decisions

`DESIGN.md` leaves the route to `C^m` charts, and its split into issues, to
this file.

1. **Route: the contraction in $C^{k,\alpha}$, not interior elliptic
   regularity.** Everything the contraction needs at order $k$ is in Tau
   Ceti except the operator $h\mapsto\mu\,Bh$ on supported $C^{k,\alpha}$
   data and the fixed point. The elliptic route
   (`Analysis/Pseudodifferential/InteriorRegularity.lean`) would also need
   the identification of the localized operator with
   $\bar\partial-\mu\partial$ on a $C^1$ chart, and a Sobolev embedding into
   `C^m`, neither of which exists in a usable form. The contraction runs
   separately for each $k$: a fresh rescaling, small in $C^{k,\alpha}$, and
   a fresh fixed point, giving a chart of class `C^{k+1}`. Charts of
   different orders need not agree; `contDiffOn_infty_of_fderiv_comp` takes
   one chart for each order.
2. **The normalization at the centre comes before the rescaling.** The
   coefficient is first made zero at the centre by the linear change
   `TauCeti.Beltrami.linearEquiv (μ c)`, as in Tau Ceti; only then do the
   rescaled $C^{k,\alpha}$ norms tend to zero
   (`exists_pos_cutoff_rescale_mem_supportedCkHolderSubmodule` assumes
   `μ 0 = 0`).
3. **The operator.** $B h$ is known with bounds only on a closed disc
   (`beurlingCkCLM` takes values in fields on `closedBall c R`). It is made a
   global element of `CkHolderSpace` by a fixed smooth bump `χ`, equal to one
   on `closedBall c r` and with `tsupport χ ⊆ ball c (r + 1)`, through
   `CkHolderSpace.cutoff` on `ball c (r + 1)`, and then multiplied by `μ` with
   `compCkHolder₂` of complex multiplication. Since `μ` vanishes off
   `closedBall c r`, where `χ = 1`, the product is $\mu\,Bh$ everywhere. Tau
   Ceti's main branch builds this operator, privately, in
   `Beltrami/HigherHolder.lean`, which the library copies (*Files taken from
   Tau Ceti*).
4. **Statements of finite order are for `J` of class `C^m` at a point, tame
   there**, as in `exists_isothermal_chart_of_contDiffAt`, with `1 ≤ m`; the
   chart is of class `C^m`. This is the natural generality of the route
   ($J\in C^m$ gives $\mu\in C^{m-1,\alpha}$ near the centre, since the
   $(m-1)$-st derivative is `C¹` there, hence Lipschitz and Hölder on a
   ball), and the conclusion has exactly the shape of the hypothesis of
   `contDiffOn_infty_of_fderiv_comp` (applied with `max m 1`).
5. **Surfaces over any two-dimensional model.** The chart on a surface is
   proved over a boundaryless model `I : ModelWithCorners ℝ E H` with
   `Module.finrank ℝ E = 2`, using a real isomorphism `E ≃L[ℝ] ℂ`
   (`ContinuousLinearEquiv.ofFinrankEq`). If the pushed-forward structure is
   not tame at the point, the chart is first composed with conjugation
   (`stdComplexSymplecticForm_tames_or_tames_transport_conj`).
6. **`IsIntegrable` uses one linear structure**, the transport of
   multiplication by `i` along `E ≃L[ℝ] ℂ` (`TauCeti.AlmostComplexStructure.transport`),
   whatever conjugation the chart needed at each point. So the remark in
   #862 about empty manifolds does not arise here.
7. **Isothermal coordinates for a metric** are stated as conformality of the
   differential of a smooth chart `M → ℂ`: at each point of its source
   `IsConformalMap (mvfderiv I ψ y)`, which Mathlib's `isConformalMap_iff`
   turns into `⟪dψ v, dψ w⟫ = c ⟪v, w⟫` for some `c > 0`. They are the isothermal
   charts of the rotation structure of the metric and the orientation; the
   rotation structure is built from `contMDiff_rightAngleRotation` with
   `contMDiff_hom_iff`, which needs `[T2Space M]`.
8. **No instance `HasIsothermalCharts`, and no copy of
   `exists_isIsothermalChart`.** Tau Ceti's main branch proves the existence
   of `C¹` isothermal charts for every structure
   (`SmoothAlmostComplexStructure.exists_isIsothermalChart`) and removes the
   class, so an instance here would repeat that theorem and break at the
   move of Tau Ceti past it. Neither issue 3 nor issue 4 uses that theorem:
   `IsIntegrable` asks for smooth charts, which come from the planar charts of
   issue 2, while Tau Ceti's charts are only `C¹`. So the part neither copies
   it nor waits for it; it reaches the library with the move. On the model
   `𝓘(ℝ, ℂ)`, smooth isothermal charts of the smooth maximal atlas follow
   from issue 4 through `isIntegrable_iff_forall_exists_isIsothermalChart`
   (#862). The theorem `IsIntegrable.hasIsothermalCharts` of
   `Geometry/Manifold/Complex/Integrable.lean` (#862) concludes the class,
   and nothing in the library uses it. It stays until the move; the pull
   request of that move deletes it, with no replacement, since
   `exists_isIsothermalChart` gives its conclusion with no hypothesis, and
   takes the class out of that file's module docstring and of part 23 of
   `DESIGN.md`. `isIntegrable_iff_forall_exists_isIsothermalChart` stays.

## Files and their contents

| File | Contents | Issue |
|---|---|---|
| `Analysis/Calculus/ContDiff/Holder.lean` | a map of class `C^{k+1}` at a point has a Hölder `k`-th derivative near it | 2 |
| `Analysis/Calculus/ContinuousLinearMapInverse.lean` | taken from Tau Ceti: invertible strict derivatives of `y ↦ y + f y` | 1 |
| `Analysis/Calculus/IteratedFDeriv/Basic.lean` | taken from Tau Ceti: iterated derivatives of a continuous linear map plus a function | 1 |
| `Analysis/Complex/Beltrami/CkHolder.lean` | charts of class `C^{k+1}` for small coefficients | 1 |
| `Analysis/Complex/Beltrami/HigherHolder.lean` | taken from Tau Ceti: the Beltrami operator on supported $C^{k,\alpha}$ data and the fixed point | 1 |
| `Analysis/Complex/Beltrami/Regularity.lean` | planar isothermal charts of class `C^m`, smooth planar isothermal charts | 2 |
| `Analysis/Complex/Pompeiu/Holder/Higher.lean` | taken from Tau Ceti: smoothness of the Cauchy transform of supported $C^{k,\alpha}$ data | 1 |
| `Analysis/Complex/Wirtinger/Basic.lean` | taken from Tau Ceti: Wirtinger derivatives of `z + f z` | 1 |
| `Analysis/Holder/Iterated.lean` | taken from Tau Ceti: Hölder continuity of $C^{k,\alpha}$ maps, the supported subspace is closed | 1 |
| `Analysis/Holder/Normed.lean` | taken from Tau Ceti: Hölder bounds on a subset | 1 |
| `Analysis/InnerProductSpace/TwoDim.lean` | a nonzero linear map of an oriented Euclidean plane carrying the rotation to `i` is conformal | 4 |
| `Analysis/Normed/Operator/Basic.lean` | taken from Tau Ceti: the Neumann series for `v + A x = x` | 1 |
| `Geometry/Manifold/Complex/Isothermal.lean` | smooth isothermal charts on surfaces (issue 3); `IsIntegrable` in dimension two, the rotation structure, isothermal coordinates, the milestone (issue 4) | 3, 4 |

`CkHolder.lean` and `Regularity.lean` avoid the names of Tau Ceti's `Beltrami/` files
(`Chart`, `Holder`, `Isothermal`, `Linear`, `Transition`). The surface file
is named like Tau Ceti's, as `DESIGN.md` says.

### `Analysis/Complex/Beltrami/CkHolder.lean`

Imports `Analysis/Complex/Beltrami/HigherHolder.lean` (below), Tau Ceti's
`Beltrami/Chart.lean` and `Beltrami/Linear.lean`.
Write `S k α c r` for
`supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)`.

The operator of Decision 3 and the fixed point are not in this file: Tau
Ceti's main branch has them, after the version this library pins, in
`TauCeti/Analysis/Complex/Beltrami/HigherHolder.lean` (the operator private,
the fixed point as
`TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`, which
also gives an invertible strict derivative at every point of the disc). The
library copies that file, and the declarations of other Tau Ceti files that
it uses, under *Files taken from Tau Ceti* below. The names
`beltramiCkCLM`, `beltramiCkCLM_apply` and
`exists_contDiff_conjWirtingerDeriv_eq_mul_wirtingerDeriv` are not used.

- `exists_isComplexLinear_contDiff_chart (k : ℕ) (hα : 0 < α) (hα1 : α < 1)
  (c : ℂ) (hr : 0 < r) : ∃ δ > 0, ∀ (J : ℂ → AlmostComplexStructure ℂ)
  (hJ : ∀ z ∈ closedBall c r, stdComplexSymplecticForm.Tames (J z)),
  ∀ μ ∈ S k α c r, (∀ z (hz : z ∈ closedBall c r),
    μ z = (coefficientEquiv ⟨J z, hJ z hz⟩).val) → ‖μ‖ < δ →
  ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ ball c r ∧
    ContDiffOn ℝ (k + 1) e e.source ∧
    (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
    ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v`.
  The chart is the solution itself near `c`, by the inverse function theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph`) restricted to `ball c r`; the
  pointwise equation is `isComplexLinear_iff_conjWirtingerDeriv_eq`. No
  normalization `normalizedChart` is needed for this conclusion.

About 100 lines.

### Files taken from Tau Ceti

These files copy declarations of Tau Ceti's main branch, from its commit
`0fef288e2f0539135f050168f1153e762b0189a8`, at the paths of their Tau Ceti
files with `SymplecticGeometry/` in place of `TauCeti/`, under Tau Ceti's
names and with Tau Ceti's headers, as `AGENTS.md` asks. A move of Tau Ceti
past that commit deletes them.

- `Analysis/Complex/Beltrami/HigherHolder.lean`: the whole of Tau Ceti's
  file, `exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv` and its
  private steps.
- `Analysis/Calculus/ContinuousLinearMapInverse.lean`:
  `HasStrictFDerivAt.exists_continuousLinearEquiv_id_add`.
- `Analysis/Calculus/IteratedFDeriv/Basic.lean`:
  `ContinuousLinearMap.iteratedFDeriv_succ_eq`,
  `ContinuousLinearMap.iteratedFDeriv_succ_add_apply`,
  `ContinuousLinearMap.holderOnWith_iteratedFDeriv_succ_add_left_iff`.
- `Analysis/Complex/Pompeiu/Holder/Higher.lean`:
  `contDiff_cauchyTransform_of_mem_supportedCkHolderSubmodule`.
- `Analysis/Complex/Wirtinger/Basic.lean`:
  `DifferentiableAt.conjWirtingerDeriv_add_left`,
  `conjWirtingerDeriv_id_add`, `wirtingerDeriv_id_add`.
- `Analysis/Holder/Iterated.lean`: `CkHolderSpace.holderWith`,
  `hasCompactSupport_of_mem_supportedCkHolderSubmodule`,
  `isClosed_supportedCkHolderSubmodule` and the instance
  `instCompleteSpaceSupportedCkHolderSubmodule`.
- `Analysis/Holder/Normed.lean`: `HolderSpace.holderOnWith_of_apply_eq`.
- `Analysis/Normed/Operator/Basic.lean`:
  `ContinuousLinearMap.exists_add_apply_eq_of_norm_lt_one`.

### `Analysis/Calculus/ContDiff/Holder.lean`

Imports Tau Ceti's `ContDiff/Bounds.lean` and `Holder/JetBounds.lean`.

- `ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv {f : E → F} {x : E} {k : ℕ}
  (hf : ContDiffAt ℝ (k + 1) f x) {α : ℝ≥0} (hα : α ≤ 1) :
  ∃ ρ > 0, ∃ H : ℝ≥0, ContDiffOn ℝ (k + 1) f (ball x ρ) ∧
    HolderOnWith H α (iteratedFDeriv ℝ k f) (ball x ρ)`, from
  `ContDiffAt.exists_ball_bound_iteratedFDeriv` and
  `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt`.

### `Analysis/Complex/Beltrami/Regularity.lean`

Imports `Calculus/ContDiff/Holder.lean`, `CkHolder.lean`,
Tau Ceti's `Beltrami/Isothermal.lean`,
`Beltrami/Transition.lean`, `Holder/Rescaling.lean` and
`Symplectic/Cayley/Smooth.lean`, and, for its proofs only, Tau Ceti's
`Conformal/PseudoHyperbolic.lean`. Write `toCLM J z` for
`LinearMap.toContinuousLinearMap (J z).toLinearMap`.

- `exists_contDiffOn_isothermal_chart_of_contDiffAt {m : ℕ} (hm : 1 ≤ m)
  {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
  (hJ : ContDiffAt ℝ m (fun z ↦ toCLM J z) c)
  (hJc : stdComplexSymplecticForm.Tames (J c)) :
  ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ ContDiffOn ℝ m e e.source ∧
    (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
    ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v`.
  With `k = m - 1`: the coefficient is `C^m` at `c` (`Tames.contMDiffAt_cayley`);
  normalized by `L = linearEquiv (μ c)` and read at `c + L⁻¹ x`, it is
  `C^m` at `0`, vanishes there, and its `k`-th derivative is Lipschitz,
  hence `α`-Hölder, on a ball
  (`ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv`); rescaled and cut off by
  `eventually_exists_ckHolderSpace_cutoff_rescale` it falls below
  the `δ` of `exists_isComplexLinear_contDiff_chart`, which is applied to
  the structure whose coefficient is the rescaled one at every point
  (`coefficientEquiv.symm`, as Tau Ceti's `exists_chart_of_norm_lt` does);
  that chart, restricted to the unit disc, where the cutoff is one, and
  composed with `z ↦ ε⁻¹ L (z - c)`, is the chart, its
  equation transported by `isComplexLinear_comp_linearMap_iff`. These are
  the steps of Tau Ceti's `exists_isothermal_chart` with `C^m` in place of
  Hölder; the docstring credits it and its private
  `exists_rescaled_coefficient` and `exists_chart_comp_affine`, whose
  `C^m` analogues are steps here (private, or public in Tau Ceti's
  namespaces if another proof uses them).
- `exists_smooth_isothermal_chart_of_contDiffOn {J : ℂ → AlmostComplexStructure ℂ}
  {U : Set ℂ} (hU : IsOpen U) (hJ : ContDiffOn ℝ ∞ (fun z ↦ toCLM J z) U)
  (hJU : ∀ z ∈ U, stdComplexSymplecticForm.Tames (J z)) {c : ℂ} (hc : c ∈ U) :
  ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ U ∧
    ContDiffOn ℝ ∞ e e.source ∧ (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
    ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v`.
  Tau Ceti's `C¹` chart, restricted to `U` (`restrOpen`), made smooth by
  `contDiffOn_infty_of_fderiv_comp` with the previous theorem at each point
  of `U`.

About 350 lines.

### `Geometry/Manifold/Complex/Isothermal.lean`

**Issue 3** imports Mathlib's `Geometry/Manifold/LocalDiffeomorph.lean` and
Tau Ceti's `Symplectic/Manifold/AlmostComplex/Chart.lean`, and, for its
proof only, `Regularity.lean` and Tau Ceti's
`Calculus/InverseFunctionTheorem.lean`, `Manifold/Diffeomorph/Basic.lean`,
`Manifold/LocalDiffeomorph/Basic.lean` and `Manifold/MFDeriv/NormedSpace.lean`, and
`Geometry/Manifold/Complex/Integrable.lean` and
`Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean` of *Nijenhuis tensor*. Throughout,
`I : ModelWithCorners ℝ E H` with
`[I.Boundaryless]` and `[IsManifold I ∞ M]`; `[FiniteDimensional ℝ E]`
follows from `hE`.

- `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph
  (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2)
  (x : M) : ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
  ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
    mvfderiv I ψ y (J y v) = Complex.I * mvfderiv I ψ y v`, with Mathlib's
  `mvfderiv`, whose values lie in `ℂ` rather than in a tangent space of
  `ℂ`, so that the product with `Complex.I` is defined.
  The chart at `x` followed by `I` and `E ≃L[ℝ] ℂ` pushes `J` forward to
  a smooth field on its target
  (`contDiffOn_chartPushforward`, squaring to `-1` by
  `chartPushforward_apply_chartPushforward_apply` of the library's `Chart.lean`); the smooth planar
  chart of `TauCeti.Beltrami.exists_smooth_isothermal_chart` composed with
  it is `ψ`, its inverse smooth by
  `OpenPartialHomeomorph.contDiffOn_symm_of_isInvertible_fderiv`, its
  equation from `mfderiv_apply_eq_chartPushforward_apply` of the library's `Chart.lean`. That planar theorem, in
  `Regularity.lean`, drops the tameness hypothesis of
  `exists_smooth_isothermal_chart_of_contDiffOn`: where the field is not
  tame it composes with conjugation (Decision 5), and it restricts to where
  the field is tame (`SymplecticForm.Tames.eventually_of_continuousAt`).
  The conversions to `PartialDiffeomorph` are Tau Ceti's
  `OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas` and
  `PartialDiffeomorph.ofOpenPartialHomeomorph`, with Mathlib's
  `Diffeomorph.toPartialDiffeomorph` and `PartialDiffeomorph.trans`.

No instance `HasIsothermalCharts` (Decision 8).

About 250 lines.

**Issue 4** adds, importing `Geometry/Manifold/Complex/Integrable.lean` of
*Nijenhuis tensor* (#862) and Tau Ceti's
`Riemannian/Orientation/Rotation.lean` and `VectorBundle/Hom.lean`, and, for
its proofs only, `Analysis/InnerProductSpace/TwoDim.lean` (below) and
`Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean` of *Moser isotopy*:

- `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two
  (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2) :
  J.IsIntegrable`, with the linear structure of Decision 6: the charts are
  those of `exists_isothermal_partialDiffeomorph` followed by `ℂ ≃L[ℝ] E`.
  The docstring ends with the milestone line.
- `TauCeti.Manifold.Orientation.rightAngleRotationStructure
  (o : Manifold.Orientation I M (Fin 2)) : SmoothAlmostComplexStructure I M`,
  for `[T2Space M]`, `[RiemannianBundle (fun x : M ↦ TangentSpace I x)]` and
  `[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]`:
  rotation by a right angle in each tangent plane, smooth by
  `contMDiff_hom_iff` and `contMDiff_rightAngleRotation`, of square `-1` by
  `Orientation.rightAngleRotation_rightAngleRotation`; with
  `rightAngleRotationStructure_apply` (the value at `x` on `v` is
  `(o.orientationAt x).rightAngleRotation v`, under the
  `fact_finrank_tangentSpace` instance), proved by `(rfl)`.
- `TauCeti.Manifold.Orientation.exists_isothermal_coordinates
  (o : Manifold.Orientation I M (Fin 2)) (x : M) :
  ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
  ∀ y ∈ ψ.source, IsConformalMap (mvfderiv I ψ y)`,
  with the instances above and `[I.Boundaryless]`, and Mathlib's `mvfderiv`
  as in issue 3. The finrank of `E` comes from `o` and `x`
  (`fact_finrank_tangentSpace`). The chart is that of
  `exists_isothermal_partialDiffeomorph` for `o.rightAngleRotationStructure`;
  at each point its differential, read through an orientation-preserving
  isometry of the tangent plane with `ℂ`
  (`Orientation.rightAngleRotation_map_complex`), is complex linear and
  nonzero, hence conformal (`isConformalMap_complex_linear`). The pointwise
  step is `Orientation.isConformalMap_of_map_rightAngleRotation`, in
  `Analysis/InnerProductSpace/TwoDim.lean`: a nonzero real-linear map from an
  oriented Euclidean plane to a complex normed space carrying the rotation to
  `i` is conformal. The docstring ends with the milestone line.

About 300 lines.

## What the part uses

- Tau Ceti, as listed under *What there is*, and the declarations of its main
  branch copied under *Files taken from Tau Ceti*. The chart of
  `CkHolder.lean` follows `TauCeti.Beltrami.exists_isComplexLinear_chart`
  (`Beltrami/Chart.lean`), and `Regularity.lean` the proof of
  `TauCeti.Beltrami.exists_isothermal_chart`; their docstrings credit them.
  `Calculus/ContDiff/Holder.lean` uses Tau Ceti's
  `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt` (`Analysis/Holder/JetBounds.lean`,
  which goes through `LipschitzOnWith.holderOnWith_of_norm_le`),
  `ContDiffAt.exists_ball_bound_iteratedFDeriv`
  (`Analysis/Calculus/ContDiff/Bounds.lean`), and `Regularity.lean`
  `one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one`
  (`Analysis/Complex/Conformal/PseudoHyperbolic.lean`).
- Mathlib: `HasStrictFDerivAt.toOpenPartialHomeomorph`,
  `OpenPartialHomeomorph.contDiffAt_symm`, `ContDiffBump`,
  `ContinuousLinearEquiv.ofFinrankEq`, `PartialDiffeomorph`,
  `Orientation.rightAngleRotation`, `Orientation.rightAngleRotation_map_complex`,
  `isConformalMap_complex_linear`.
- *Nijenhuis tensor*: `Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean`
  (#1295), for the chart pushforward lemmas in issue 3, and
  `Geometry/Manifold/Complex/Integrable.lean` (#862), for `IsIntegrable` in
  issue 4.

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #866, *Build the part Isothermal coordinates*. Sizes are
estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Planar charts of class `C^{k+1}` for a small $C^{k,\alpha}$ coefficient | `Analysis/Complex/Beltrami/CkHolder.lean`, and the files under *Files taken from Tau Ceti* | — | 1000 |
| 2 | Planar isothermal charts of class `C^m`, and smooth ones | `Analysis/Calculus/ContDiff/Holder.lean`, `Analysis/Complex/Beltrami/Regularity.lean` | 1 | 350 |
| 3 | Smooth isothermal charts on surfaces | `Geometry/Manifold/Complex/Isothermal.lean` | 2; #862, #1295 | 250 |
| 4 | Integrability in dimension two, isothermal coordinates of a metric, and the milestone | `Geometry/Manifold/Complex/Isothermal.lean`, `Analysis/InnerProductSpace/TwoDim.lean` | 3; #862 | 300 |

Issue 1 can start at once. The milestone *Integrability of almost complex
structures on surfaces* is proved in issue 4.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 4.2.6 and Exercise 4.2.8.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed.][McDuffSalamon2012], Appendix B (Hölder estimates for the Cauchy
  and Beurling transforms) and Appendix E.
* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS
  University Lecture Series 38, 2006, Chapter V. The plan's bibliography has
  no key for it.
* [S.-S. Chern, *An elementary proof of the existence of isothermal
  parameters on a surface*][Chern1955].
