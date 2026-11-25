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

Tau Ceti has the whole planar Beltrami route, up to smooth charts.

- **Planar charts of every finite order, and smooth ones.**
  `TauCeti.Beltrami.exists_isothermal_chart_finite_order`
  (`Analysis/Complex/Beltrami/Isothermal.lean`): a field
  `J : ℂ → ℂ →L[ℝ] ℂ` of class `C^(k+1)` at `c` and squaring to `-1` near
  `c` has an isothermal chart of class `C^(k+1)` centred at `c`, with
  invertible derivative. `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`:
  a smooth such field on an open set `U` has, at each point of `U`, a smooth
  isothermal chart with source in `U` and smooth inverse.
- **Planar charts of class $C^1$.**
  `TauCeti.Beltrami.exists_isothermal_chart` and
  `exists_isothermal_chart_of_contDiffAt` (`Analysis/Complex/Beltrami/Isothermal.lean`):
  a field `J : ℂ → AlmostComplexStructure ℂ`, tame for
  `stdComplexSymplecticForm` near `c` with Hölder coefficient (or $C^1$ at
  `c`, tame there or not), has an open partial homeomorphism `e` with
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
- **Surfaces.** `TauCeti.IsIsothermalChart`,
  `TauCeti.SmoothAlmostComplexStructure.exists_isIsothermalChart` and the
  complex curve `TauCeti.IsothermalSurface`
  (`Geometry/Manifold/Complex/Isothermal.lean`): every smooth structure on a
  surface modelled on `𝓘(ℝ, ℂ)` has isothermal charts, of class `C¹`. An
  isothermal chart there needs only to lie in the `C¹` maximal atlas. Tau
  Ceti removed its class `HasIsothermalCharts` at commit `659fa713d6`, which
  the library reached with the move to `c9d170eed5a8` (#2025; Decision 8).
- **Charts and structures.** `SmoothAlmostComplexStructure.chartPushforward`,
  `mfderiv_comp_toEndomorphism`, `chartPushforward_apply_chartPushforward_apply`
  and `SmoothAlmostComplexStructure.contDiffOn_chartPushforward`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean`);
  `TauCeti.stdComplexSymplecticForm_tames_or_tames_transport_conj` and
  `stdComplexSymplecticForm_tames_iff_im_pos`
  (`Geometry/Symplectic/Complex/Line.lean`); `SymplecticForm.Tames.contMDiffAt_cayley`
  (`Geometry/Symplectic/Cayley/Smooth.lean`), for any order.
- **Rotation.** `TauCeti.Manifold.Orientation.rightAngleAlmostComplexStructure`
  and `rightAngleAlmostComplexStructure_apply`
  (`Geometry/Manifold/Riemannian/Orientation/AlmostComplex.lean`);
  Mathlib's `Orientation.rightAngleRotation`,
  `Orientation.rightAngleRotation_map_complex` and
  `isConformalMap_complex_linear`.

Missing, and built here: the reading of Tau Ceti's smooth planar charts on
a surface, `IsIntegrable` in real
dimension two, and the isothermal coordinates of an oriented Riemannian
surface.

## Decisions

Decisions 1 to 4 chose a route to planar isothermal charts of class `C^m`.
Tau Ceti's `exists_isothermal_chart_finite_order` and
`exists_centered_smooth_isothermal_chart` now give those charts, so these
decisions are settled by Tau Ceti. The part builds neither the operator of
Decision 3 nor the contraction of Decision 1: the chart of `CkHolder.lean`
applies Tau Ceti's fixed point
`TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`.

1. **Route: the contraction in $C^{k,\alpha}$, not interior elliptic
   regularity.** Tau Ceti has the contraction at order $k$, with the
   operator $h\mapsto\mu\,Bh$ on supported $C^{k,\alpha}$ data and its
   fixed point. The elliptic route
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
   on `closedBall c (r + 1)` and vanishing off `ball c (r + 2)`, through
   `CkHolderSpace.cutoff` on `ball c (r + 3)`, and then multiplied by `μ` with
   `compCkHolder₂` of complex multiplication. Since `μ` vanishes off
   `closedBall c r`, where `χ = 1`, the product is $\mu\,Bh$ everywhere. Tau
   Ceti builds this operator, privately, in its
   `Beltrami/HigherHolder.lean` (*Files taken from Tau Ceti*).
4. **Statements of finite order are for `J` of class `C^m` at a point**, as
   in `exists_isothermal_chart_of_contDiffAt`, with `1 ≤ m`; the
   chart is of class `C^m`. This is the natural generality of the route
   ($J\in C^m$ gives $\mu\in C^{m-1,\alpha}$ near the centre, since the
   $(m-1)$-st derivative is `C¹` there, hence Lipschitz and Hölder on a
   ball), and the conclusion has exactly the shape of the hypothesis of
   `contDiffOn_infty_of_fderiv_comp` (applied with `max m 1`). The route
   needs `J` tame at the point; where it is not, the chart of the field
   transported by conjugation is composed with conjugation
   (`stdComplexSymplecticForm_tames_or_tames_transport_conj`), as Tau Ceti's
   theorem does.
5. **Surfaces over any two-dimensional model.** The chart on a surface is
   proved over a boundaryless model `I : ModelWithCorners ℝ E H` with
   `Module.finrank ℝ E = 2`, using a real isomorphism `E ≃L[ℝ] ℂ`
   (`ContinuousLinearEquiv.ofFinrankEq`). The planar charts need no
   tameness: `exists_centered_smooth_isothermal_chart` asks only that the
   field square to `-1`.
6. **`IsIntegrable` comes from the charts into `ℂ`.** The charts
   `ψ : M → ℂ` of `exists_isothermal_partialDiffeomorph`, with
   multiplication by `i` on `ℂ`, go to
   `isIntegrable_of_forall_exists_partialDiffeomorph`
   (`Geometry/Manifold/Complex/Integrable.lean`), which brings each chart
   to the model by the inverse of its derivative at the point.
7. **Isothermal coordinates for a metric** are stated as conformality of the
   differential of a smooth chart `M → ℂ`: at each point of its source
   `IsConformalMap (mvfderiv I ψ y)`, which Mathlib's `isConformalMap_iff`
   turns into `⟪dψ v, dψ w⟫ = c ⟪v, w⟫` for some `c > 0`. They are the isothermal
   charts of the rotation structure of the metric and the orientation, Tau
   Ceti's `rightAngleAlmostComplexStructure`, which needs `[T2Space M]`.
8. **Tau Ceti's `exists_isIsothermalChart` is used as it is.** Tau Ceti
   proves the existence of `C¹` isothermal charts for every structure
   (`SmoothAlmostComplexStructure.exists_isIsothermalChart`), and no longer
   has the class `HasIsothermalCharts`. Neither issue 3 nor issue 4 uses
   that theorem: `IsIntegrable` asks for smooth charts, which come from Tau
   Ceti's smooth planar charts. On the
   model `𝓘(ℝ, ℂ)`, Tau Ceti's isothermal charts lie in the smooth maximal
   atlas (`IsIsothermalChart.mem_maximalAtlas_infty`), which gives the
   forward direction of
   `isIntegrable_iff_forall_exists_isIsothermalChart` (#862). The theorem
   `IsIntegrable.hasIsothermalCharts` that #862 added, which concluded the
   class, was deleted by the move to `c9d170eed5a8` (#2025), with no
   replacement, since `exists_isIsothermalChart` gives its conclusion with no
   hypothesis. `isIntegrable_iff_forall_exists_isIsothermalChart` stays.

## Files and their contents

| File | Contents | Issue |
|---|---|---|
| `Analysis/Calculus/ContDiff/Holder.lean` | a map of class `C^{k+1}` at a point has a Hölder `k`-th derivative near it | 2 |
| `Analysis/Complex/Beltrami/CkHolder.lean` | charts of class `C^{k+1}` for small coefficients | 1 |
| `Analysis/InnerProductSpace/TwoDim.lean` | a nonzero linear map of an oriented Euclidean plane carrying the rotation to `i` is conformal | 4 |
| `Geometry/Manifold/Complex/Isothermal.lean` | smooth isothermal charts on surfaces (issue 3); `IsIntegrable` in dimension two, isothermal coordinates, the milestone (issue 4) | 3, 4 |

`CkHolder.lean` avoids the names of Tau Ceti's `Beltrami/` files
(`Chart`, `Holder`, `Isothermal`, `Linear`, `Transition`). The surface file
is named like Tau Ceti's, as `DESIGN.md` says.

The planar isothermal charts of finite order and the smooth ones are Tau
Ceti's (`TauCeti.Beltrami.exists_isothermal_chart_finite_order`,
`TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`, in
`Beltrami/Isothermal.lean`), for a field of real-linear operators on the
plane squaring to `-1`; the part has no file for them.

### `Analysis/Complex/Beltrami/CkHolder.lean`

Imports Tau Ceti's `Beltrami/HigherHolder.lean`, `Beltrami/Chart.lean` and
`Beltrami/Linear.lean`.
Write `S k α c r` for
`supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)`.

The operator of Decision 3 and the fixed point are not in this file: Tau
Ceti has them in `Analysis/Complex/Beltrami/HigherHolder.lean` (the
operator private, the fixed point as
`TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`, which
also gives an invertible strict derivative at every point of the disc; see
*Files taken from Tau Ceti* below). The names
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

Issue 1 copied the declarations below from Tau Ceti's main branch, at its
commit `0fef288e2f0539135f050168f1153e762b0189a8`, which the pinned version
did not have yet, into files at the paths of their Tau Ceti files. The move
to `c9d170eed5a8` (#2025) deleted those copies: the declarations are Tau
Ceti's now, in the files of these paths under `TauCeti/`, and the library
uses them from there.

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

Imports Tau Ceti's `ContDiff/Bounds.lean` and `Holder/Jet/Bounds.lean`.

- `ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv {f : E → F} {x : E} {k : ℕ}
  (hf : ContDiffAt ℝ (k + 1) f x) {α : ℝ≥0} (hα : α ≤ 1) :
  ∃ ρ > 0, ∃ H : ℝ≥0, ContDiffOn ℝ (k + 1) f (ball x ρ) ∧
    HolderOnWith H α (iteratedFDeriv ℝ k f) (ball x ρ)`, from
  `ContDiffAt.exists_ball_bound_iteratedFDeriv` and
  `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt`.

### `Geometry/Manifold/Complex/Isothermal.lean`

**Issue 3** imports Mathlib's `Geometry/Manifold/LocalDiffeomorph.lean` and
Tau Ceti's `Symplectic/Manifold/AlmostComplex/Chart.lean`, and, for its
proof only, Tau Ceti's
`Beltrami/Isothermal.lean`, `Manifold/Diffeomorph/Basic.lean`,
`Manifold/LocalDiffeomorph/Basic.lean` and `Manifold/MFDeriv/NormedSpace.lean`, and
`Geometry/Manifold/Complex/Integrable.lean` and
`Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean` of *Nijenhuis tensor*. Throughout,
`I : ModelWithCorners ℝ E H` with
`[I.Boundaryless]` and `[IsManifold I ∞ M]`; `[FiniteDimensional ℝ E]`
follows from `hE`.

- `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph
  (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2)
  (x : M) : ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
  ∀ y ∈ ψ.source, IsPseudoholomorphicAt J (ofComplexManifold ℂ ℂ) ψ y`,
  with Tau Ceti's `IsPseudoholomorphicAt` and `ofComplexManifold`
  (`Symplectic/Manifold/JHolomorphic.lean`,
  `Manifold/Complex/AlmostComplexStructure.lean`).
  The chart at `x` followed by `I` and `E ≃L[ℝ] ℂ` pushes `J` forward to
  a smooth field on its target
  (`contDiffOn_chartPushforward`, squaring to `-1` by
  `chartPushforward_apply_chartPushforward_apply` of the library's `Chart.lean`); the smooth planar
  chart of `TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`,
  smooth with smooth inverse, composed with
  it is `ψ`, its
  equation from `mfderiv_apply_eq_chartPushforward_apply` of the library's `Chart.lean`.
  The conversions to `PartialDiffeomorph` are Tau Ceti's
  `OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas` and
  `PartialDiffeomorph.ofOpenPartialHomeomorph`, with Mathlib's
  `Diffeomorph.toPartialDiffeomorph` and `PartialDiffeomorph.trans`.

This issue gives no isothermal-chart instance; Tau Ceti's
`exists_isIsothermalChart` gives `C¹` charts for every structure
(Decision 8).

About 250 lines.

**Issue 4** adds, importing `Geometry/Manifold/Complex/Integrable.lean` of
*Nijenhuis tensor* (#862) and Tau Ceti's
`Riemannian/Orientation/Rotation.lean` and `VectorBundle/Hom.lean`, and, for
its proofs only, `Analysis/InnerProductSpace/TwoDim.lean` (below) and
`Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean` of *Moser isotopy*:

- `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two
  (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2) :
  J.IsIntegrable`, as in Decision 6: the charts of
  `exists_isothermal_partialDiffeomorph`, with multiplication by `i`, go to
  `isIntegrable_of_forall_exists_partialDiffeomorph`.
  The docstring ends with the milestone line.
- `TauCeti.Manifold.Orientation.exists_isothermal_coordinates
  (o : Manifold.Orientation I M (Fin 2)) (x : M) :
  ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
  ∀ y ∈ ψ.source, IsConformalMap (mvfderiv I ψ y)`,
  for `[T2Space M]`, `[RiemannianBundle (fun x : M ↦ TangentSpace I x)]`,
  `[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]` and
  `[I.Boundaryless]`, and Mathlib's `mvfderiv`, whose values lie in `ℂ`.
  The finrank of `E` comes from `o` and `x`
  (`fact_finrank_tangentSpace`). The chart is that of
  `exists_isothermal_partialDiffeomorph` for Tau Ceti's
  `o.rightAngleAlmostComplexStructure`
  (`Geometry/Manifold/Riemannian/Orientation/AlmostComplex.lean`, with
  `rightAngleAlmostComplexStructure_apply`);
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

- Tau Ceti, as listed under *What there is* and under *Files taken from Tau
  Ceti*. The chart of
  `CkHolder.lean` follows `TauCeti.Beltrami.exists_isComplexLinear_chart`
  (`Beltrami/Chart.lean`); its docstring credits it.
  `Calculus/ContDiff/Holder.lean` uses Tau Ceti's
  `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt` (`Analysis/Holder/Jet/Bounds.lean`,
  which goes through `LipschitzOnWith.holderOnWith_of_norm_le`),
  `ContDiffAt.exists_ball_bound_iteratedFDeriv`
  (`Analysis/Calculus/ContDiff/Bounds.lean`).
- Mathlib: `HasStrictFDerivAt.toOpenPartialHomeomorph`,
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
| 1 | Planar charts of class `C^{k+1}` for a small $C^{k,\alpha}$ coefficient | `Analysis/Complex/Beltrami/CkHolder.lean`, and the copies under *Files taken from Tau Ceti*, which the move to `c9d170eed5a8` (#2025) deleted | — | 1000 |
| 2 | Planar isothermal charts of class `C^m`, and smooth ones | `Analysis/Calculus/ContDiff/Holder.lean` | 1 | 350 |
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
