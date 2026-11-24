# Equivariant localization

This is the detailed design of part 43 of `DESIGN.md`, *Equivariant
localization*. It proves the milestone *Duistermaat–Heckman localization*
of `atlas/symplectic-group-actions.md`, and settles the two questions that
`DESIGN.md` leaves to this file: how forms with the parameter $\hbar$ are
represented, given that Tau Ceti integrates real top forms only, and how the
contribution of a fixed point is computed in the weight chart.

Sources: McDuff–Salamon [McDuffSalamon2017], §5.6 (Theorem 5.6.1, Remark
5.6.2(i), Lemmas 5.6.3 and 5.6.4), in the conventions of the page; for the
deformation of an equivariantly closed form by $e^{d_\hbar\theta}$ that
replaces the book's Lemma 5.6.4, N. Berline, E. Getzler and M. Vergne,
*Heat Kernels and Dirac Operators*, Grundlehren 298, Springer, 1992,
§7.2 (the localization formula and its proof); for the original
formula, J. J. Duistermaat and G. J. Heckman, *On the variation in the
cohomology of the symplectic form of the reduced phase space*, Invent.
Math. 69 (1982), 259–268.

Paths of new files are under `SymplecticGeometry/`; Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`. All declarations of Tau Ceti
and Mathlib named below were checked against the pinned versions (Tau Ceti
`c9d170eed5a8`).

## Conventions

The conventions are those of *Group actions, moment maps and periods* in
`DESIGN.md`. In Lean the symplectic form is `σ : TauCeti.SmoothTwoForm I M`
(`ω` is notation once `ContDiff` is open), on a compact boundaryless
manifold `M` modelled on `E` with `[Fact (finrank ℝ E = 2 * n)]`. The circle
acts by `[MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]`,
preserving `σ`. The period-one generator is
$\xi_1 = 2\pi\cdot$ `SymplecticGeometry.circleLieGenerator`, its fundamental
vector field is $X$ (Tau Ceti's `TauCeti.fundamentalVectorField I ξ₁`),
and the page's Hamiltonian is $H = \langle\mu,\xi_1\rangle$ for a moment map
$\mu$ in the page's sign, that is
`σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) (fun x ↦ -μ x)`.
Then $\iota_X\sigma = -dH$. In the weight chart at a fixed point the action
is $z_j\mapsto e^{2\pi i k_jt}z_j$, $X=\sum_j2\pi k_j(x_j\partial_{y_j}-y_j\partial_{x_j})$,
and $H = H(p)+\pi\sum_jk_j|z_j|^2$, so the weights at a minimum are
positive, as the page says.

The Cartan differential is $d_\hbar = d-\hbar\,\iota_X$, and
$d_\hbar(\sigma-\hbar H) = -\hbar(\iota_X\sigma+dH) = 0$.

## What there is, and what is missing

- **Forms** (Tau Ceti, `Geometry/Manifold/DifferentialForm/`): smooth forms
  `TauCeti.SmoothForm I M F k` with values in any normed space; the wedge
  `TauCeti.SmoothForm.wedge` with associativity (`Wedge/Smooth/Assoc.lean`)
  and graded commutativity (`wedge_eq_smul_cast_wedge_comm`); wedge powers
  `TauCeti.SmoothForm.wedgePow` (`Wedge/Smooth/Pow.lean`); the exterior
  derivative `mextDerivₗ` with `mextDeriv_mextDeriv` (`Squared.lean`) and the
  Leibniz rule `mextDerivₗ_wedge` (`Wedge/Leibniz.lean`); the interior
  product of rough forms `TauCeti.RoughForm.interior` with
  `interior_self`, its smoothness `IsSmoothForm.interior`
  (`Interior.lean`) and its Leibniz rule `RoughForm.interior_wedge_apply`
  (`Wedge/Interior.lean`); Lie derivatives, and $L_X=d\iota_X+\iota_Xd$ as
  `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add` (`LieDeriv.lean`); and
  `TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`
  (`GroupAction/InvariantForm.lean`): a form invariant under the group has
  zero Lie derivative along every fundamental vector field. There is no
  bundled interior product of smooth forms, and no algebra of forms of
  mixed degree: Tau Ceti's graded ring structure is on de Rham cohomology
  only (`DeRham/Algebra.lean`, through `DirectSum.GRing`).
- **Integration** (`DifferentialForm/Integration/`): `TauCeti.integralTopForm o φ`
  for a real rough top form and an orientation `o`, and Stokes' theorem on
  a boundaryless manifold, `TauCeti.integralTopForm_mextDeriv_eq_zero`, for
  compactly supported `C¹` forms. The comparison of `integralTopForm` with
  the measure `|φ|` of a top form (`TauCeti.RoughForm.measure`,
  `Integration/Measure.lean`) exists only for the Riemannian volume form,
  `TauCeti.integralTopForm_smul_riemannianVolumeForm`
  (`Riemannian/VolumeForm/Measure.lean`).
- **Symplectic volume** (`Geometry/Symplectic/Manifold/`): `σ.volumeForm n`
  $=\sigma^n/n!$, the symplectic orientation
  `IsNondegenerate.volumeOrientation`, the Liouville measure
  `σ.liouvilleMeasure n` $=|\sigma^n/n!|$ (`LiouvilleMeasure.lean`) with
  `MeasurableEmbedding.map_liouvilleMeasure`,
  `Homeomorph.measurePreserving_liouvilleMeasure` and
  `SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm` (Lebesgue
  measure on the product model); the Duistermaat–Heckman measure
  `duistermaatHeckmanMeasure` (`DuistermaatHeckman.lean`), the push-forward
  of the Liouville measure, with `duistermaatHeckmanMeasure_univ`.
- **The model integral** (`MeasureTheory/Measure/Lebesgue/HalfSqRadius.lean`):
  `TauCeti.map_volume_euclideanSpace_half_sq_add_sq`, the push-forward of
  Lebesgue measure under $z\mapsto(|z_j|^2/2)_j$ is $(2\pi)^n$ times Lebesgue
  measure on the closed orthant.
- **Invariant metrics** (`Riemannian/Invariant.lean`):
  `TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`, averaging a
  metric over a compact group.
- **Weights at a fixed point**: Tau Ceti's
  `TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`, translated to
  `StdSpace (Fin n)`, `stdForm`, period-one weights and the page's sign by
  *Equivariant normal forms* (`WeightModel/NormalForm.lean`, #2261). Its
  chart is an equivariant symplectomorphism from an invariant neighbourhood
  of $p$ onto a ball, on which $H$ is $H(p)+\pi\sum_jk_j|z_j|^2$.
- **Sylvester's law of inertia** (Mathlib,
  `LinearAlgebra/QuadraticForm/Signature.lean`):
  `QuadraticForm.sigNeg_of_equiv_weightedSumSquares`.
- **Analytic continuation** (Mathlib): `ProbabilityTheory.complexMGF` with
  `analyticOnNhd_complexMGF`, and
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.

Missing: everything about forms of mixed degree, the Cartan differential,
the localization argument, the comparison of the symplectic top-form
integral with the Liouville measure, and the formula.

## Decisions

1. **Real $\hbar$ for forms, complex $\hbar$ by analytic continuation.**
   The Cartan complex has a real parameter `ħ : ℝ` and real-valued forms,
   so that Tau Ceti's real `integralTopForm` and Stokes' theorem apply as
   they are. The formula is first proved for real $\hbar>0$. The left side,
   $\hbar\mapsto\int_Me^{-\hbar H}\,d\lambda_\sigma$ for the Liouville measure
   $\lambda_\sigma$, is `complexMGF H λσ (-ħ)`, an entire function since $H$
   is bounded and $\lambda_\sigma$ finite; the right side is analytic on
   $\mathbb C\setminus\{0\}$, which is connected. They agree on the positive
   reals, so they agree on $\mathbb C\setminus\{0\}$. Complex-valued forms
   (Tau Ceti's `Complexification.lean`) are not used: the localization
   below evaluates a smooth function of a real variable at $-\hbar s$,
   which has no meaning for complex $\hbar$.
2. **The milestone integrates against the Liouville measure.** The page's
   $\int_Me^{-\hbar H}\omega^n/n!$ is stated as
   `∫ x, Complex.exp (-ħ * H x) ∂σ.liouvilleMeasure n`, which needs no
   orientation and makes sense for complex $\hbar$. It equals the integral
   of the top form $e^{-\hbar H}\sigma^n/n!$ over $M$ with its symplectic
   orientation, by a lemma of its own (issue 6). At $\hbar=0$ it is the
   total Liouville measure, `duistermaatHeckmanMeasure_univ` of the
   Duistermaat–Heckman measure, as the review of #2250 suggested.
3. **Mixed forms are the direct sum** `⨁ k, TauCeti.SmoothForm I M ℝ k`,
   made a ring and an `ℝ`-algebra by instances
   `DirectSum.GRing` and `DirectSum.GAlgebra ℝ` on
   `fun k ↦ TauCeti.SmoothForm I M ℝ k`, with multiplication the wedge, as
   Tau Ceti does for cohomology. The ring laws then come from Mathlib, and
   `DirectSum.of` gives the homogeneous forms. No grading by powers of
   $\hbar$ is kept: $\hbar$ is a number, and an equivariant form is a mixed
   form. Components above the dimension vanish, so the sums are finite.
4. **The Cartan differential is defined for any smooth vector field** `X`,
   not only for a circle action: `cartanDiff X hX ħ`, with
   `hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))`.
   Invariance is the hypothesis that the Lie derivative along `X` of every
   component vanishes; for a circle action it follows from invariance under
   the group by `mlieDerivForm_fundamentalVectorField_eq_zero`. An
   equivariantly closed form is a form with `cartanDiff X hX ħ β = 0`; no
   predicate is defined for it.
5. **Localization by a functional calculus, not by the book's Lemma 5.6.4.**
   For a closed two-form $\tau$, a smooth function $f$ and a smooth
   $F:\mathbb R\to\mathbb R$, put
   $$F(f+\tau) := \sum_{k\ge0}F^{(k)}(f)\,\frac{\tau^k}{k!},$$
   a finite sum of even forms. It is multiplicative,
   $(FG)(f+\tau) = F(f+\tau)\wedge G(f+\tau)$, and the identity function
   gives $f+\tau$. If $\hbar\,\iota_X\tau = df$, then
   $d_\hbar F(f+\tau)=0$: the terms of degree $2k+1$ are
   $F^{(k+1)}(f)(df-\hbar\iota_X\tau)\wedge\tau^k/k!$. Two cases are used:
   - $e^{\sigma-\hbar H}=\exp(-\hbar H+\sigma)$ is equivariantly closed,
     with top component $e^{-\hbar H}\sigma^n/n!$;
   - for an invariant one-form $\theta$, with $s=\theta(X)$ and
     $\eta=d_\hbar\theta=d\theta-\hbar s$, Cartan's formula gives
     $\iota_Xd\theta=-ds$, so every $F(\eta)$ is equivariantly closed. If
     $F(0)=1$ and $G(u)=(1-F(u))/u$, then $1-F(\eta)=d_\hbar(\theta\wedge
     G(\eta))$, so for every equivariantly closed $\beta$,
     $\beta - F(\eta)\wedge\beta = d_\hbar(\theta\wedge G(\eta)\wedge\beta)$,
     whose top component is exact. By Stokes' theorem
     $$\int_M\beta_{[2n]} = \int_M\bigl(F(\eta)\wedge\beta\bigr)_{[2n]}.$$
   When $s\ge0$ vanishes only at the fixed points and $F$ is supported in
   $[-\delta,\delta]$, $F(\eta)$ is supported where $\hbar s\le\delta$, a
   small neighbourhood of the fixed points. This is the deformation of
   Berline–Getzler–Vergne, §7.2, with a cut-off in place of
   $e^{tu}$; it replaces the book's forms supported near a fixed point
   (Lemma 5.6.4) and its localization lemma (Lemma 5.6.3), and needs no
   limit, no boundary and no equivariant homotopy.
6. **The localizing one-form is the model one near each fixed point.**
   With the weight chart $\varphi_p$ at each fixed point $p$, the model
   form $\theta_p=\sum_jk_j(x_jdy_j-y_jdx_j)$ is invariant, with
   $\theta_p(X)=2\pi\sum_jk_j^2|z_j|^2$ and $d\theta_p = 2\sum_jk_j\,dx_j\wedge dy_j$.
   The global $\theta$ is $\sum_p\rho_p\,\varphi_p^*\theta_p+(1-\sum_p\rho_p)\,g(X,\cdot)$
   for an invariant metric $g$ and cut-offs $\rho_p$ that are radial in the
   chart, so invariant, and equal to $1$ near $p$. Then $\theta$ is
   invariant, $s=\theta(X)\ge0$, and $s=0$ exactly on the fixed points
   (the weights are nonzero at isolated fixed points).
7. **The contribution of a fixed point is computed exactly.** Near $p$ the
   chart is symplectic and $H=H(p)+\pi\sum k_j|z_j|^2$, so with
   $\theta_0 = \tfrac12\sum_j(x_jdy_j-y_jdx_j)$, $d\theta_0=\sigma$ and
   $\theta_0(X)=H-H(p)$: there $e^{\sigma-\hbar H}=e^{-\hbar H(p)}\exp(\eta_0)$
   with $\eta_0=d_\hbar\theta_0$, and $\exp(\eta_0)-1 = d_\hbar(\theta_0\wedge
   E(\eta_0))$ with the entire $E(u)=(e^u-1)/u$. Hence near $p$
   $$F(\eta)\wedge e^{\sigma-\hbar H} = e^{-\hbar H(p)}\bigl(F(\eta) +
   d_\hbar(\theta_0\wedge E(\eta_0)\wedge F(\eta))\bigr),$$
   and the second term is compactly supported in the chart, so integrates
   to zero. What remains is
   $\int F^{(n)}(-\hbar s_p)\,(d\theta_p)^n/n!$ on the model, which is
   $2^n\prod_jk_j$ times the Lebesgue integral of
   $F^{(n)}\bigl(-2\pi\hbar\sum_jk_j^2|z_j|^2\bigr)$. Through
   `map_volume_euclideanSpace_half_sq_add_sq` this is an integral over the
   orthant, and $n$ applications of the fundamental theorem of calculus give
   $$\int_{\mathbb R^{2n}}F^{(n)}\Bigl(-\sum_ja_j|z_j|^2\Bigr)\,dz =
   \frac{\pi^n}{\prod_ja_j}\,F(0)\qquad(a_j>0),$$
   so the contribution is $e^{-\hbar H(p)}F(0)/(\hbar^n\prod_jk_j)$ with
   $F(0)=1$. In dimension $0$ every sum and product is empty and the
   argument holds as it is.
8. **The weights are hypotheses, as on the page.** The milestone takes
   `k : M → Fin n → ℤ` and, at each fixed point $p$, a real-linear
   `L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ)` that carries $\sigma_p$ to
   `TauCeti.stdComplexPiSymplecticForm (Fin n)` and conjugates the
   derivative at $p$ of `Circle.exp (2 * π * t) • ·` to
   $z\mapsto(e^{2\pi ik_{p,j}t}z_j)_j$. This is what a unitary basis of an
   invariant compatible complex structure gives; the theorem does not need
   the complex structure itself, so it is not a hypothesis. Nor is the
   connectedness of $M$, which the proof does not use, or the nonvanishing
   of the weights, which follows from the isolation of the fixed points
   (issue 8). The proof uses the chart's
   weights. Their product is that of `k`, since both are read off the
   infinitesimal tangent action $A_p$ (the derivative at $t=0$ of the
   tangent action): $\det A_p=\prod_j(2\pi k_{p,j})^2$ gives its absolute
   value, and the quadratic form $u\mapsto\sigma_p(u,A_pu)$, which is
   $2\pi\sum_jk_{p,j}|z_j|^2$ in the coordinates of `L`, has negative index
   twice the number of negative weights, by Sylvester's law of inertia;
   this gives its sign. A lemma shows that such `k` exist, so the
   hypothesis is never empty.

## Files

| File | Contents |
|---|---|
| `Geometry/Manifold/DifferentialForm/Wedge/Smooth/Graded.lean` | the graded ring of smooth forms |
| `Geometry/Manifold/DifferentialForm/Interior.lean` | the interior product of smooth forms, bundled |
| `Geometry/Manifold/DifferentialForm/Equivariant/Basic.lean` | the Cartan differential |
| `Geometry/Manifold/DifferentialForm/Equivariant/Calculus.lean` | the functional calculus $F(f+\tau)$ |
| `Geometry/Manifold/DifferentialForm/Equivariant/Localization.lean` | the localization lemma |
| `Geometry/Manifold/DifferentialForm/Integration/Measure.lean` | integrating a top form against its measure |
| `Geometry/Symplectic/Manifold/LiouvilleMeasure.lean` | the symplectic case |
| `MeasureTheory/Measure/Lebesgue/HalfSqRadius.lean` | the model integral |
| `Geometry/Symplectic/Hamiltonian/Localization/Weights.lean` | weights at isolated fixed points |
| `Geometry/Symplectic/Hamiltonian/Localization/LocalizingForm.lean` | the one-form $\theta$ of Decision 6 |
| `Geometry/Symplectic/Hamiltonian/Localization/Real.lean` | the formula for real $\hbar>0$ |
| `Geometry/Symplectic/Hamiltonian/Localization/DuistermaatHeckman.lean` | the milestone |

The library's `Integration/Measure.lean`, `LiouvilleMeasure.lean`,
`Interior.lean` and `HalfSqRadius.lean` have the names of Tau Ceti files,
whose declarations they extend; upstream they merge.

## Definitions and their API

### `Wedge/Smooth/Graded.lean`

In `TauCeti.SmoothForm`, on a `C²` manifold: instances `gMul`, `gOne`
(the constant function `1`), `gMonoid`, `gRing` and `gAlgebra` on
`fun k ↦ SmoothForm I M ℝ k`, proved from Tau Ceti's wedge associativity,
unit laws and bilinearity, as `DeRham/Algebra.lean` does for cohomology.
API: `of_mul_of` in the form
`DirectSum.of _ k φ * DirectSum.of _ l ψ = DirectSum.of _ (k + l) (wedge φ ψ)`
(`@[simp]`), `of_zero_one`, `algebraMap_apply`, and
`of_pow : DirectSum.of _ k φ ^ m = DirectSum.of _ (k * m) (wedgePow φ m)`.
Two even homogeneous forms commute (`commute_of_of_of_even`, from
`wedge_eq_smul_cast_wedge_comm`).

### `Interior.lean`

`TauCeti.SmoothForm.interiorProduct X : SmoothForm I M F (k + 1) →ₗ[ℝ] SmoothForm I M F k`,
the interior product with a smooth vector field
`X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯`, with `coe_interiorProduct`
(its rough form is `RoughForm.interior X`), `interiorProduct_interiorProduct`
($\iota_X\iota_X=0$), `interiorProduct_wedge` (the graded Leibniz rule, from
`RoughForm.interior_wedge_apply`) and `interiorProduct_apply_degree_one`
(on a one-form it is evaluation on `X`).

### `Equivariant/Basic.lean`

In `SymplecticGeometry`:

- `cartanDiff X hX ħ : (⨁ k, SmoothForm I M ℝ k) →ₗ[ℝ] ⨁ k, SmoothForm I M ℝ k`,
  defined on homogeneous forms by
  `cartanDiff_of_zero : cartanDiff X hX ħ (of _ 0 f) = of _ 1 (mextDerivₗ f)` and
  `cartanDiff_of_succ : cartanDiff X hX ħ (of _ (k + 1) φ) = of _ (k + 2) (mextDerivₗ φ) - ħ • of _ k (interiorProduct ⟨X, hX⟩ φ)`;
- `cartanDiff_zero_param` (at `ħ = 0` it is `d`), `cartanDiff_mul_of`
  (for `φ` of degree `k`,
  `cartanDiff (of _ k φ * β) = cartanDiff (of _ k φ) * β + (-1) ^ k • of _ k φ * cartanDiff β`),
  and `cartanDiff_mul_of_even` for products of forms with even components;
- `cartanDiff_cartanDiff`: $d_\hbar^2=-\hbar L_X$ on every homogeneous
  form, by Cartan's formula, so `cartanDiff_cartanDiff_of_mlieDerivForm_eq_zero`
  for invariant forms;
- `integralTopForm_cartanDiff_eq_zero`: on a compact boundaryless
  manifold of dimension `m`, the top component of `cartanDiff X hX ħ γ`
  is `mextDerivₗ` of the component of degree `m - 1`, so its integral
  against any orientation is zero.

### `Equivariant/Calculus.lean`

`SymplecticGeometry.formCalculus F hF f τ : ⨁ k, SmoothForm I M ℝ k` for
`F : ℝ → ℝ` with `hF : ContDiff ℝ ∞ F`, `f : C^∞⟮I, M; ℝ⟯` and a two-form
`τ`: the sum over `k ≤ finrank ℝ E` of
`of _ (2 * k) ((k ! : ℝ)⁻¹ • iteratedDeriv k F ∘ f • wedgePow τ k)`. API:
`formCalculus_apply` (its components), `formCalculus_zero_component`
(`F ∘ f`), `formCalculus_mul` (`F * G`), `formCalculus_id`
(`of _ 0 f + of _ 2 τ`), `formCalculus_const`, `tsupport_formCalculus_subset`
(each component vanishes outside `f ⁻¹' tsupport F`), and
`cartanDiff_formCalculus`: if `τ` is closed and
`ħ • interiorProduct ⟨X, hX⟩ τ = mextDerivₗ f`, then
`cartanDiff X hX ħ (formCalculus F hF f τ) = 0`. The exponential
`formCalculus Real.exp _ (-ħ • H) σ` is the page's $e^{\sigma-\hbar H}$;
it gets no name of its own.

### `Equivariant/Localization.lean`

For a one-form `θ` with zero Lie derivative along `X`, put
`s := θ(X)` and `η := formCalculus · · (-ħ • s) (mextDerivₗ θ)`. Then
`sub_formCalculus_eq_cartanDiff` (for `F 0 = 1`,
`1 - formCalculus F hF (-ħ • s) (dθ) = cartanDiff X hX ħ (of _ 1 θ * formCalculus G hG (-ħ • s) (dθ))`
with `G u = (1 - F u) / u`, smooth since `F 0 = 1`), and the localization
lemma `integralTopForm_formCalculus_mul`: on a compact boundaryless
manifold of dimension `m`, for `F 0 = 1` and `cartanDiff X hX ħ β = 0`,
`integralTopForm o ((formCalculus F hF (-ħ • s) (dθ) * β) m) = integralTopForm o (β m)`.

### `Integration/Measure.lean` and `LiouvilleMeasure.lean`

`TauCeti.integralTopForm_smul_eq_integral_measure`: for a continuous top
form `φ` that is nonnegative on every positively oriented basis of `o`,
and a continuous compactly supported `f`,
`integralTopForm o (fun x ↦ f x • φ x) = ∫ x, f x ∂φ.measure`. The proof is
that of `TauCeti.integralTopForm_smul_riemannianVolumeForm`, credited by
name. Its symplectic case is
`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_smul_volumeForm`:
`integralTopForm (h.volumeOrientation hn) (fun x ↦ f x • σ.volumeForm n x) = ∫ x, f x ∂σ.liouvilleMeasure n`.

### `HalfSqRadius.lean`

`TauCeti.setIntegral_iteratedDeriv_neg_sum`: for `F` smooth with compact
support, the integral over the closed orthant of $\mathbb R^\iota$ of
`iteratedDeriv (card ι) F (-∑ i, t i)` is `F 0`; and
`TauCeti.integral_iteratedDeriv_neg_sum_mul_sq`: for `a i > 0`,
`∫ z, iteratedDeriv (card ι) F (-∑ i, a i * (z.1 i ^ 2 + z.2 i ^ 2)) = F 0 * π ^ card ι / ∏ i, a i`
on `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, by
`map_volume_euclideanSpace_half_sq_add_sq`.

### `Localization/Weights.lean`

For a symplectic circle action with a moment map, at a fixed point `p`:
`prod_weights_eq` (two families of weights given as in Decision 8 have the
same product), `weights_ne_zero_of_isolated` (at an isolated fixed point
no weight vanishes, since a zero weight gives a fixed disc in the chart),
`exists_weights` (weights as in Decision 8 exist, from the chart of
`WeightModel/NormalForm.lean`), and `finite_fixedPoints` (on a compact
manifold, isolated fixed points are finite).

### `Localization/LocalizingForm.lean`

`exists_localizingForm`: for isolated fixed points on a compact `M`, a
smooth invariant one-form `θ` such that `θ(X) ≥ 0`, with equality exactly at the
fixed points, and equal near each fixed point `p` to the pullback of the
model form $\theta_p$ under the weight chart, as in Decision 6. It is an
existence theorem, not a definition.

## Main results

| Result | Lean name | File |
|---|---|---|
| localization lemma | `SymplecticGeometry.integralTopForm_formCalculus_mul` | `Equivariant/Localization.lean` |
| top forms and their measure | `TauCeti.integralTopForm_smul_eq_integral_measure` | `Integration/Measure.lean` |
| the model integral | `TauCeti.integral_iteratedDeriv_neg_sum_mul_sq` | `HalfSqRadius.lean` |
| the formula for real $\hbar>0$ | `SymplecticGeometry.integral_exp_neg_mul_eq_finsum_of_pos` | `Localization/Real.lean` |
| the milestone | `SymplecticGeometry.integral_cexp_neg_mul_eq_finsum_fixedPoints` | `Localization/DuistermaatHeckman.lean` |
| its value at $\hbar=0$ | `SymplecticGeometry.tendsto_finsum_fixedPoints_liouvilleMeasure` | `Localization/DuistermaatHeckman.lean` |

The milestone, with `H x := μ x ξ₁` and `fixedPoints := MulAction.fixedPoints Circle M`:

```lean
theorem integral_cexp_neg_mul_eq_finsum_fixedPoints [CompactSpace M]
    [BoundarylessManifold I M] (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (g • ·) _ σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M)
      (fun x ↦ -μ x))
    (hiso : ∀ p ∈ fixedPoints, ∀ᶠ x in 𝓝[≠] p, x ∉ fixedPoints)
    (k : M → Fin n → ℤ)
    (hk : ∀ p ∈ fixedPoints, ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ),
      (∀ v w, σ.eval₂ p v w = stdComplexPiSymplecticForm (Fin n) (L v) (L w)) ∧
      ∀ (t : ℝ) v, L (mfderiv I I (Circle.exp (2 * π * t) • ·) p v) =
        fun j ↦ Complex.exp (2 * π * k p j * t * Complex.I) * L v j)
    {ħ : ℂ} (hħ : ħ ≠ 0) :
    ∫ x, Complex.exp (-ħ * H x) ∂σ.liouvilleMeasure n =
      ∑ᶠ p ∈ fixedPoints, Complex.exp (-ħ * H p) / (ħ ^ n * ∏ j, (k p j : ℂ))
```

Here the `_` is the smoothness of `g • ·`, `ContMDiffSMul.contMDiff_const_smul g`,
and the variables are those of *Conventions*.

For the value at $\hbar=0$: under the same hypotheses the right side tends,
as `ħ → 0` in `𝓝[≠] 0`, to `(σ.liouvilleMeasure n univ).toReal`. Both
docstrings end with the milestone line. The real theorem has the same
hypotheses, real `ħ > 0` and `Real.exp`, and the left side as
`integralTopForm` of the top component of $e^{\sigma-\hbar H}$, which
Decision 2's lemma turns into the Liouville integral.

## What it uses

- From other parts: `SymplecticGeometry.circleLieGenerator`
  (`Geometry/Lie/Exponential/Circle.lean`, merged) and
  `GroupAction/Circle.lean` of *Lie group actions* (#2256: the generator
  $\xi_1$ and the fixed points as the zeros of $X$); the weight chart of
  `WeightModel/NormalForm.lean` of *Equivariant normal forms* (#2261). The
  invariant primitives of `GroupAction/InvariantPrimitive.lean` are not
  needed.
- From Tau Ceti: the declarations of *What there is*.
- From Mathlib: `DirectSum.GRing`, `DirectSum.GAlgebra`, `iteratedDeriv`,
  `integral_Ioi_of_hasDerivAt_of_tendsto`, `ProbabilityTheory.complexMGF`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
  `QuadraticForm.sigNeg_of_equiv_weightedSumSquares`.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **The graded ring of smooth forms.** `Wedge/Smooth/Graded.lean`. About
   250 lines. No blockers.
2. **The interior product of smooth forms.** `Interior.lean`. About 150
   lines. No blockers.
3. **The Cartan differential.** `Equivariant/Basic.lean`. About 300 lines.
   Blocked by 1 and 2.
4. **The functional calculus of an even form.** `Equivariant/Calculus.lean`.
   About 350 lines. Blocked by 3.
5. **The localization lemma.** `Equivariant/Localization.lean`. About 250
   lines. Blocked by 4.
6. **Top forms and their measure.** `Integration/Measure.lean` and
   `LiouvilleMeasure.lean`. About 250 lines. No blockers.
7. **The model integral.** `HalfSqRadius.lean`. About 200 lines. No
   blockers.
8. **Weights at isolated fixed points.** `Localization/Weights.lean`. About
   300 lines. Blocked by #2256 and #2261.
9. **The localizing one-form.** `Localization/LocalizingForm.lean`. About
   300 lines. Blocked by 8.
10. **The formula for real $\hbar$.** `Localization/Real.lean`, by
    Decisions 5 and 7. About 350 lines. Blocked by 5, 6, 7 and 9.
11. **The milestone.** `Localization/DuistermaatHeckman.lean`, by Decisions
    1 and 2. About 150 lines. Blocked by 10.

Issues 1, 2, 6 and 7 can start at once.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.6.
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac
  Operators*, Grundlehren der mathematischen Wissenschaften 298,
  Springer, 1992, §7.2.
* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology
  of the symplectic form of the reduced phase space*, Invent. Math. 69
  (1982), 259–268.
