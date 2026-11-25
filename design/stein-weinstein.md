# Stein and Weinstein structures

The detailed design of part 65 of `DESIGN.md`, *Stein and Weinstein
structures*. It fixes the files of the part, its definitions and their
API, the Lean statements of its two milestones, what it takes from Tau
Ceti, Mathlib and the other parts, and the building issues in the order
they can be done.

The part proves two milestones of `atlas/constructing-symplectic-manifolds.md`
(§7.4): *Passage between Stein and Weinstein structures* and *Stein and
Weinstein complements of Donaldson hypersurfaces*. Its sources are
McDuff–Salamon [McDuffSalamon2017], Definitions 7.4.5, 7.4.7 and 7.4.8 and
Remarks 7.4.6 and 7.4.9 (pp. 332–334); Cieliebak–Eliashberg
[CieliebakEliashberg2012], for the definitions of gradient-like fields,
Weinstein structures and Weinstein homotopies, for the Weinstein manifold
of a Stein function and its completeness reparametrization (§11.5,
Definition 11.15 and Remark 11.16), and for the two directions of their
Theorem 1.1 (a) (Theorem 13.9 and the results it rests on); and
Giroux [Giroux2017], Theorems 1 and 2, Remark 3, Corollary 4 and Sections
B and C.

Paths of Tau Ceti files are relative to `.lake/packages/TauCeti/TauCeti/`,
and every Tau Ceti name below was checked at commit `0651fdb`, the version
that `lakefile.toml` pins now. Paths of new files are under
`SymplecticGeometry/`. A new name without a namespace is in
`SymplecticGeometry`.

## Signs and setting

The page's conventions (*Liouville, Weinstein and Stein* in `DESIGN.md`)
fit Tau Ceti's without a change of sign.

- **Liouville fields.** A Liouville field `X` of `ω` has
  $\mathcal L_X\omega=\omega$ (Tau Ceti's
  `TauCeti.IsLiouvilleVectorField ω.val X`), and its primitive is
  $\lambda=\iota_X\omega$ with $d\lambda=\omega$: this is Tau Ceti's
  primitive `RoughForm.interior X ω.val`, the `β` of
  `design/liouville-structures.md`. A Weinstein domain is built on a
  strong filling of the merged *Liouville structures*, whose primitives
  have the book's sign ($\beta=-\lambda_{\text{book}}$). Its field `Y`
  and form are the same in both conventions, and Weinstein structures and
  domains mention no primitive, so no conversion is needed.
- **Stein functions.** The part works on a complex manifold in Tau Ceti's
  sense: `[NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]`, seen
  as a real manifold over `𝓘(ℝ, E)`, as Tau Ceti's
  `Geometry/Manifold/Complex/DdbarForm/` does. Its complex structure is
  `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, which acts
  as multiplication by `Complex.I` on each tangent space. For a smooth
  real function `f`, write $\lambda_f=-df\circ J$, whose exterior
  derivative is $\omega_f$.
  The value of $\lambda_f$ on `v` is `-mfderiv f x (Complex.I • v)`, Tau
  Ceti's `dC` of `f` read as a complex function (`dC_apply_apply`), and
  $\omega_f$ is twice Tau Ceti's `TauCeti.ddbarForm E f`, by
  `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`. With these signs,
  $f=|z|^2$ on `ℂ` gives $\omega_f=4\,dx\wedge dy$, and
  $\omega_f(v,Jv)>0$ is strict plurisubharmonicity.
- **An integrable complex structure on an open set.** Giroux's complex
  structure lives on the complement of a hypersurface in a manifold that
  is not complex. The part states it as a complex manifold `N` in the
  sense above and a diffeomorphism of `N`, as a real manifold, onto the
  open submanifold. This is the same as an integrable structure in the
  sense of the library's `SmoothAlmostComplexStructure.IsIntegrable`
  (`Geometry/Manifold/Complex/Integrable.lean`), whose charts make the
  complement a complex manifold, but it lets every statement about
  plurisubharmonic functions use Tau Ceti's notions. No new
  plurisubharmonicity predicate for an almost complex structure on a real
  manifold is defined.
- **Dimension and degenerate cases.** A Weinstein structure needs a
  symplectic form, so an odd-dimensional model forces `M` to be empty, and
  every statement then holds trivially. In dimension zero, a proper
  function bounded below on a discrete space forces `M` finite, and every
  point is a nondegenerate critical point; the first milestone holds
  there with the zero field. Nothing in Giroux's theorem assumes the
  hypersurface `Z` nonempty.

## Decisions

`DESIGN.md` leaves these questions to this file.

- **Gradient-like fields.** The book's quantitative condition
  (Definition 7.4.5), which is also Cieliebak–Eliashberg's: `X`
  is gradient-like for `f` if, for some smooth Riemannian metric and some
  continuous positive function `δ`,
  $df(X)\ge\delta\,(|X|^2+|df|^2)$. Tau Ceti's
  `TauCeti.IsAdaptedPseudoGradient` is not used for it: it asks the field
  to be linear in a Morse chart at each critical point, which a Liouville
  field near a critical point is not, and it is written for decreasing
  functions. The metric is `g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
  (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)` (Mathlib), and $|df|^2$ is the
  square norm of Tau Ceti's `TauCeti.mgradient` for the
  `RiemannianBundle` instance that `g` gives, introduced by `letI` in the
  definition only.
- **Generalized Morse functions.** Critical points are nondegenerate (Tau
  Ceti's `TauCeti.IsManifoldNondegenerateCriticalPoint`) or of birth–death
  type: in some chart of the maximal atlas,
  $f=f(p)+z_1^3-\sum_{2\le i\le k+1}z_i^2+\sum_{i>k+1}z_i^2$. Neither
  library has the second kind. Weinstein *structures* only need it
  because Weinstein *homotopies* pass through it; the part defines it in
  Tau Ceti's style, with a chart structure `BirthDeathChart E f p` beside
  Tau Ceti's `TauCeti.MorseChart`.
- **Weinstein structures as a predicate on a triple.** As in
  Cieliebak–Eliashberg, a Weinstein structure is the triple
  $(\omega,X,f)$: `IsWeinsteinStructure ω X f`, with the primitive
  $\iota_X\omega$ derived. The field is data, not an existential as in
  Tau Ceti's `IsLiouvilleDomain`, since the homotopy and the gradient-like
  condition both mention it.
- **Stein structures.** On a complex manifold, a Stein structure is a
  function: `IsSteinFunction E φ`, smooth, proper, bounded below and
  strictly plurisubharmonic at every point (Tau Ceti's
  `TauCeti.IsManifoldStrictlyPlurisubharmonicAt`). It asks no Morse
  condition, as the page does not; where a Morse function is needed, Tau
  Ceti's `exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt`
  perturbs it. Tau Ceti's `TauCeti.IsSteinManifold`, defined by holomorphic
  convexity, is not related to it: no milestone needs that (Grauert's
  theorem would be a part of its own).
- **The converse up to homotopy.** A Weinstein homotopy on `M` is a family
  `t ↦ (ω t, X t, f t)` over `[0, 1]`, smooth in `(t, x)` in the sense of
  *Smooth families* (`DESIGN.md`, *Manifolds, families and signs*), each
  member a Weinstein structure, and with Cieliebak–Eliashberg's
  condition at infinity: continuous functions $c_1<c_2<\dots$ on `[0, 1]`, tending to infinity
  uniformly, with $c_k(t)$ a regular value of `f t` for all `k` and `t`.
  On a compact `M` it holds with $c_k(t)=\max f_t+k$, whose levels are
  empty; the building issue proves this as a lemma.
- **The route to the converse.** Cieliebak–Eliashberg's proof, followed
  chapter by chapter, is the only proof known to this design. The part
  plans it as a sequence of supporting files (*Files*), each an issue or a
  few. The largest blocks (the $J$-convex surrounding of totally real
  discs, the normal forms of Weinstein homotopies, and Stein handle
  attachment) begin with an issue that extends this file by their lemma
  lists, since their split depends on the Lean form of the earlier blocks.
- **Giroux's theorem waits for part 64.** Its hypersurfaces are zero sets
  of the quasiholomorphic sections of Giroux's Section B, built with the
  peak sections, the transversality estimates and the line bundle of
  *Asymptotically holomorphic sections*. The statement of `Complement/Basic.lean`
  uses that part's notion of a degree-`k` hypersurface, whose name its
  design file (#3290) fixes. The issues of `Complement/` therefore come
  after that design file, and each begins by checking its statement
  against it.

## Files and declarations

| File | Contents | Issues |
|---|---|---|
| `Geometry/Manifold/Morse/GradientLike.lean` | gradient-like fields and their API | 1 |
| `Geometry/Manifold/Morse/BirthDeath.lean` | birth–death charts, generalized Morse functions | 2 |
| `Geometry/Manifold/Complex/Plurisubharmonic.lean` | $\lambda_f$, $\omega_f$, Stein functions, positivity | 3, 4 |
| `Geometry/Symplectic/Weinstein/Basic.lean` | Weinstein structures and domains | 5 |
| `Geometry/Symplectic/Weinstein/Completion.lean` | the completion of a Weinstein domain | 6 |
| `Geometry/Symplectic/Weinstein/Homotopy.lean` | Weinstein homotopies | 7 |
| `Geometry/Symplectic/Weinstein/Stein.lean` | both directions of the passage; first milestone | 8, 9, 21 |
| `Geometry/Manifold/Complex/JConvex/` | the $J$-convex toolkit of the converse | 10–14 |
| `Geometry/Symplectic/Weinstein/Handle/` | Weinstein cobordisms, handles and their homotopies | 15–18 |
| `Geometry/Symplectic/Weinstein/SteinHandle.lean` | Stein structures on elementary cobordisms | 19, 20 |
| `Geometry/Symplectic/Weinstein/Complement/` | Giroux's Sections B and C; second milestone | 22–27 |

### `Geometry/Manifold/Morse/GradientLike.lean`

In `TauCeti`, since it is about Tau Ceti's and Mathlib's notions only,
for a boundaryless `M` over `𝓘(ℝ, E)` with `E` finite-dimensional:

- `IsGradientLike (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop`,
  the existence of a metric `g` and a continuous `δ > 0` with
  `δ x * (g.inner x (X x) (X x) + ‖mgradient f x‖ ^ 2) ≤ mvfderiv f x (X x)`
  for every `x` (the gradient and its norm for `g`).
- `IsGradientLike.mvfderiv_apply_pos` ($df(X)>0$ off the critical
  points), `IsGradientLike.eq_zero_iff` (the zeros of `X` are the critical
  points of `f`), `IsGradientLike.strictMono_comp` (`f` increases along an
  integral curve that meets no critical point), `IsGradientLike.smul`
  (by a continuous positive function `a`, with $\delta\min(a,a^{-1})$),
  `IsGradientLike.comp` (`h ∘ f` for `h` with `h' > 0`), and
  `isGradientLike_mgradient` (the gradient of `f` for any smooth metric,
  with `δ = 1 / 2`).
- `isGradientLike_of_forall_exists_nhds`: the condition is local. If each
  point has a neighbourhood, a metric and a constant for which the
  inequality holds there, the metrics glue by a partition of unity: for a
  convex combination of metrics, $|X|^2$ is the combination, and $|df|^2$ is
  at most the combination, since inverting a positive definite form is
  convex. Near a point where $df(X)>0$ the inequality holds for any metric
  and a small constant, so only the critical points need an argument; this
  is how later files check the condition.

Expected size: 300 lines.

### `Geometry/Manifold/Morse/BirthDeath.lean`

In `TauCeti`, beside Tau Ceti's `Morse/Lemma.lean`:

- `BirthDeathChart E f p`: a chart of the smooth maximal atlas centred at
  `p`, coordinates `coord` as in `TauCeti.MorseChart`, and an index `k`,
  with `f` equal to $f(p)+z_1^3-\sum_{2\le i\le k+1}z_i^2+\sum_{i>k+1}z_i^2$
  on its source; `restr` and its lemmas, as for `MorseChart`.
- `IsGeneralizedMorse (f : M → ℝ) : Prop`: smooth, and every critical
  point nondegenerate or the centre of a birth–death chart.
  `IsMorse.isGeneralizedMorse`, `IsGeneralizedMorse.isClosed_criticalPoints`
  and `IsGeneralizedMorse.isDiscrete_criticalPoints` (so the critical
  points of a proper one in a sublevel are finite), and
  `IsGeneralizedMorse.comp` (`h ∘ f`, `h' > 0`).
- An example: the cubic on `ℝ` is generalized Morse and not Morse.

Expected size: 350 lines.

### `Geometry/Manifold/Complex/Plurisubharmonic.lean`

In `SymplecticGeometry`, on a complex manifold as in *Signs and setting*.
Issue 3:

- `realDC (f : M → ℝ) : SmoothForm 𝓘(ℝ, E) M ℝ 1` for smooth `f`
  (junk value otherwise), $-df\circ J$, with `realDC_apply`
  (`realDC f x ![v] = -mfderiv f x (Complex.I • v)`, from
  `dC_apply_apply` and `toEndomorphism_ofComplexManifold`), `realDC_add`,
  `realDC_smul`, and `realDC_comp`
  ($\lambda_{h\circ f}=h'(f)\,\lambda_f$).
- `realDDC f : SmoothTwoForm 𝓘(ℝ, E) M`, `mextDerivₗ _ 1 (realDC f)`,
  closed; `realDDC_apply_eq_two_mul_ddbarForm`
  (`= 2 • ddbarForm E f`, from `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`),
  and `realDDC_comp` ($\omega_{h\circ f}=h'(f)\,\omega_f+h''(f)\,df\wedge\lambda_f$).

Issue 4:

- `isManifoldStrictlyPlurisubharmonicAt_iff_realDDC_pos`: for `f`
  smooth at `x`, `IsManifoldStrictlyPlurisubharmonicAt E f x ↔ ∀ v ≠ 0,
  0 < realDDC f x v (Complex.I • v)`, from
  `mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm` and
  `isManifoldStrictlyPlurisubharmonicAt_iff`. This is the lemma that
  `DESIGN.md` asks for.
- `IsSteinFunction E φ` (a structure: `contMDiff`, `isProperMap`,
  `bddBelow`, `isStrictlyPlurisubharmonic`), with `IsSteinFunction.comp`
  (`h ∘ φ` for smooth `h` with `h' > 0`, `h'' ≥ 0` and `h` tending to
  infinity, from Tau Ceti's `IsManifoldStrictlyPlurisubharmonicAt.scalar_comp`),
  `IsSteinFunction.exists_isMorse` (Tau Ceti's perturbation), and the
  example `isSteinFunction_norm_sq` ($|z|^2$ on `E`).
- For a Stein function, `realDDC φ` is a Kähler form for
  `ofComplexManifold E M`: `IsSteinFunction.isKahler_realDDC` (Tau
  Ceti's `TauCeti.SmoothTwoForm.IsKahler`; closed, compatible by the
  positivity lemma and the $J$-invariance of `ddbarForm`, and the
  Nijenhuis tensor vanishes by the library's
  `isIntegrable_ofComplexManifold` and `IsIntegrable.nijenhuis_eq_zero`). Hence
  `IsSteinFunction.isSymplectic_realDDC`.

Expected size: 300 lines for issue 3, 350 for issue 4.

### `Geometry/Symplectic/Weinstein/Basic.lean`

Issue 5. For a boundaryless `M` over `𝓘(ℝ, E)`, `E` finite-dimensional:

```lean
structure IsWeinsteinStructure (ω : SmoothTwoForm 𝓘(ℝ, E) M)
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : M → ℝ) : Prop where
  isSymplectic : ω.IsSymplectic
  contMDiff_field : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% X)
  isLiouvilleVectorField : IsLiouvilleVectorField ω.val X
  isCompleteVectorField : IsCompleteVectorField X
  isProperMap : IsProperMap f
  bddBelow : BddBelow (range f)
  isGeneralizedMorse : IsGeneralizedMorse f
  isGradientLike : IsGradientLike f X
```

with `IsWeinsteinStructure.mextDeriv_interior` ($d(\iota_X\omega)=\omega$,
from Tau Ceti's `isLiouvilleVectorField_iff_mextDeriv_interior_eq`),
`IsWeinsteinStructure.comp` (`h ∘ f`), `IsWeinsteinStructure.pullback`
(along a diffeomorphism), and the example of `ℂⁿ` with the radial field
and $|z|^2$, from Tau Ceti's `Liouville/Radial/`.

A Weinstein domain is a compact manifold with boundary over the
half-space, as a strong filling is in *Liouville structures*:
`IsWeinsteinDomain σ Y f c` asks `IsStrongFilling σ univ Y`, `f` smooth
with `f = c` on `∂W` and `f < c` on the interior, and, on the interior
as a boundaryless manifold (Tau Ceti's `BoundarylessModel.interiorChartedSpace`,
as in `Liouville/Domain.lean`), `f` generalized Morse and `Y` gradient-like
for it. `IsWeinsteinDomain.mvfderiv_pos_of_mem_boundary` and the finiteness
of the critical points follow.

Expected size: 450 lines.

### `Geometry/Symplectic/Weinstein/Completion.lean`

Issue 6. The completion of a Weinstein domain, built by
`IsStrongFilling.Completion`, carries a Weinstein structure: the form
`completionForm`, the field `completionField` (both from
`Liouville/Completion.lean`), and the function equal to `f` on `W` and to
$c+\varepsilon\,(e^{s}-1)$, smoothed along the collar, on the end
(Remark 7.4.6). `IsWeinsteinDomain.isWeinsteinStructure_completion`, with
completeness from `isCompleteVectorField_completionField`.

Expected size: 400 lines.

### `Geometry/Symplectic/Weinstein/Homotopy.lean`

Issue 7. `IsWeinsteinHomotopy ω X f` for families over `ℝ`, read on
`[0, 1]`, as in *Decisions*; `IsWeinsteinHomotopy.refl`, `.symm`,
`.trans` (after a reparametrization of time that is flat at the ends),
`.pullback`, and `IsWeinsteinHomotopy.of_isCompact` (the condition at
infinity on a compact manifold). Also the relation
`AreWeinsteinHomotopic` between two Weinstein structures and that it is
an equivalence relation.

Expected size: 450 lines.

### `Geometry/Symplectic/Weinstein/Stein.lean`

Issue 8: the Weinstein structure of a Stein function.

- `dCLiouvilleField φ`, the vector field with
  `ι (dCLiouvilleField φ) (realDDC φ) = realDC φ`, defined by the inverse of the flat map of
  `realDDC φ` where it is nondegenerate (Tau Ceti's
  `SmoothTwoForm.IsNondegenerate.interiorEquiv`), zero elsewhere; it is
  the gradient of `φ` for the Kähler metric $\omega_\varphi(\cdot,J\cdot)$,
  so `isGradientLike_dCLiouvilleField` with `δ = 1 / 2`, and
  `isLiouvilleVectorField_dCLiouvilleField`.
- `IsSteinFunction.exists_comp_isCompleteVectorField`
  (Cieliebak–Eliashberg, Remark 11.16): a smooth convex increasing `h` with
  `dCLiouvilleField (h ∘ φ)` complete. The field of `h ∘ φ` is computed from
  `realDDC_comp`, and `h` is chosen to grow fast enough on each
  sublevel of `φ`. Tau Ceti's `isCompleteVectorField_rateDampedField`
  proves completeness of a field damped by a similar estimate; if the
  building issue follows its proof, it credits it.

Issue 9: the first half of the milestone.
`IsSteinFunction.exists_isWeinsteinStructure`: for a Stein function `φ`
there is a Stein function `ψ`, Morse and of the form `h ∘ φ'` for a Morse
perturbation `φ'` of `φ`, with
`IsWeinsteinStructure (realDDC ψ) (dCLiouvilleField ψ) ψ`; and
`IsSteinFunction.isWeinsteinStructure_comp` for `φ` already generalized
Morse, with `ψ = h ∘ φ`.

Issue 21: the second half and the milestone,
`IsWeinsteinStructure.exists_isSteinFunction_areWeinsteinHomotopic`:
for `M` over `EuclideanSpace ℝ (Fin (2 * n))`, second countable and
Hausdorff, and `IsWeinsteinStructure ω X f`, there are a complex manifold
`N` over `EuclideanSpace ℂ (Fin n)`, a diffeomorphism
`e : N ≃ₘ⟮𝓘(ℝ, _), 𝓘(ℝ, _)⟯ M` and a Stein function `ψ` on `N`,
generalized Morse and with `dCLiouvilleField ψ` complete, such that
`(ω, X, f)` is Weinstein homotopic to the pushforward along `e`
of `(realDDC ψ, dCLiouvilleField ψ, ψ)`. The theorem
`exists_isWeinsteinStructure_of_isSteinFunction_and_areWeinsteinHomotopic`
is the conjunction of the two halves, in the
page's form. Docstring line: "Milestone: *Passage between Stein and
Weinstein structures*."

Expected size: 400 lines for issue 8, 250 for issue 9, 400 for issue 21.

### `Geometry/Manifold/Complex/JConvex/`

The analytic results of Cieliebak–Eliashberg on $J$-convex functions
(their name for strictly plurisubharmonic ones) that the converse uses
and that neither library has. Each file is in
`SymplecticGeometry`, on a complex manifold as above.

- `Hypersurface.lean` (issue 10): $J$-convex hypersurfaces, as regular
  levels of strictly plurisubharmonic functions; the Levi form of a level
  and its independence of the defining function (Tau Ceti's
  `manifoldLeviForm` and `Pseudoconvex/` give the pointwise part); the
  contact structure of complex tangencies on a $J$-convex level, as a
  contact form `realDC` restricted (Tau Ceti's `IsContactForm`).
- `Smoothing.lean` (issue 11): smoothing of the maximum of two strictly
  plurisubharmonic functions, and gluing by
  $\max$ near a hypersurface.
- `TotallyReal.lean` (issue 12): for a totally real submanifold (Tau
  Ceti's `IsTotallyRealEmbedding`, `TotallyReal/AdaptedChart/`), the
  squared distance for a suitable metric is strictly plurisubharmonic near
  it (Tau Ceti's `SquaredDistance.lean` has the complex-chart
  computation); isotropic submanifolds of a $J$-convex level, tangent to
  the complex tangencies, are totally real.
- `Surround.lean` (issues 13 and 14): the $J$-convex surrounding of a
  totally real disc attached to a $J$-convex level, split into a design issue and its parts as
  *Decisions* says.

Expected size: 400 lines each for issues 10–12; issues 13 and 14 are
sized by their design issue.

### `Geometry/Symplectic/Weinstein/Handle/`

The symplectic side of the converse: Cieliebak–Eliashberg's Morse and
Weinstein theory before Theorem 13.9.

- `Cobordism.lean` (issue 15): Weinstein cobordisms between two regular
  levels; elementary cobordisms (critical points in one level); the stable
  disc of a critical point is isotropic and its boundary sphere is an
  isotropic sphere in the contact lower level (from Tau Ceti's
  `Contact/Isotropic.lean`).
- `Model.lean` (issue 16): the standard Weinstein handle of index `k` on
  `ℂⁿ`, and the attachment of a handle along an isotropic sphere with its
  conformal symplectic normal framing (Tau Ceti's
  `Contact/ConformalSymplecticNormal.lean`).
- `Homotopy.lean` (issues 17 and 18): normal forms of Weinstein
  homotopies: two Weinstein structures on an elementary
  cobordism with the same function and isotopic attaching spheres are
  homotopic; creation and cancellation of critical points; a Weinstein
  structure is homotopic to one adjusted to a handle decomposition. Issue
  17 is its design issue.

Expected size: 450 lines for each of issues 15 and 16; issue 18 is sized
by issue 17.

### `Geometry/Symplectic/Weinstein/SteinHandle.lean`

Issues 19 and 20: Cieliebak–Eliashberg's proof of Theorem 13.9. A
Stein function on the lower part extends across an elementary Weinstein
cobordism attached along isotropic spheres, made totally real by issue
12, by the surrounding of issues 13–14 and the smoothing of issue 11;
the Weinstein structure of the extension is homotopic to the given one by
issue 18. Issue 19 covers one critical level; issue 20 runs the induction
over an exhaustion by regular sublevels (Tau Ceti's
`IsMorse.exists_regular_sublevel_exhaustion`, adapted to generalized Morse
functions), with the condition at infinity of the homotopy.

Expected size: 500 lines each.

### `Geometry/Symplectic/Weinstein/Complement/`

Giroux's paper, for a closed integral symplectic manifold, in the
conventions of *Integral classes and line bundles* in `DESIGN.md`.

- `Quasiholomorphic.lean` (issue 22): quasiholomorphic sections
  (Definition 11) and Lemma 12, on the sections and estimates of
  *Asymptotically holomorphic sections*.
- `Transversality.lean` (issue 23): the derivative transversality of
  Lemma 14 and the local estimates of Lemmas 15–16.
- `Weinstein.lean` (issue 24): Proposition 13: for large `k`, the
  function $-\log|s_k|^2$ on the complement, modified near its critical
  points, is generalized Morse, and the Liouville field of the primitive
  $d^c$ of it, for the connection, is gradient-like; with the collar of
  the normal circle bundle of `Z` this gives the Weinstein domain `F`.
- `Stein.lean` (issue 25): Section C: Cieliebak–Eliashberg's theorem
  (issue 21), its version with the symplectic form fixed (Corollary 18,
  through Moser's argument and *Moser isotopy*), and the rescaling of
  Lemma 19, give the complex manifold `N`, the diffeomorphism onto the
  complement and the Stein function `φ`, with `realDDC φ` the pullback
  of `ω` and no critical point near `Z`.
- `Basic.lean` (issue 26): the milestone,
  `exists_steinFunction_and_weinsteinDomain_compl`: for every large `k`,
  a degree-`k` hypersurface `Z` of part 64 with both conclusions: the
  Stein conclusion of `Stein.lean`, the Stein function with finitely many
  critical points; and a Weinstein domain `F` (`IsWeinsteinDomain`), a
  symplectomorphism of its interior onto the complement of `Z`, which
  extends continuously to `F` and maps `∂F` onto `Z` as the projection
  of the normal circle bundle (Tau Ceti's tubular neighbourhoods). Docstring
  line: "Milestone: *Stein and Weinstein complements of Donaldson
  hypersurfaces*."
- `Skeleton.lean` (issue 27): Remark 3 (Giroux's hypersurfaces are
  Hamiltonian isotopic to the zero sets of part 64, by *Hamiltonian
  flows*) and Corollary 4 (the skeleton of the Weinstein domain, the union
  of the stable manifolds of its critical points, is a finite union of
  isotropic submanifolds, and its complement is symplectomorphic to the
  disc bundle of area $1/k$ in the normal bundle of `Z`, with the form of
  the connection). The page asks for both; they may be two issues if the
  disc bundle needs a file of its own.

Expected sizes: 400 to 500 lines each; issue 24 begins with a design
issue if Proposition 13 does not fit in one.

## What the part uses

- *Liouville structures* (merged): `IsStrongFilling`, `fillingContactForm`,
  `IsStrongFilling.Completion` with `completionForm`, `completionField`,
  `isCompleteVectorField_completionField` and
  `isLiouvilleCompletion_completion`.
- *Asymptotically holomorphic sections*: the line bundle, the peak
  sections, the transversality estimates and the hypersurface theorem,
  only in `Complement/`.
- *Smooth families*: smooth families of forms, fields and functions, in
  `Homotopy.lean`; *Moser isotopy*, in `Complement/Stein.lean`;
  *Hamiltonian flows*, in `Complement/Skeleton.lean`.
- The library: `SmoothAlmostComplexStructure.IsIntegrable` and
  `isIntegrable_ofComplexManifold` (`Geometry/Manifold/Complex/Integrable.lean`).
- Tau Ceti, complex manifolds: `ofComplexManifold`,
  `toEndomorphism_ofComplexManifold`, `dC`, `dC_apply_apply`, `ddbarForm`,
  `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`,
  `mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm`, `manifoldLeviForm`,
  `IsManifoldStrictlyPlurisubharmonicAt` with `.scalar_comp`, `.add`,
  `isManifoldStrictlyPlurisubharmonicAt_iff`,
  `isOpen_setOf_forall_isManifoldStrictlyPlurisubharmonicAt`,
  `exists_isMorse_isProperMap_bddBelow_isManifoldStrictlyPlurisubharmonicAt`,
  `isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff`,
  `IsTotallyRealEmbedding`, `SmoothTwoForm.IsKahler`.
- Tau Ceti, Morse theory: `IsMorse`, `IsManifoldNondegenerateCriticalPoint`,
  `MorseChart`, `criticalPoints`, `IsMorse.exists_regular_sublevel_exhaustion`,
  `mgradient`, `rateDampedField` and `isCompleteVectorField_rateDampedField`,
  `IsCompleteVectorField`.
- Tau Ceti, Liouville and contact: `IsLiouvilleVectorField`,
  `isLiouvilleVectorField_iff_mextDeriv_interior_eq`,
  `SmoothTwoForm.IsNondegenerate.interiorEquiv`, `Liouville/Radial/`,
  `SmoothForm.IsContactForm`, `Contact/Isotropic.lean`,
  `Contact/ConformalSymplecticNormal.lean`.
- Mathlib: `ContMDiffRiemannianMetric`, `RiemannianBundle`, smooth bump
  functions and partitions of unity.

Searched at the pinned versions, in Mathlib, Tau Ceti and this library:
gradient-like vector fields in the quantitative sense, birth–death
critical points and generalized Morse functions, Weinstein structures,
domains and homotopies, the Liouville field of a strictly
plurisubharmonic function, the completeness reparametrization, smoothing
of maxima of plurisubharmonic functions, $J$-convex surrounding, Stein
handles, and quasiholomorphic sections. None exists. Tau Ceti has the
pointwise theory of plurisubharmonic functions, Morse perturbations of
them, Levi forms, totally real embeddings, pseudo-gradients adapted to
Morse functions and the completeness of damped ones, which the part uses.

## Building issues

In this order; each is blocked by the ones listed. All are parts of
#3293, *Build the part Stein and Weinstein structures*. "AHS" is part 64,
*Asymptotically holomorphic sections* (#3291), and its design file (#3290).

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Gradient-like vector fields | `Morse/GradientLike.lean` | — | 300 |
| 2 | Birth–death points and generalized Morse functions | `Morse/BirthDeath.lean` | — | 350 |
| 3 | The primitive $-df\circ J$ and the form $\omega_f$ | `Complex/Plurisubharmonic.lean` | — | 300 |
| 4 | Stein functions, positivity and the Kähler form | `Complex/Plurisubharmonic.lean` | 3 | 350 |
| 5 | Weinstein structures and domains | `Weinstein/Basic.lean` | 1, 2 | 450 |
| 6 | The completion of a Weinstein domain | `Weinstein/Completion.lean` | 5 | 400 |
| 7 | Weinstein homotopies | `Weinstein/Homotopy.lean` | 5 | 450 |
| 8 | The Liouville field of a Stein function, made complete | `Weinstein/Stein.lean` | 4, 5 | 400 |
| 9 | From Stein to Weinstein | `Weinstein/Stein.lean` | 8 | 250 |
| 10 | $J$-convex hypersurfaces and their contact structure | `JConvex/Hypersurface.lean` | 4 | 400 |
| 11 | Smoothing maxima of plurisubharmonic functions | `JConvex/Smoothing.lean` | 4 | 400 |
| 12 | Plurisubharmonic squared distance to totally real submanifolds | `JConvex/TotallyReal.lean` | 10 | 400 |
| 13 | Design: $J$-convex surrounding | this file | 11, 12 | — |
| 14 | $J$-convex surrounding of totally real discs | `JConvex/Surround.lean` | 13 | by 13 |
| 15 | Weinstein cobordisms and stable discs | `Handle/Cobordism.lean` | 7 | 450 |
| 16 | Standard Weinstein handles and their attachment | `Handle/Model.lean` | 15 | 450 |
| 17 | Design: normal forms of Weinstein homotopies | this file | 16 | — |
| 18 | Normal forms of Weinstein homotopies | `Handle/Homotopy.lean` | 17 | by 17 |
| 19 | A Stein structure across one critical level | `SteinHandle.lean` | 14, 18 | 500 |
| 20 | Stein structures on Weinstein manifolds | `SteinHandle.lean` | 19 | 500 |
| 21 | From Weinstein to Stein up to homotopy; first milestone | `Weinstein/Stein.lean` | 9, 20 | 400 |
| 22 | Quasiholomorphic sections | `Complement/Quasiholomorphic.lean` | AHS | 450 |
| 23 | Derivative transversality and local estimates | `Complement/Transversality.lean` | 22 | 500 |
| 24 | The Weinstein domain of the complement | `Complement/Weinstein.lean` | 6, 23 | 500 |
| 25 | The Stein structure of the complement | `Complement/Stein.lean` | 21, 24 | 450 |
| 26 | Giroux's theorem; second milestone | `Complement/Basic.lean` | 25 | 300 |
| 27 | Giroux's Remark 3 and Corollary 4 | `Complement/Skeleton.lean` | 26 | 500 |

Issues 1, 2 and 3 can start at once. The first milestone is proved in
issue 21 and the second in issue 26. Issues 13 and 17 are design issues:
their pull requests extend this file by the lemma lists of issues 14 and
18 and split them into issues of a few hundred lines. Issues 22–27 wait
for the design file of *Asymptotically holomorphic sections*, which fixes
the hypersurfaces that issue 26 states its result for; issue 22 is
written after it.

Credit: the statements follow Cieliebak–Eliashberg and Giroux; a building
issue that finds an error in them, or a hypothesis of dimension in
Theorem 13.9 that the page omits, records it in `ERRATA.md`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Definitions 7.4.5, 7.4.7, 7.4.8 and Remarks 7.4.6, 7.4.9.
* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.5, Definition 11.15, Remark 11.16, Theorem 1.1 and Theorem 13.9.
* [E. Giroux, *Remarks on Donaldson's symplectic submanifolds*][Giroux2017],
  Theorems 1 and 2, Remark 3, Corollary 4, Sections B and C.
