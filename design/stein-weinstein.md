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
A, B and C.

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
  real function `f : SmoothForm 𝓘(ℝ, E) M ℝ 0` (Tau Ceti's
  `SmoothForm.ofFunction` makes one of a smooth map), the one-form
  $\lambda_f=-df\circ J$ is already Tau Ceti's
  `(ofComplexManifold E M).covectorComplexStructure (mextDerivₗ 𝓘(ℝ, E) 0 f)`
  (`SmoothAlmostComplexStructure.covectorComplexStructure`, evaluated by
  `covectorComplexStructure_apply_vec`), and $\omega_f$ is
  `mextDerivₗ 𝓘(ℝ, E) 1` of it. The part defines neither form. Below,
  $\lambda_f$ and $\omega_f$ stand for these two expressions. The
  library's `dC_mapCoeff_ofReal` identifies $\lambda_f$ with Tau Ceti's
  `dC` of `f` read as a complex function, and
  `del_delBar_mapCoeff_ofReal_ofComplexManifold` relates $\omega_f$ to
  $\partial\bar\partial f$ (both in
  `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`). With
  `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`, $\omega_f$ is
  twice Tau Ceti's `TauCeti.ddbarForm E f`. With these signs,
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
  `t ↦ (ω t, X t, f t)` indexed by `t : unitInterval`, smooth in `(t, x)`
  on `unitInterval × M` in the sense of *Smooth families* (`DESIGN.md`,
  *Manifolds, families and signs*; the forms by `IsSmoothFamily`), each
  member a Weinstein structure, and with Cieliebak–Eliashberg's
  condition at infinity: smooth functions $c_1<c_2<\dots$ on `[0, 1]`, tending to infinity
  uniformly, with $c_k(t)$ a regular value of `f t` for all `k` and `t`.
  On a compact `M` it holds with the constants $c_k=B+k+1$, where $B$ is an
  upper bound of $f$ on `[0, 1] × M`, so that their levels are empty; the
  building issue proves this as a lemma.
- **Concatenation and the relation.** Two Weinstein homotopies whose end
  and start agree need not concatenate to one. A continuous path of
  regular values cannot cross the time at which a pair of critical points
  is born or dies at a value between the pair's values, so the barriers of
  the two halves can be forced into disjoint sets of regular values at the
  seam (#5352 gives a family on $\mathbb C^2$ with infinitely many births
  in the first half and deaths in the second). The predicate keeps its
  barriers as an existential, and the part adds `IsRegularBarrier E f c`,
  the conditions that the predicate asks of `c` for the family `f`, with
  `IsWeinsteinHomotopy.exists_isRegularBarrier`. `.trans` takes, besides
  the two homotopies and their agreement at the seam, barriers `c` of the
  first family and `c'` of the second with `c k 1 = c' k 0` for every `k`;
  after the reparametrization flat at the ends, the glued `c k` are
  smooth. Cieliebak–Eliashberg's step-by-step constructions meet in this
  way, at fixed regular levels. `AreWeinsteinHomotopic` means joined by
  one Weinstein homotopy, as in their Theorem 1.1 and the milestone; it is
  reflexive and symmetric, and the part does not claim that it is
  transitive. A proof that builds the homotopy of issue 21 in steps glues
  them by `.trans` with matching barriers.
- **The route to the converse.** Cieliebak–Eliashberg's proof, followed
  chapter by chapter, is the only proof known to this design. The part
  plans it as a sequence of supporting files (*Files*), each an issue or a
  few. The largest blocks (the $J$-convex surrounding of totally real
  discs, the normal forms of Weinstein homotopies, and Stein handle
  attachment) begin with an issue that extends this file by their lemma
  lists, since their split depends on the Lean form of the earlier blocks.
- **Giroux's theorem waits for part 64.** Its hypersurfaces are symplectic
  hyperplane sections, whose complements Giroux's Section A studies in
  general, and zero sets of the quasiholomorphic sections of his Section B,
  built with the peak sections, the transversality estimates and the line
  bundle of
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
| `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean` (existing) | $\lambda_f$ and $\omega_f$ under composition, and $\omega_f$ as $2\,i\partial\bar\partial f$ | 3 |
| `Geometry/Manifold/Complex/Plurisubharmonic.lean` | Stein functions, positivity | 4 |
| `Geometry/Symplectic/Weinstein/Basic.lean` | Weinstein structures and domains | 5 |
| `Geometry/Symplectic/Weinstein/Completion.lean` | the completion of a Weinstein domain | 6 |
| `Geometry/Symplectic/Weinstein/Homotopy.lean` | Weinstein homotopies | 7 |
| `Geometry/Symplectic/Weinstein/Rescale.lean` | rescaling the Liouville form | 18a |
| `Geometry/Symplectic/Weinstein/OfStein.lean` | the Weinstein structure of a Stein function | 8, 9 |
| `Geometry/Symplectic/Weinstein/Stein.lean` | the converse and the first milestone | 21 |
| `Geometry/Manifold/Complex/JConvex/` | the $J$-convex toolkit of the converse | 10–14e |
| `Analysis/ODE/LyapunovPerron/ParameterDerivative.lean` | the bounded parameter derivative of local stable solutions | 15b |
| `Geometry/Symplectic/Weinstein/Handle/` | Weinstein cobordisms, handles and their homotopies | 15–18 |
| `Geometry/Symplectic/Weinstein/SteinHandle.lean` | Stein structures on elementary cobordisms | 19, 20 |
| `Geometry/Symplectic/Weinstein/Complement/` | Giroux's Sections A, B and C; second milestone | 22–29 |

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
  `p`, coordinates `coord` and weights $w_i=\pm1$ as in `TauCeti.MorseChart`
  off one cubic coordinate $i_0$ of weight $0$, with `f` equal to
  $f(p)+\tfrac12\sum_{i\ne i_0}w_iz_i^2+z_{i_0}^3/3$ on its source (the
  cubic is Tau Ceti's `birthDeathPotential 0`), recorded as a
  `MorseBottChart` of the quadratic part; its `index` is the number of
  negative weights; `restr` and its lemmas, as for `MorseChart`.
- `IsGeneralizedMorse E (f : M → ℝ) : Prop`: smooth, and every critical
  point nondegenerate or the centre of a birth–death chart.
  `IsMorse.isGeneralizedMorse`, `IsGeneralizedMorse.isClosed_criticalPoints`
  and `IsGeneralizedMorse.isDiscrete_criticalPoints` (so the critical
  points of a proper one in a sublevel are finite), and
  `IsGeneralizedMorse.comp` (`h ∘ f`, `h' > 0`).
- An example: the cubic on `ℝ` is generalized Morse and not Morse.

Expected size: 350 lines.

### `Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`

Issue 3 adds to the library's existing file, in `TauCeti`, since the
statements mention only Tau Ceti's notions; on a complex manifold as in
*Signs and setting*, with $\lambda_f$ and $\omega_f$ the expressions given
there. Sums and scalar multiples need nothing new (`map_add`,
`map_smul`). The new facts:

- the value of $\lambda_f$ on `v` at `x`, `-mfderiv f x (Complex.I • v)`
  for the function underlying `f`, from `covectorComplexStructure_apply_vec`
  and `toEndomorphism_ofComplexManifold`;
- $\lambda_g=h'(f)\,\lambda_f$ and
  $\omega_g=h'(f)\,\omega_f+h''(f)\,df\wedge\lambda_f$, for smooth
  `h : ℝ → ℝ` and a `0`-form `g` whose values are `h` of those of `f`;
- $\omega_f$ at `x`, as a form, equals `2 • ddbarForm E u x` for the
  function `u` underlying `f`, from `dC_mapCoeff_ofReal` and
  `ddbarForm_apply_eq_inv_two_smul_mextDerivₗ_dC_apply`.

Expected size: 300 lines.

### `Geometry/Manifold/Complex/Plurisubharmonic.lean`

In `SymplecticGeometry`, on a complex manifold as in *Signs and setting*,
with $\omega_\varphi$ for `SmoothForm.ofFunction` of a smooth `φ`.
Issue 4:

- `isManifoldStrictlyPlurisubharmonicAt_iff_forall_pos`: for `f`
  in `C^∞⟮𝓘(ℝ, E), M; ℝ⟯`, `IsManifoldStrictlyPlurisubharmonicAt E f x` holds iff
  $0<\omega_f(v,\,i v)$ at `x` for every `v ≠ 0`, from the identity of
  issue 3, `mk_ddbarForm_apply_eq_two_mul_manifoldLeviForm` and
  `isManifoldStrictlyPlurisubharmonicAt_iff`. This is the lemma that
  `DESIGN.md` asks for.
- `IsSteinFunction E φ` (a structure: `contMDiff`, `isProperMap`,
  `bddBelow`, `isStrictlyPlurisubharmonic`), with `IsSteinFunction.comp`
  (`h ∘ φ` for smooth `h` with `h' > 0` and `h'' ≥ 0`,
  from Tau Ceti's `IsManifoldStrictlyPlurisubharmonicAt.scalar_comp`),
  `IsSteinFunction.exists_isMorse` (Tau Ceti's perturbation), and the
  example `isSteinFunction_norm_sq` ($|z|^2$ on `E`).
- For a Stein function, $\omega_\varphi$ is a Kähler form for
  `ofComplexManifold E M`: `IsSteinFunction.isKahler` (Tau
  Ceti's `TauCeti.SmoothTwoForm.IsKahler`; closed, compatible by the
  positivity lemma and the $J$-invariance of `ddbarForm`, and
  `TauCeti.SmoothTwoForm.isKahler_ofComplexManifold_iff`). Hence
  `IsSteinFunction.isSymplectic`.

Expected size: 350 lines.

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
  isGeneralizedMorse : IsGeneralizedMorse E f
  isGradientLike : IsGradientLike f X
```

with `IsWeinsteinStructure.mextDeriv_interior` ($d(\iota_X\omega)=\omega$,
from Tau Ceti's `isLiouvilleVectorField_iff_mextDeriv_interior_eq`),
`IsWeinsteinStructure.comp` (`h ∘ f`), `IsWeinsteinStructure.pullback`
(along a diffeomorphism), and the example of `ℂⁿ` with the radial field
and $|z|^2$, Liouville by `SymplecticForm.isLiouvilleVectorField_constSmooth`.

A Weinstein domain is a compact manifold with boundary over the
half-space, as a strong filling is in *Liouville structures*:
`IsWeinsteinDomain σ Y f c` asks `IsStrongFilling σ univ Y`, `f` smooth
with `f = c` on `∂W` and `f < c` on the interior,
`0 < mvfderiv f x (Y x)` for every `x ∈ ∂W`, and, on the interior
as a boundaryless manifold (Tau Ceti's charted interior `(𝓡∂ (n + 1)).interior W`,
with `ModelWithCorners.instChartedSpaceInterior`), `f` generalized Morse and `Y` gradient-like
for it. The boundary condition makes `∂W = f ⁻¹' {c}` a regular level: it
does not follow from the others, since `δ` may tend to zero at `∂W` (on
the closed unit disc with the radial field, `f = -(1 - r²)²` and `c = 0`
satisfy all the other conditions and have `df = 0` along the boundary).
It also gives the completion of issue 6 a gradient-like function across
the seam. `IsWeinsteinDomain.finite_criticalPoints` follows: the critical
points form a closed subset of the compact `W` that misses `∂W` and is
discrete.

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

Issue 7. `IsWeinsteinHomotopy ω X f` for families indexed by
`t : unitInterval` and smooth on `unitInterval × M`, as in *Decisions*;
`IsWeinsteinHomotopy.refl`, `.symm`,
`.trans` (for barriers that agree at the seam, as in *Decisions*, after a
reparametrization of time that is flat at the ends;
the proof may pass to the model over `ℝ`, which no statement uses),
`.pullback`, and `IsWeinsteinHomotopy.of_isCompact` (the condition at
infinity on a compact manifold). Also `IsRegularBarrier` with
`IsWeinsteinHomotopy.exists_isRegularBarrier`, and the relation
`AreWeinsteinHomotopic` between two Weinstein structures, joined by one
Weinstein homotopy, with `AreWeinsteinHomotopic.refl` and `.symm`; it is
not claimed to be an equivalence relation (*Decisions*).

Expected size: 450 lines.

### `Geometry/Symplectic/Weinstein/OfStein.lean`

Issue 8: the Weinstein structure of a Stein function.

- `dCLiouvilleField φ`, the vector field with
  $\iota_{X}\,\omega_\varphi=\lambda_\varphi$, defined by the inverse of the flat map of
  $\omega_\varphi$ where it is nondegenerate (Tau Ceti's
  `SmoothTwoForm.IsNondegenerate.interiorEquiv`), zero elsewhere; it is
  the gradient of `φ` for the Kähler metric $\omega_\varphi(\cdot,J\cdot)$,
  so `isGradientLike_dCLiouvilleField` with `δ = 1 / 2`, and
  `isLiouvilleVectorField_dCLiouvilleField`.
- `IsSteinFunction.exists_comp_isCompleteVectorField`
  (Cieliebak–Eliashberg, Remark 11.16): a smooth convex increasing `h` with
  `dCLiouvilleField (h ∘ φ)` complete. The field of `h ∘ φ` is computed from
  the composition formulas of issue 3, and `h = exp` works for every `φ`
  on a Hausdorff `M`. Tau Ceti's `isCompleteVectorField_rateDampedField`
  proves completeness of a field damped by a similar estimate; if the
  building issue follows its proof, it credits it.

Issue 9: the first half of the milestone.
`IsSteinFunction.exists_isWeinsteinStructure`: for a Stein function `φ`
there is a Stein function `ψ`, Morse and of the form `exp ∘ φ'` for a Morse
perturbation `φ'` of `φ`, with
`IsWeinsteinStructure` $(\omega_\psi,$ `dCLiouvilleField ψ`$,\psi)$; and
`IsSteinFunction.isWeinsteinStructure_comp` for `φ` already generalized
Morse, with `ψ = exp ∘ φ`, which also says that `ψ` is a Stein function.

Expected size: 400 lines for issue 8, 250 for issue 9.

### `Geometry/Symplectic/Weinstein/Stein.lean`

Issue 21: the second half and the milestone,
`IsWeinsteinStructure.exists_isSteinFunction_areWeinsteinHomotopic`:
for `M` over `EuclideanSpace ℝ (Fin (2 * n))`, second countable and
Hausdorff, and `IsWeinsteinStructure ω X f`, there are a complex manifold
`N` over `EuclideanSpace ℂ (Fin n)`, a diffeomorphism
`e : N ≃ₘ⟮𝓘(ℝ, _), 𝓘(ℝ, _)⟯ M` and a Stein function `ψ` on `N`,
generalized Morse and with `dCLiouvilleField ψ` complete, such that
`(ω, X, f)` is Weinstein homotopic to the pushforward along `e`
of $(\omega_\psi,$ `dCLiouvilleField ψ`$,\psi)$. The theorem
`exists_isWeinsteinStructure_of_isSteinFunction_and_areWeinsteinHomotopic`
is the conjunction of the two halves, in the
page's form. Docstring line: "Milestone: *Passage between Stein and
Weinstein structures*."

Expected size: 400 lines.

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
  contact form $\lambda_\varphi$ restricted (Tau Ceti's `IsContactForm`).
- `Smoothing.lean` (issue 11): smoothing of the maximum of two strictly
  plurisubharmonic functions, and gluing by
  $\max$ near a hypersurface.
- `TotallyReal.lean` (issue 12): for a totally real submanifold (Tau
  Ceti's `IsTotallyRealEmbedding`, `TotallyReal/AdaptedChart/`), the
  squared distance for a suitable metric is strictly plurisubharmonic near
  it (Tau Ceti's `SquaredDistance.lean` has the complex-chart
  computation); isotropic submanifolds of a $J$-convex level, tangent to
  the complex tangencies, are totally real.
- `Interpolation.lean` (issue 14d17): two strictly
  plurisubharmonic functions with the same 1-jet along a compact part of
  a totally real submanifold are joined by one equal to the second near
  it and to the first farther away (Cieliebak–Eliashberg's Proposition
  3.26); designed with `Surround/` below.
- `Surround/` (issue 13 designs it, issues 14a–14e build it): the
  $J$-convex surrounding of a totally real disc attached to a $J$-convex
  level, below.

Expected size: 400 lines each for issues 10–12.

### `Geometry/Manifold/Complex/JConvex/Surround/`

Cieliebak–Eliashberg's $J$-convex surrounding: a domain
$W=\{\varphi\le0\}$ with $J$-convex boundary, together with a totally real
disc $\Delta$ attached to $\partial W$ along its boundary sphere, has
arbitrarily small neighbourhoods $\{\psi\le0\}$ with $J$-convex boundary,
where $\psi$ agrees with a convex reparametrization of $\varphi$ away from
$\Delta$ and has one new
critical point, of index $\dim\Delta$, on $\Delta$. It is what issue 19
needs to extend a Stein function across a handle. The work is more than one
file of 1000 lines, so it is a folder. Each file is in `SymplecticGeometry`,
on a complex manifold as in *Signs and setting*.

**The disc.** A disc is given by a map `ι : F → M` from a finite-dimensional
real inner product space, with $\Delta$ = `ι '' closedBall 0 1` and
$\partial\Delta$ = `ι '' sphere 0 1`. It is a smooth embedding
(`Manifold.IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ι`) whose tangent images are
totally real in Tau Ceti's weak sense,
`∀ x, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι x)).toLinearMap
(LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x).toLinearMap)`, the form in
which `IsJConvexLevel.isTotallyReal_range_mfderiv` (issue 12) gives it.
`TauCeti.IsTotallyRealEmbedding` is not used here: it forces half the
dimension, and the cores of subcritical handles are smaller. Asking for an
embedding of all of `F` loses nothing, since an embedded closed disc
extends to a slightly larger open ball, which a radial diffeomorphism
fixing `closedBall 0 1` identifies with `F`. For `F = 0` the disc is a point
outside `W` and the sphere is empty; the statements below hold there too,
the new critical point being a minimum.

**$J$-orthogonal attachment.** `IsJOrthogonallyAttached E φ ι : Prop`, a
structure with the fields

- `pos : ∀ x, ‖x‖ < 1 → 0 < φ (ι x)` (the open disc lies outside `W`),
- `eq_zero : ∀ x, ‖x‖ = 1 → φ (ι x) = 0` (its boundary lies on `∂W`),
- `mvfderiv_mfderiv_self_neg : ∀ x, ‖x‖ = 1 →
  mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x x) < 0` (the disc
  meets `∂W` transversally, and continues into `W`),
- `mvfderiv_I_smul_mfderiv : ∀ x, ‖x‖ = 1 → ∀ v,
  mvfderiv 𝓘(ℝ, E) φ (ι x) (Complex.I • (show E from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x v)) = 0`
  ($J\,T_p\Delta\subseteq T_p\partial W$ along $\partial\Delta$).

The last field says that $\partial\Delta$ is tangent to the complex
tangencies of $\partial W$ and that the radial direction of $\Delta$ is sent
by $J$ into $T\partial W$. The fields agree with Cieliebak–Eliashberg's
attachment of a disc in §7.9, $J$-orthogonal in the sense of their
Definition 2.22; embedding and total reality are separate hypotheses.

**The statements.** With `φ` smooth, strictly plurisubharmonic at every
point of `{x | φ x ≤ 0}`, `0` a regular value of `φ`, `ι` a disc as above
with `IsJOrthogonallyAttached E φ ι`, `[T2Space M]`, and an open `U`
containing `ι '' closedBall 0 1`:

- `IsJOrthogonallyAttached.exists_surround`: there are a smooth
  `h : ℝ → ℝ` with `h 0 = 0`, `∀ y, 0 < deriv h y` and
  `∀ y, 0 ≤ iteratedDeriv 2 h y`, and a smooth `ψ : M → ℝ` with
  `ψ =ᶠ[𝓝 x] h ∘ φ` for every `x ∉ U`, `ψ` strictly plurisubharmonic at
  every point of `{x | ψ x ≤ 0}`, `0` a regular value of `ψ`, and
  `ι '' closedBall 0 1 ⊆ {x | ψ x < 0}`. So `{ψ ≤ 0}` agrees with `W`
  outside `U`, contains the disc in its interior, lies in `W ∪ U`, and
  has a $J$-convex boundary. Outside `U` the function is a convex
  reparametrization of `φ`, not `φ` itself: Cieliebak–Eliashberg's
  Theorem 8.5 asserts only $J$-convex levels for its function, and the
  junction below needs one reparametrization of everything; `h ∘ φ` is
  strictly plurisubharmonic wherever `φ` is, and `IsSteinFunction.comp`
  takes exactly these hypotheses on `h`, so issue 19 can use it. Neither
  `ψ ≤ h ∘ φ` nor `W ⊆ {ψ ≤ 0}` is asked; see *Comparison with `φ`*
  below.
- `IsJOrthogonallyAttached.exists_surround_critical`: moreover, every
  critical point `x ∈ U` of `ψ` with `ψ x ≤ 0` is `ι 0` or a critical point
  of `φ` near which `ψ = h ∘ φ`, for the `h` of the statement; `ι 0` is
  a nondegenerate critical point of `ψ`
  (`TauCeti.IsManifoldNondegenerateCriticalPoint`) with
  `manifoldMorseIndex 𝓘(ℝ, E) ψ (ι 0) = finrank ℝ F`; and `ψ ∘ ι` strictly
  decreases along each radius `t ↦ t • x`, `t ∈ [0, 1]`, `‖x‖ = 1`.

**The files and their declarations.**

- `JConvex/TotallyReal.lean` (existing; issue 14a):
  `Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isCompact`.
  For a `C^n` embedding, `2 ≤ n` (`n = ∞` for a smooth one), `ι : N → M`
  of a boundaryless manifold into a Hausdorff `M`, and a compact `K ⊆ N`
  at whose points the tangent images of `ι` are totally real in the weak
  sense, there are a `C^n` function `ρ : M → ℝ`, `ρ ≥ 0`, and an open `V ⊇ ι '' K` such
  that on `V` the function `ρ` vanishes exactly on `range ι` and is
  strictly plurisubharmonic, and its critical Hessian at `ι y`, `y ∈ K`, is
  positive off the tangent image of `ι` at `y`. It glues the squared
  normal coordinates of slice charts
  (`Manifold.IsSmoothEmbedding.exists_contMDiffOn_criticalHessian_pos`),
  finitely many of them, which compactness of `K` gives, by bump
  functions. The closed-range form,
  `Manifold.IsSmoothEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isClosed_range`
  (`M` also σ-compact, `range ι` closed, all tangent images totally real
  in the weak sense), glues the same local functions by a partition of
  unity; `TauCeti.IsTotallyRealEmbedding.exists_contMDiff_isManifoldStrictlyPlurisubharmonicAt_of_isClosed_range`
  is its case of a totally real embedding.
- `Surround/Attached.lean` (issue 14b): `IsJOrthogonallyAttached` and its
  API: `IsJOrthogonallyAttached.image_closedBall_inter` (the disc meets
  `{φ ≤ 0}` exactly in its boundary sphere),
  `IsJOrthogonallyAttached.exists_lt_forall_neg` (some `r > 1` with
  `φ (ι x) < 0` for `1 < ‖x‖ < r`, by transversality and compactness of the
  sphere),
  `IsJOrthogonallyAttached.comp` (for `h ∘ φ` with `h 0 = 0` and `h' > 0`),
  `IsJOrthogonallyAttached.comp_linearIsometry` (for `ι ∘ e`, `e` a linear
  isometry).
- `Surround/Shape.lean` (issue 14c): the model. On
  `V = EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)`, write
  `p = (x + i y, w)`, $s=|x|^2$ and $t=|y|^2+|w|^2$, and `ι₀` for the
  inclusion of `EuclideanSpace ℝ (Fin k)` as `y = 0`, `w = 0`. For `C²`
  functions of $(s,t)$: the Levi form at `p` in terms of the first and
  second partial derivatives and of `x`, `y`, `w`
  (`re_leviForm_comp_shape_apply_self`), and the sufficient criterion
  `isManifoldStrictlyPlurisubharmonicAt_shape` for
  $f(s)+g(t)$: with $u^-=\min(u,0)$,
  $f'+g'+2f''^-s+2g''^-t>0$, and $g'+2g''^-t>0$ when `m ≠ 0`. The model
  level $\varphi_0=1-s+2t$ and the model handle function $bt-as$,
  $0<a<b$: both strictly plurisubharmonic by the criterion,
  `IsJConvexLevel` for $\varphi_0$ at `0`, and the handle function with
  one critical point, at `0`, nondegenerate of index `k`. With
  `isJOrthogonallyAttached_model`, $(\varphi_0,\iota_0)$ satisfies
  every hypothesis of the statements above (`ι₀` is a linear embedding with
  totally real image), and is the test case of issue 14d. These are the
  first computations of Cieliebak–Eliashberg's chapter on shapes of
  $i$-convex hypersurfaces that the surrounding uses; the rest are below.
- **The $i$-convex model handle (issues 14d1–14d8).** These files carry
  out Cieliebak–Eliashberg's Chapter 4 on `V`, with $\mathbb C^n=V$,
  $n=k+m$. Their coordinates are $R=\sqrt s$, along the core, and
  $r=\sqrt t$, across it; their standard function $ar^2-R^2$ is
  `modelHandle k m 1 a`, and the model level of issue 14c is its case
  $a=2$ plus `1`. Their Chapter 4 treats a hypersurface whose trace on the
  quadrant of $(r,R)$ is a curve $R=\chi(r)$, the *shape*, and states
  everything in terms of the one-variable function $\chi$; the files do
  the same (below, `s p = (shape p).1` and `t p = (shape p).2`), so
  that most of the work is real analysis of one variable.
  Two choices differ from the book. (1) The book proves its criterion
  for $k=n$ first and passes to $k<n$ by a maximum over $U(n-k)$
  (Lemma 4.14 (a)); here `re_leviForm_comp_shape_apply_self` already
  covers `m ≠ 0`, and the extra directions only ask for $\chi'>0$, which
  (4.3) implies. (2) In the proof of Theorem 4.2 the book
  interpolates between $ar^2-R^2$ and $64r^2-R^2$ by Proposition 3.26.
  Both are functions $g(t)-s$, and `isStrictlyPlurisubharmonicAt_shape`
  shows $g(t)-s$ strictly plurisubharmonic as soon as
  $g'+2\min(g'',0)\,t>1$; for a concave $g$ this says that
  $\sqrt t\,(g'(t)-1)$ has positive derivative. A concave $g$ with
  slope 64 on $[0,t_0]$ and slope $a$ on $[\gamma^2,\infty)$ meets it
  once $63\sqrt{t_0}<(a-1)\gamma$ (and if $a\ge64$ a convex $g$ with
  $g'>1$ does), so this interpolation is separable and Proposition 3.26
  is not needed here.

  *Shapes.* For `χ : ℝ → ℝ` and `r : ℝ`, `IsConvexShapeAt χ r : Prop`
  is the structure with fields `pos : 0 < r`, `pos_value : 0 < χ r`
  and `levi : ∀ σ u : ℝ, σ ^ 2 + u ^ 2 = r ^ 2 →
  1 / χ r * (1 + deriv χ r ^ 2 * u ^ 2 / r ^ 2) < iteratedDeriv 2 χ r *
  σ ^ 2 / r ^ 2 + deriv χ r * u ^ 2 / r ^ 3 + deriv χ r ^ 3 / r` (the
  book's (4.4)). The book's (4.3) is the case `σ = 0` of (4.4), so it is
  not a field but the theorem
  `IsConvexShapeAt.one_div_lt_deriv_div : 1 / χ r < deriv χ r / r`; it gives
  `IsConvexShapeAt.deriv_pos : 0 < deriv χ r`. The defining function of the shape is
  `shapeGraph χ : ℝ × ℝ → ℝ`, `(s, t) ↦ χ (√t) - √s`, with
  `shapeGraph_def`.

- `Surround/ConvexShape/Basic.lean` (issues 14d1 and 14d2): $i$-convex shapes.
  - `IsConvexShapeAt.re_leviForm_pos` (14d1; the book's
    Proposition 4.8 (a), (b), Proposition 4.10 and Lemma 4.14 (a)): if
    `χ` is `C²` at `r` and `IsConvexShapeAt χ r`, then at every `p` with
    `shape p = (χ r ^ 2, r ^ 2)`, writing `F = shapeGraph χ ∘ shape`
    (which is `C²` near `p`, since `s, t > 0` there), every `v ≠ 0` with
    `fderiv ℝ F p v = 0` and `fderiv ℝ F p (Complex.I • v) = 0` has
    `0 < (leviForm F p v v).re`. The proof evaluates
    `re_leviForm_comp_shape_apply_self` on the complex tangencies; in
    place of the book's splitting into $\Lambda^{\mathbb C}_\perp$ and
    $\Lambda^{\mathbb C}_{xy}$, a Cauchy–Schwarz bound for a combination
    of `σ` and `τ` (proportional on a complex tangency) bounds `|σ|²` by `|v|²`.
  - `isConvexShapeAt_of_iteratedDeriv_two_nonpos` (14d2; Corollary
    4.11 (a)): `0 < r`, `0 < χ r`, `iteratedDeriv 2 χ r ≤ 0` and
    `(1 + deriv χ r ^ 2) / χ r < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r`
    give `IsConvexShapeAt χ r`.
  - `IsConvexShapeAt.add_const` (14d2; Lemma 4.13 (a)), for `0 ≤ c`, and
    `IsConvexShapeAt.rescale` (Lemma 4.13 (b)): for `0 < ℓ`,
    `IsConvexShapeAt (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r)`.
  - `exists_isConvexShapeAt_eq_max` (14d2; Lemma 4.13 (d); in
    `Surround/ConvexShape/SmoothedMax.lean`): let `χ₁`,
    `χ₂` be `C²` with `IsConvexShapeAt` at every point of a compact
    interval `Icc r₁ r₂`, and let `O` be a
    neighbourhood of `Icc r₁ r₂ ∩ {r | χ₁ r = χ₂ r}`. Then there is a `C²` (smooth if
    `χ₁`, `χ₂` are) `χ`, a convex shape at every point of `Icc r₁ r₂`,
    equal to `max (χ₁ r) (χ₂ r)` on `Icc r₁ r₂` off `O`, with
    `0 ≤ iteratedDeriv 2 χ r` wherever both `χᵢ` have it; no transversality
    of the crossings is needed. Condition (4.3) passes to
    `smoothedMax δ (χ₁ r) (χ₂ r)` (`Analysis/SpecialFunctions/SmoothedMax.lean`),
    whose value is at least each `χᵢ r` and whose slope is a convex
    combination of theirs; for (4.4) the book makes the second
    derivative large near each crossing by a quadratic bridge, and the
    smoothed maximum does the same if `smoothedAbs`'s second derivative
    is large wherever its first is away from `±1`; the building issue
    takes whichever of the two the library's `smoothedAbs` allows.

- `Surround/SpecialShape.lean` (issues 14d3 and 14d4): the shapes of
  §4.5, and Theorem 4.1 (i)–(iii).
  - `struweShape δ K c : ℝ → ℝ`, `r ↦ c + ∫ u in K * δ..r, 1 / √(log (u / δ))`,
    the solution of Struwe's equation $\chi''+\chi'^3/2r=0$ with
    $\chi'(\delta)=+\infty$ and $\chi(K\delta)=c$ (Remark 4.16), with
    `deriv_struweShape` ($1/\sqrt{\log(r/\delta)}$ for `δ < r`) and
    `iteratedDeriv_two_struweShape`. `isConvexShapeAt_struweShape`
    (14d3; Lemma 4.15): for `0 < d`, `0 < δ`, `exp (4 / d ^ 2) ≤ K` and
    `4 * K * δ ≤ (log K) ^ (-3 / 2 : ℝ)`, the shape with
    `c = 1 + d * K * δ` is convex at every `r ∈ Ioc δ (K * δ)`, has
    `deriv ≤ d` at `K * δ`, satisfies
    `1 + d * δ ≤ struweShape δ K c δ < 1 + d * K * δ`, and its derivative
    tends to `atTop` along `𝓝[>] δ`. The rescaled forms of the lemma
    follow by `IsConvexShapeAt.rescale`.
  - `isConvexShapeAt_sqrt` (14d3; Lemma 4.17 (a)): for `1 < a` and any
    `ℓ`, `r ↦ √(ℓ ^ 2 + a * r ^ 2)` is a convex shape at every
    `r > 0`; `isConvexShapeAt_quadratic` (Lemma 4.17 (b)): for `0 < ℓ`,
    `0 ≤ b`, `1 < c`, `r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)` at every
    `r > 0`; `isConvexShapeAt_linear` (Lemma 4.17 (e)): for `0 < ℓ`,
    `0 < d`, `r ↦ ℓ + d * r` at every `r ∈ Ioo 0 (ℓ * d ^ 3)`.
  - (14d4) The crossings of Lemma 4.18 (a)–(c), as statements about the
    real roots of the differences of these three functions;
    `exists_isConvexShapeAt_eq_linear_eq_sqrt` (Lemma 4.19): for
    `1 < a` and `0 < γ` there are `d ∈ Ioo 0 1`, `β ∈ Ioo 0 γ` and a
    smooth `ψ`, convex shape at every `r > 0`, with
    `ψ r = √(1 + a * r ^ 2)` for `γ ≤ r`, `ψ r = 1 + d * r` for
    `r ≤ β` and `r * deriv ψ r < ψ r` for `0 ≤ r`; Remark 4.20's admissible constants
    (`c = (1 + a) / 2`, `b = γ * (a - 1) / 16`), which §4.7 needs.
  - `exists_convexShape_surround` (14d4; Proposition 4.21, which is
    Theorem 4.1 (i)–(iii) in terms of the shape): for `1 < a` and
    `0 < γ` there are `δ ∈ Ioo 0 γ` and `χ : ℝ → ℝ`, smooth on
    `Ioi δ` and continuous on `Ici δ`, with `IsConvexShapeAt χ r` for
    all `r > δ`, `χ r = √(1 + a * r ^ 2)` for `γ ≤ r`,
    `Tendsto (deriv χ) (𝓝[>] δ) atTop` and `1 < χ δ < 1 + γ`. The
    hypersurface of Theorem 4.1 is
    $\Sigma=\{t=\delta^2,\ \sqrt s\le\chi(\delta)\}\cup\{t>\delta^2,\ \sqrt s=\chi(\sqrt t)\}$;
    theorems about this `χ` record (ii) and (iii) as
    `Σ ∩ {p | γ ^ 2 ≤ t p} = {p | a * t p - s p = -1} ∩ {p | γ ^ 2 ≤ t p}`
    and `Σ ∩ {p | s p ≤ 1} = {p | t p = δ ^ 2 ∧ s p ≤ 1}`, and (i) by
    `IsConvexShapeAt.re_leviForm_pos` on the curved part and
    `leviForm_shape_snd_apply` on the cylinder `t = δ ^ 2`. The book
    joins the two parts of $\Sigma$ at $r=\delta$, $R=\chi(\delta)>1$,
    where the Struwe curve meets the line $r=\delta$ with the same
    tangent; there $r-\delta$ grows like $(R-\chi(\delta))^2$ on one side
    and vanishes on the other, so $\Sigma$ is $C^{1,1}$ and not $C^2$ at
    that corner, although the book's Theorem 4.2 (iii) makes it a level of
    a function with nonzero gradient. Every leaf of the family of
    issue 14d5 has the same corner, at its own height `χ ℓ δ`, and
    contains the segment of the cylinder below it, so the leaves are not
    disjoint there and their level function is not defined on the
    cylinder. Issue 14d7 avoids both: the level `-1` of its final
    function is a smooth hypersurface `Σ'` that agrees with `Σ` on
    `{p | γ ^ 2 ≤ t p}` and beyond the corner, and is the cylinder
    `t = δ' ^ 2` on `{p | s p ≤ 1}` for a `δ' < δ` close to `δ`.
    Written as graphs over `R`, `Σ` is `r = ρ₁ R` (`ρ₁ = δ` for
    `R ≤ χ δ`) and `Σ'` is `r = ρ' R`, `ρ'` the smoothed minimum
    (Lemma 4.13 (d) for graphs over `R`, see issue 14d6) of `ρ₁` and a
    second shape `ρ₂`, with `ρ₂ = δ'` on `Icc 0 R₀` for an
    `R₀ ∈ Ioo 1 (χ δ)` and, after a short transition, convex with
    `1 / (2 * δ) < ρ₂'' < 1 / δ`. Since the inside is the side where
    `Ψ < -1`, two insides combine by intersection (the minimum of the
    graphs over `R`, the maximum of the shapes over `r`). Where `|ρ₂'|`
    is small the criterion over `R` allows a curvature `ρ₂''` up to
    about `1 / r`, and the Struwe leaf has `ρ₁'' = 1 / (2 * ρ₁)`; so
    `ρ₂ - ρ₁` is convex, negative with zero slope at `R₀`, and has one
    zero `R_c`, transversal, which lies beyond `χ δ` if `ρ₂` rises by
    less than `δ - δ'` on `Icc R₀ (χ δ)`; there `Σ` is smooth.
    Issue 14d4 or 14d7, whichever proves the statement that meets the
    corner, records it in `ERRATA.md` with that route.

- `Surround/ShapeFamily.lean` (issue 14d5): the families of §4.6.
  `isConvexShapeAt_struweShape_two` (Lemma 4.23: for `0 < δ`, `4 ≤ d`,
  the solution on `Ioc δ (2 * δ)` with value `2 * d * δ` at `2 * δ`),
  `exists_convexShapeFamily_sqrt_sub` (the leaves with `ℓ ≤ 0`, below),
  `exists_isConvexShapeAt_struweSwitchLeaf` (the leaves
  `ℓ ∈ Icc 0 (7 * δ)`, below, in `Surround/CutoffLeaf.lean`),
  `exists_convexShapeFamily_sqrt` (Lemma 4.26: for `1 < a` and
  `0 < γ`, the leaves `ℓ ≥ 0` from the cone `√a * r` at `ℓ = 0`, linear,
  `ℓ + d * r`, for `r ≤ ℓ * β` and `√(ℓ ^ 2 + a * r ^ 2)` for
  `ℓ * γ ≤ r`), `exists_convexShapeFamily_struweShape` (the leaves
  `ℓ ≥ ℓ₁`, below), and `exists_convexShapeFamily_surround`
  (Proposition 4.27): for `0 < γ` and all small enough `δ ∈ Ioo 0 γ`, a
  family `χ : ℝ → ℝ → ℝ`, `ℓ ∈ Icc (-8 * δ) 1`, continuous in
  `(ℓ, r)` and smooth in `r` on `Ioi δ` for each `ℓ`, with every
  `χ ℓ` increasing and a convex shape at every `r > δ`,
  `χ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2)`, `χ ℓ r` equal to the
  standard `√(64 * r ^ 2 + ℓ * |ℓ|)` for `γ ≤ r`, and, for some
  `r₀ ∈ Ioo δ γ`, for all `r ≥ r₀` when `ℓ` is near `-8 * δ` (as issue
  14d7 needs; not for all `r > δ`, since for `-8 * δ < ℓ` the standard
  leaf has a finite slope at `δ`),
  `Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop`, `χ ℓ ≤ χ 1` on `Ioi δ` and
  `1 < χ 1 δ < 1 + γ`. The book's family is piecewise smooth in `ℓ`,
  smooth in `(ℓ, r)` on each piece, so the statement asks for `χ`,
  `∂χ/∂r` and `∂²χ/∂r²` to be jointly continuous on
  `Icc (-8 * δ) 1 ×ˢ Ioi δ`, which is what issue 14d6 uses, and not for
  smoothness in `ℓ`.
  - `isConvexShapeAt_sqrt_sub` (in `Surround/SpecialShape.lean`, next to
    `isConvexShapeAt_sqrt`): for `1 < a`, `0 < r` and `c < a * r ^ 2`,
    `r ↦ √(a * r ^ 2 - c)` is a convex shape at `r`. With
    `χ ^ 2 = a * r ^ 2 - c` one has `χ' = a * r / χ` and
    `χ'' = -a * c / χ ^ 3`, so the first inequality of
    `isConvexShapeAt_iff` is `1 < a` and the second is
    `(a - 1) * c < (a ^ 3 - a) * r ^ 2`. Its case `c = -ℓ ^ 2` is
    `isConvexShapeAt_sqrt`; its case `a = 64`, `c = 64 * δ ^ 2` is the
    bottom leaf at every `r > δ`.
  - `exists_convexShapeFamily_sqrt_sub`, the leaves `ℓ ∈ Icc (-8 * δ) 0`
    of `exists_convexShapeFamily_surround`. The design does not follow the
    book's bending of linear shapes (Lemma 4.25) here: these leaves have
    an explicit formula. Statement: there is `K > 2` such that for every
    `δ > 0` there is `χ : ℝ → ℝ → ℝ` with
    - `ContDiffOn ℝ ∞ (Function.uncurry χ) U` for some
      `U ∈ 𝓝ˢ (Icc (-8 * δ) 0 ×ˢ Ioi δ)`;
    - `IsConvexShapeAt (χ ℓ) r` for `ℓ ∈ Icc (-8 * δ) 0` and `δ < r`;
    - `χ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2)` for every `r`;
    - `χ ℓ r = (ℓ + 8 * δ) / 64 + √(64 * r ^ 2 - 64 * δ ^ 2)` for
      `ℓ ∈ Icc (-8 * δ) 0` and `r ∈ Icc δ (2 * δ)`, and
      `Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop`;
    - `χ ℓ r = √(64 * r ^ 2 + ℓ * |ℓ|)` for `ℓ ∈ Icc (-8 * δ) 0` and
      `K * δ ≤ r`;
    - `StrictMonoOn (fun ℓ ↦ χ ℓ r) (Icc (-8 * δ) 0)` for `δ < r`.

    Near the cylinder the leaves are the bottom leaf raised by
    `(ℓ + 8 * δ) / 64`, so their heights `χ ℓ δ` rise strictly from `0`,
    as issue 14d7 expects of the leaves of small height. The proof takes
    `h r = Real.smoothTransition ((r - 2 * δ) / (L * δ))` and
    `χ ℓ r = (ℓ + 8 * δ) / 64 * (1 - h r) +
    √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 - ℓ ^ 2) * h r)`, with `K = 2 + L`
    and `L ≥ 1` large. The radicand is positive on
    `Ioo (-16 * δ) (16 * δ) ×ˢ Ioi δ`, which serves as `U`. For
    `r < 2 * δ` the leaf is, near `r`, the bottom leaf plus a constant
    `≥ 0` (`isConvexShapeAt_sqrt_sub`, `IsConvexShapeAt.add_const`). For
    `2 * δ ≤ r` write `F` for the radicand and `A` for a bound of the
    first two derivatives of `smoothTransition` (continuous, and zero
    outside `Icc 0 1`); with `L ≥ 64 * A` what `h` adds is small:
    `F'' ≥ 127`, `128 * r ≤ F' ≤ 128 * r + δ` and
    `4 * √3 * r ≤ √F ≤ 8 * r`, so `χ' ≥ 8 - 1 / 512` and
    `χ'' ≥ -F' ^ 2 / (4 * √F ^ 3) - 1 / (100 * r) > -13 / r`, against
    `χ' ^ 3 / r > 500 / r` and `1 / χ < 1 / (6 * r)`. These bounds do
    not depend on `δ`, nor does `L`; alternatively, prove the case
    `δ = 1` and pass to `δ` by `IsConvexShapeAt.rescale`, the leaf `ℓ`
    for `δ` being `r ↦ δ * χ₁ (ℓ / δ) (r / δ)`. Monotonicity in `ℓ`: both
    terms are nondecreasing on `ℓ ≤ 0`, the first strictly where
    `h r < 1` and the second strictly where `0 < h r`.

    `exists_convexShapeFamily_surround` does not apply it but takes its
    leaves `sqrtSubLeaf L δ ℓ`, through the lemmas that prove it, for one
    `L` that also serves `exists_isConvexShapeAt_struweSwitchLeaf` below:
    the leaf `0` of both pieces must be `sqrtSubLeaf L δ 0` for the same
    `L`, which the `χ` of the statement does not say. With `K = 2 + L`,
    `δ < γ / K` and `r₀ = K * δ`, its part `ℓ ∈ Icc (-8 * δ) 0` gives the
    bottom leaf; the clause near `-8 * δ`, since every leaf with `ℓ ≤ 0`
    is standard on `Ici r₀` and `Icc (-8 * δ) 0 ∈ 𝓝[≥] (-8 * δ)`; the
    standard leaves for `γ ≤ r`; convexity and the vertical tangent;
    `χ ℓ` increasing in `r` (`strictMonoOn_Ici_of_isConvexShapeAt`, the
    formula giving continuity at `δ`); and the joint continuity of `χ`,
    `∂χ/∂r` and `∂²χ/∂r²` on `Icc (-8 * δ) 0 ×ˢ Ioi δ`, from the
    smoothness on `U` through Tau Ceti's
    `ContDiffAt.iteratedFDeriv_prod_right`
    (`Analysis/Calculus/IteratedFDeriv/Prod.lean`). Monotonicity in `ℓ`
    reduces `χ ℓ ≤ χ 1` to `χ 0 ≤ χ 1`. The leaves `ℓ ∈ Icc 0 1` start
    at this `χ 0`, which has height `δ / 8` at `δ` and is `8 * r` on
    `Ici r₀`: their family equals `χ 0` at `ℓ = 0`, so that the joint
    continuity holds on the union of the two closed pieces. The leaves
    `ℓ ∈ Icc 0 (7 * δ)` are `struweSwitchLeaf L δ ℓ` below, those in
    `Icc ℓ₁ 1` come from `exists_convexShapeFamily_struweShape` below,
    and those in `Icc (7 * δ) ℓ₁`, which join the leaf `7 * δ` to the
    leaf `ℓ₁`, are the bridge leaves below (`Surround/BridgeLeaf.lean`).
  - The leaves `ℓ ∈ Icc 0 (7 * δ)`, in `Surround/CutoffLeaf.lean`, which
    `Surround/ShapeFamily.lean` imports (they would take that file past
    the limit of 1500 lines). First the leaf `0` is raised near the
    cylinder while its far part becomes standard; from `ℓ = 6 * δ` on, a
    Struwe shape with value above the raised leaf at `δ` takes over near
    the cylinder, through a smoothed maximum whose width is proportional
    to the gap of the two values at `δ`.
    - `sqrtAddLeaf L δ ℓ r`, with the cutoff
      `h r = Real.smoothTransition ((r - 2 * δ) / (L * δ))` of
      `sqrtSubLeaf`: `(δ / 8 + ℓ) * (1 - h r) +
      √(64 * (r ^ 2 - δ ^ 2) + (64 * δ ^ 2 + ℓ ^ 2) * h r)`. API, as for
      `sqrtSubLeaf`: `sqrtAddLeaf_def`,
      `sqrtAddLeaf_eq_mul_sqrtAddLeaf_one`, `sqrtAddLeaf_of_le`
      (`√(64 * r ^ 2 - 64 * δ ^ 2) + (δ / 8 + ℓ)` for `r ≤ 2 * δ`, with
      `0 ≤ L`, `0 ≤ δ`), `sqrtAddLeaf_of_ge` (`√(64 * r ^ 2 + ℓ ^ 2)` for
      `(2 + L) * δ ≤ r`, with `0 < L`, `0 < δ`),
      `contDiffOn_uncurry_sqrtAddLeaf` (smooth on `univ ×ˢ Ioi δ` for
      `0 ≤ δ`, the radicand being at least `64 * (r ^ 2 - δ ^ 2)`),
      `tendsto_deriv_sqrtAddLeaf`, `strictMonoOn_sqrtAddLeaf` (in `ℓ` on
      `Ici 0` at each `r > δ`: the first term is strictly increasing
      where `h r < 1`, the second where `0 < h r`), and, in
      `Surround/ShapeFamily.lean`,
      `sqrtAddLeaf_zero : sqrtAddLeaf L δ 0 = sqrtSubLeaf L δ 0`.
      Both leaves are `cutoffLeaf L δ b c r =
      b * (1 - h r) + √(64 * (r ^ 2 - δ ^ 2) + c * h r)` (in
      `Surround/CutoffLeaf.lean`): `sqrtAddLeaf` with `b = δ / 8 + ℓ`,
      `c = 64 * δ ^ 2 + ℓ ^ 2`, and `sqrtSubLeaf` with
      `b = (ℓ + 8 * δ) / 64`, `c = 64 * δ ^ 2 - ℓ ^ 2`. Their rescaling,
      `_of_le`, `_of_ge`, `tendsto_deriv_`, convexity, smoothness in
      `(ℓ, r)` and strict monotonicity in `ℓ`, and the slope bound of
      `sqrtAddLeaf`, follow from those of `cutoffLeaf`.
    - `exists_isConvexShapeAt_sqrtAddLeaf`: there is `L₀ ≥ 1` such that
      for `L ≥ L₀`, `δ > 0`, `ℓ ∈ Icc 0 (15 * δ / 2)` and `r > δ`,
      `IsConvexShapeAt (sqrtAddLeaf L δ ℓ) r` (the range above `7 * δ`
      serves the bridge leaves below). For `δ = 1` both
      families are `b * (1 - H) + S` with `S ^ 2 = 64 * r ^ 2 - 64 + c * H`:
      `b = (ℓ + 8) / 64 ≤ 1 / 8` and `c = 64 - ℓ ^ 2 ≤ 64` for
      `sqrtSubLeaf`, `b = 1 / 8 + ℓ ≤ 61 / 8` and `c = 64 + ℓ ^ 2 ≤ 121`
      here. So the private steps of `exists_isConvexShapeAt_sqrtSubLeaf`
      move to `CutoffLeaf.lean` and become public, for both:
      `isConvexShapeAt_of_bounds`, as `isConvexShapeAt_of_cutoff_bounds`,
      with `0 ≤ b ≤ 8`, `0 ≤ c ≤ 128`, `|p| ≤ 1 / 1024` and
      `|r * q| ≤ 1 / 1024` in place of `1 / 8`, `64` and `1 / 64`;
      `abs_deriv_cutoff_le`, as `Real.smoothTransition.abs_deriv_sub_div_le`
      in `SmoothTransition/Deriv.lean`, for the cutoff
      `x ↦ smoothTransition ((x - a) / L)` with `0 ≤ a` and
      `A + a * B + M ≤ ε * L`, bounding both quantities by `ε` (here
      `a = 2`, `ε = 1 / 1024`); and the
      first two derivatives of
      `x ↦ b * (1 - H x) + √(64 * x ^ 2 - 64 + c * H x)`, `0 ≤ c`, in
      place of `deriv_sqrtSubLeaf_one` and
      `iteratedDeriv_two_sqrtSubLeaf_one`.
      `exists_isConvexShapeAt_sqrtSubLeaf` keeps its statement, with
      the larger `L₀`. For `2 ≤ r` the bounds become `6 * r ≤ S ≤ 9 * r`,
      `|c * p| ≤ 1 / 8` and `|b * p| ≤ 1 / 128`, so the slope is still at
      least `7`, and the second derivative is at least
      `-(20 + 1 / 128) / r`, against `343 / r` and `1 / χ ≤ 1 / (6 * r)`.
      For `r < 2` the leaf is near `r` the shape of
      `isConvexShapeAt_sqrt_sub` plus `b ≥ 0`.
    - `struweSwitchLeaf L δ ℓ r`: with `A = sqrtAddLeaf L δ ℓ` and
      `T = struweShape δ 1 (2 * ℓ - 47 * δ / 8)` (Struwe's shape with
      that value at `δ`), it is `A r` if `ℓ ≤ 6 * δ`, and
      `smoothedMax ((ℓ - 6 * δ) / 200) (A r) (T r)` otherwise. The gap
      `T δ - A δ` is `g = ℓ - 6 * δ`, and the width is `g / 200`. A
      fixed width fails, since for small `g` the crossing of `A` and `T`
      lies near `δ`, where both slopes are unbounded. API:
      `struweSwitchLeaf_def`, `struweSwitchLeaf_of_le` (`= A` for
      `ℓ ≤ 6 * δ`) and `struweSwitchLeaf_eq_mul_struweSwitchLeaf_one`.
    - `exists_isConvexShapeAt_struweSwitchLeaf`: there is `L₀ ≥ 1` such
      that for `L ≥ L₀` and `δ > 0`, with `χ = struweSwitchLeaf L δ`:
      - `ContDiffAt ℝ ∞ (Function.uncurry χ) q` for
        `q ∈ Icc 0 (7 * δ) ×ˢ Ioi δ`;
      - `IsConvexShapeAt (χ ℓ) r` for `ℓ ∈ Icc 0 (7 * δ)` and `δ < r`;
      - `ContinuousOn (χ ℓ) (Ici δ)` and
        `Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop` for `ℓ ∈ Icc 0 (7 * δ)`;
      - `χ 0 = sqrtAddLeaf L δ 0`, which is `sqrtSubLeaf L δ 0` by
        `sqrtAddLeaf_zero`;
      - `χ ℓ r = sqrtAddLeaf L δ ℓ r` for `ℓ ∈ Icc 0 (7 * δ)` and
        `2 * δ ≤ r`, so `χ ℓ r = √(64 * r ^ 2 + ℓ ^ 2)` for
        `(2 + L) * δ ≤ r`;
      - `StrictMonoOn (fun ℓ ↦ χ ℓ r) (Icc 0 (7 * δ))` for `δ < r`;
      - `χ (7 * δ) r = struweShape δ 1 (65 * δ / 8) r` for
        `r ∈ Ioc δ (257 * δ / 256)`.

      So `ℓₐ = 7 * δ`, and the leaf `ℓₐ` is, by definition,
      `smoothedMax (δ / 200) (sqrtAddLeaf L δ (7 * δ) r)
      (struweShape δ 1 (65 * δ / 8) r)`: Struwe's shape near the
      cylinder and `sqrtAddLeaf L δ (7 * δ)` from `2 * δ` on.

      Proof, for `δ = 1` (then `IsConvexShapeAt.rescale`), with
      `ℓ ∈ Icc 0 7`, `g = ℓ - 6` and `w = √(r ^ 2 - 1)`. Two bounds
      carry it. For `1 < r ≤ 2`, `A r = 1 / 8 + ℓ + 8 * w`, and
      `0 ≤ T r - T 1 ≤ √2 * w`, since `log u ≥ (u ^ 2 - 1) / (2 * u ^ 2)`
      bounds the integrand by `√2 * u / √(u ^ 2 - 1)`; so
      `-g + (8 - √2) * w ≤ A r - T r ≤ -g + 8 * w`. For `2 ≤ r`,
      `A r - T r ≥ 2`: `A r ≥ √(64 * r ^ 2 - 64) ≥ 8 * r - 3`,
      `T 2 ≤ T 1 + √6 ≤ 11`, and the slope of `T` is at most
      `1 / √(log 2) < 5 / 4` on `Ici 2`.
      - Convexity, for `ℓ > 6` (for `ℓ ≤ 6` it is
        `exists_isConvexShapeAt_sqrtAddLeaf`), with `η = g / 200`. Where
        `A - T > η` the leaf is `A` near `r` (`smoothedMax_eq_left`);
        where `A - T < -η` it is `T` (`smoothedMax_eq_right`), and by the
        bounds this happens only in `Ioc 1 2`, where `T` is a convex
        shape by `isConvexShapeAt_struweShape_of_le_of_mem_Ioc` (with
        `K = 1`, `m = 6`, `R = 2`, as `T 1 = 2 * ℓ - 47 / 8 ≥ 6` and
        `log 2 < 1`). Where `|A r - T r| ≤ η`, again in `Ioc 1 2`, the
        upper bound gives `w ≥ 199 * g / 1600`, while
        `deriv A r = 8 * r / w ≤ 16 / w` and
        `deriv T r = 1 / √(log r) ≤ 2 * √2 / w`; so
        `η * (deriv A r + deriv T r) ≤ 152 / 199 < 2 * r`, and
        `isConvexShapeAt_smoothedMax` applies to `A` and `T`, which are
        `C²` at `r > 1`; it asks for `ContDiffAt ℝ 2` only at the point.
      - The far part: `A - T ≥ 2 > η` on `Ici 2`, so `χ ℓ = A` there.
      - The germ: for `ℓ = 7` and `r ≤ 257 / 256`, `w ≤ 1 / 11`, so
        `A r - T r ≤ -3 / 11 < -1 / 200` and `χ 7 r = T r`.
      - The vertical tangent: for `ℓ ≤ 6` that of `A`; for `ℓ > 6` the
        leaf is `T` on some `Ioo 1 (1 + ε)`, as `A - T` tends to `-g`
        at `1`, and `tendsto_deriv_struweShape`. Continuity on `Ici 1`:
        the formula of `A` and `continuousOn_struweShape`.
      - Smoothness: near `(ℓ, r)` with `ℓ < 6` the family is `A`
        (`contDiffOn_uncurry_sqrtAddLeaf`); for `ℓ > 6` it is
        `η * smoothedMax 1 (A r / η) (T r / η)`
        (`smoothedMax_eq_mul_smoothedMax_one`, `contDiff_smoothedMax`),
        and `T r = 2 * ℓ - 47 / 8 + struweShape 1 1 0 r`
        (`struweShape_def`) is smooth in `(ℓ, r)` on `univ ×ˢ Ioi 1`
        (`contDiffOn_struweShape`); near `(6, r)`, `A - T - (ℓ - 6) / 200`
        is continuous and, by the lower bounds, positive at `(6, r)`, so
        the family is `A` on both sides of `ℓ = 6`.
      - Monotonicity in `ℓ`: `A` (`strictMonoOn_sqrtAddLeaf`) and `T`
        are strictly increasing in `ℓ`. For `ℓ ≤ 6 < ℓ'` use
        `max_le_smoothedMax`. For `6 < ℓ < ℓ'` the width grows
        (`monotoneOn_smoothedMax_width`) and both arguments grow by at
        least some `m > 0`, so `smoothedMax_add_add_right` and
        `smoothedMax_le_smoothedMax` give a strict increase.

      Lemma 4.23 (`isConvexShapeAt_struweShape_two`) is not used here.
    - What this needs elsewhere: in
      `Analysis/SpecialFunctions/SmoothedMax.lean`,
      `smoothedAbs_eq_mul_smoothedAbs_one`
      (`smoothedAbs δ t = δ * smoothedAbs 1 (t / δ)` for `δ ≠ 0`: both
      sides have derivative `smoothedSign δ t`, as
      `smoothedSign δ s = smoothedSign 1 (s / δ)`, and agree at `δ`),
      `smoothedMax_eq_mul_smoothedMax_one`,
      `smoothedMax_add_add_right`
      (`smoothedMax δ (a + c) (b + c) = smoothedMax δ a b + c`),
      `monotoneOn_smoothedAbs_width`
      (`MonotoneOn (fun δ ↦ smoothedAbs δ t) (Ioi 0)`: by the rescaling,
      the derivative in `δ` is `f s - s * deriv f s` at `s = t / δ`, with
      `f = smoothedAbs 1`, which vanishes for `1 ≤ |s|` and decreases in
      `|s|` since `f` is convex) and `monotoneOn_smoothedMax_width`; in
      `Surround/SpecialShape.lean`, `struweShape_eq_mul_struweShape_one`
      (`struweShape δ K c = fun r ↦ δ * struweShape 1 K (c / δ) (r / δ)`
      for `δ ≠ 0`, by the substitution `u = δ * v`).

    `exists_convexShapeFamily_surround` takes these leaves as its part
    `ℓ ∈ Icc 0 (7 * δ)`, with one `L` at least the `L₀` of
    `exists_isConvexShapeAt_sqrtSubLeaf` and of
    `exists_isConvexShapeAt_struweSwitchLeaf`. They are standard from
    `r₀ = (2 + L) * δ` on, and they meet `sqrtSubLeaf L δ` at `ℓ = 0`,
    so the joint continuity of `χ`, `∂χ/∂r` and `∂²χ/∂r²` on
    `Icc (-8 * δ) (7 * δ) ×ˢ Ioi δ` follows from
    `ContDiffAt.continuousAt_iteratedDeriv_prod_right` on each of the
    two closed pieces.

    Building issues, in this order: (1) in `Surround/CutoffLeaf.lean`,
    the shared estimate, `sqrtAddLeaf` with its API and
    `exists_isConvexShapeAt_sqrtAddLeaf`, with the proof of
    `exists_isConvexShapeAt_sqrtSubLeaf` rewritten through the estimate
    (about 300 lines); (2) the rescalings and the monotonicity in the
    width above, in `SmoothedMax.lean` and `SpecialShape.lean` (about
    150 lines), independent of (1); (3) in `Surround/CutoffLeaf.lean`,
    `struweSwitchLeaf` and `exists_isConvexShapeAt_struweSwitchLeaf`
    (about 350 lines), after (1) and (2).
  - `exists_isConvexShapeAt_eq_struweShape_eq_linear` (in
    `Surround/SpecialShape.lean`, next to `exists_convexShape_surround`):
    a Struwe shape joined to the line of slope `d` where they cross, the
    step of `exists_convexShape_surround` that the leaves `ℓ ≥ ℓ₁` repeat.
    For `0 < d`, `0 < δ`, `exp (4 / d ^ 2) ≤ K`, `4 < K` and an `ℓ` with
    `2 * K * δ * √(log (2 * K)) ≤ ℓ`,
    `4 * K * δ * √(log (2 * K)) ^ 3 ≤ ℓ` and `2 * K * δ < ℓ * d ^ 3`,
    there is `G : ℝ → ℝ` with `ContDiffOn ℝ ∞ G (Ioi δ)`,
    `IsConvexShapeAt G r` for `r ∈ Ioc δ (2 * K * δ)`,
    `G r = struweShape δ K (ℓ + d * K * δ) r` for `r ≤ 3 * K * δ / 4`,
    and `G r = ℓ + d * r` for `3 * K * δ / 2 ≤ r`. Proof: with
    `S = struweShape δ K (ℓ + d * K * δ)`, `sub_le_struweShape` gives
    `ℓ + d * δ ≤ S δ`, so `S` is a convex shape on
    `Ioc δ (2 * K * δ)` by `isConvexShapeAt_struweShape_of_le_of_mem_Ioc`
    (with `m = ℓ`; the two bounds are the first two hypotheses on `ℓ`),
    and it crosses `ℓ + d * r` only at `K * δ` (`linear_lt_struweShape`,
    `struweShape_lt_linear`). The line is a convex shape on
    `Icc (K * δ / 2) (2 * K * δ)` by `isConvexShapeAt_linear` (the third
    hypothesis). Tau Ceti's
    `ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact` gives a smooth
    function on `ℝ` that is `S` near `Icc (K * δ / 4) (2 * K * δ)`, which
    lies in `Ioi δ` since `4 < K`, and `exists_isConvexShapeAt_eqOn_Iic_Ici` on
    `Icc (K * δ / 2) (2 * K * δ)` with `u = 3 * K * δ / 4` and
    `v = 3 * K * δ / 2` joins the two; `G` is `S` left of `K * δ / 2`
    and that join from there on. So no version of the smoothed maximum
    for shapes that are `C²` only near `Icc r₁ r₂` is needed.
    `exists_convexShape_surround` is this lemma with `ℓ = 1`, followed by
    the shape `ψ` of Lemma 4.19 from `2 * K * δ` on (where `ψ` is still
    `1 + d * r` once `2 * K * δ < β`); its proof is rewritten through it.
  - `exists_convexShapeFamily_struweShape`, the leaves `ℓ ≥ ℓ₁` of
    `exists_convexShapeFamily_surround`: Struwe shapes near the cylinder
    on the members of the square-root family, the construction of
    `exists_convexShape_surround` made uniform in `ℓ`. It takes the
    family `φ` of `exists_convexShapeFamily_sqrt` as hypotheses, so that
    the leaves `ℓ ∈ Icc (7 * δ) ℓ₁` can use the same `φ`: let `0 < d`,
    `exp (4 / d ^ 2) ≤ K`, `4 < K`, `0 < β`, and `φ : ℝ → ℝ → ℝ` with
    `ContDiffAt ℝ ∞ (Function.uncurry φ) q` for
    `q ∈ Ici 0 ×ˢ Ioi 0`, `IsConvexShapeAt (φ ℓ) r` for `0 ≤ ℓ` and
    `0 < r`, `φ ℓ r < φ ℓ' r` for `0 ≤ ℓ < ℓ'` and `0 < r`, and
    `φ ℓ r = ℓ + d * r` for `0 < ℓ` and `r ≤ ℓ * β`, in the form of the
    clauses of `exists_convexShapeFamily_sqrt`. Then there is `C > 0`
    such that for all `δ > 0` and `ℓ₁` with `C * δ ≤ ℓ₁` there is
    `F : ℝ → ℝ → ℝ` with
    - `ContDiffAt ℝ ∞ (Function.uncurry F) q` for
      `q ∈ Ici ℓ₁ ×ˢ Ioi δ`;
    - `IsConvexShapeAt (F ℓ) r` for `ℓ₁ ≤ ℓ` and `δ < r`;
    - `StrictMonoOn (fun ℓ ↦ F ℓ r) (Ici ℓ₁)` for `δ < r`;
    - `F ℓ r = ℓ + struweShape δ K (d * K * δ) r` for every `ℓ` and
      `r ≤ 3 * K * δ / 4`, and `Tendsto (deriv (F ℓ)) (𝓝[>] δ) atTop`
      for every `ℓ`;
    - `F ℓ r = F ℓ₁ r + (ℓ - ℓ₁)` for every `ℓ` and `r < 2 * K * δ`;
    - `F ℓ r = φ ℓ r` for `ℓ₁ ≤ ℓ` and `3 * K * δ / 2 ≤ r`.

    So the leaf `ℓ₁` is `ℓ₁ + S₀` on `Icc δ (3 * K * δ / 4)`, with
    `S₀ = struweShape δ K (d * K * δ)`, the member `φ ℓ₁` from
    `3 * K * δ / 2` on, and the join of the previous lemma in between;
    every other leaf is it raised by `ℓ - ℓ₁` below `2 * K * δ`. Proof:
    take any `C` with `2 * K * √(log (2 * K)) ≤ C`,
    `4 * K * √(log (2 * K)) ^ 3 ≤ C`, `2 * K < C * d ^ 3` and
    `2 * K < C * β`, so that `C * δ ≤ ℓ₁` gives the hypotheses of the
    previous lemma for `ℓ₁` and `2 * K * δ < ℓ₁ * β`. With its `G` for
    `ℓ₁`, put `F ℓ r = G r + (ℓ - ℓ₁)` for `r < 2 * K * δ` and
    `F ℓ r = φ ℓ r` otherwise. Since
    `struweShape δ K (ℓ₁ + c) r = ℓ₁ + struweShape δ K c r`
    (`struweShape_def`), the formula near the cylinder holds, and the
    vertical tangent is `tendsto_deriv_struweShape`. For `ℓ'` near some
    `ℓ ≥ ℓ₁` and `r ∈ Ioo (3 * K * δ / 2) (ℓ' * β)` both pieces are
    `ℓ' + d * r`, so `F` is near each point the smooth `G r + (ℓ - ℓ₁)`
    or `φ`: this gives the smoothness, and with
    `IsConvexShapeAt.add_const` (for `ℓ - ℓ₁ ≥ 0`) and
    `IsConvexShapeAt.congr_of_eventuallyEq` the convexity. Monotonicity
    in `ℓ` holds piece by piece, as each piece is used for a fixed `r`.

    `exists_convexShapeFamily_surround` applies
    `exists_convexShapeFamily_sqrt` with `a = 64` and
    `γ' = min γ (1 / 16)` (a member standard for `ℓ * γ' ≤ r` is standard
    for `ℓ * γ ≤ r`), and this lemma with `K = exp (4 / d ^ 2)` (`4 < K`
    as `d < 1`) at the base point `ℓ₀ = C' * δ` in place of its `ℓ₁`,
    where `C' = max C (max 24 (3 * K / (2 * γ')))`, for `δ` with
    `2 * C' * δ ≤ 1`, `3 * K * δ / 2 ≤ γ` and the conditions of the other
    pieces. It fixes `ℓ₁ = 2 * ℓ₀ ∈ Icc (C * δ) 1`; the `F ℓ` with
    `ℓ ∈ Icc ℓ₀ ℓ₁` serve the last bridge leaves below. Its leaves
    `ℓ ∈ Icc ℓ₁ 1` are the `F ℓ`. They
    are standard for `γ ≤ r`, as `F ℓ = φ ℓ` there and `ℓ * γ' ≤ γ`; the
    joint continuity of `F`, `∂F/∂r` and `∂²F/∂r²` on
    `Icc ℓ₁ 1 ×ˢ Ioi δ` is `ContDiffAt.continuousAt_iteratedDeriv_prod_right`
    applied to the smoothness; `F ℓ` is continuous on `Ici δ` by the
    formula and `continuousOn_struweShape`, so increasing in `r` by
    `strictMonoOn_Ici_of_isConvexShapeAt`; `F ℓ ≤ F 1` is the
    monotonicity in `ℓ`; and the top leaf has height
    `F 1 δ = 1 + S₀ δ`, with `d * δ ≤ S₀ δ` (`sub_le_struweShape`) and
    `S₀ δ < S₀ (K * δ) = d * K * δ < γ` (`strictMonoOn_struweShape`), so
    `1 < F 1 δ < 1 + γ`.

    Building issues, in this order: (1) in `Surround/SpecialShape.lean`,
    `exists_isConvexShapeAt_eq_struweShape_eq_linear`, with the proof of
    `exists_convexShape_surround` rewritten through it (about 150
    lines); (2) in `Surround/ShapeFamily.lean`,
    `exists_convexShapeFamily_struweShape` (about 200 lines).

  - The bridge leaves `ℓ ∈ Icc (7 * δ) ℓ₁`, in `Surround/BridgeLeaf.lean`,
    which `Surround/ShapeFamily.lean` imports; it imports
    `Surround/CutoffLeaf.lean` and takes the family `F` of
    `exists_convexShapeFamily_struweShape` as hypotheses. A Struwe shape
    can only cross a slope-8 shape at radii below about `12 * δ` (at a
    crossing `r` its value is near `8 * r`, and
    `isConvexShapeAt_struweShape_of_lt` needs it above
    `2 * r * √(log (r / δ)) ^ 3`), while the cutoff region of
    `sqrtAddLeaf` reaches `(2 + L) * δ` and the slope `d` of the leaf
    `ℓ₁` is small. So the bridge raises one fixed shape `P`, Struwe's
    near the cylinder and the line of slope `2` from `9 * δ / 2` on,
    over the far parts: a line `c + 2 * r` meets a slope-8 shape near
    `r = c / 6`, and is a convex shape for `r < 8 * c`. Then the far
    part changes from `sqrtAddLeaf` to the standard leaf to `F ℓ` where
    `P` hides it, and `P` sinks below `F ℓ`.
    - `struweLineShape δ r`:
      `smoothedMax (δ / 4) (struweShape δ 4 0 r) (2 * r - 8 * δ)`, the
      Struwe shape and the line meeting at `4 * δ`. With
      `S = struweShape δ 4 0`: `S δ ∈ Icc (-√30 * δ) 0` (the bound
      `1 / √(log u) ≤ √2 * u / √(u ^ 2 - 1)` of the leaves
      `ℓ ∈ Icc 0 (7 * δ)`), `S - (2 * r - 8 * δ) ≥ δ / 4` on
      `Ioc δ (7 * δ / 2)` (it rises up to `exp (1 / 4) * δ`, then falls;
      `0.52 * δ` at `δ` and `0.55 * δ` at `7 * δ / 2`, by `S' ≤ 1 /
      √(log (7 / 2))` on `Icc (7 * δ / 2) (4 * δ)`), and
      `2 * r - 8 * δ - S ≥ δ / 4` on `Ici (9 * δ / 2)`. API:
      `struweLineShape_def`, `struweLineShape_eq_struweShape` (`= S r`
      on `Icc δ (7 * δ / 2)`), `struweLineShape_eq_linear`
      (`= 2 * r - 8 * δ` on `Ici (9 * δ / 2)`),
      `contDiffOn_struweLineShape` (`Ioi δ`),
      `struweShape_le_struweLineShape` and `struweLineShape_le`
      (`≤ max (S r) (2 * r - 8 * δ) + δ / 8`, `smoothedMax_le_max_add`),
      `deriv_struweLineShape_le` (`≤ 2` on `Ici (2 * δ)`,
      `deriv_smoothedMax_le_max`), and
      `isConvexShapeAt_struweLineShape_add`: for `δ < r` and `t` with
      `2 * r * √(log (r / δ)) ^ 3 + 2 * δ < struweLineShape δ r + t` and
      `r * √(log (r / δ)) + 2 * δ < struweLineShape δ r + t` when
      `r ≤ 9 * δ / 2`, and `r < 8 * (t - 8 * δ)` when
      `7 * δ / 2 ≤ r`, `r ↦ struweLineShape δ r + t` is a convex shape
      at `r` (`isConvexShapeAt_struweShape_of_lt`,
      `isConvexShapeAt_linear`, `isConvexShapeAt_smoothedMax` with
      `δ / 4 * (1 + 2) ≤ 2 * r`, applied to the two shapes, which are
      `C²` at `r`; on
      `Icc (7 * δ / 2) (9 * δ / 2)` the shape is within `9 * δ / 8` of
      each piece, as `|S r - (2 * r - 8 * δ)| ≤ δ` there). Write
      `P t r = struweLineShape δ r + t` and `t₀ = 65 * δ / 8 - S δ`, so
      that `P t₀ = struweShape δ 1 (65 * δ / 8)` on
      `Ioc δ (7 * δ / 2)`.
    - What this needs in `Surround/SpecialShape.lean`:
      `struweShape_add` (`struweShape δ K (a + c) r = a +
      struweShape δ K c r`, by `struweShape_def`) and
      `struweShape_eq_struweShape_apply_mul` (for `0 < δ`, `1 ≤ K`, `1 ≤ K'` and
      `δ ≤ r`, `struweShape δ K c r = struweShape δ K'
      (struweShape δ K c (K' * δ)) r`, by
      `intervalIntegral.integral_add_adjacent_intervals`): all Struwe
      shapes at `δ` differ by constants, so near the cylinder every leaf
      below is a Struwe shape plus a constant.
    - `isConvexShapeAt_bridgeLeaf_sqrtAddLeaf` (first stage,
      `ℓ ∈ Icc (7 * δ) (15 * δ / 2)`): for `L` with the hypotheses on `L`
      of `isConvexShapeAt_sqrtAddLeaf`, `δ > 0`, such
      `ℓ`, `t₀ ≤ t` and `δ < r`,
      `r ↦ smoothedMax (δ / 200) (sqrtAddLeaf L δ ℓ r) (P t r)` is a
      convex shape at `r`. With `A = sqrtAddLeaf L δ ℓ` and
      `w = √(r ^ 2 - δ ^ 2)`: `A ≥ 8 * w`, `A ≤ δ / 8 + ℓ + 8 * r + ℓ`,
      `A = δ / 8 + ℓ + 8 * w` on `Ioc δ (2 * δ)` and
      `deriv A ≤ 11` on `Ici (2 * δ)` (the bounds in the proof of
      `exists_isConvexShapeAt_sqrtAddLeaf`, made public). Where
      `P t ≥ A - δ / 200`, the height conditions of
      `isConvexShapeAt_struweLineShape_add` hold (`A ≥ 7 * δ` on
      `Ioc δ (2 * δ)`, `8 * w - 2 * r * √(log (r / δ)) ^ 3 > 3 * δ` on
      `Icc (2 * δ) (9 * δ / 2)`, and `t - 8 * δ ≥ 8 * w - 2 * r - 2 * δ
      > r / 8` on `Ici (7 * δ / 2)`). Where `|A - P t| ≤ δ / 200` and
      `r ≤ 2 * δ`, `P t = struweShape δ 1 (65 * δ / 8) + (t - t₀)` and
      `A - struweShape δ 1 (65 * δ / 8) ≤ -δ / 2 + 8 * w`, so
      `w ≥ δ / 17` and, as for `struweSwitchLeaf`,
      `δ / 200 * (8 * r / w + 2 * √2 * δ / w) ≤ 2 * r`; for
      `2 * δ ≤ r` the slopes are at most `11` and `2`. Also
      `bridgeLeaf_sqrtAddLeaf_eqOn_struweSwitchLeaf`: at `ℓ = 7 * δ` and
      `t = t₀` the leaf is `struweSwitchLeaf L δ (7 * δ)` on `Ioi δ`
      (`P t₀` is its Struwe shape `T` on `Ioc δ (7 * δ / 2)`; beyond,
      `P t₀ ≤ max (T r) (2 * r + 6 * δ) + δ / 8`, and `T` and
      `2 * r + 6 * δ` are more than `δ / 200 + δ / 8` below `A`, as
      `A - T ≥ 2 * δ` there), and `bridgeLeaf_sqrtAddLeaf_eqOn_sqrt`: if
      `S δ + t ≥ 3 * ℓ + 8 * (3 + L) * δ` (and `0 < L`, `0 ≤ ℓ`), `A` may be
      replaced by `√(64 * r ^ 2 + ℓ ^ 2)` (`P t` is above both by more
      than `δ / 200` on `Ioc δ ((2 + L) * δ)`, and they agree beyond).
    - `isConvexShapeAt_bridgeLeaf_sqrt` (second stage): for `δ > 0`,
      `ℓ ≥ 0`, `η ∈ Ioc 0 (δ / 200)`, `t` with
      `3 * ℓ + 30 * δ ≤ S δ + t` and `δ < r`,
      `r ↦ smoothedMax η (√(64 * r ^ 2 + ℓ ^ 2)) (P t r)` is a convex
      shape at `r` (`isConvexShapeAt_sqrt`; where `P t` is used it is
      above `8 * r - δ`; the two meet only where
      `√(64 * r ^ 2 + ℓ ^ 2) ≥ 3 * ℓ + 29 * δ`, so at `r > 7 * δ / 2`,
      where the slopes are at most `8` and `2`).
    - `isConvexShapeAt_bridgeLeaf_of_eq_struweShape` (last stage), for a
      single leaf `G` (one `F ℓ`): let `0 < δ`, `24 * δ ≤ ℓ`, `8 ≤ M`,
      `c₀ : ℝ`, and `G : ℝ → ℝ` a convex shape at every `r > δ`, `C²` on
      `Ioi δ`, with `G r = c₀ + S r` on `Ioc δ (9 * δ / 2)`, `ℓ ≤ G r`
      for `δ < r`, `G r = √(64 * r ^ 2 + ℓ ^ 2)` for `ℓ / 4 ≤ r`, and
      `|deriv G r| ≤ M` on `Icc (3 * δ) (ℓ / 4)`. Then for
      `η ∈ Ioc 0 (6 * δ / (2 + M))`, any `t` and
      `δ < r`, `r ↦ smoothedMax η (G r) (P t r)` is a convex shape at
      `r`. On `Ioo δ (7 * δ / 2)` it is `G` plus the constant
      `smoothedMax η 0 (t - c₀)` (`struweShape_add`,
      `smoothedMax_add_add_right`, `IsConvexShapeAt.add_const`), so no
      bound on slopes near the cylinder is needed. On
      `Icc (7 * δ / 2) (9 * δ / 2)`, where `P t ≥ G - η` the height
      conditions hold as `ℓ ≥ 24 * δ`, and the slopes are at most `1`
      and `2`. Where the line part is used, `t - 8 * δ > r / 8`: below
      `ℓ / 4`, from `G ≥ ℓ`; above,
      from `(t - 8 * δ + δ + 2 * r) ^ 2 ≥ ℓ ^ 2 + 64 * r ^ 2`, which
      gives `r ≤ (t - 7 * δ) / 6`, while `r ≥ ℓ / 4 ≥ 6 * δ`. Where the
      two meet beyond `9 * δ / 2`, `η * (2 + M) ≤ 2 * r`. Also
      `bridgeLeaf_eq_of_le`: for `t ≤ 8 * δ` and `η ≤ 3 * δ` the leaf is `G`
      (`P t ≤ 2 * r + 8 * δ + δ / 8 ≤ G - η`, as `G ≥ ℓ ≥ 4 * r` below
      `ℓ / 4` and `G ≥ 8 * r` beyond), and `bridgeLeaf_sqrt_eq`: if
      `S δ + t ≥ 3 * ℓ + η`, the standard leaf may be replaced by `G`
      (`G` and the standard leaf are at most `√5 * ℓ` on `Ioc δ (ℓ / 4)`,
      being increasing, and agree beyond).

    `exists_convexShapeFamily_surround` takes, with `ℓ₀`, `ℓ₁ = 2 * ℓ₀`
    and the `F` from base point `ℓ₀` as fixed above, `τ =
    Real.smoothTransition`, `t₁ = 3 * ℓ₁ + 8 * (3 + L) * δ - S δ`,
    `M ≥ 8` a bound of `|∂F/∂r|` on `Icc ℓ₀ ℓ₁ ×ˢ Icc (3 * δ) (ℓ₁ / 4)`
    (continuity on a compact set) and
    `η₁ = min (δ / 200) (6 * δ / (2 + M))`, the bridge leaves
    - `smoothedMax (δ / 200) (sqrtAddLeaf L δ ℓ r) (P t r)` with
      `t = t₀ + (t₁ - t₀) * τ ((ℓ - 7 * δ) / (δ / 2))` for
      `ℓ ∈ Icc (7 * δ) (15 * δ / 2)`;
    - `smoothedMax η (√(64 * r ^ 2 + ℓ ^ 2)) (P t₁ r)` with
      `η = δ / 200 - (δ / 200 - η₁) * τ ((ℓ - 15 * δ / 2) /
      (ℓ₀ - 15 * δ / 2))` for `ℓ ∈ Icc (15 * δ / 2) ℓ₀`;
    - `smoothedMax η₁ (F ℓ r) (P t r)` with
      `t = t₁ - (t₁ - 8 * δ) * τ ((ℓ - ℓ₀) / ℓ₀)` for
      `ℓ ∈ Icc ℓ₀ ℓ₁`.

    Consecutive pieces agree at their common `ℓ` by the equalities
    above, the first one with `struweSwitchLeaf L δ (7 * δ)` and the
    last one with `F ℓ₁`. Each formula is smooth in `(ℓ, r)` near every
    point of its piece times `Ioi δ`
    (`smoothedMax_eq_mul_smoothedMax_one` for the varying width), so
    `ContDiffAt.continuousAt_iteratedDeriv_prod_right` on each closed
    piece gives the joint continuity of `χ`, `∂χ/∂r` and
    `∂²χ/∂r²` on `Icc (-8 * δ) 1 ×ˢ Ioi δ`. Near the cylinder each
    bridge leaf is a Struwe shape plus a constant (in the first two
    stages `P t` exceeds the other shape by at least `δ / 2` at `δ`; in
    the last one the leaf is `F ℓ` plus a constant there), which gives
    the vertical tangent (`tendsto_deriv_struweShape`) and the
    continuity on `Ici δ`.
    For `r ≥ (t₁ + 2 * δ) / 6`, `P t` is below the standard leaf by more
    than the width, and `sqrtAddLeaf` and `F ℓ` are standard from
    `max ((2 + L) * δ) (ℓ₁ * γ')` on, so the bridge leaves are standard
    for `γ ≤ r` once `δ` is small. Below that radius each is at most
    `2 * t₁ + 9 * ℓ₁` or equal to `F ℓ ≤ F 1`, and above it each is
    `F ℓ` or the standard leaf with `ℓ < 1`, which is below `F 1` (the
    standard leaf `1` from `γ'` on, and at least `1` before); so
    `χ ℓ ≤ χ 1` once `δ` is small.

    Building issues, in this order, after the leaves
    `ℓ ∈ Icc 0 (7 * δ)` and `exists_convexShapeFamily_struweShape`:
    (1) in `Surround/SpecialShape.lean`, `struweShape_add` and
    `struweShape_eq_struweShape_apply_mul`, and in `Surround/BridgeLeaf.lean`,
    `struweLineShape` with its API (about 250 lines); (2) the first two
    stages, with the public bounds on `sqrtAddLeaf` in
    `Surround/CutoffLeaf.lean` (about 300 lines); (3) the last stage
    (about 250 lines). The gluing is part of the issue of
    `exists_convexShapeFamily_surround`.

- `Surround/ShapeFoliation/` (issue 14d6): from families of shapes
  to functions.
  - `exists_shapeFoliation` (Proposition 3.25 within shapes, Corollary
    4.29). Write `Q = Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂` and `E` for the part of
    its boundary where the family is kept,
    `({ℓ₀, ℓ₁} ×ˢ Icc r₁ r₂) ∪ (Icc ℓ₀ ℓ₁ ×ˢ {r₂})`. Hypotheses:
    `0 < r₁`, `ℓ₀ < ℓ₁`, `r₁ < r₂`; `ContDiffAt ℝ 2 (χ ℓ) r` and
    `IsConvexShapeAt (χ ℓ) r` on `Q`; for `k ≤ 2` the map
    `fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2` is continuous on `Q`
    (the value and the first two `r`-derivatives are jointly continuous);
    `χ ℓ r < χ ℓ₁ r` for `ℓ ∈ Ico ℓ₀ ℓ₁` and `r ∈ Icc r₁ r₂`; and some
    `U ∈ 𝓝ˢ E` on which `Function.uncurry χ` is smooth with
    `0 < deriv (fun ℓ' ↦ χ ℓ' r) ℓ`. Conclusion: a `ψ : ℝ → ℝ → ℝ`,
    `ContDiffOn ℝ ∞ (Function.uncurry ψ) Q`, with
    `IsConvexShapeAt (ψ ℓ) r` and `0 < deriv (fun ℓ' ↦ ψ ℓ' r) ℓ` on
    `Q`, and `Function.uncurry ψ =ᶠ[𝓝ˢ E] Function.uncurry χ`.
    "Increasing in `ℓ`" is always this strict sign of the
    `ℓ`-derivative, the hypothesis of `exists_contDiff_shapeLevel`, and
    `ℓ` is whatever parameter the caller uses (issue 14d7 takes
    `u = ℓ * |ℓ|`, see there). No lower bound `χ ℓ₀ ≤ χ ℓ` is needed,
    and the members in between need not be ordered; the strict upper
    bound is what lets the new family end on `χ ℓ₁` exactly. Without the
    joint continuity of the `r`-derivatives the statement is not proved
    this way: `χ ℓ r = f r + c * h ^ 2 * sin (r / h)`, `h = (ℓ - ℓ') ^ 2`,
    is jointly continuous with every member a smooth convex shape, but
    `∂²χ/∂r²` has no limit at `ℓ'`, so no margin of `isConvexShapeAt_iff`
    is uniform in `ℓ`.

    The proof is in five steps, each a building issue of 14d6.
    1. `exists_forall_isConvexShapeAt_of_abs_sub_lt`
       (`Surround/ConvexShape/Basic.lean`): for a compact `K ⊆ ℝ × ℝ` with
       `IsConvexShapeAt (χ ℓ) r` and the joint continuity above on `K`,
       there is `η > 0` such that every `φ : ℝ → ℝ` and `(ℓ, r) ∈ K`
       with `|iteratedDeriv k φ r -
       iteratedDeriv k (χ ℓ) r| < η` for `k ≤ 2` give
       `IsConvexShapeAt φ r`. The two strict inequalities of
       `isConvexShapeAt_iff`, and `0 < χ`, are an open condition on
       `(χ, χ', χ'', r)`, and the image of `K` is compact. Every later
       step only checks closeness to some member in this sense.
    2. `ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt`
       (`Analysis/Calculus/BumpFunction/SmoothApprox.lean`, a statement about
       real functions): a function `Cⁿ` on a neighbourhood of `Icc a b` is,
       for each `ε > 0`, within `ε` on `Icc a b` of a smooth `g` in its
       derivatives of order at most `n`, and `g` equals it near `Icc c b` if it
       is smooth on a neighbourhood of `Icc c b` (convolution with a
       `ContDiffBump`, glued by a cutoff). It turns finitely many members
       into smooth convex shapes `A i` (step 1).
    3. `exists_forall_isConvexShapeAt_smoothedMax`
       (`Surround/ConvexShape/SmoothedMax.lean`, through the public pointwise step
       `exists_pos_forall_isConvexShapeAt_smoothedMax`, whose `δ₀` depends
       only on a margin `a > 0` and bounds `G`, `Q`): for a compact `K`
       and families `M p`, `A p`, `p ∈ K`, of convex shapes that are `C²`
       at each point of `Icc r₁ r₂`, whose values and first two `r`-derivatives are
       continuous on `K ×ˢ Icc r₁ r₂`, some `δ₀ > 0` makes
       `fun r ↦ smoothedMax δ (M p r) (A p r)` a convex shape on
       `Icc r₁ r₂` for all `δ ∈ Ioc 0 δ₀` and `p ∈ K` at once:
       the margins and bounds in the proof of
       `exists_isConvexShapeAt_eq_max`, which is its case of one point, are
       uniform over the compact set. Step 4 takes `A p = A - p`,
       `p ∈ Icc 0 η'`.
    4. `exists_monotone_shapeChain` (`Surround/ShapeFoliation/Chain.lean`): a
       smooth family that is only weakly increasing. Take
       `ℓ₀ < a < b < ℓ₁` with `Icc ℓ₀ a ×ˢ Icc r₁ r₂` and
       `Icc b ℓ₁ ×ˢ Icc r₁ r₂` in `U`, points `a = t 0 < … < t N = b` of a
       small mesh `h`, `A 0 = χ a` near `Icc r₁ r₂`, `A i` smooth and close
       to `χ (t i)`
       (step 2), and `M 0 = A 0`,
       `M (i + 1) = smoothedMax δᵢ (M i) (A (i + 1))`. By uniform continuity
       `A (i + 1) - η' < M i - δᵢ` once `h` is small, so the path
       `σ ↦ smoothedMax δᵢ (M i) (A (i + 1) - (1 - σ) * η')`, run through a
       smooth step that is flat at both ends, goes from `M i` to
       `M (i + 1)`, is smooth in `(σ, r)`, weakly increasing in `σ`
       (`smoothedMax` is monotone in its second argument), and consists of
       convex shapes (step 3). The paths glue, being flat at the joints, to
       a smooth `C` on `Icc a b`, weakly increasing in `ℓ`, with `C a`
       equal to `χ a` near `Icc r₁ r₂`
       and `C b = M N ≤ max over Icc a b of χ ℓ + ∑ δᵢ + ε`. Near `r₂`,
       where `∂χ/∂ℓ ≥ m > 0` and `χ` is smooth, `M i = A i = χ (t i)` once
       `δᵢ < m * h / 2`, and `C ℓ` is within any given tolerance of `χ ℓ`
       in value and two `r`-derivatives once `h` is small, since there
       `∂χ/∂r` is Lipschitz in `ℓ` and the second derivative of
       `smoothedAbs δᵢ` is of order `1 / δᵢ`. The order of choice is
       tolerance and `ε`, `η'`, then `δᵢ = c * h` with `c` fixed, last `h`.
    5. `exists_shapeFoliation` itself (`Surround/ShapeFoliation/Smoothing.lean`):
       with `κ > 0` small and a smooth `θ`, nondecreasing, `0` near `ℓ₀`,
       constant near `ℓ₁` and with `θ' > 0` in between, the family is
       `χ (λ₀ ℓ) + κ * θ ℓ` near `ℓ₀` (`λ₀` a smooth reparametrization onto
       `Icc ℓ₀ a`, the identity near `ℓ₀` and flat at its other end),
       `C ℓ + κ * θ ℓ` in the middle, and
       `smoothedMax δ (M N + κ * θ ℓ) (χ (λ₁ ℓ))` near `ℓ₁` (`λ₁` onto
       `Icc b ℓ₁`, flat at its first end, the identity near `ℓ₁`). The
       shifts keep convex shapes by `IsConvexShapeAt.add_const`; the
       `ℓ`-derivative is positive because at each point `θ' > 0` or the
       reparametrization has positive slope, and the two partial
       derivatives of `smoothedMax` are nonnegative with sum `1`; the
       strict upper bound gives `χ ℓ > M N + κ * θ ℓ + δ` near `ℓ₁`, where
       the family is then `χ ℓ`. Last, near `r₂` the family is blended
       with `χ` by a cutoff `ρ ≥ 0` in `r`: both are increasing in `ℓ` there
       and close in value and first `r`-derivative (step 4), while their
       second `r`-derivatives are close only from below: near `ℓ₁` the term of
       `iteratedDeriv_two_smoothedMax` with `(smoothedAbs δ)''` is
       nonnegative and may be of order `1 / δ`. So the blend is increasing
       and, by the one-sided blend lemma
       `exists_forall_isConvexShapeAt_mul_add_one_sub_mul_of_sub_lt_iteratedDeriv_two`
       (`Surround/ConvexShape/Basic.lean`), a convex shape.
    The shapes of `exists_convexShapeFamily_surround` have vertical
    tangents at `r = δ`, where they are not graphs over `r`; there the
    same statement is used with `r` as a function of `R`, the shapes
    being graphs over `R` near that line, and the building issue states
    that second form (`Surround/ShapeFoliation/OverR.lean`) with the
    criterion of 14d1 rewritten for it.
  - `exists_contDiff_shapeLevel` (`Surround/ShapeFoliation/Level.lean`,
    the function of a foliation): a family
    as above, on `Ioo ℓ₀ ℓ₁ ×ˢ Ioo r₁ r₂` and with `0 < ∂χ/∂ℓ`, defines,
    by the inverse function theorem for `(ℓ, r) ↦ (χ ℓ r ^ 2, r ^ 2)`
    (Mathlib's `ContDiffAt.to_localInverse`), an `H : ℝ × ℝ → ℝ`
    smooth at each point of the region it sweeps out, with `H (χ ℓ r ^ 2, r ^ 2) = -ℓ`,
    `∂H/∂t > 0` and `∂H/∂s < 0` there (the leaves rise with `ℓ`, so
    `H` falls as `s` grows and rises as `t` grows); `dH` is then a
    positive multiple of the differential of `shapeGraph (χ ℓ) ∘ shape`,
    and every level of `H ∘ shape` is $i$-convex by
    `IsConvexShapeAt.re_leviForm_pos` and
    `forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`.
  - In `JConvex/Hypersurface.lean`:
    `exists_isManifoldStrictlyPlurisubharmonicAt_comp_of_isCompact`
    (the book's Lemma 2.7, on a compact set): let `f : M → ℝ` be `C²`
    at each point of a compact `K`, and the Levi form of `f` positive
    on the nonzero `v` with
    `df(v) = df(i v) = 0` at each `x ∈ K`. Then there is `C ≥ 0` such
    that `g ∘ f` is strictly plurisubharmonic at every point of `K`
    for each `g` that is `C²` at the points of `f '' K`, with
    `0 < deriv g` and
    `C * deriv g ≤ iteratedDeriv 2 g` on `f '' K`. This is a
    statement about $J$-convex levels and belongs with them.

- `Surround/ModelHandle.lean` (issue 14d7): Theorems 4.2 (i)–(iii),
  Corollary 4.3 and Corollary 4.4 for `J = i`, with `1 < a`,
  `γ ∈ Ioo 0 1` and `Ψst = modelHandle k m 1 a`.
  - `exists_shapeFoliation_cylinder` (the leaves near the cylinder; the
    book has no counterpart, see issue 14d4's paragraph on the corner):
    take the family of `exists_convexShapeFamily_surround`, made smooth
    by `exists_shapeFoliation` (applied in the parameter `u = ℓ * |ℓ|`,
    in which the standard leaves `√(64 * r ^ 2 + u)` have positive
    `u`-derivative, also at `u = 0`; on a rectangle whose lower end in
    `r` lies above the `r₀` of issue 14d5, where the family is standard
    for `ℓ` near `-8 * δ`; and continued a little past `u = 1` by
    `χ 1 r + √(64 * r ^ 2 + u) - √(64 * r ^ 2 + 1)`, which is standard
    for `γ ≤ r`, so smooth across `u = 1` there, is a convex shape for
    `u` close to `1` by
    `exists_forall_isConvexShapeAt_of_abs_sub_lt`, and lies
    strictly above `χ 1`, hence above every earlier member), and write its leaf `ℓ` near the line
    `r = δ` as `r = ρ ℓ R` over `R ≥ 0`, with `ρ ℓ = δ` on
    `Icc 0 (χ ℓ δ)`. For `δ' < δ` close to `δ` there are `r₁ ∈ Ioo δ γ`,
    `R₁ > 0` and curves `r = ρ' ℓ R`, `ℓ ∈ Icc (-8 * δ) 1`, smooth in
    `ℓ` and in `R ^ 2`, such that `ρ' ℓ = ρ ℓ` outside
    `{r < r₁ ∧ R < R₁}`, `ρ' 1` is the `ρ'` of `Σ'`, `ρ' ℓ R` is
    strictly decreasing in `ℓ` (the new leaves are disjoint), each new
    leaf is a convex shape over `R` at each of its points (the criterion
    of issue 14d1 for graphs over `R`), and for `ℓ` near `1` the function
    `ρ' ℓ` is constant on `Icc 0 1`. The leaf `ℓ` is built as `Σ'` is:
    `ρ' ℓ` is the smoothed minimum of `ρ ℓ` and a curve `q ℓ`, constant
    equal to `c ℓ` up to `R₀ ℓ` and convex beyond, crossing `ρ ℓ` once,
    transversally, beyond the corner, with `c` strictly decreasing from
    `δ` at `ℓ = -8 * δ` to `δ'` at `ℓ = 1`. For the leaves of small
    height, near `ℓ = -8 * δ`, `R₀ ℓ = 0` and `q ℓ` is a function of
    `R ^ 2`, so that the leaf is smooth on the axis `s = 0`, and `q ℓ`
    must tend, with the crossing, to the smooth leaf `χ (-8 * δ)`
    (`r = √(δ ^ 2 + R ^ 2 / 64)`) as the height tends to `0`. That limit
    is the step to check first.
  - `exists_modelHandle_exterior` (Theorem 4.2 (i)–(iii), with `Σ'` for
    `Σ`): there are `δ ∈ Ioo 0 γ` and a shape `χ` with the properties
    that `exists_convexShape_surround` gives, so that `Σ` is a
    hypersurface as in Theorem 4.1, a `δ' ∈ Ioo 0 δ` and the `Σ'` of
    issue 14d4's paragraph on the corner, and on the closed outside
    `Ωext = {p | ρ' (√(s p)) ≤ √(t p)}` of `Σ'` a continuous
    `Ψ = H ∘ shape`, with `Ψ = Ψst` on `Ωext ∩ {p | γ ^ 2 ≤ t p}` and
    `Ψ = -1` exactly on `Σ'`, smooth on `Ωext` with `∂H/∂t > 0` and
    `∂H/∂s ≤ 0`, such that `g ∘ Ψ` is strictly plurisubharmonic on
    `Ωext ∩ K` for each compact `K` and a `g` as in the lemma of
    `Hypersurface.lean`, and `Ψ` is a function of `t` alone on
    `Ωext ∩ {p | s p ≤ 1 ∧ t p ≤ δ₁ ^ 2}` for some `δ₁ > δ'`. Below
    the leaf `χ (-8 * δ)`, which the family does not sweep, `Ψ` is
    `64 * t - s`, the value on the standard leaves
    `s = 64 * t + ℓ * |ℓ|` with `ℓ < -8 * δ` (whose foliation level is
    `√(64 * t - s)`), continued by the interpolation towards `Ψst`.
    The proof: the shapes of `exists_convexShapeFamily_surround` (with a
    smaller `γ'` for `γ`) continued by the levels of the separable
    interpolation above, which replaces Proposition 3.26,
    `exists_shapeFoliation` for Proposition 3.25, and
    `exists_shapeFoliation_cylinder` near the cylinder; `Ψ` is `-ℓ` on
    the new leaf `ℓ`, smooth by `exists_contDiff_shapeLevel` (in the form
    over `R` near `r = δ`). So `χ` is the shape `χ 1` of that family,
    continued, and not the one of `exists_convexShape_surround`.
  - `exists_modelHandle_collar` (Corollary 4.3): for small `σ > 0`, the
    same on an open `Ω ⊇ Ωext` with values in `Ioi (-1 - σ)`, and a
    smooth increasing `f` with `f (Ψ p) = √(t p)` on
    `Ω ∩ {p | t p ≤ δ' ^ 2 ∧ s p ≤ 1}`. Near the cylinder the leaves
    are the cylinders `r = c ℓ`, so `Ψ` there is a function of `t`, and
    continuing that function inside gives `f`; elsewhere the family is
    continued past `ℓ = 1`.
  - `exists_modelSurround` (Corollary 4.4 for `t = 1`): for `1 < a` and
    `γ ∈ Ioo 0 1` there are `δ ∈ Ioo 0 γ`, a smooth `Ψ : V → ℝ` of the
    form `H ∘ shape` with `∂H/∂t > 0` and `∂H/∂s ≤ 0` where `t > 0`,
    and a smooth `g : ℝ → ℝ` with `0 < deriv g`,
    `0 ≤ iteratedDeriv 2 g`, such that `g ∘ Ψ` is strictly
    plurisubharmonic at every point of `V`, `Ψ = Ψst` on
    `{p | γ ^ 2 ≤ t p ∨ (1 + γ) ^ 2 ≤ s p}`, `Ψ = -1` on
    `{p | t p = δ ^ 2 ∧ s p ≤ 1}` and `Ψ < -1` on
    `{p | t p < δ ^ 2 ∧ s p ≤ 1}` (so the image of `closedBall 0 1`
    under `modelDisc k m` lies in `{Ψ < -1}`), `-1` is a regular value
    of `Ψ`, and near `{p | t p = 0}` the function `Ψ` is `e ∘ Ψst` for
    a smooth `e` with `0 < deriv e` everywhere (target equivalent, the
    book's (iii)); issue 14e needs the positive derivative for the
    nondegeneracy of `ι 0`. Its
    `δ` is the `δ'` of `exists_modelHandle_collar`, and its level `-1`
    is `Σ'`. The
    homotopy `Ψ_t` of the book's Corollary 4.4 is not stated: the
    statements of issues 14d and 14e need only its end, and the book's
    homotopy serves its Theorem 8.5, which the design does not state.
    This is the model that issue 14d implants: with `a = 2`,
    `1 + Ψ` agrees with `modelLevel k m` where `Ψ = Ψst`.

- `Surround/ModelMargin.lean` (issue 14d8): the margin of §4.7 that the
  move onto a manifold (issue 14d15) needs. With the normalized modulus
  of the book's (3.10), the statement is
  `exists_modelSurround_margin`: there are `c > 0` and `N : ℕ`,
  depending on `a`, `k`, `m` only, such that for every `γ ∈ Ioo 0 1`
  the `Ψ` and `g` of `exists_modelSurround` can be chosen with
  `c * γ ^ N * max ‖fderiv ℝ (fderiv ℝ (g ∘ Ψ)) p‖ ‖fderiv ℝ (g ∘ Ψ) p‖ * ‖v‖ ^ 2 ≤
  (leviForm (g ∘ Ψ) p v v).re` for all `v` and all `p` with
  `t p ≤ γ ^ 2` and `s p ≤ (1 + γ) ^ 2`. Its steps are the quantitative
  versions of the above: Proposition 4.30 (the margin conditions
  (4.15)–(4.20) on a shape), Lemma 4.31 (Struwe's solutions),
  Lemma 4.32 (a), (b), (e) (the shapes `S`, `Q`, `L`), Propositions 4.33
  and 4.34, and the book's Proposition 3.38 in shape form (a defining
  function of a convex shape with a margin). The book reaches
  `‖J - i‖_{C²} ≤ c γ ^ 12` in (4.1), from a margin `c γ ^ 6` on each
  shape (proof of Proposition 4.33); the statement keeps `N`
  existential, since issue 14d needs only a fixed power of `γ` and
  chooses the order of the chart of issue 14d13 after it.

- **The model handle on the manifold (issues 14d9–14d15).** Issue 14d
  places the model of `Surround/ModelHandle.lean` along the disc through
  one map `Φ` from a neighbourhood of the core of `V` into `M`, and reads
  `g ∘ Ψ ∘ Φ⁻¹` there. Here `V`, `s`, `t` and `modelDisc k m` are those of
  `Surround/Shape.lean`, `ι : EuclideanSpace ℝ (Fin k) → M` is a disc as
  above (issue 14d composes with a linear isometry onto `F`, which
  `IsJOrthogonallyAttached.comp_linearIsometry` allows), and
  `finrank ℂ E = k + m`. For `G : V → W` between complex normed spaces
  write `∂̄G x = (fderiv ℝ G x).comp (Complex.I • ContinuousLinearMap.id ℝ V)
  - Complex.I • fderiv ℝ G x`, the defect of complex linearity of its
  differential; the statements write this expression out and define no
  new operator. `F^* J - i` of the book and `∂̄` of `Φ` read in holomorphic
  charts of `M` control each other, with constants that depend on `dΦ` and
  `dΦ⁻¹`.

  *Route.* The book's Proposition 5.55 gives, for a totally real disc in
  an almost complex manifold, an extension `Φ` of a parametrization with
  `Φ^* J - i` vanishing to a prescribed order along the core, and the
  proof of its Theorem 8.5 combines it with the margin of §4.7 through
  the estimate (8.1) and the hypothesis (4.1) of Theorems 4.1 (iv) and
  4.2 (iv). Here `J` is integrable, and the design follows that
  proposition in this case, in two steps. (1) A first-order chart `Φ₀`
  with `Φ₀ ∘ modelDisc k m = ι` and complex-linear differential along the
  core, by Tau Ceti's extension with a prescribed differential. (2) The
  correction to order `N` by almost holomorphic Taylor extension:
  in the coordinates of `Φ₀` the core lies in the real points
  `Re V = {Im z = 0, Im w = 0}`, a real subspace of dimension
  `n = k + m`, totally real for `Φ₀^* J` near the core since
  `Φ₀^* J = i` along the core; in a holomorphic chart `κ` of `M` the map
  `h = κ ∘ Φ₀` restricted to `Re V` has the Taylor extension of order `N`,
  whose `∂̄` vanishes to order `N` along `Re V`; pulled back by `h`, these
  local extensions agree with each other to order `N + 1`, so a partition
  of unity glues them in `V` into one map `G` with `G = id` on `Re V`,
  and `Φ = Φ₀ ∘ G`. The disc is not moved: `Φ ∘ modelDisc k m = ι`
  exactly, so every field of `IsJOrthogonallyAttached` holds for the
  disc that the model is read along, and no approximation of `φ` or `ι`
  is needed. The route of the proof of Proposition 8.12 (real analytic
  approximation by Theorem 5.53 and complexification, Lemma 5.40) is not
  taken: it moves the disc, so the equalities `eq_zero` and
  `mvfderiv_I_smul_mfderiv` would have to be restored afterwards, and it
  needs approximation results that neither library has.

  *Comparison.* The Levi form of `u ∘ Φ⁻¹` is read in Tau Ceti's sense,
  in charts of `M`, so it is the Euclidean Levi form of `u ∘ e⁻¹` for
  `e = κ ∘ Φ`. With `ξ = de_p v`, `Re leviForm (u ∘ e⁻¹) (e p) ξ ξ` is
  `(D²u(v, v) + D²u(Jv, Jv)) / 4` plus `Du` applied to
  `(D²e⁻¹(ξ, ξ) + D²e⁻¹(iξ, iξ)) / 4`, where `J = de_p⁻¹ ∘ i ∘ de_p`.
  The first part differs from `Re leviForm u p v v` by at most a constant
  times `‖∂̄e p‖ ‖D²u p‖ ‖v‖²`; the vector in the second is
  `i (D ∂̄e⁻¹)(ξ) ξ + (D ∂̄e⁻¹)(iξ) ξ`, which vanishes for holomorphic `e`
  (Tau Ceti's `manifoldLeviForm_comp_apply`) and is bounded by
  `‖∂̄e p‖ + ‖D (∂̄e) p‖` in general. So the error is first order in `∂̄e`
  against `D²u` and `Du`; this is the role that the bound (4.1) on
  `J - i` plays in the book. If `∂̄e` vanishes to order `N` along
  `Re V`, the error is at most
  `C * √(t p) ^ (N - 1) * max ‖D²u p‖ ‖Du p‖ * ‖v‖ ^ 2` on the handle, and
  the margin `c * γ ^ N₀` of `exists_modelSurround_margin` absorbs it for
  small `γ` as soon as `N₀ + 2 ≤ N`. Issue 14d20 chooses `N = N₀ + 2` after
  issue 14d8 has fixed `N₀`.

- `Surround/ComplexFrame.lean` (issue 14d9): complex frames along a
  disc. `exists_complexFrame_mfderiv`: for `ι` a smooth embedding of
  `EuclideanSpace ℝ (Fin k)` whose tangent images are totally real in the
  weak sense, there is `A : ∀ x, V →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x)`,
  smooth in tangent coordinates (`inTangentCoordinates`, as Tau Ceti's
  `exists_partialDiffeomorph_mfderiv_eq` asks), with each `A x`
  invertible, complex linear (`A x (Complex.I • v) = ofComplexManifold E M (ι x) (A x v)`)
  and `(A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, V)
  (modelDisc k m) x) = mfderiv _ _ ι x`. The theorem itself asks only
  that `ι` be a smooth immersion (`IsImmersion`), which a smooth embedding
  is. On the first factor `A x` is the
  complex-linear extension of `dι x`, injective since `dι x` is and its
  image is totally real;
  the second factor needs a frame of a complex complement, which exists
  because the base is contractible: Tau Ceti's
  `ContMDiffAlmostComplexStructure.exists_continuous_frame` and
  `exists_trivialization_baseSet_eq_univ_of_contractibleSpace` give it
  continuously, and Mathlib's smoothing with values in convex sets
  (`exists_contMDiffSection_forall_mem_convex_of_local`,
  `Geometry/Manifold/PartitionOfUnity.lean`) makes it smooth, since
  complex-linear maps with the prescribed restriction to the first
  factor and close to a given one form a convex set, and invertibility
  is open. The building issue checks this step first; if the complement
  as a vector bundle costs more than the row allows, the row splits.

- `Surround/AlmostHolomorphic.lean` (issues 14d11 and 14d12): almost
  holomorphic extension, in Euclidean spaces. For a finite type `ι'`,
  write `re z` and `im z` for the real and imaginary parts of
  `z : EuclideanSpace ℂ ι'`, as points of `EuclideanSpace ℝ ι'`, and call
  `z` real when `im z = 0`. Issue 14d13 applies these results to `V`
  through the continuous complex linear equivalence
  `EuclideanSpace.sumEquivProd.symm` of `V` with
  `EuclideanSpace ℂ (Fin k ⊕ Fin m)`, under which the real points are
  `{Im z = 0, Im w = 0}` and `‖im p‖ ≤ √(t p)`.
  - `taylorExtension N f z = ∑ j ∈ Finset.range (N + 1),
    (Complex.I ^ j / j.factorial) • iteratedFDeriv ℝ j f (re z) (fun _ ↦ im z)`
    for `f : EuclideanSpace ℝ ι' → W`, `W` a complex normed space
    (14d11), with `taylorExtension_def`, `taylorExtension_ofReal`
    (it restricts to `f` on real points), `contDiff_taylorExtension`
    (`C^r` for `f` of class `C^(r + N)`), and the formula of its defect:
    for real directions `u`,
    `conjWirtingerDeriv (taylorExtension N f) z u =
    ((2 : ℂ)⁻¹ * Complex.I ^ N / N.factorial) •
    iteratedFDeriv ℝ (N + 1) f (re z) (Fin.cons u (fun _ ↦ im z))`
    (`conjWirtingerDeriv_taylorExtension_apply_real`, for `f` of class
    `C^(N + 1)`),
    the terms of lower order cancelling in pairs, and it is
    conjugate linear. Hence `norm_conjWirtingerDeriv_taylorExtension_le`: on
    `{z | re z ∈ K}`, `K` compact, `‖∂̄ (taylorExtension N f) z‖ ≤
    C * ‖im z‖ ^ N`, and `norm_fderiv_complexAntilinearPartL_fderiv_taylorExtension_le`:
    for `f` of class `C^(N + 2)`, the same for the derivative of
    `z ↦ complexAntilinearPartL (fderiv ℝ (taylorExtension N f) z)` with
    `‖im z‖ ^ (N - 1)`, where also `‖im z‖ ≤ 1`. This is the almost analytic extension of a
    smooth function, truncated at order `N`.
  - (14d12) `exists_norm_iteratedFDeriv_le_of_norm_conjWirtingerDeriv_le`: if
    `D : EuclideanSpace ℂ ι' → W`
    is `C^(N + 1)` on a neighbourhood `U` of a compact set of real points,
    vanishes on the real points of `U`, and
    `‖∂̄ D z‖ ≤ C * ‖im z‖ ^ N` on `U`, then
    `iteratedFDeriv ℝ j D x = 0` for `j ≤ N` at those real points (the
    derivatives in the imaginary directions are those in the real ones
    turned by `i`, up to `∂̄ D`, so they vanish by induction on `j`), and
    so, by Taylor's formula,
    `‖iteratedFDeriv ℝ j D z‖ ≤ C' * ‖im z‖ ^ (N + 1 - j)` for
    `j ≤ N + 1` near them. Applied to a difference, it says that two
    maps with the same values on real points and `∂̄ = O(‖im z‖ ^ N)`
    agree to order `N + 1`; by the chain rule, composing such a map with
    a holomorphic one keeps `∂̄ = O(‖im z‖ ^ N)`.

- `Surround/Chart.lean` (issues 14d10 and 14d13): the chart along the
  disc.
  - `exists_partialDiffeomorph_modelDisc` (14d10): for `ι` smooth and
    inducing (as in 14d9)
    and an open `O ⊇ range ι`, there is
    `Φ₀ : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, E) V M ∞` with
    `range (modelDisc k m) ⊆ Φ₀.source`, `Φ₀.target ⊆ O`,
    `Φ₀ (modelDisc k m x) = ι x` and `mfderiv _ _ Φ₀ (modelDisc k m x) = A x`
    (so complex linear when `A` is) for all `x`. It is Tau Ceti's
    `SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq` with
    `i = modelDisc k m`, `g = ι` and a frame `A` with the properties
    that 14d9 gives (that of 14d9, or the adapted one of 14d18), applied on an
    open submanifold of `O` around `range ι` that is second countable
    (countably many chart domains, `range ι` being σ-compact), since that
    theorem asks for `SecondCountableTopology` and the statements above
    do not.
  - `exists_modelChart` (14d13; Proposition 5.55 for integrable `J`):
    for `ι`, `O`, `A` as above and `N : ℕ`, there is `Φ` as in 14d10 (source,
    target, `Φ ∘ modelDisc k m = ι`, `mfderiv _ _ Φ (modelDisc k m x) = A x`
    for all `x`), when `A x (Complex.I • v) = Complex.I • A x v` for all
    `x` and `v`, such that `IsHolomorphicToOrderAlongCore N Φ`, defined in
    `Surround/Chart.lean` as: every point `p₀` of
    `range (modelDisc k m)` has a neighbourhood `U ⊆ Φ.source` with
    `U ⊆ Φ ⁻¹' (chartAt E (Φ p₀)).source`
    and a constant `C` with, for `e = writtenInExtChartAt 𝓘(ℝ, V)
    𝓘(ℝ, E) p₀ Φ` (the chart of `M` at `Φ p₀`, holomorphic) and all
    `p ∈ U`, `‖∂̄e p‖ ≤ C * √(t p) ^ N` and
    `‖fderiv ℝ (fun q ↦ ∂̄e q) p‖ ≤ C * √(t p) ^ (N - 1)`. The bound is
    stated near each point of the core in one fixed chart because
    `chartAt` need not vary continuously. Proof as in *Route* above:
    the local maps `G = h⁻¹ ∘ taylorExtension N (h ∘ ofReal)`,
    `h = κ ∘ Φ₀`, agree pairwise to order `N + 1` by
    `iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le` and
    `exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero`, a smooth partition of
    unity on `V` glues them to a `G` with `G = id` on real points and
    differential the identity on the core, Tau Ceti's
    `exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt`
    (or the inverse function theorem with injectivity near a compact
    set) makes it a diffeomorphism near the core, and `Φ = Φ₀ ∘ G`.
    `√(t p)` bounds `‖im p‖`, the distance to the real points.

- `Surround/ChartLeviForm.lean` (issue 14d15) and
  `Analysis/Complex/LeviForm/CompSymm.lean` (issue 14d14): the
  comparison.
  - `TauCeti.le_re_leviForm_comp_symm` (14d14): for complex normed
    spaces `V`, `W` and every `K` there is `C` such that for
    every `e : OpenPartialHomeomorph V W`, `p ∈ e.source` with `e` `C²` at `p`
    and `e.symm` `C²` at `e p`, `‖fderiv ℝ e p‖ ≤ K`,
    `‖fderiv ℝ e.symm (e p)‖ ≤ K`, `‖fderiv ℝ (fderiv ℝ e) p‖ ≤ K`,
    every `u` `C²` at `p` and every `v`,
    `(leviForm u p v v).re - C * (‖conjWirtingerDeriv e p‖ * ‖fderiv ℝ (fderiv ℝ u) p‖ +
    (‖conjWirtingerDeriv e p‖ + ‖fderiv ℝ (conjWirtingerDeriv e) p‖) * ‖fderiv ℝ u p‖) * ‖v‖ ^ 2 ≤
    (leviForm (u ∘ e.symm) (e p) (fderiv ℝ e p v) (fderiv ℝ e p v)).re`,
    with Tau Ceti's `leviForm` (`Analysis/Complex/LeviForm/Basic.lean`).
    The proof is the computation of *Comparison*; it is the
    counterpart, for `e` not holomorphic, of Tau Ceti's
    `leviForm_comp_symm_apply_of_mem_maximalAtlas`.
  - `isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm` (14d15;
    the book's (8.1) with Theorem 4.2 (iv)): let `Φ` satisfy
    `IsHolomorphicToOrderAlongCore N Φ` for some `N`, as `exists_modelChart`
    gives it, and `c > 0`, `N₀ : ℕ` with
    `N₀ + 2 ≤ N`. There is `γ₀ ∈ Ioc 0 1` such that for every
    `γ ∈ Ioo 0 γ₀` the handle `{p | t p ≤ γ ^ 2 ∧ s p ≤ (1 + γ) ^ 2}` lies in
    `Φ.source`, and for every `u : V → ℝ` that is `C²` and, at each
    point `p` of the handle, `IsStrictlyPlurisubharmonicAt u p` with
    `c * γ ^ N₀ * max ‖fderiv ℝ (fderiv ℝ u) p‖ ‖fderiv ℝ u p‖ * ‖v‖ ^ 2 ≤
    (leviForm u p v v).re` for all `v`, the function `u ∘ Φ.symm` is
    `IsManifoldStrictlyPlurisubharmonicAt E (u ∘ Φ.symm) (Φ p)` at each
    point `p` of the handle. Strict plurisubharmonicity of `u` makes
    `D²u p ≠ 0`, so the margin is positive. The handles shrink to the
    compact `modelDisc k m '' closedBall 0 1` as `γ → 0`, so for small
    `γ` finitely many of the neighbourhoods of `exists_modelChart` cover
    them, which gives one `C` and one `K`; the error of 14d14 is then
    at most `C * γ ^ (N - 1)` times the maximum, below the margin for
    small `γ`. Read in `M`'s charts with
    `isManifoldStrictlyPlurisubharmonicAt_iff_of_mem_maximalAtlas`.
    With `u` an affine image of the `g ∘ Ψ` of
    `exists_modelSurround_margin`, this is the step of issue 14d20 that
    carries the model to `M`; the statement takes the
    margin as a hypothesis, so it does not depend on issue 14d8.

- **Interpolation and the normal form near the sphere (issues
  14d16–14d19).** Before the model of `Surround/ModelHandle.lean` is
  placed near the attaching sphere, `φ` is replaced there by the model
  level read through the chart `Φ` of 14d13. Cieliebak–Eliashberg do this
  in Steps 2–4 of their proof of Theorem 8.5: a parametrization of the
  disc (their Corollary 8.1), a comparison of 1-jets along the core, and
  their Proposition 3.26. Here the comparison holds on less than the
  core. Along the core, `modelLevel k m` has zero derivative in the
  directions `Complex.I • v` and `(0, w)` of `V`, while `φ ∘ Φ` has
  `dφ (J dι v)` and `dφ (A x (0, w))` there; `IsJOrthogonallyAttached`
  makes the first vanish on the sphere only, and nothing makes the second
  vanish. So the interpolation runs along the sphere `ι '' sphere 0 1`, a
  compact totally real submanifold of dimension `k - 1`, once the two
  1-jets agree on it: the radial derivative of `φ ∘ ι` is fixed by a
  radial reparametrization of the disc, and `dφ ∘ A x` on the second
  factor by the choice of the frame (14d18). Away from a neighbourhood of
  the sphere `θ` is `φ`, and issue 14d20 covers the rest of the disc by
  the model handle.

  *Route for Proposition 3.26.* For a cutoff `β` and `D = ψ - φ`, the
  Levi form of `θ = φ + β D` is `(1 - β) L φ + β L ψ` up to an error at
  most `|D| ‖D²β‖ + ‖Dβ‖ ‖DD‖` (times `‖v‖²`). If the 1-jets agree along
  the submanifold, then near it `|D| ≤ A ρ` and `‖DD‖ ≤ A √ρ`, with `ρ`
  the function of issue 14a, comparable to the squared distance. With
  `β = 1 - logCutoffProfile ε δ ∘ ρ` (Tau Ceti), whose first and second
  derivatives are bounded by a constant over `√ρ log (δ / ε)` and over
  `ρ log (δ / ε)` (using `‖Dρ‖ ≤ A √ρ`), both errors are bounded by a constant
  over `log (δ / ε)`, below the positivity of `L φ` and `L ψ` near the
  compact set once `ε` is small. Since `ρ` also vanishes on parts of
  `range ι` where the 1-jets differ, `β` is in fact this cutoff times a
  bump function equal to `1` near the compact set and supported where
  the 1-jets agree; the terms that its derivatives add are at most a
  constant times `δ` or `√δ` there, so `δ` is chosen small first. This
  logarithmic cutoff is the whole
  proof: it needs neither the book's Proposition 5.55 nor coordinates in
  which `J` is standard, and total reality enters only through `ρ`. The
  building issues look up the numbers of the book's lemmas in its proof
  and cite those whose steps they follow.

- `Geometry/Manifold/Riemannian/Surface/LogCutoff/SecondDeriv.lean` and
  `Analysis/Complex/LeviForm/Interpolation.lean` (issue 14d16):
  - `TauCeti.exists_abs_iteratedDeriv_two_logCutoffProfile_le` (the
    first file): there
    is an absolute constant `c₁` with
    `|iteratedDeriv 2 (logCutoffProfile ε δ) u| ≤ c₁ / (u ^ 2 * Real.log (δ / ε))`
    for `0 < 4 * ε ≤ δ` and every `u`, the second-order companion of Tau
    Ceti's `deriv_logCutoffProfile_le`; in the namespace `TauCeti`,
    since it concerns Tau Ceti's profile only.
  - `TauCeti.le_re_leviForm_add_mul_sub_apply_self` (the second file):
    on a complex normed space `V`,
    for `f g β : V → ℝ` that are `C²` at `p` and every `v`,
    `(1 - β p) * (leviForm f p v v).re + β p * (leviForm g p v v).re -
    (|g p - f p| * ‖fderiv ℝ (fderiv ℝ β) p‖ + ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖) * ‖v‖ ^ 2 ≤
    (leviForm (f + β * (g - f)) p v v).re`, from Tau Ceti's
    `leviForm_add`, `leviForm_mul_apply` and
    `ContinuousLinearMap.abs_re_leviForm_toBilinForm_apply_self_le`.
- `JConvex/Interpolation.lean` (issue 14d17):
  - `Manifold.IsSmoothEmbedding.exists_abs_comp_symm_le` (14d17):
    the Taylor bounds, at one point `y` of a real manifold. Let `ι` be a
    `C^n` embedding, `n ≥ 2`, `ρ` be `C²` at `ι y`, nonnegative near
    `ι y`, zero on `ι` near `y`, with critical Hessian at `ι y` positive
    off the tangent image (as 14a gives it), and `D : M → ℝ` be `C²` near
    `ι y` with `D (ι y') = 0` and `mvfderiv 𝓘(ℝ, E) D (ι y') = 0` for `y'`
    near `y`. For a chart `e` at `ι y` of the `C²` maximal atlas (holomorphic
    charts are among them) there is `A` such that, for `z` near
    `e (ι y)` and `x = e.symm z`, `|D x| ≤ A * ρ x`,
    `‖fderiv ℝ (D ∘ e.symm) z‖ ≤ A * √(ρ x)`,
    `‖fderiv ℝ (ρ ∘ e.symm) z‖ ≤ A * √(ρ x)` and
    `‖fderiv ℝ (fderiv ℝ (ρ ∘ e.symm)) z‖ ≤ A`. The bound of the squared
    distance to `range ι` by `ρ` comes from the critical Hessian of `ρ`,
    positive off the tangent image at `ι y`; the bounds on `D` are
    Taylor's formula at the nearest point of the image in `e`, and the
    bound on `fderiv ℝ (ρ ∘ e.symm)` is Glaeser's inequality.
  - `Manifold.IsSmoothEmbedding.exists_isManifoldStrictlyPlurisubharmonicAt_interpolate`
    (14d17; Proposition 3.26): with `[T2Space M]`, `I'` boundaryless,
    `h : IsSmoothEmbedding I' 𝓘(ℝ, E) ∞ ι`, `K : Set N` compact with the
    tangent images of `ι` at its points totally real in the weak sense,
    an open `O ⊇ ι '' K`, `φ ψ : M → ℝ` smooth on `O`, strictly
    plurisubharmonic at the points of `ι '' K`, with `φ (ι y) = ψ (ι y)`
    and `mvfderiv 𝓘(ℝ, E) φ (ι y) = mvfderiv 𝓘(ℝ, E) ψ (ι y)` for all `y`
    in a neighbourhood of `K`, and an open `U ⊇ ι '' K`: there are open
    `V ⊆ W` with `ι '' K ⊆ V` and `W ⊆ U ∩ O`, and `θ : M → ℝ` smooth on
    `O`, with `θ = ψ` on `V`, `θ =ᶠ[𝓝 x] φ` for every `x ∉ W`, `θ`
    strictly plurisubharmonic at every point of `W`,
    `min (φ x) (ψ x) ≤ θ x ≤ max (φ x) (ψ x)` for all `x`, and no
    critical point of `θ` in `W` if `mvfderiv 𝓘(ℝ, E) φ x ≠ 0` at the
    points of `ι '' K`. The proof is *Route* above, with finitely many
    charts over `ι '' K` for uniform constants; the differential of `θ`
    differs from a convex combination of those of `φ` and `ψ` by
    `D • dβ`, which is small in the same way.

- `Surround/NormalForm.lean` (issues 14d18 and 14d19), with `V`,
  `modelDisc k m` and `finrank ℂ E = k + m` as for issues 14d9–14d15.
  - `IsJOrthogonallyAttached.exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two`
    (14d18): for `φ`, `ι` smooth, `F` a finite-dimensional real inner
    product space and `h : IsJOrthogonallyAttached E φ ι`,
    there is a smooth `τ : F → ℝ`, positive, equal to `1` near `0` and
    on the sphere, such that `σ x = τ x • x` is a smooth diffeomorphism
    of `F` (`F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F`) with `‖σ x‖ < 1 ↔ ‖x‖ < 1`, and
    `mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (ι ∘ σ) x x) = -2`
    for `‖x‖ = 1`. Then `ι ∘ σ` is again a smooth embedding with the same
    image of `closedBall 0 1`, its tangent images are those of `ι`, and
    `IsJOrthogonallyAttached E φ (ι ∘ σ)`. The radial derivative of `τ`
    on the sphere is fixed by `mvfderiv_mfderiv_self_neg`, and the
    building issue keeps `‖x‖ τ x` increasing along each ray.
  - `IsJOrthogonallyAttached.exists_complexFrame_mfderiv_ker` (14d18):
    for `ι : EuclideanSpace ℝ (Fin k) → M` as in 14d9, `φ` smooth and
    `IsJOrthogonallyAttached E φ ι`, there is a frame `A` with every
    property of `exists_complexFrame_mfderiv` and
    `mvfderiv 𝓘(ℝ, E) φ (ι x) (A x (0, w)) = 0` for `‖x‖ = 1` and all `w`.
    From the frame `A` of 14d9, put
    `A' x (z, w) = A x (z - χ x • ℓ x w, w)` with
    `ℓ x w = (λ x ((modelDisc k m x).1))⁻¹ * μ x w • (modelDisc k m x).1`,
    where `λ x` and `μ x` are the complex-linear extensions
    (`StrongDual.extendRCLike`) of `z ↦ dφ (A x (z, 0))` and
    `w ↦ dφ (A x (0, w))`, and `χ : ℝᵏ → ℝ` is smooth, equal to `1` on the
    sphere and to `0` near the points where `λ x ((modelDisc k m x).1)` has
    non-negative real part. On the sphere that
    number is `dφ (dι x x) - i dφ (J dι x x)`, negative and real by
    `mvfderiv_mfderiv_self_neg` and `mvfderiv_I_smul_mfderiv`. `A' x`
    agrees with `A x` on the first factor and is `A x` composed with a
    unipotent complex-linear map, so it stays complex linear and
    invertible.
  - `IsJOrthogonallyAttached.exists_normalForm` (14d19): let `φ` be
    smooth and strictly plurisubharmonic at every point of
    `{x | φ x ≤ 0}`, `ι` a disc as in 14d9 with
    `IsJOrthogonallyAttached E φ ι`, `[T2Space M]`, `O ⊇ range ι` and
    `U ⊇ ι '' sphere 0 1` open, and `2 ≤ N`. There are `σ` as in
    `exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two`;
    `Φ` from `exists_modelChart` for `ι ∘ σ`,
    `O`, `N` and the frame of `exists_complexFrame_mfderiv_ker` for
    `ι ∘ σ`; open `V ⊆ W ⊆ U ∩ Φ.target` with `ι '' sphere 0 1 ⊆ V`; and a smooth
    `θ : M → ℝ` with `θ = modelLevel k m ∘ Φ.symm` on `V`,
    `θ =ᶠ[𝓝 x] φ` for every `x ∉ W`, `θ x` between `φ x` and
    `modelLevel k m (Φ.symm x)` on `W`, `θ` strictly plurisubharmonic at
    every point of `W ∪ {x | θ x ≤ 0}`, no critical point of `θ` in `W`,
    and `IsJOrthogonallyAttached E θ (ι ∘ σ)`. The proof:
    `modelLevel k m` is strictly plurisubharmonic with a margin of the
    form of 14d15 for `N₀ = 0` on a compact handle, so by 14d15 the
    function `modelLevel k m ∘ Φ.symm` is strictly plurisubharmonic on
    `Φ` of a handle, a neighbourhood of the sphere; so is `φ`, since the
    sphere lies in `{φ = 0}`. The 1-jets agree on the sphere: both
    values are `0` (`eq_zero`, `modelLevel_modelDisc`), and, as
    `dΦ = A x` along the core, on `A x (u, 0)` with `u` real both
    differentials are `-2 ⟪x, u⟫` (tangentially by `eq_zero`, radially by
    `σ`), on `A x (Complex.I • u, 0)` both vanish
    (`mvfderiv_I_smul_mfderiv`, `fderiv_modelLevel_apply`), and on
    `A x (0, w)` both vanish (the frame, `fderiv_modelLevel_apply`).
    `exists_isManifoldStrictlyPlurisubharmonicAt_interpolate` then
    applies to `ι ∘ σ ∘ (↑)` on `sphere (0 : EuclideanSpace ℝ (Fin k)) 1`
    with Mathlib's manifold structure, for `k = j + 1`
    (`contMDiff_coe_sphere`, `mfderiv_coe_sphere_injective`), with `K`
    the whole sphere; total reality passes to the smaller tangent
    images. For `k = 0` the sphere is empty and `θ = φ`. The attachment
    of `θ` holds because `θ ∘ ι ∘ σ` lies between two functions positive
    on the open ball, and `θ` is the model level near the sphere, where
    `isJOrthogonallyAttached_model` carries over through `Φ`.

  `θ` is not below `φ`: near the sphere the two differ at second order,
  with either sign; see *Comparison with `φ`* below.

- **The junction near the sphere (issue 14d20).** Near the sphere the
  model of 14d7 and the function `θ` of 14d19 do not fit as they stand:
  only `g ∘ Ψ` is strictly plurisubharmonic, and `θ` there is
  `modelLevel k m ∘ Φ.symm = (1 + Ψst) ∘ Φ.symm`. Let
  `G y = (g (y - 1) - g (-1)) / deriv g (-1)`, so that `G 0 = 0`,
  `deriv G 0 = 1` and `G ∘ (1 + Ψ)` is an affine image of `g ∘ Ψ`, with the
  same margin. Joining `G ∘ θ` to `θ` by a cutoff fails: the Levi-form
  error is of the order of the largest `G''`, where `θ < 0`. That `G''` is
  large: `g` comes from the lemma of `Hypersurface.lean`, with
  `C * deriv g ≤ iteratedDeriv 2 g` on the values of `Ψ` where `Ψ ≠ Ψst`.
  Near the sphere the values of `1 + Ψ` there fill `(-2 * γ - γ ^ 2, 0]`,
  and `C` grows as `γ` shrinks. So `g` can be neither independent of `γ` nor
  affine on those values. The smoothed maximum of issue 11 cannot choose
  between the two either, since `G ∘ θ ≥ θ`. And Cieliebak–Eliashberg's
  Corollary 4.3 asserts only $J$-convex levels, so `Ψ` itself is not
  plurisubharmonic there. The design follows Step 5 of the book's proof of
  Theorem 8.5 instead: the pieces are joined before any reparametrization.
  The joined function `f` is the level function `(1 + Ψ) ∘ Φ.symm` on the
  handle and `θ` farther out. Near the sphere the two agree where the
  handle ends, because `Ψ = Ψst` there. Away from the sphere both are
  positive where the handle ends, so a convex combination joins them
  without meeting `{f ≤ 0}`. A single convex `G` then makes `G ∘ f`
  strictly plurisubharmonic on `{f ≤ 0}`. On the handle this is 14d15.
  Elsewhere it holds because `θ` is strictly plurisubharmonic and `G` is
  convex and increasing (Tau Ceti's
  `IsManifoldStrictlyPlurisubharmonicAt.scalar_comp`). Outside `U`,
  `G ∘ f` is `G ∘ φ`, which is why `exists_surround` is stated with an
  `h`. No neighbourhood depends on `G`.

- `Surround/Implant.lean` (issue 14d20), with `V`, `s`, `t`,
  `modelDisc k m` and `finrank ℂ E = k + m` as for issues 14d9–14d15, and
  `H γ = {p | t p ≤ γ ^ 2 ∧ s p ≤ (1 + γ) ^ 2}` the handle of 14d8 and 14d15.
  - `IsJOrthogonallyAttached.exists_modelSurround_implant`: let `φ` be
    smooth, strictly plurisubharmonic at every point of `{x | φ x ≤ 0}`,
    with `0` a regular value; let `ι` be a disc as in 14d9 with
    `IsJOrthogonallyAttached E φ ι`; let `[T2Space M]` hold; and let `U` be
    an open set containing `ι '' closedBall 0 1`. There are:
    - `σ`, `Φ`, `V₀ ⊆ W₀` and `θ` as `exists_normalForm` gives them for
      `O = univ`, for `U` and for some `N`;
    - `γ ∈ Ioo 0 1` and `γ' ∈ Ioo γ 1` with `H γ' ⊆ Φ.source` and
      `Φ '' H γ' ⊆ U`;
    - `Ψ` and `g` as `exists_modelSurround` gives them for `a = 2` and
      `γ`;
    - a smooth `f : M → ℝ` and an `h : ℝ → ℝ` with `ContDiff ℝ ∞ h`.
    They satisfy:
    - `f =ᶠ[𝓝 x] φ` for every `x ∉ W₀ ∪ Φ '' H γ'`;
    - `f = (1 + Ψ) ∘ Φ.symm` on `Φ '' H γ`;
    - every `x` with `f x ≤ 0` has `f =ᶠ[𝓝 x] θ`, or `x ∈ Φ '' H γ` and
      `f =ᶠ[𝓝 x] (1 + Ψ) ∘ Φ.symm`;
    - `h 0 = 0`, `∀ y, 0 < deriv h y`, `∀ y, 0 ≤ iteratedDeriv 2 h y`,
      and `h ∘ f` strictly plurisubharmonic at every point of
      `{x | f x ≤ 0}` (the proof takes `h = G`);
    - `0` is a regular value of `f`;
    - `ι '' closedBall 0 1 ⊆ {x | f x < 0}`.
    `exists_surround` is then `ψ = h ∘ f`, and 14e reads `ψ` near `ι 0`
    through `Φ`, where `Ψ = e ∘ Ψst`.

    The choices are made in this order, each by the statement named:
    1. `c` and `N₀` by `exists_modelSurround_margin` for `a = 2`. They
       depend on `k` and `m` only. Then `N = N₀ + 2`.
    2. `σ`, the frame, `Φ`, `V₀`, `W₀` and `θ` by `exists_normalForm`
       for `O = univ`, `U` and `N`. None of these depends on `γ`.
    3. `γ₀` by `isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm`
       for `Φ`, `c` and `N₀`.
    4. `ε ∈ Ioo 0 γ₀` with
       `Φ '' {p | t p ≤ ε ^ 2 ∧ (1 - ε) ^ 2 ≤ s p ∧ s p ≤ (1 + ε) ^ 2} ⊆ V₀`.
       These compact sets lie in `Φ.source` and decrease, as `ε → 0`, to
       `modelDisc k m '' sphere 0 1`. Its image `ι '' sphere 0 1` lies in
       the open set `V₀`.
    5. `γ' ∈ Ioo 0 ε` with `Φ '' H γ' ⊆ U` and with `0 < φ (Φ p)` for
       `p ∈ H γ'` with `s p ≤ (1 - ε) ^ 2`. The first holds because the
       `H γ'` decrease to `modelDisc k m '' closedBall 0 1`. For the
       second, `φ ∘ ι ∘ σ` has a positive minimum on `closedBall 0 (1 - ε)`
       (`pos`), and each point of `H γ'` lies within `γ'` of a core point,
       so uniform continuity on a compact handle gives it. Then `γ ∈ Ioo 0 γ'`.
    6. `Ψ` and `g` by `exists_modelSurround_margin` for `γ`. `u = G ∘ (1 + Ψ)`
       has the margin `c * γ ^ N₀`, since dividing by `deriv g (-1) > 0`
       and adding a constant scale both sides of it alike. So by step 3,
       `u ∘ Φ.symm` is strictly plurisubharmonic at the points of
       `Φ '' H γ`.
    7. A smooth `β : V → ℝ` with values in `[0, 1]`, equal to `1` on `H γ`
       and with compact support inside `H γ'`: Mathlib's
       `exists_contDiff_support_eq_eq_one_iff` for the closed set `H γ`
       and the open set `{p | t p < γ'' ^ 2 ∧ s p < (1 + γ'') ^ 2}`,
       `γ < γ'' < γ'`,
       whose closure `H γ''` lies in `H γ'`. Then
       `f = θ + (β ∘ Φ.symm) * ((1 + Ψ) ∘ Φ.symm - θ)` on `Φ.target`, and
       `f = θ` elsewhere.

    The checks:
    - On `H γ' \ H γ` we have `Ψ = Ψst`.
    - Where moreover `(1 - ε) ^ 2 ≤ s`, the point lies in `V₀` by step 4,
      so `(1 + Ψ) ∘ Φ.symm = θ` there and `f = θ`.
    - Where `s ≤ (1 - ε) ^ 2`, `φ > 0` by step 5 and
      `modelLevel k m ≥ 1 - (1 - ε) ^ 2 > 0`. `θ` is `φ` or lies between
      the two, so `f` is a convex combination of positive numbers.
    - So `{f ≤ 0}` meets only the parts where `f` is `θ` or the level
      function of the model. Strict plurisubharmonicity then follows from
      14d19 and step 6, and the regular value from the regular value `-1`
      of `Ψ`, from 14d19 (no critical point in `W₀`) and from that of `φ`.
    - The disc lies in `Φ '' (modelDisc k m '' closedBall 0 1)`, where
      `Ψ < -1`.

  *Comparison with `φ`.* `f` is `φ` off `W₀ ∪ Φ '' H γ'`. Both sets lie in
  `U`, and `U` may be taken as small as wished. On the part of
  `Φ '' H γ'` where `s ≤ (1 - ε) ^ 2` we have `φ > 0`, so no point of
  `W = {φ ≤ 0}` is lost there. Near the sphere, `φ x ≤ 0 → f x ≤ 0` needs
  two facts that no statement gives:
  - (P1) `Ψ ≤ Ψst` on `H γ`. 14d7's construction suggests it (`Ψ = -1` on
    the cylinder `t = δ ^ 2`, `s ≤ 1`, where `Ψst > -1`), but it does not
    state it.
  - (P2) `modelLevel k m (Φ.symm x) ≤ 0` wherever `φ x ≤ 0` near the
    sphere.

  (P2) does not follow from the statements, and fails for some charts
  that they allow. Along the sphere the zero sets of `φ ∘ Φ` and of
  `modelLevel k m` are tangent. Over each point of the sphere both are
  graphs `s - 1 = q (y, w)`, up to third order, over the transverse
  directions `y` (along `Complex.I • u`, `u` tangent to the sphere) and
  `w`. For the model, `q = 2 * t`. (P2) asks that `q` for `φ ∘ Φ` be at
  least this. $J$-convexity of `∂W` bounds `q` below in the `y` directions,
  but not necessarily by the model's bound. In the `w` directions it
  gives only that `q w + q (Complex.I • w)` is positive. So `q` may be negative along some
  `w`, as it is near the origin for a boundary that is locally
  `Re z₁ = |z₂| ^ 2 + 2 * Re (z₂ ^ 2)` in `ℂ²`. A complex-linear frame
  cannot remove that term; a holomorphic change of the chart at second
  order along the core could. So
  `W ⊆ {ψ ≤ 0}` cannot be had from the statements above. What does hold
  is that `{ψ ≤ 0}` and `W` agree outside `W₀ ∪ Φ '' H γ'`, which lies in
  any given neighbourhood `U` of the disc.

  *Decision.* `exists_surround` asks neither `ψ ≤ φ`, nor `ψ ≤ h ∘ φ`,
  nor `W ⊆ {ψ ≤ 0}`. The construction gives neither of the first two: on the
  handle `ψ` is `G ∘ (1 + Ψ) ∘ Φ.symm`, and where `θ ≠ φ` near the sphere
  it differs from `h ∘ φ` at second order with either sign.
  Cieliebak–Eliashberg's Theorem 8.5 (a) does not give such a bound
  either: it fixes the function only near `∂₋W` and away from the disc.
  The third is the weaker form that the review of the design (#4863)
  suggested, and (P2) shows that the statements of 14d1–14d20 do not give
  it. Issue 19 uses `exists_surround` as stated: `{ψ ≤ 0}` agrees with `W`
  outside `U`, contains the disc in its interior, and, by issue 14e, has
  in `U ∩ {ψ ≤ 0}` no critical point other than `ι 0` and those of `φ`. If issue
  19 finds that it needs `W ⊆ {ψ ≤ 0}`, it proposes the change in an
  issue. There are two routes: state (P1) in 14d7, and correct `Φ` along
  the core at second order by a holomorphic map, so that (P2) holds.

- `Surround/Basic.lean` (issues 14d and 14e). Issue 14d proves
  `IsJOrthogonallyAttached.exists_surround`, Cieliebak–Eliashberg's
  Theorem 8.4 (§8.2) in the form of *The statements* above. The book
  deduces Theorem 8.4 from its Theorem 8.5 through Lemma 8.7 and
  Corollary 8.9. The design follows the proof of Theorem 8.5 instead,
  for one disc and the integrable `J` of this section, and states
  neither Theorem 8.5 nor its homotopies. Proposition 5.55 is issues
  14d9–14d13; Steps 2–4 of that proof (Corollary 8.1 and
  Proposition 3.26) are issues 14d16–14d19; and its Step 5, the model of
  Theorem 4.2 and Corollary 4.4 carried over by (8.1), is issues
  14d1–14d8, 14d14, 14d15 and 14d20. What is left to 14d is a short
  assembly. Its hypotheses are those of *The statements*: `φ` smooth,
  `∀ x, φ x ≤ 0 → IsManifoldStrictlyPlurisubharmonicAt E φ x`,
  `IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) φ 0`, `[FiniteDimensional ℂ E]`, and `ι`,
  `IsJOrthogonallyAttached E φ ι`, `[T2Space M]` and `U` as there.
  1. Put `k = finrank ℝ F`. Then `k ≤ finrank ℂ E`, by Tau Ceti's
     `IsTotallyReal.two_mul_finrank_le` at `0`, with the injectivity of `J` and
     of the `mfderiv` of the embedding. Write
     `finrank ℂ E = k + m`, and let `L` be the linear isometry
     equivalence `(stdOrthonormalBasis ℝ F).repr.symm` from
     `EuclideanSpace ℝ (Fin k)` onto `F`. Then `ι ∘ L` is a disc as in
     14d9: a smooth embedding, as a composite with a diffeomorphism (as
     `ι ∘ σ` in 14d18), with the same tangent images as `ι`, attached
     by `IsJOrthogonallyAttached.comp_linearIsometry`, and with the same
     image of `closedBall 0 1`, since `L` maps that ball onto the ball.
  2. `exists_modelSurround_implant` (issue 14d20) for `φ`, `ι ∘ L` and
     `U` gives `f` and `h`. Put `ψ = h ∘ f`.
  3. The checks. `ψ` is smooth, and `h` has the properties that the
     statement asks. For `x ∉ U`, `x ∉ W₀ ∪ Φ '' H γ'`, since both sets
     lie in `U` (`W₀ ⊆ U ∩ Φ.target` by 14d19, `Φ '' H γ' ⊆ U` by
     14d20); so `f =ᶠ[𝓝 x] φ` and `ψ =ᶠ[𝓝 x] h ∘ φ`. As `h` is strictly
     increasing with `h 0 = 0`, `ψ x ≤ 0 ↔ f x ≤ 0` and
     `ψ x < 0 ↔ f x < 0`, which give strict plurisubharmonicity on
     `{ψ ≤ 0}` and the disc in `{ψ < 0}` from 14d20. `0 = h 0` is a
     regular value of `ψ` by `TauCeti.IsRegularValue.scalar_comp`
     (`RegularValue/CriticalSet.lean`).
  For `F = 0` the sphere is empty; 14d19 and 14d20 cover that case, so
  the assembly needs no separate argument. Issue 14e proves
  `IsJOrthogonallyAttached.exists_surround_critical`, making the
  restriction of `ψ` to the disc a function with one critical point, at
  its centre, which the model handle function of issue 14c describes
  there. It reads `ψ` near `ι 0` through `Φ`, where `Ψ` is a
  reparametrization of `Ψst` (`exists_modelSurround`), so it repeats
  steps 1–3 with the further data that 14d20 gives.

Expected sizes: 300 lines for each of issues 14a and 14b, 400 for 14c,
the sizes of the table below for the numbered parts of 14d,
150 for 14d and 400 for 14e.

### `Geometry/Symplectic/Weinstein/Handle/`

The symplectic side of the converse: Cieliebak–Eliashberg's Morse and
Weinstein theory before Theorem 13.9.

- `Cobordism.lean` (issue 15): Weinstein cobordisms between two regular
  levels; elementary cobordisms (critical points in one level).
- `Linearization.lean`, `StableDisc.lean` and `AttachingSphere.lean`
  (issues 15c–15e, after issue 15b in
  `Analysis/ODE/LyapunovPerron/ParameterDerivative.lean`): the stable disc
  of a nondegenerate critical point is isotropic and its boundary sphere is
  an isotropic sphere in the contact lower level (from Tau Ceti's
  `Contact/Isotropic.lean`); see *Stable discs* below.
- `Model.lean` (issue 16b) and `Attachment.lean` (issues 16c and 16d):
  the standard Weinstein handle of index `k` on `ℂᵏ × ℂᵐ`, and the
  attachment of handles, stated inside one manifold; see *Handles and
  attachment* below.
- `Homotopy/` (issues 17 and 18): normal forms of Weinstein
  homotopies near a critical point and near a stable disc, and the
  removal of birth–death points; with `Weinstein/Rescale.lean`, the
  rescaling of the Liouville form. Issue 17 is its design issue; see
  *Normal forms of homotopies* below.

Expected size: 450 lines for issue 15; issues 15b–15e, 16b–16d and
18a–18g are sized by the table.

#### Stable discs

Issue 15a, the design issue of the stable discs, fixed this subsection.
Throughout, `hW : IsWeinsteinStructure ω X f`, and `p` is a critical point
with `IsManifoldNondegenerateCriticalPoint` (Tau Ceti), of index
`k = manifoldMorseIndex f p`.

**Birth–death points are left out.** At such a point the zero of `X` is not
hyperbolic and its stable set is not a disc. Handles are attached only at
nondegenerate points (issues 16b, 19 and 20; the isotopy of 16d needs no
nondegeneracy), and Weinstein homotopies pass
through birth–death points only in issue 18, which treats them by their
normal form. So every statement below assumes `p` nondegenerate, and issue
15e assumes it of every critical point in the cobordism.

**Lean form.**

- The flow of `X` is Tau Ceti's `globalFlow X _ hW.isCompleteVectorField`
  (`Geometry/Manifold/IntegralCurve/GlobalFlow.lean`), named
  `IsWeinsteinStructure.flow hW : Flow ℝ M` with `flow_apply`, so that the
  smoothness argument is not repeated. Its conformal scaling,
  $\varphi_t^*(\iota_X\omega)=e^t\,\iota_X\omega$ and
  $\varphi_t^*\omega=e^t\omega$, is Tau Ceti's (`Liouville/Scaling.lean`),
  used as it is.
- The stable disc of `p` in the cobordism between `a` and `b` is
  `hW.flow.stableSet p ∩ f ⁻¹' Icc a b`, with Tau Ceti's `Flow.stableSet`
  (`Dynamics/Flow/Stable.lean`), and its boundary sphere is
  `hW.flow.stableSet p ∩ f ⁻¹' {a}`. Neither gets a definition. The stable
  set lies in `f ⁻¹' Iic (f p)`, since `f` increases along orbits.
- Isotropic means, pointwise: for a map `γ : N → M` from any manifold,
  differentiable at `y`, with `range γ ⊆ hW.flow.stableSet p`, the forms
  `ι_X ω` and `ω` vanish on the image of `mfderiv γ y`. No predicate for
  isotropic sets is added; this form covers every `C¹` parametrization and
  needs no manifold structure on the stable set.
- For the sphere, the lower level is the boundary of the Weinstein domain
  `{x | f x ≤ a}` of `IsWeinsteinStructure.isWeinsteinDomain_scalarRegularSublevel`,
  with its contact form `fillingContactForm`. Isotropic there means Tau
  Ceti's `IsHorizontalMap` for the kernel distribution of that form, which
  `SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero` turns
  into the vanishing of a pullback of `ι_X ω`.

**The route.** Route (a): Tau Ceti already has the local stable manifold
theorem at a hyperbolic zero of a `C^n` field on a finite-dimensional
normed space, `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt`
(`Analysis/ODE/LyapunovPerron/VectorField.lean`): the confined forward
solutions start on a `C^n` graph `z ↦ z + g z` over a ball in `range P`,
and tend to the zero. The dichotomy it needs comes from
`ContinuousLinearMap.exists_projection_exponential_bounds`
(`Analysis/ODE/ExponentialDichotomy/Hyperbolic.lean`), whose hypothesis
is hyperbolicity in real form: no `v, w`, not both zero, with
`A v = -θ • w` and `A w = θ • v`. Route (b) is not taken: it would carry a
homotopy through issues 16–21, and Tau Ceti's adapted pseudo-gradients
are set on compact manifolds. Three pieces are missing:

1. The bound in time. The isotropy argument writes
   $(\iota_X\omega)(d\iota\,v)=e^{-t}(\iota_X\omega)(d(\varphi_t\circ\iota)\,v)$,
   and the same with $\omega$, and lets `t → ∞`. It needs
   `d(φ_t ∘ ι)` bounded in `t`. Tau Ceti's theorem does not state this,
   but its proof builds the solutions as Lyapunov–Perron fixed points in
   bounded continuous curves, whose derivative in the parameter
   (`fderiv_lyapunovPerronSolution_apply`) is a bounded curve; issue 15b
   exposes it.
2. Hyperbolicity and the index (issue 15c). The gradient-like inequality,
   to second order at `p`, makes $v\mapsto H(v,Av)$ positive definite, for
   `A` the linearization of `X` and `H` the Hessian of `f` in a chart. A
   rotating pair `v, w` would give $H(v,Av)+H(w,Aw)=0$, so `A` is
   hyperbolic. Along $e^{tA}v$ the form $H$ increases strictly, so it is
   negative definite on `range P` and positive definite on `ker P`, and
   `finrank (range P) = k`. The Liouville condition at the zero gives
   $\omega_p(Au,v)+\omega_p(u,Av)=\omega_p(u,v)$, so
   $F(t)=\omega_p(e^{tA}u,e^{tA}v)$ solves $F'=F$; on `range P` it tends
   to `0`, so $\omega_p$ vanishes there and $2k\le\dim M$. This gives the
   index bound without the stable manifold.
3. Globalization (issue 15d). For `x` in the stable set, some `φ_T x` lies
   in the open part of the local disc. Inside the ball of confinement, a
   point of the stable set with `f` close to `f p` cannot leave the ball:
   crossing the annulus between half the radius and the radius takes `f`
   up by a fixed amount, as `df(X)` is bounded below there and `X` above,
   while `f` stays below `f p`. So `φ_T ∘ γ` maps the points near `y`
   (continuity at `y`) into the graph, and the chain rule on
   `z = P z + g (P z)` puts its derivative at `y` in the tangent space of
   the graph.

**Lemma list.**

- Issue 15b, `Analysis/ODE/LyapunovPerron/ParameterDerivative.lean`,
  namespace `ContinuousLinearMap`, under the hypotheses of
  `exists_localStableGraph_of_contDiffAt`:
  `exists_localStableGraph_of_contDiffAt_fderiv` gives that theorem's
  `r`, `ρ` and `g` with its conclusions, with `r` at most any given
  `r₀ > 0`, and moreover a family
  `y : E → ℝ → E` such that, for `z ∈ range P ∩ closedBall 0 ρ`,
  `y z` is a confined forward integral curve of `fun _ w ↦ V (x + w)` with
  `y z 0 = z + g z`, each `fun w ↦ y w t` (`t ≥ 0`) is differentiable at
  `z`, and `∃ C, ∀ t ≥ 0, ‖fderiv ℝ (fun w ↦ y w t) z‖ ≤ C`. The family is
  the Lyapunov–Perron solution of the cut-off remainder, and the bound is
  the norm of its derivative into bounded continuous curves; the module
  docstring credits Tau Ceti's proof of
  `exists_localStableGraph_of_contDiffAt`, which it follows.
- Issue 15c, `Weinstein/Handle/Linearization.lean`, with `A` the
  `sectionLinearization` of `X` at `p` (Tau Ceti,
  `VectorBundle/Section/Linearization.lean`) and `H` the bilinear form of
  the Hessian (`hessianQuadraticForm`, by `associated_hessianQuadraticForm`)
  of `f` read in `extChartAt 𝓘(ℝ, E) p`:
  `IsGradientLike.exists_pos_mul_norm_sq_le_hessian` (in `TauCeti`, a
  `c > 0` with $c\|v\|^2\le H(v,Av)$),
  `IsGradientLike.exists_projection_exponential_bounds` (the dichotomy),
  `IsGradientLike.finrank_range_eq_manifoldMorseIndex` (for the projection
  of any such dichotomy),
  `IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace` ($\omega_p$
  vanishes on `A.stableSubspace`), and
  `IsWeinsteinStructure.two_mul_manifoldMorseIndex_le`
  (`2 * k ≤ finrank ℝ E`), with the dimension bound for isotropic
  subspaces of a nondegenerate form taken from Mathlib, Tau Ceti or the
  library. The identity for $\omega_p$ at a zero,
  `IsLiouvilleVectorField.apply_sectionLinearization_add`, is in
  `Geometry/Symplectic/Liouville/VectorField.lean`.
- Issue 15d, `Weinstein/Handle/StableDisc.lean`: `IsWeinsteinStructure.flow`
  and `flow_apply`; `IsWeinsteinStructure.apply_le_of_mem_stableSet`
  (`f ≤ f p` on the stable set); `IsWeinsteinStructure.exists_localStableDisc`
  (`Nonempty (hW.LocalStableDisc p A)`, for the structure
  `IsWeinsteinStructure.LocalStableDisc` whose fields are a map
  `ι : A.stableSubspace → M` with `ι 0 = p` and a radius `ρ > 0`, with `ι`
  smooth with injective `mfderiv` on `ball 0 ρ`, its image there in
  the stable set and containing the points of the stable set near `p` with
  `f` near `f p`, and with `φ_t (ι z)` in the source of `e` and
  `e ∘ φ_t ∘ ι` differentiable at `z`, with derivative bounded in `t ≥ 0`,
  `e` the extended chart at `p`; an idempotent `P` commuting with `A`,
  with range `A.stableSubspace` and kernel `A.unstableSubspace`, with
  `x ↦ P (e x - e p)` a left inverse of `ι` on `ball 0 ρ`; so its data
  are `ι`, `ρ` and `P`, and the corestriction `Q` of `P` to
  `A.stableSubspace` is defined from `P`); and the main results
  `IsWeinsteinStructure.interior_apply_mfderiv_eq_zero_of_range_subset_stableSet`
  and `IsWeinsteinStructure.apply_mfderiv_mfderiv_eq_zero_of_range_subset_stableSet`.
- Issue 15e, `Weinstein/Handle/AttachingSphere.lean`, for
  `IsElementaryWeinsteinCobordism ω X f a b` and `p` in the region:
  `IsWeinsteinCobordism.stableSet_inter_preimage_eq_empty` for
  `k = 0` (the stable set is `{p}`), and, for `k = m + 1`,
  `IsElementaryWeinsteinCobordism.exists_attachingSphere`, a smooth
  embedding of the unit sphere of `EuclideanSpace ℝ (Fin (m + 1))` into
  the boundary of `{x | f x ≤ a}` whose image in `M` is
  `hW.flow.stableSet p ∩ f ⁻¹' {a}`, horizontal for the contact form of
  that boundary. The sphere is first a small level of $-H$ in the local
  disc, which every orbit of the disc other than `p` crosses once and
  transversally. That disc must be smooth, as `exists_localStableDisc`
  gives it. The sphere is then carried back to the level `a`, which every
  backward orbit of the stable set reaches since the cobordism is
  elementary, at a time that Tau Ceti's `Flow.levelCrossingTime`
  (`Dynamics/Flow/LevelCrossing.lean`) gives as a continuous function and
  the implicit function theorem makes smooth. With
  `IsHorizontalMap.two_mul_finrank_add_one_le` it gives the index bound
  of issue 15c again, for `k ≥ 1`.

Sources: Cieliebak–Eliashberg [CieliebakEliashberg2012], Chapter 11, for
the stable discs and their isotropy; this design could not check the
numbers of their statements against the book, so each building issue
looks them up and cites them. The stable manifold theorem is the one that
Tau Ceti proves after Chicone and Coppel.

#### Handles and attachment

Issue 16a, the design issue of `Model.lean`, fixed this subsection. It
splits issue 16 (#3540) into 16b–16d.

**The model is not a Weinstein structure.** For `k ≥ 1` the standard
handle's function is unbounded below along its core, so it is neither
proper nor bounded below, and `IsWeinsteinStructure` fails for it. The
model is therefore stated field by field: a symplectic form, a smooth
complete Liouville field, and a Morse function for which the field is
gradient-like (`IsGradientLike`), with one critical point. No predicate
for such a "local Weinstein structure" is added. Every statement below
names the three objects, and only for `k = 0` is the model a Weinstein
structure.

**The model (issue 16b, `Handle/Model.lean`).** On
`V = EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)`, with the
coordinates `p = (x + i y, w)`, `s = |x|²` and `t = |y|² + |w|²` of issue
14c (`JConvex/Surround/Shape.lean`):

- the form is the constant form of
  `(imInnerSymplecticForm _).prod (imInnerSymplecticForm _)` (Tau Ceti's
  `Geometry/Symplectic/Complex/ImInner/Basic.lean` and
  `SymplecticForm.prod`, `Geometry/Symplectic/Prod/Basic.lean`). It gets
  no definition of its own;
- the field is the linear map `modelHandleField k m : V →L[ℝ] V`,
  $(x+iy,w)\mapsto(-x+2iy,\ w/2)$, with `modelHandleField_apply`;
- the function is 14c's `modelHandle k m a b` $=bt-as$ with `0 < a` and
  `0 < b`. The Stein side and the Weinstein side thus share one function.
  Its Morse data are already proved there (`criticalPoints_modelHandle`,
  `isMorse_modelHandle`, `manifoldMorseIndex_modelHandle`, through Tau
  Ceti's `Morse/Examples/Saddle.lean`), and `Model.lean` imports them
  rather than proving them again.

With $A$ the field, $\omega(Au,v)+\omega(u,Av)=\omega(u,v)$ holds on
each complex line of the first factor ($A=\operatorname{diag}(-1,2)$,
trace `1`) and on the second ($A=\tfrac12$). This holds for either sign
of the area form, so the conventions of *Signs and setting* raise no
question here. Also $d(bt-as)(Ap)=2as+4b|y|^2+b|w|^2$, a positive
definite quadratic form in `p`, so the field is gradient-like with a
constant `δ`. The flow is
$(x+iy,w)\mapsto(e^{-t}x+ie^{2t}y,\ e^{t/2}w)$, and the stable set of `0`
is the core `range (modelDisc k m)` (14c's `modelDisc`), on which the form
vanishes.

Lemma list: `modelHandleField_apply`, `contMDiff_modelHandleField`,
`isLiouvilleVectorField_modelHandleField` (for the constant form above, by
the identity, as `isWeinsteinStructure_constSmooth_norm_sq` does for
the radial field), `modelHandleField_flow_apply` (the explicit value of
`(modelHandleField k m).flow t p`, for Tau Ceti's linear flow
`ContinuousLinearMap.flow` of `TauCeti/Analysis/ODE/Linear.lean`, from
its `flow_apply`), `isCompleteVectorField_modelHandleField` (the curves of
that flow are integral curves), `mvfderiv_modelHandle_modelHandleField` (the
formula above), `isGradientLike_modelHandle_modelHandleField`,
`stableSubspace_modelHandleField`
(`((modelHandleField k m).stableSubspace : Set V) = range (modelDisc k m)`,
through Tau Ceti's `coe_stableSubspace` and `mem_stableSubspace`), the
isotropy
of the core, `range (modelDisc k m) ∩ modelHandle k m a b ⁻¹' {-c} =
modelDisc k m '' sphere 0 √(c / a)` for `0 < c` (the attaching sphere of
the model), and, for `k = 0`, `isWeinsteinStructure_modelHandle_zero`. That
last lemma checks the conditions one by one: the results above,
`isMorse_modelHandle`, and `b ‖p‖²` being proper and bounded below. No flow is defined
here: Tau Ceti's `ContinuousLinearMap.flow` and `stableSubspace` give
the flow of any bounded linear field and the stable set of `0`, as 15c
already uses them. Searched: neither Tau Ceti nor the library has this
hyperbolic Liouville field. Tau Ceti's linear Liouville fields are the
radial one (`Liouville/Radial/`, `isCompleteVectorField_dilation`) and
`cotangentLiouvilleField` on the linear cotangent space
(`isLiouvilleVectorField_cotangentLiouvilleField`), which is not
hyperbolic.

**The Lean form of attachment: route (b).** The converse never builds a
new manifold. Cieliebak–Eliashberg's proof of Theorem 13.9 works inside
the given Weinstein manifold, one elementary cobordism after another, and
Giroux's Section C applies issue 21 to the complement, which is also
given. So the attachment is stated in the setting of `Cobordism.lean`, as
regions of one boundaryless `M`. Route (a), a gluing by `GluedAlong`, is
not taken. It would need a Weinstein structure carried across the glued
region, a contact neighbourhood theorem for isotropic spheres and a
framing, and no statement of issues 17–21 would use the glued manifold.
A gluing construction, if a later part needs one, gets a design issue of
its own.

The statement is that the upper sublevel of a Weinstein cobordism is the
lower domain with the stable sets of its critical points attached, in
the form of an isotopy along the flow. For
`hW : IsWeinsteinCobordism ω X f a b` (any number of critical levels;
elementary cobordisms are a case), put
`K = {x | f x ≤ a} ∪ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b,
hW.isWeinsteinStructure.flow.stableSet p`.

```lean
theorem IsWeinsteinCobordism.exists_diffeomorph_image_sublevel_eq
    (hW : IsWeinsteinCobordism ω X f a b) {g : M → ℝ}
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g)
    (hgX : ∀ x, g x = 0 → 0 < mvfderiv 𝓘(ℝ, E) g x (X x))
    (hK : K ⊆ {x | g x < 0}) (hgb : ∀ x, g x ≤ 0 → f x < b) :
    ∃ τ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ τ ∧ (∀ x, 0 ≤ τ x) ∧
      (∀ x, f x ≤ a → τ x = 0) ∧
      (∀ x ∈ ⋃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b,
        hW.isWeinsteinStructure.flow.stableSet p, τ x = 0) ∧ HasCompactSupport τ ∧
      ∃ Ψ : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M,
        (∀ x, Ψ x = hW.isWeinsteinStructure.flow (τ x) x) ∧
        Ψ '' {x | g x ≤ 0} = {x | f x ≤ b}
```

So any sublevel `{g ≤ 0}` with `X` pointing out along its boundary, that
contains `K` in its interior and stays below `b`, is moved onto
`{f ≤ b}` along the orbits of `X`, without moving `{f ≤ a}` or the stable
sets in `K`. This is the
form in which issue 19 can say that the domain a surrounding produces is
the lower domain with the handles attached (the note of the review of
#6050). The proof uses `ω` only through the flow and the gradient-like
condition. Nondegeneracy of the critical points is not needed, so
birth–death points are allowed.

- **Issue 16c** (`Handle/Attachment.lean`): the orbit facts.
  (1) Under `hgX`, an orbit meets `g ⁻¹' {0}` at most once, going from
  `g < 0` to `g > 0`. This is a fact about any flow; its case `g = f`, at
  a regular level of `f`, gives `eq_levelCrossingTime_iff` (15e), and it
  comes from the library's `Geometry/Manifold/IntegralCurve/Monotone.lean`
  applied to the orbits, with no statement of its own in
  `Attachment.lean`, so that 15e does not import it.
  (2) The backward orbit of every point of `{f ≤ b}` enters `{g < 0}`:
  it reaches `{f ≤ a}`, or it stays in the compact region, where its
  limit set consists of critical points
  (`IsGradientLike.exists_flow_apply_le_or_mapClusterPt_atBot`),
  which lie in the open set `{g < 0}`.
  (3) The forward orbit of every point of `g ⁻¹' {0}` reaches
  `f ⁻¹' {b}`. Otherwise it would tend to a critical point `q`, of which
  there are finitely many in the region, and the point would lie in
  `K ⊆ {g < 0}`.
  (4) The crossing times of `g ⁻¹' {0}` and of `f ⁻¹' {b}`
  (`Flow.levelCrossingTime`) are smooth where the crossing exists,
  through the library's `contMDiffOn_flow_levelCrossingTime` as in 15e, and
  the crossing time of `f ⁻¹' {b}` from `g ⁻¹' {0}` is bounded, as
  `g ⁻¹' {0}` is compact.
- **Issue 16d** (`Handle/Attachment.lean`): the theorem. On the open set
  of points whose orbits cross `g ⁻¹' {0}`, write `x = φ_s y` with
  `y ∈ g ⁻¹' {0}`. Then put `Ψ (φ_s y) = φ_{s + T y · μ s} y`, where
  `T y` is the time from `y` to `f ⁻¹' {b}` and `μ` is a fixed smooth
  bump with these properties: it vanishes for `s ≤ -δ`, where `δ` is
  less than the time any orbit takes from `{f ≤ a}` to `g ⁻¹' {0}`; it
  increases to `1` at `0`; and it then decreases back to `0` slowly
  enough that `1 + T y · μ' s > 0`. Put `Ψ = id` elsewhere. Each orbit
  is then reparametrized by an increasing diffeomorphism, so `Ψ` is a
  bijection whose inverse is smooth by the inverse function theorem.

**The local normal form belongs to issue 17.** Cieliebak–Eliashberg also
make a Weinstein structure standard near a nondegenerate critical point
`p`: up to a Weinstein homotopy fixed away from `p`, it agrees near `p`,
through a chart `Φ` with `Φ 0 = p`, with the constant form above,
`modelHandleField k m` and `f p + modelHandle k m a b`. That is a statement
about homotopies, so issue 17 designs it with the rest of
`Handle/Homotopy/` (18d), and issue 16b gives it its target.

**The framing.** No statement of issue 16 takes a framing. Inside one
manifold the handle is already there, and its attaching sphere is the
one of 15e. A framing of the conformal symplectic normal bundle (Tau
Ceti's `Geometry/Contact/ConformalSymplecticNormal.lean`) is what tells
two attachments along the same isotropic sphere apart when the index is
below half the dimension. So it would enter only where two cobordisms
are compared, and issue 17 plans no such statement (*Normal forms of
homotopies*). In the model, at each
point of the attaching sphere the factor `ℂᵐ` lies in the contact
hyperplane, is `ω`-orthogonal to the sphere, and is symplectic. So it
represents the conformal symplectic normal space, of real rank `2m`, the
rank that `IsHorizontalMap.finrank_conformalSymplecticNormal_add`
gives ($2(k-1)+2m+1=2n-1$), and the model sphere comes with a constant
framing.

**Index zero.** The model for `k = 0` is a Weinstein structure
(`isWeinsteinStructure_modelHandle_zero`). The stable set of a minimum is the
point itself (`IsWeinsteinStructure.stableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`,
15e), so in the attachment theorem `hK` asks only that the minimum lie
in `{g < 0}`, and a new component of the sublevel is a ball around it.
No separate statement is needed.

Sources: Cieliebak–Eliashberg [CieliebakEliashberg2012], Chapters 11 and
12, for the standard handle and for Weinstein cobordisms. As in *Stable
discs*, this design could not check the numbers of their statements
against the book, so each building issue looks them up and cites them,
and records in `ERRATA.md` any error it finds. The attachment theorem is
the Weinstein form of the handle-attachment theorem of Morse theory
(Milnor, *Morse Theory*, §3).

#### Normal forms of homotopies

Issue 17, the design issue of `Handle/Homotopy/`, fixed this subsection.
It splits issue 18 (#3542) into 18a–18g.

**What the converse needs.** The statements of Cieliebak–Eliashberg's
Chapter 12 that their proof of Theorem 13.9 uses are few. Theorem 13.9
follows from the cobordism version, Theorem 13.4, by induction over
sublevels, and Theorem 13.4 from Proposition 13.12. Its proof uses
Corollary 12.13 (from Proposition 12.12: near a critical point, a
Weinstein structure can be made equal to any local one with the same
critical value and index), Proposition 12.14 (the same near a stable
disc, for a local structure that agrees with the given one on the disc),
and Lemma 12.1 (i) with Corollary 12.3 (i) (rescaling the Liouville form
by a positive function, with fixed function). Their proofs rest on
Lemmas 12.8 and 12.9 and on Proposition 9.23 (a). The other statements
of the chapter serve their Chapter 14 on flexible structures, which no
milestone of this part needs, and are not planned:

- two structures with the same function and isotopic attaching spheres
  (Lemmas 12.18 and 12.23, through the holonomy of Lemmas 12.5–12.7): the
  proof of Proposition 13.12 never compares two cobordisms, so no
  statement takes a framing either;
- creation and cancellation of pairs of critical points
  (Propositions 12.21 and 12.22, through Lemma 12.10);
- a structure adjusted to a handle decomposition: the decomposition that
  Proposition 13.12 uses is a choice of regular levels with at most one
  critical value between neighbours. It needs no homotopy: regular values
  exist in every interval (`IsGeneralizedMorse.exists_isRegularValue_mem_Ioo`),
  and `IsWeinsteinCobordism.isElementary_iff` makes each piece
  elementary. Reordering critical values (Lemma 12.20) is not used.

One statement is added that the book does not need: the library's
Weinstein structures allow birth–death points, theirs do not
(Definition 11.10). So a structure is first made Morse by a homotopy
(issue 18g); issue 20 or 21 applies it before the induction.

**Barriers.** Every homotopy below either keeps the function fixed, or
changes it only on a compact set, with values within a given `ε > 0` of
the values of `f` at the critical point `p` it is about (in 18f, on
the disc). The conclusions say which, so that every regular value of
`f` farther than `ε` from those values stays a regular value of every
`f t`: a regular barrier of the constant family `fun _ ↦ f` that
keeps that distance is one of the homotopy, and steps glue by `.trans`
at those levels, as *Decisions* asks (the note of the review of #5426).
Each statement of 18c–18g that changes the function gives this as a
conclusion, near a point in the form
`∀ c, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c → c ∉ Ioo (f p - ε) (f p + ε) →
∀ t, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (g t) c` for the family `g`; with the
function fixed, it says `∀ t, g t = f`.

**Local structures.** As for the model of 16b, a structure near a point
is stated field by field, on an open set `U : Opens M` as a manifold: a
symplectic form on `U`, a smooth Liouville field of it, gradient-like for
a function on `U` (Tau Ceti's `IsLiouvilleVectorField` and the library's
`IsGradientLike` on the manifold `U`). It is not complete and its
function is not proper, so it is not an `IsWeinsteinStructure`; no
predicate is added. That the homotopy ends at a structure equal to the
local one near `p` means that their restrictions to some open `U' ∋ p`
agree (forms pulled back by `Subtype.val`).

**Lemma list.**

- **Issue 18a** (`Weinstein/Rescale.lean`; Lemma 12.1 (i), Remark 12.2 (a),
  Corollary 12.3 (i)). For `hW : IsWeinsteinStructure ω X f` and a smooth
  `h : M → ℝ` with `0 < h` and `0 ≤ dh(X)`:
  `IsWeinsteinStructure.rescaledForm hW hh`, the form `mextDerivₗ 𝓘(ℝ, E) 1`
  of the smooth 1-form `h • ι_X ω`, with `rescaledForm_def`;
  `rescaledField X h`, the field `x ↦ (h x / (h x + dh(X x))) • X x`, with
  `rescaledField_apply`; `IsWeinsteinStructure.rescale`
  (`IsWeinsteinStructure (hW.rescaledForm hh) (rescaledField X h) f`; its
  primitive is `h • ι_X ω`: `interior_rescaledField_rescaledForm`); and
  `IsWeinsteinStructure.isWeinsteinHomotopy_rescale`, the family
  `t ↦` rescaling by `1 - t + t h`, a Weinstein homotopy from `(ω, X, f)`
  to the rescaled structure with function `f` at every time. The form is
  nondegenerate since its top power is `h ^ (n - 1) (h + dh(X))` times
  that of `ω`; pointwise, the building issue may argue on the kernel
  instead. The field is `X` times a function with values in `(0, 1]`, so
  it is complete; if neither library has that fact for a field multiplied
  by a bounded positive function, it is added with Tau Ceti's flows.
  Issue 19 uses 18a for `h = g' ∘ f` with `g'' ≥ 0`, the Liouville form of
  `W(J, g ∘ f)` near the boundary of the surrounding (Proposition 13.12,
  step 4), and again for the chain of homotopies that ends the proof of
  Theorem 13.4. Expected size: 350 lines.
- **Issue 18b** (`Handle/Homotopy/LiouvilleField.lean`; Lemma 12.9 for an
  isotropic submanifold that is a point, its steps 1 and 2). With `ω` and
  `f` fixed: if `X` and `X'` are Liouville fields of `ω` on `M` and on an
  open `U ∋ p`, both gradient-like for `f` near `p`, where `p` is a
  nondegenerate critical point of `f` or the centre of a birth–death
  chart, then there is a family `Y t` of Liouville fields of `ω`, each
  gradient-like for `f`, equal to `X` off a compact subset of `U` and at
  `t = 0`, and to `X'` near `p` at `t = 1`. So
  `IsWeinsteinHomotopy (fun _ ↦ ω) Y (fun _ ↦ f)` when `(ω, X, f)` is a
  Weinstein structure (completeness: the fields equal `X` off a compact
  set). The proof writes `X' - X` as the Hamiltonian field of a function
  `H` on a ball around `p` vanishing at `p` (by a Poincaré lemma on a
  ball; Mathlib, Tau Ceti and the library are searched for one first), and
  cuts `t H` off; the estimate $|H|\le\alpha\,r\,|df|$ holds in a Morse or
  birth–death chart, where $|df(sv)|\le|df(v)|$ for $0\le s\le1$; for
  `X'` far from `X` the book takes finitely many small steps.
  Name: `IsWeinsteinStructure.exists_isWeinsteinHomotopy_field_eq_nhds`.
  Expected size: 400 lines.
- **Issue 18c** (`Handle/Homotopy/Function.lean`; Proposition 9.23 (a), the
  Weinstein case). With `ω` and `X` fixed: if `X` is gradient-like for
  `f` and, on an open `U ∋ p`, for `f'` with `f' p = f p`, where `p` is a
  critical point of `f` and of `f'` as in 18b, then for every `ε > 0`
  there is a homotopy `f t` of functions for which `X` is gradient-like, equal to `f` off a
  compact subset of `U` and at `t = 0`, to `f'` near `p` at `t = 1`, with
  values in `Ioo (f p - ε) (f p + ε)` where it differs from `f`, and with
  no critical point there but `p`. Each `f t` is generalized Morse, so
  `(ω, X, f t)` is a Weinstein homotopy with the barriers of *Barriers*.
  Name: `IsWeinsteinStructure.exists_isWeinsteinHomotopy_function_eq_nhds`.
  Expected size: 350 lines.
- **Issue 18d** (`Handle/Homotopy/CriticalPoint.lean`; Proposition 12.12,
  hyperbolic case, and Corollary 12.13). The local normal form: for
  `hW : IsWeinsteinStructure ω X f`, `p` a nondegenerate critical point
  of `f` of index `k`, and a local structure `(ω', X', f')` on an open
  `U ∋ p` with `p` a nondegenerate critical point of `f'` of value `f p`
  and index `k`, and `ε > 0`, there is a Weinstein homotopy
  `(ω t, X t, f t)` starting at `(ω, X, f)`, equal to it off a compact
  subset of `U`, with `p` the only zero of `X t` in `U` and nondegenerate,
  ending equal to `(ω', X', f')` near `p`, with the barriers of *Barriers*;
  if `ω' = ω` on `U` then `ω t = ω`, and if `f' = f` on `U` then
  `f t = f`. The proof follows the book, with a linear step that 18b
  and 18c do not give. Darboux charts for `ω` and `ω'` at `p` (Tau Ceti's
  `IsSymplectic.exists_standardDarbouxChart`) let the local structure be
  pulled back so that `ω' = ω` is the constant form near `p` in one
  chart. There let `A` and `A'` be the linearizations of `X` and `X'` at
  `p`, and `Q` and `Q'` the Hessians of `f` and `f'`. Each of `A`, `A'`
  is a linear Liouville field of the constant form (`A - ½ I` lies in
  the symplectic Lie algebra), hyperbolic with a stable subspace of
  dimension `k` (15c's `IsGradientLike.exists_projection_exponential_bounds`
  and the isotropy of `IsLiouvilleVectorField.apply_eq_zero_of_mem_stableSubspace`),
  and the Hessian is a Lyapunov form of it (`Handle/Linearization.lean`).
  Two such fields need not have a common Lyapunov form, and 18b keeps
  the function while 18c keeps the field, so neither applies to
  `(X, f)` and `(X', f')` at once. The steps:
  1. 18b replaces `X` near `p` by its linearization `A`, both being
     gradient-like for `f` near `p`; then 18c replaces `f` by `f p + Q`,
     for which `A` is gradient-like too. At the end the same two steps,
     in the other order, go from `(A', f p + Q')` to `(X', f')`.
  2. A path `A t` from `A` to `A'` of hyperbolic linear Liouville fields
     of the constant form, each with a stable subspace of dimension `k`.
     The form `ω` pairs generalized eigenvectors of eigenvalues `λ` and
     `μ` only if `λ + μ = 1`, so the sums of the generalized eigenspaces
     of real part below `0`, above `1`, and in `(0, 1)` are isotropic,
     isotropic and symplectic, the first two paired by `ω` and both
     `ω`-orthogonal to the third. A path in `Matrix.symplecticGroup`
     (Tau Ceti's `isPathConnected_symplecticGroup`) conjugates the field
     to a block form `C ⊕ (I - Cᵀ) ⊕ (½ I + B)`, with `C` of eigenvalues
     of negative real part and `B` in the symplectic Lie algebra, of
     eigenvalues of real part in `(-½, ½)`. The segments from `C` to `-I`
     and from `B` to `0` stay among such fields and end at
     `modelHandleField k m`, so `A` and `A'` are both joined to it.
  3. Each `A t` has a Lyapunov form (Tau Ceti's
     `hasLyapunovForm_iff_forall_eq_zero_of_apply_eq_neg_smul_of_apply_eq_smul`),
     its negative index is `k`
     (`ContinuousLinearMap.sigNeg_toQuadraticMap_eq_finrank_stableSubspace`),
     and it serves all fields near `A t`
     (`HasLyapunovForm.exists_eventually_nhds`). By compactness there
     are times `0 = t₀ < … < t_N = 1` and forms `R_i` such that `R_i` is
     a Lyapunov form of `A t` for all `t` in `[t_i, t_{i+1}]`.
  4. 18c moves the function from `f p + Q` to `f p + R_0` with the field
     `A` fixed. Then for each `i`, 18b moves the field near `p` from
     `A t_i` to `A t_{i+1}` with the function `f p + R_i` fixed, and 18c
     moves the function from `f p + R_i` to `f p + R_{i+1}` with the field
     `A t_{i+1}` fixed; the last move goes to `f p + Q'`. The homotopies
     glue by `IsWeinsteinHomotopy.trans` at the barriers of *Barriers*.
  The linear steps 2 and 3 are lemmas about operators on the model
  space, stated in the same file. The target
  of 16b is the case `(ω', X', f')` = the constant form, `modelHandleField
  k m` and `f p + modelHandle k m a b` read through the chart: the
  corollary `IsWeinsteinStructure.exists_isWeinsteinHomotopy_eq_modelHandle_nhds`.
  Name of the theorem:
  `IsWeinsteinStructure.exists_isWeinsteinHomotopy_eq_nhds_of_isManifoldNondegenerateCriticalPoint`.
  Expected size: 600 lines.
- **Issue 18e** (`Handle/Homotopy/IsotropicLift.lean`; Lemma 12.8). In the
  model `ℂᵏ × ℂᵐ` with the constant form of 16b, a smooth field `Y` on
  `ℝᵏ` (the core `range (modelDisc k m)`) extends to the Liouville field
  $\hat Y(x+iy,w)=Y(x)+i\,(y-DY(x)^{T}y)+w/2$, tangent to the core and
  equal to `Y` there, so its zeros on the core are those of `Y`. Let `K`
  be a compact subset of `ℝᵏ` and `P` a positive definite symmetric form
  on `ℝᵏ` such that, at every zero $x_0$ of `Y` in `K`, the form
  $y\mapsto P(y,\,y-DY(x_0)^{T}y)$ is positive definite. Then, on a
  neighbourhood of `K` in the model, the zeros of $\hat Y$ are those of
  `Y` on the core; at each, the linearization of $\hat Y$ is block
  triangular with diagonal blocks $DY(x_0)$, $I-DY(x_0)^{T}$ and
  $\tfrac12 I$, and `P` is a Lyapunov form of the middle block, whose
  eigenvalues thus have positive real part. So the nullity and the
  dimension of the stable subspace are those of `Y` at $x_0$. If moreover
  `Y` is gradient-like for `ψ` near `K`, then $\hat Y$ is gradient-like
  for $\hat\psi=\psi(x)+P(y,y)+|w|^2$ near `K`. The hypothesis on `P` is
  needed. For `P` the standard form it says that the symmetric part of
  $DY(x_0)$ is below `I`; for `k = 2` the field `Y x = M x` with
  $M=\begin{pmatrix}1/2&3\\0&1/2\end{pmatrix}$ is gradient-like for a
  quadratic form `ψ`, yet $\psi+|y|^2+|w|^2$ decreases along $\hat Y$ at
  $y=\varepsilon(1,1)$. An eigenvalue `1` of $DY(x_0)$ gives zeros off the
  core, and an eigenvalue of real part above `1` a larger stable
  subspace. For one zero, a `P` exists exactly when the eigenvalues of
  $DY(x_0)$ have real part below `1`. For `Y = -x` and `P` the standard
  form, $\hat Y$ is `modelHandleField k m` on the first factor, which
  serves as a check. Names: `isotropicLiftField`,
  `isotropicLiftField_apply`, `isLiouvilleVectorField_isotropicLiftField`,
  `isotropicLiftField_apply_of_mem_range_modelDisc`,
  `exists_nhds_isGradientLike_isotropicLiftField`. Carried to a manifold
  by the library's isotropic neighbourhood theorem
  (`Neighborhood/Isotropic.lean`, `IsIsotropicMap.exists_symplectomorphism_opens`).
  Expected size: 400 lines.
- **Issue 18f** (`Handle/Homotopy/StableDisc.lean`; Lemma 12.9 for a disc,
  its step 3, and Proposition 12.14). For `hW : IsWeinsteinStructure ω X f`,
  `p` nondegenerate of index `k`, an embedded closed `k`-disc `Δ` in the
  stable set of `p` containing `p` (15d's `LocalStableDisc` and 15e give
  them), and a local structure on an open `U ⊇ Δ` that agrees with
  `(ω, X, f)` on `Δ` and near `∂Δ`, there is a Weinstein homotopy fixed
  off a compact subset of `U` and where the two agree, ending equal to the
  local structure near `Δ`, with `ω t = ω` if `ω' = ω` on `U`, and with
  barriers as in *Barriers*: the function changes only near `Δ`, with
  values within `ε` of `f '' Δ`, so every regular value of `f` farther
  than `ε` from `f '' Δ` stays regular. It applies 18e with `K = Δ` to
  the field `Y` that `X` induces on `Δ`, read through the isotropic
  neighbourhood theorem, and to `ψ = f` on `Δ`, and the hypothesis of
  18e holds there: the only zero of `Y` in `Δ` is `p`, a nondegenerate
  maximum of `ψ`, and $\mathrm{Hess}\,\psi(p)$ is a Lyapunov form of
  $DY(p)$, the stable part of the linearization. With
  $S=-\mathrm{Hess}\,\psi(p)$, positive definite, take for `P` the
  inverse form of `S` on the `y` coordinates: for $y=Sv$,
  $P(y,DY(p)^{T}y)=S(v,DY(p)v)<0$, so $P(y,\,y-DY(p)^{T}y)>0$.
  Name: `IsWeinsteinStructure.exists_isWeinsteinHomotopy_eq_nhds_of_subset_stableSet`.
  Issue 19 uses it in step 3 of Proposition 13.12, where the local
  structure is the one of a $J$-convex function on a neighbourhood of the
  disc. Expected size: 450 lines.
- **Issue 18g** (`Handle/Homotopy/BirthDeath.lean`): removing birth–death
  points. For `hW : IsWeinsteinStructure ω X f` there is a Weinstein
  homotopy from `(ω, X, f)` to a structure whose function is Morse
  (`IsMorse`), changing the structure only on disjoint compact
  neighbourhoods of the birth–death points (a closed discrete set, by
  `IsGeneralizedMorse.isDiscrete_criticalPoints`), each within `ε` of the
  value of its point, so with the barriers of *Barriers* for every regular
  value at distance at least `ε` from those values. Near one point, the
  normal form of Proposition 12.12 in its embryonic case brings the
  structure to the model on `ℂ × ℂᵏ × ℂᵐ` whose first factor carries the
  field `x² ∂ₓ + (1 - 2x) y ∂_y`, Liouville for the standard area form
  (its divergence is `1`), and the function `x³/3 + y²`; the family that
  adds `s x` to the function and `s` to the first component of the field
  stays Liouville and removes the critical point for `s > 0`. The
  embryonic case needs the stable half-disc of the book's Lemma 9.35, which 15d does not give; the issue begins by checking that
  the steps of 18b–18d carry over (18b and 18c already allow birth–death
  points), and is split by a design issue of its own if they do not.
  Name: `IsWeinsteinStructure.exists_isWeinsteinHomotopy_isMorse`.
  Expected size: 400 lines.

Sources: Cieliebak–Eliashberg [CieliebakEliashberg2012], Lemma 12.1 and
Remark 12.2, Corollary 12.3, Lemmas 12.8 and 12.9, Proposition 12.12 and
Corollary 12.13, Proposition 12.14, Proposition 9.23, and the proof of
Proposition 13.12, whose statement numbers this design checked against the
book. Each building issue cites them and records in `ERRATA.md` any error
it finds.

### `Geometry/Symplectic/Weinstein/SteinHandle.lean`

Issues 19 and 20: Cieliebak–Eliashberg's proof of Theorem 13.9. A
Stein function on the lower part extends across an elementary Weinstein
cobordism attached along isotropic spheres, made totally real by issue
12, by the surrounding of issues 13–14e and the smoothing of issue 11;
the Weinstein structure of the extension is homotopic to the given one by
issue 18. Issue 19 covers one critical level; issue 20 runs the induction
over an exhaustion by regular sublevels (Tau Ceti's
`IsMorse.exists_regular_sublevel_exhaustion`, adapted to generalized Morse
functions), with the condition at infinity of the homotopy.

Expected size: 500 lines each.

### `Geometry/Symplectic/Weinstein/Complement/`

Giroux's paper, for a closed integral symplectic manifold, in the
conventions of *Integral classes and line bundles* in `DESIGN.md`.

- `Liouville.lean` (issue 22): Section A, Lemma 7 and Proposition 5.
  Lemma 7 corrects a Liouville form on the complement whose behaviour
  near `Z` degenerates, so that it extends to a Liouville form on a
  compact manifold with boundary. Proposition 5: the complement of a
  symplectic hyperplane section `Z` is the interior of a Liouville domain `F`
  (`IsStrongFilling σ univ Y`), and the map of that interior onto the
  complement extends to `F → M`, sending `∂F` onto `Z` as the projection
  of the unit circle bundle of the normal bundle of `Z`.
- `DiscBundle.lean` (issue 23): Corollary 8, from Proposition 5: `M` is
  the union of the Liouville domain of Proposition 5 and a neighbourhood
  of `Z` symplectomorphic to the disc bundle of area $1/k$ in the normal
  bundle of `Z`, with the form of the connection, glued along their
  common boundary.
- `Quasiholomorphic.lean` (issue 24): quasiholomorphic sections
  (Definition 11) and Lemma 12, on the sections and estimates of
  *Asymptotically holomorphic sections*.
- `Transversality.lean` (issue 25): the derivative transversality of
  Lemma 14 and the local estimates of Lemmas 15–16.
- `Weinstein.lean` (issue 26): Proposition 13: for large `k`, the
  function $-\log|s_k|^2$ on the complement, modified near its critical
  points, is generalized Morse, and the Liouville field of the primitive
  $d^c$ of it, for the connection, is gradient-like; with the Liouville
  domain of Proposition 5 (issue 22) this gives the Weinstein domain `F`.
- `Stein.lean` (issue 27): Section C: Cieliebak–Eliashberg's theorem
  (issue 21), its version with the symplectic form fixed (Corollary 18,
  through Moser's argument and *Moser isotopy*), and the rescaling of
  Lemma 19, give the complex manifold `N`, the diffeomorphism onto the
  complement and the Stein function `φ`, with $\omega_\varphi$ the pullback
  of `ω` and no critical point near `Z`.
- `Basic.lean` (issue 28): the milestone,
  `exists_steinFunction_and_weinsteinDomain_compl`: for every large `k`,
  a degree-`k` hypersurface `Z` of part 64 with both conclusions: the
  Stein conclusion of `Stein.lean`, the Stein function with finitely many
  critical points; and a Weinstein domain `F` (`IsWeinsteinDomain`), a
  symplectomorphism of its interior onto the complement of `Z`, which
  extends continuously to `F` and maps `∂F` onto `Z` as the projection
  of the normal circle bundle (Tau Ceti's tubular neighbourhoods). Docstring
  line: "Milestone: *Stein and Weinstein complements of Donaldson
  hypersurfaces*."
- `Skeleton.lean` (issue 29): Remark 3 (Giroux's hypersurfaces are
  Hamiltonian isotopic to the zero sets of part 64, by *Hamiltonian
  flows*) and Corollary 4 (the skeleton of the Weinstein domain, the union
  of the stable manifolds of its critical points, is a finite union of
  isotropic submanifolds, and its complement is symplectomorphic to the
  disc bundle of area $1/k$ in the normal bundle of `Z`, with the form of
  the connection), which follows from the milestone and Corollary 8
  (issue 23). The page asks for both.

Expected sizes: 400 to 500 lines each; issue 26 begins with a design
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
- The library: `dC_mapCoeff_ofReal` and
  `del_delBar_mapCoeff_ofReal_ofComplexManifold`
  (`Geometry/Manifold/DifferentialForm/Dolbeault/Potential.lean`),
  `SmoothAlmostComplexStructure.IsIntegrable` and
  `isIntegrable_ofComplexManifold` (`Geometry/Manifold/Complex/Integrable.lean`).
- Tau Ceti, complex manifolds: `ofComplexManifold`,
  `toEndomorphism_ofComplexManifold`,
  `SmoothAlmostComplexStructure.covectorComplexStructure` with
  `covectorComplexStructure_apply_vec`, `SmoothForm.ofFunction`, `dC`,
  `ddbarForm`,
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
handles, Liouville structures on complements of hyperplane sections, their
standard disc-bundle neighbourhoods, and quasiholomorphic sections. None
exists. Tau Ceti has the
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
| 3 | The primitive $-df\circ J$ and the form $\omega_f$ | `Dolbeault/Potential.lean` | — | 300 |
| 4 | Stein functions, positivity and the Kähler form | `Complex/Plurisubharmonic.lean` | 3 | 350 |
| 5 | Weinstein structures and domains | `Weinstein/Basic.lean` | 1, 2 | 450 |
| 6 | The completion of a Weinstein domain | `Weinstein/Completion.lean` | 5 | 400 |
| 7 | Weinstein homotopies | `Weinstein/Homotopy.lean` | 5 | 450 |
| 8 | The Liouville field of a Stein function, made complete | `Weinstein/OfStein.lean` | 4, 5 | 400 |
| 9 | From Stein to Weinstein | `Weinstein/OfStein.lean` | 8 | 250 |
| 10 | $J$-convex hypersurfaces and their contact structure | `JConvex/Hypersurface.lean` | 4 | 400 |
| 11 | Smoothing maxima of plurisubharmonic functions | `JConvex/Smoothing.lean` | 4 | 400 |
| 12 | Plurisubharmonic squared distance to totally real submanifolds | `JConvex/TotallyReal.lean` | 10 | 400 |
| 13 | Design: $J$-convex surrounding | this file | 11, 12 | — |
| 14a | Squared distance near a compact part of a totally real embedding | `JConvex/TotallyReal.lean` | 13 | 300 |
| 14b | $J$-orthogonally attached discs | `JConvex/Surround/Attached.lean` | 13 | 300 |
| 14c | Shape functions and the model handle | `JConvex/Surround/Shape.lean` | 13 | 400 |
| 14d1 | The Levi form of an $i$-convex shape | `JConvex/Surround/ConvexShape/Basic.lean` | 14c | 400 |
| 14d2 | Sufficient conditions, shifts, rescaling and smoothed maxima of shapes | `JConvex/Surround/ConvexShape/Basic.lean`, `JConvex/Surround/ConvexShape/SmoothedMax.lean` | 14d1 | 400 |
| 14d3 | Struwe’s solutions and the shapes $S$, $Q$, $L$ | `JConvex/Surround/SpecialShape.lean` | 14d2 | 400 |
| 14d4 | The surrounding shape: Theorem 4.1 (i)–(iii) | `JConvex/Surround/SpecialShape.lean` | 14d3 | 400 |
| 14d5 | Families of special shapes | `JConvex/Surround/ShapeFamily.lean` | 14d4 | 400 |
| 14d6 | Foliations by shapes and their level functions | `JConvex/Surround/ShapeFoliation/`, `JConvex/Hypersurface.lean` | 14d2 | 400 |
| 14d7 | The model handle: Theorem 4.2 (i)–(iii), Corollaries 4.3 and 4.4 | `JConvex/Surround/ModelHandle.lean` | 14d5, 14d6 | 400 |
| 14d8 | The margin of the model handle (§4.7) | `JConvex/Surround/ModelMargin.lean` | 14d7 | 400 |
| 14d9 | Complex frames along a totally real disc | `JConvex/Surround/ComplexFrame.lean` | 14c | 300 |
| 14d10 | The first-order chart along a disc | `JConvex/Surround/Chart.lean` | 14d9 | 250 |
| 14d11 | Almost holomorphic Taylor extensions | `JConvex/Surround/AlmostHolomorphic.lean` | 13 | 350 |
| 14d12 | Maps with small $\bar\partial$ that vanish on the real points | `JConvex/Surround/AlmostHolomorphic.lean` | 14d11 | 350 |
| 14d13 | The chart of order $N$ along a disc (Proposition 5.55) | `JConvex/Surround/Chart.lean` | 14d10, 14d12 | 400 |
| 14d14 | The Levi form through a chart that is not holomorphic | `Analysis/Complex/LeviForm/CompSymm.lean` | 13 | 300 |
| 14d15 | Margins carried to the manifold by the chart | `JConvex/Surround/ChartLeviForm.lean` | 14d13, 14d14 | 300 |
| 14d16 | Logarithmic cutoffs and the Levi form of an interpolation | `Geometry/Manifold/Riemannian/Surface/LogCutoff/SecondDeriv.lean`, `Analysis/Complex/LeviForm/Interpolation.lean` | 13 | 250 |
| 14d17 | Interpolation along a totally real submanifold (Proposition 3.26) | `JConvex/Interpolation.lean` | 14a, 14d16 | 400 |
| 14d18 | Radial reparametrization and frames adapted to the attaching sphere | `JConvex/Surround/NormalForm.lean` | 14b, 14d9 | 300 |
| 14d19 | The normal form of $\varphi$ near the attaching sphere | `JConvex/Surround/NormalForm.lean` | 14d13, 14d15, 14d17, 14d18 | 300 |
| 14d20 | The model handle joined to the normal form near the attaching sphere | `JConvex/Surround/Implant.lean` | 14d8, 14d19 | 400 |
| 14d | The $J$-convex surrounding of an attached disc | `JConvex/Surround/Basic.lean` | 14d20 | 150 |
| 14e | The surrounding with one new critical point | `JConvex/Surround/Basic.lean` | 14d | 400 |
| 15 | Weinstein cobordisms and elementary cobordisms | `Handle/Cobordism.lean` | 7 | 450 |
| 15a | Design: stable discs | this file | 15 | — |
| 15b | The bounded parameter derivative of local stable solutions | `LyapunovPerron/ParameterDerivative.lean` | 15a | 250 |
| 15c | The linearization at a nondegenerate critical point; the index bound | `Handle/Linearization.lean` | 15a | 400 |
| 15d | Stable discs are isotropic | `Handle/StableDisc.lean` | 15b, 15c | 450 |
| 15e | The attaching sphere in the lower level | `Handle/AttachingSphere.lean` | 15d | 500 |
| 16a | Design: standard Weinstein handles and their attachment | this file | 15, 15e | — |
| 16b | The standard Weinstein handle | `Handle/Model.lean` | 16a | 400 |
| 16c | Orbits across a sublevel transverse to the Liouville field | `Handle/Attachment.lean` | 16a | 400 |
| 16d | The upper sublevel is the lower domain with handles attached | `Handle/Attachment.lean` | 16c | 400 |
| 16 | Standard Weinstein handles and their attachment | `Handle/Model.lean`, `Handle/Attachment.lean` | 16b, 16d | — |
| 17 | Design: normal forms of Weinstein homotopies | this file | 16 | — |
| 18a | Rescaling the Liouville form | `Weinstein/Rescale.lean` | 17 | 350 |
| 18b | Interpolating Liouville fields near a critical point | `Handle/Homotopy/LiouvilleField.lean` | 17 | 400 |
| 18c | Changing the function near a critical point | `Handle/Homotopy/Function.lean` | 17 | 350 |
| 18d | The normal form near a nondegenerate critical point | `Handle/Homotopy/CriticalPoint.lean` | 18b, 18c | 600 |
| 18e | Liouville fields extending a field on an isotropic disc | `Handle/Homotopy/IsotropicLift.lean` | 17 | 400 |
| 18f | The normal form near a stable disc | `Handle/Homotopy/StableDisc.lean` | 18b, 18c, 18e | 450 |
| 18g | Removing birth–death points | `Handle/Homotopy/BirthDeath.lean` | 18d | 400 |
| 18 | Normal forms of Weinstein homotopies | `Weinstein/Rescale.lean`, `Handle/Homotopy/` | 18a, 18d, 18f, 18g | — |
| 19 | A Stein structure across one critical level | `SteinHandle.lean` | 9, 14e, 18 | 500 |
| 20 | Stein structures on Weinstein manifolds | `SteinHandle.lean` | 19 | 500 |
| 21 | From Weinstein to Stein up to homotopy; first milestone | `Weinstein/Stein.lean` | 9, 20 | 400 |
| 22 | Giroux's Lemma 7 and Proposition 5 | `Complement/Liouville.lean` | AHS | 500 |
| 23 | Giroux's Corollary 8: the disc bundle decomposition | `Complement/DiscBundle.lean` | 22 | 450 |
| 24 | Quasiholomorphic sections | `Complement/Quasiholomorphic.lean` | AHS | 450 |
| 25 | Derivative transversality and local estimates | `Complement/Transversality.lean` | 24 | 500 |
| 26 | The Weinstein domain of the complement | `Complement/Weinstein.lean` | 6, 22, 25 | 500 |
| 27 | The Stein structure of the complement | `Complement/Stein.lean` | 21, 26 | 450 |
| 28 | Giroux's theorem; second milestone | `Complement/Basic.lean` | 27 | 300 |
| 29 | Giroux's Remark 3 and Corollary 4 | `Complement/Skeleton.lean` | 23, 28 | 500 |

Issues 1, 2 and 3 can start at once. The first milestone is proved in
issue 21 and the second in issue 28. Issues 13 and 17 are design issues:
their pull requests extend this file by the lemma lists of issues 14 and
18 and split them into issues of a few hundred lines; issue 13 has split
issue 14 (#3538) into 14a–14e. Issue 15a is a design issue too: it split
the stable discs of issue 15 into 15b–15e, and issue 16a splits issue 16
(#3540) into 16b–16d, which are its parts, and issue 17 splits issue 18
(#3542) into 18a–18g, which are its parts. Issues 22–29 wait
for the design file of *Asymptotically holomorphic sections*, which fixes
the hypersurfaces that issue 28 states its result for; issues 22 and 24
are written after it.

Credit: the statements follow Cieliebak–Eliashberg and Giroux; a building
issue that finds an error in them, or a hypothesis of dimension in
Theorem 13.9 that the page omits, records it in `ERRATA.md`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Definitions 7.4.5, 7.4.7, 7.4.8 and Remarks 7.4.6, 7.4.9.
* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.5, Definition 11.15, Remark 11.16, Theorem 1.1 and Theorem 13.9, and
  their $J$-convex surrounding theorem with the shapes of $i$-convex
  hypersurfaces it uses.
* [E. Giroux, *Remarks on Donaldson's symplectic submanifolds*][Giroux2017],
  Theorems 1 and 2, Remark 3, Corollary 4, Section A (Proposition 5, Lemma 7,
  Corollary 8), Sections B and C.
