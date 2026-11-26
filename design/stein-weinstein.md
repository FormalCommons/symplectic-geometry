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
  barriers as an existential, and the part adds `IsRegularBarrier f c`,
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
| `Geometry/Symplectic/Weinstein/OfStein.lean` | the Weinstein structure of a Stein function | 8, 9 |
| `Geometry/Symplectic/Weinstein/Stein.lean` | the converse and the first milestone | 21 |
| `Geometry/Manifold/Complex/JConvex/` | the $J$-convex toolkit of the converse | 10–14e |
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
and $|z|^2$, from Tau Ceti's `Liouville/Radial/`.

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
- `Surround/` (issue 13 designs it, issues 14a–14e build it): the
  $J$-convex surrounding of a totally real disc attached to a $J$-convex
  level, below.

Expected size: 400 lines each for issues 10–12.

### `Geometry/Manifold/Complex/JConvex/Surround/`

Cieliebak–Eliashberg's $J$-convex surrounding: a domain
$W=\{\varphi\le0\}$ with $J$-convex boundary, together with a totally real
disc $\Delta$ attached to $\partial W$ along its boundary sphere, has
arbitrarily small neighbourhoods $\{\psi\le0\}$ with $J$-convex boundary,
where $\psi$ agrees with $\varphi$ away from $\Delta$ and has one new
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

- `IsJOrthogonallyAttached.exists_surround`: there is a smooth
  `ψ : M → ℝ` with `ψ ≤ φ`, `EqOn ψ φ Uᶜ`, `ψ` strictly plurisubharmonic at
  every point of `{x | ψ x ≤ 0}`, `0` a regular value of `ψ`, and
  `ι '' closedBall 0 1 ⊆ {x | ψ x < 0}`. So `{ψ ≤ 0}` contains `W` and the
  disc in its interior, lies in `W ∪ U`, and has a $J$-convex boundary.
- `IsJOrthogonallyAttached.exists_surround_critical`: moreover, every
  critical point `x ∈ U` of `ψ` with `ψ x ≤ 0` is `ι 0` or a critical point
  of `φ` near which `ψ = φ`; `ι 0` is a nondegenerate critical point of `ψ`
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
  is the structure with fields `pos : 0 < r`, `pos_value : 0 < χ r`,
  `perp : 1 / χ r < deriv χ r / r` (the book's (4.3); it gives
  `IsConvexShapeAt.deriv_pos : 0 < deriv χ r`) and `levi : ∀ σ u : ℝ, σ ^ 2 + u ^ 2 = r ^ 2 →
  1 / χ r * (1 + deriv χ r ^ 2 * u ^ 2 / r ^ 2) < iteratedDeriv 2 χ r *
  σ ^ 2 / r ^ 2 + deriv χ r * u ^ 2 / r ^ 3 + deriv χ r ^ 3 / r` (the
  book's (4.4)). The defining function of the shape is
  `shapeGraph χ : ℝ × ℝ → ℝ`, `(s, t) ↦ χ (√t) - √s`, with
  `shapeGraph_def`.

- `Surround/ConvexShape.lean` (issues 14d1 and 14d2): $i$-convex shapes.
  - `IsConvexShapeAt.re_leviForm_pos` (14d1; the book's
    Proposition 4.8 (a), (b), Proposition 4.10 and Lemma 4.14 (a)): if
    `χ` is `C²` at `r` and `IsConvexShapeAt χ r`, then at every `p` with
    `shape p = (χ r ^ 2, r ^ 2)`, writing `F = shapeGraph χ ∘ shape`
    (which is `C²` near `p`, since `s, t > 0` there), every `v ≠ 0` with
    `fderiv ℝ F p v = 0` and `fderiv ℝ F p (Complex.I • v) = 0` has
    `0 < (leviForm F p v v).re`. The proof evaluates
    `re_leviForm_comp_shape_apply_self` on the complex tangencies; the
    book's splitting into $\Lambda^{\mathbb C}_\perp$ and
    $\Lambda^{\mathbb C}_{xy}$ is the case split of that formula
    according to the components of `v` along `x`, `y` and `w`.
  - `isConvexShapeAt_of_iteratedDeriv_two_nonpos` (14d2; Corollary
    4.11 (a)): `0 < r`, `0 < χ r`, `0 < deriv χ r`,
    `iteratedDeriv 2 χ r ≤ 0` and
    `(1 + deriv χ r ^ 2) / χ r < iteratedDeriv 2 χ r + deriv χ r ^ 3 / r`
    give `IsConvexShapeAt χ r`.
  - `IsConvexShapeAt.add_const` (14d2; Lemma 4.13 (a)), for `0 ≤ c`, and
    `IsConvexShapeAt.rescale` (Lemma 4.13 (b)): for `0 < ℓ`,
    `IsConvexShapeAt (fun r ↦ ℓ * χ (r / ℓ)) (ℓ * r)`.
  - `exists_isConvexShapeAt_eq_max` (14d2; Lemma 4.13 (d)): let `χ₁`,
    `χ₂` be `C²` with `IsConvexShapeAt` at every point of a compact
    interval `Icc r₁ r₂`, `0 < r₁`, crossing transversally there
    (`χ₁ r = χ₂ r → deriv χ₁ r ≠ deriv χ₂ r`), and let `O` be a
    neighbourhood of `{r | χ₁ r = χ₂ r}`. Then there is a `C²` (smooth if
    `χ₁`, `χ₂` are) `χ`, a convex shape at every point of `Icc r₁ r₂`,
    equal to `max (χ₁ r) (χ₂ r)` off `O`. Condition (4.3) passes to
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
  - `isConvexShapeAt_sqrt` (14d3; Lemma 4.17 (a)): for `1 < a` and
    `0 ≤ ℓ`, `r ↦ √(ℓ ^ 2 + a * r ^ 2)` is a convex shape at every
    `r > 0`; `isConvexShapeAt_quadratic` (Lemma 4.17 (b)): for `0 < ℓ`,
    `0 ≤ b`, `1 < c`, `r ↦ ℓ + b * r + c * r ^ 2 / (2 * ℓ)` at every
    `r > 0`; `isConvexShapeAt_linear` (Lemma 4.17 (e)): for `0 < ℓ`,
    `0 < d`, `r ↦ ℓ + d * r` at every `r ∈ Ioo 0 (ℓ * d ^ 3)`.
  - (14d4) The crossings of Lemma 4.18 (a)–(c), as statements about the
    real roots of the differences of these three functions, with the
    transversality that `exists_isConvexShapeAt_eq_max` asks for;
    `exists_isConvexShapeAt_eq_sqrt_of_eq_linear` (Lemma 4.19): for
    `1 < a` and `0 < γ` there are `d ∈ Ioo 0 1`, `β ∈ Ioo 0 γ` and a
    smooth `ψ`, convex shape at every `r > 0`, with
    `ψ r = √(1 + a * r ^ 2)` for `γ ≤ r` and `ψ r = 1 + d * r` for
    `r ≤ β`; Remark 4.20's admissible constants
    (`c = (1 + a) / 2`, `b = γ * (a - 1) / 16`), which §4.7 needs.
  - `exists_convexShape_surround` (14d4; Proposition 4.21, which is
    Theorem 4.1 (i)–(iii) in terms of the shape): for `1 < a` and
    `γ ∈ Ioo 0 1` there are `δ ∈ Ioo 0 γ` and `χ : ℝ → ℝ`, smooth on
    `Ioi δ` and continuous on `Ici δ`, with `IsConvexShapeAt χ r` for
    all `r > δ`, `χ r = √(1 + a * r ^ 2)` for `γ ≤ r`,
    `Tendsto (deriv χ) (𝓝[>] δ) atTop` and `1 < χ δ < 1 + γ`. The
    hypersurface of Theorem 4.1 is
    $\Sigma=\{t=\delta^2,\ \sqrt s\le\chi(\delta)\}\cup\{t>\delta^2,\ \sqrt s=\chi(\sqrt t)\}$;
    the statement records (ii) and (iii) as
    `Σ ∩ {p | γ ^ 2 ≤ t p} = {p | a * t p - s p = -1} ∩ {p | γ ^ 2 ≤ t p}`
    and `Σ ∩ {p | s p ≤ 1} = {p | t p = δ ^ 2 ∧ s p ≤ 1}`, and (i) by
    `IsConvexShapeAt.re_leviForm_pos` on the curved part and
    `leviForm_shape_snd_apply` on the cylinder `t = δ ^ 2`. The book
    joins the two parts of $\Sigma$ at $r=\delta$, $R=\chi(\delta)>1$,
    where the Struwe curve meets the line $r=\delta$ with the same
    tangent; there $r-\delta$ grows like $(R-\chi(\delta))^2$ on one side
    and vanishes on the other, so $\Sigma$ is $C^{1,1}$ and not $C^2$ at
    that corner, although the book's Theorem 4.2 (iii) makes it a level of
    a function with nonzero gradient. Issue 14d7 avoids the corner:
    its final function, `exists_modelSurround`, has `-1` as a regular
    value and agrees with `Σ` only on `{p | s p ≤ 1}` and on
    `{p | γ ^ 2 ≤ t p}`. Near the corner it bounds the intersection of
    the inside `{r < ρ₁ R}` of `Σ`, written as a graph over `R` (14d6;
    `ρ₁ = δ` for `R ≤ χ δ`), with the inside `{r < ρ₂ R}` of a second
    shape, a graph over `R` with `ρ₂ = δ` for `R ≤ 1` and `ρ₂ < δ` on
    `Ioc 1 (χ δ)`. Since the inside is the side where `Ψ < -1`, two
    insides combine by intersection (the minimum of the graphs over
    `R`, the maximum of the shapes over `r`). A `C²`-small perturbation
    of the cylinder cannot cross `ρ₁`, which leaves `δ` quadratically,
    from below; but where `|ρ₂'|` is small the criterion over `R`
    allows a curvature `ρ₂''` up to about `1 / r`, and the Struwe leaf
    has `ρ₁'' ≈ 1 / (2 * δ)`. So `ρ₂` can dip below `δ` after `R = 1`
    and bend up faster than `ρ₁`, crossing it once, transversally, at
    some `R_c > χ δ`, where `Σ` is smooth. The level `-1` is `ρ₂` before
    `R_c` and `Σ` after it, joined at `R_c` as in Lemma 4.13 (d), and
    the function there is a smoothed maximum (`smoothedMax`,
    `exists_isManifoldStrictlyPlurisubharmonicAt_glue`) of a defining
    function of the `ρ₂` shape and the foliation's `Ψ`, both smooth near
    the crossing.
    Issue 14d4 or 14d7, whichever proves the statement that meets the
    corner, records it in `ERRATA.md` with that route.

- `Surround/ShapeFamily.lean` (issue 14d5): the families of §4.6.
  `isConvexShapeAt_struweShape_two` (Lemma 4.23: for `0 < δ`, `4 ≤ d`,
  the solution on `Ioc δ (2 * δ)` with value `2 * d * δ` at `2 * δ`),
  `exists_convexShapeFamily_linear` (Lemma 4.25, bending the linear
  family `ℓ + d ℓ * r` down to `√(64 * r ^ 2 - 64 * δ ^ 2)`),
  `exists_convexShapeFamily_sqrt` (Lemma 4.26, from `8 * r` to
  `√(64 * r ^ 2 + ℓ ^ 2)`), and `exists_convexShapeFamily_surround`
  (Proposition 4.27): for `0 < γ` and all small enough `δ ∈ Ioo 0 γ`, a
  family `χ : ℝ → ℝ → ℝ`, `ℓ ∈ Icc (-8 * δ) 1`, continuous in
  `(ℓ, r)` and smooth in `r` on `Ioi δ` for each `ℓ`, with every
  `χ ℓ` increasing and a convex shape at every `r > δ`,
  `χ (-8 * δ) r = √(64 * r ^ 2 - 64 * δ ^ 2)`, `χ ℓ r` equal to the
  standard `√(64 * r ^ 2 + ℓ * |ℓ|)` for `γ ≤ r`,
  `Tendsto (deriv (χ ℓ)) (𝓝[>] δ) atTop` and `1 < χ 1 δ < 1 + γ`. The
  book's family is piecewise smooth in `ℓ`; the statement asks only
  for continuity in `ℓ`, which is what issue 14d6 uses.

- `Surround/ShapeFoliation.lean` (issue 14d6): from families of shapes
  to functions.
  - `exists_shapeFoliation` (Proposition 3.25 within shapes, Corollary
    4.29): let `χ : ℝ → ℝ → ℝ` be continuous on `Icc ℓ₀ ℓ₁ ×ˢ Icc r₁ r₂`,
    `0 < r₁`, with `χ ℓ` `C²` and a convex shape at every point of
    `Icc r₁ r₂` for each `ℓ`, `χ ℓ₀ ≤ χ ℓ ≤ χ ℓ₁`, and smooth in `(ℓ, r)`
    and strictly increasing in `ℓ` for `ℓ` near `ℓ₀` and `ℓ₁` and for
    `r` near `r₂`. Then there is a family with all these properties that
    is smooth in `(ℓ, r)` and strictly increasing in `ℓ` everywhere,
    agrees with `χ` for `ℓ` near `ℓ₀` and `ℓ₁` and `r` near `r₂`, and
    has the same values at `ℓ₀` and `ℓ₁`. The book makes the family
    monotone by maxima and then perturbs it; in one variable the maxima
    are those of `exists_isConvexShapeAt_eq_max`, and the perturbation is
    small in `C²`, under which the conditions of `IsConvexShapeAt`, strict
    inequalities on a compact set, persist.
    The shapes of `exists_convexShapeFamily_surround` have vertical
    tangents at `r = δ`, where they are not graphs over `r`; there the
    same statement is used with `r` as a function of `R`, the shapes
    being graphs over `R` near that line, and the building issue states
    that second form with the criterion of 14d1 rewritten for it.
  - `exists_contDiff_shapeLevel` (the function of a foliation): a family
    as above defines, by the implicit function theorem (Mathlib's
    `HasStrictFDerivAt.implicitFunction`), a smooth `H : ℝ × ℝ → ℝ` on
    the region it sweeps out, with `H (χ ℓ r ^ 2, r ^ 2) = -ℓ`,
    `∂H/∂t > 0` and `∂H/∂s < 0` there (the leaves rise with `ℓ`, so
    `H` falls as `s` grows and rises as `t` grows); `dH` is then a
    positive multiple of the differential of `shapeGraph (χ ℓ) ∘ shape`,
    and every level of `H ∘ shape` is $i$-convex by
    `IsConvexShapeAt.re_leviForm_pos` and
    `forall_re_manifoldLeviForm_pos_iff_of_mvfderiv_eq_smul`.
  - In `JConvex/Hypersurface.lean`:
    `exists_isManifoldStrictlyPlurisubharmonicAt_comp_of_isCompact`
    (the book's Lemma 2.7, on a compact set): let `f : M → ℝ` be `C²`
    on an open `U`, `K ⊆ U` compact, `mvfderiv 𝓘(ℝ, E) f x ≠ 0` for
    `x ∈ K`, and the Levi form of `f` positive on the nonzero `v` with
    `df(v) = df(i v) = 0` at each `x ∈ K`. Then there is `C ≥ 0` such
    that `g ∘ f` is strictly plurisubharmonic at every point of `K`
    for each `C²` function `g` with `0 < deriv g` and
    `C * deriv g ≤ iteratedDeriv 2 g` on `f '' K`. This is a
    statement about $J$-convex levels and belongs with them.

- `Surround/ModelHandle.lean` (issue 14d7): Theorems 4.2 (i)–(iii),
  Corollary 4.3 and Corollary 4.4 for `J = i`, with `1 < a`,
  `γ ∈ Ioo 0 1` and `Ψst = modelHandle k m 1 a`.
  - `exists_modelHandle_exterior` (Theorem 4.2 (i)–(iii)): there are
    `δ ∈ Ioo 0 γ` and a shape `χ` with the properties that
    `exists_convexShape_surround` gives, so that `Σ` is a hypersurface
    as in Theorem 4.1, and on
    `Ωext = {p | δ ^ 2 ≤ t p ∧ √(s p) ≤ χ (√(t p))}` there is a
    continuous `Ψ = H ∘ shape`, with `Ψ = Ψst` on
    `Ωext ∩ {p | γ ^ 2 ≤ t p}`, `Ψ = -1` on the curved part
    `{p | δ ^ 2 ≤ t p ∧ √(s p) = χ (√(t p))}` of `Σ`, and an `ε > 0`
    with `-1 + ε ≤ Ψ` on `Ωext ∩ {p | s p ≤ 1}`; and on
    `Ωext ∩ {p | δ ^ 2 < t p}` only, `Ψ` is smooth with `∂H/∂t > 0` and
    `∂H/∂s ≤ 0`, and `g ∘ Ψ` is strictly plurisubharmonic on
    `Ωext ∩ {p | δ ^ 2 < t p} ∩ K` for each compact `K` and a `g` as in
    the lemma of `Hypersurface.lean`. At the cylinder `Ψ` is not `C¹`:
    each leaf meets it tangentially, at a height that varies with the
    leaf, so `Ψ` grows like `√(t - δ ^ 2)` across the leaves
    (`r - δ ≈ (R - χ ℓ δ) ^ 2 / (4 * δ)`) and `∂H/∂t` tends to `+∞`.
    Below the leaf `χ (-8 * δ)`, which the family does not sweep, `Ψ` is
    `64 * t - s`, the value on the standard leaves
    `s = 64 * t + ℓ * |ℓ|` with `ℓ < -8 * δ` (whose foliation level is
    `√(64 * t - s)`), continued by the interpolation towards `Ψst`.
    `Ψ` is not `-1` on the cylinder part of `Σ`: every leaf of the
    family has its vertical tangent at `r = δ`, and their heights `χ ℓ δ` fill
    `Icc 0 (χ 1 δ)`, so each point of the cylinder below the corner lies
    on a leaf `ℓ < 1`, where `Ψ > -1`. The points with `t = δ ^ 2` and
    `s = 1` lie on a leaf `ℓ₁ < 1`, and since the leaves increase in `r`,
    the points of `Ωext` with `s ≤ 1` lie on or below it, which gives
    `ε`. The proof is
    the book's: the shapes of `exists_convexShapeFamily_surround` (with
    a smaller `γ'` for `γ`) continued by the levels of the separable
    interpolation above, which replaces Proposition 3.26, and
    `exists_shapeFoliation` for Proposition 3.25; so `χ` is the shape
    `χ 1` of that family, continued, and not the one of
    `exists_convexShape_surround`.
  - `exists_modelHandle_collar` (Corollary 4.3, with the collar given by
    a function of `t`): for small `σ > 0`, the `Ψ` above extends, with
    the same properties, to an open `Ω`
    containing `Ωext` minus the cylinder `{p | t p = δ ^ 2}`, with values
    in `Ioi (-1 - σ)`; and there is a smooth `h : ℝ → ℝ` with
    `0 < deriv h`, `h (δ ^ 2) = -1` and `g ∘ h ∘ t` strictly
    plurisubharmonic where `0 < t`. The book's collar `f (Ψ p) = √(t p)`
    on `{p | t p ≤ δ ^ 2 ∧ s p ≤ 1}` is false for the `Ψ` of the
    foliation, which is not constant on the cylinder; `h ∘ t` takes its
    place there.
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
    a smooth increasing `e` (target equivalent, the book's (iii)). Its
    `Ψ` is `h ∘ t` on `{p | s p ≤ 1}` near the cylinder and the `Ψ` of
    `exists_modelHandle_collar` away from it; the margin `ε` keeps the
    latter above `-1` on `{p | s p ≤ 1}`, so the level `-1` there is the
    cylinder. Near the corner circle the level `-1` leaves the cylinder
    for the second shape `ρ₂` of issue 14d4's paragraph on the corner,
    which crosses `Σ` transversally where both functions are smooth, and
    the two are joined there as that paragraph says. The
    homotopy `Ψ_t` of the book's Corollary 4.4 is not stated: the
    statements of issues 14d and 14e need only its end, and the book's
    homotopy serves its Theorem 8.5, which the design does not state.
    This is the model that issue 14d implants: with `a = 2`,
    `1 + Ψ` agrees with `modelLevel k m` where `Ψ = Ψst`.

- `Surround/ModelMargin.lean` (issue 14d8): the margin of §4.7 that the
  move onto a manifold (#5489) needs. With the normalized modulus of the
  book's (3.10), the statement is
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
  existential, since #5489 needs only a fixed power of `γ` and chooses
  the order of its chart after it.

- `Surround/Basic.lean` (issues 14d and 14e): issue 14d proves
  `IsJOrthogonallyAttached.exists_surround`, following
  Cieliebak–Eliashberg's proof: along the disc, away from the sphere,
  `ψ` is built from `φ` and the function `ρ` of issue 14a, which is
  strictly plurisubharmonic near the disc and vanishes on it; near the
  sphere, $J$-orthogonality lets the shapes of issue 14c, read in
  coordinates along $\partial\Delta$, replace the corner where $\{\varphi\le0\}$
  and a thin neighbourhood of the disc meet; the pieces are glued by
  `exists_isManifoldStrictlyPlurisubharmonicAt_glue` (issue 11). Issue 14e
  proves `IsJOrthogonallyAttached.exists_surround_critical`, making the
  restriction of `ψ` to the disc a function with one critical point, at its
  centre, which the model handle function of issue 14c describes there. If
  issue 14d does not fit in 500 lines, it begins by extending this section
  with its lemma list. Issue 14d cites the theorem it follows by number.

Expected sizes: 300 lines for each of issues 14a and 14b, 400 for 14c
and for each of issues 14d1–14d8,
500 for 14d and 400 for 14e.

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
| 14d1 | The Levi form of an $i$-convex shape | `JConvex/Surround/ConvexShape.lean` | 14c | 400 |
| 14d2 | Sufficient conditions, shifts, rescaling and smoothed maxima of shapes | `JConvex/Surround/ConvexShape.lean` | 14d1 | 400 |
| 14d3 | Struwe’s solutions and the shapes $S$, $Q$, $L$ | `JConvex/Surround/SpecialShape.lean` | 14d2 | 400 |
| 14d4 | The surrounding shape: Theorem 4.1 (i)–(iii) | `JConvex/Surround/SpecialShape.lean` | 14d3 | 400 |
| 14d5 | Families of special shapes | `JConvex/Surround/ShapeFamily.lean` | 14d4 | 400 |
| 14d6 | Foliations by shapes and their level functions | `JConvex/Surround/ShapeFoliation.lean`, `JConvex/Hypersurface.lean` | 14d2 | 400 |
| 14d7 | The model handle: Theorem 4.2 (i)–(iii), Corollaries 4.3 and 4.4 | `JConvex/Surround/ModelHandle.lean` | 14d5, 14d6 | 400 |
| 14d8 | The margin of the model handle (§4.7) | `JConvex/Surround/ModelMargin.lean` | 14d7 | 400 |
| 14d | The $J$-convex surrounding of an attached disc | `JConvex/Surround/Basic.lean` | 14a, 14b, 14c | 500 |
| 14e | The surrounding with one new critical point | `JConvex/Surround/Basic.lean` | 14d | 400 |
| 15 | Weinstein cobordisms and stable discs | `Handle/Cobordism.lean` | 7 | 450 |
| 16 | Standard Weinstein handles and their attachment | `Handle/Model.lean` | 15 | 450 |
| 17 | Design: normal forms of Weinstein homotopies | this file | 16 | — |
| 18 | Normal forms of Weinstein homotopies | `Handle/Homotopy.lean` | 17 | by 17 |
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
issue 14 (#3538) into 14a–14e. Issues 22–29 wait
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
