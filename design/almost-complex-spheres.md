# Almost complex spheres

This is the detailed design of part 60 of `DESIGN.md`, *Almost complex
spheres*. It proves that the sphere $S^{2n}$ carries no almost complex
structure when $n=2$ or $n\ge4$, McDuff–Salamon [McDuffSalamon2017],
Exercise 4.1.9. The part has no milestone of its own: its theorem is the
input of *Symplectic sums*' `Pointwise.lean`, for *Pointwise connected-sum
obstruction for symplectic forms*. For $n=0$ the statement is false
($S^0$ is two points, and a zero-dimensional tangent space carries the
zero complex structure), so it is stated for $n\ne0$, besides $n\ne1,3$.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Every
merged declaration named below was checked against the library at
`dc5de482` and Tau Ceti `0651fdbae946`.

## Setting and notation

- **The sphere.** $S^{m}$ is Mathlib's `sphere (0 : E) 1` for a real inner
  product space `E` with `[Fact (finrank ℝ E = m + 1)]`, a manifold over
  `𝓡 m`, as in Tau Ceti's `Geometry/Manifold/Instances/Sphere.lean`. Its
  tangent bundle is `TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type`, with
  model `EuclideanSpace ℝ (Fin m)`.
- **Complex structures on the tangent bundle.** The theorems are stated
  for Tau Ceti's `TauCeti.Bundle.ContinuousComplexStructure` on the
  tangent bundle (`Topology/VectorBundle/Complex/Structure.lean`), a
  continuous $J$ with $J^2=-1$, and its complex vector bundle `J.Fiber`.
  A smooth almost complex structure, Tau Ceti's
  `TauCeti.SmoothAlmostComplexStructure (𝓡 (2 * n)) (sphere (0 : E) 1)`,
  gives one through the library's
  `Bundle.ContMDiffComplexStructure.tangentEquiv` and
  `toContinuousComplexStructure`
  (`Geometry/Manifold/VectorBundle/ComplexStructure.lean`). So the
  topological statement is the general one, and the smooth one, which
  *Symplectic sums* uses, is its corollary.
- **Chern classes** are *Chern classes*' `Bundle.chernClass G E k` and
  `Bundle.totalChernClass G E`, in Tau Ceti's `TopCat.integralCohomology`
  and the even integral cohomology ring `TopCat.EvenIntegralCohomology`
  (`design/chern-classes.md`). They need fibres `E : B → Type` over
  `B : Type`; every bundle of this part lives in `Type`.
- **Evaluation.** For an orientation `o` of the sphere, classes of degree
  $2n$ are evaluated on the fundamental class by Tau Ceti's
  `TauCeti.HomologicalOrientation.evalFundamentalClass`, through
  `Manifold.Orientation.toHomologicalOrientation`, as in the merged
  `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`
  (`Geometry/Manifold/Orientation/EulerCharacteristic.lean`). No statement
  depends on which orientation: the one used is that of `J`
  (`TauCeti.Bundle.ContinuousComplexStructure` orients the bundle through
  `Topology/VectorBundle/Complex/Orientation.lean`).
- **The projective line.** In the K-theory files $S^2$ is
  $\mathbb CP^1$, `ℙ ℂ (Fin 2 → ℂ)`, so that the line bundle $H$ of Bott
  periodicity is the library's tautological line
  `Projectivization.Tautological ℂ (Fin 2 → ℂ)`, whose first Chern class
  is minus the generator `Projectivization.hyperplaneClass` (the merged
  `complexEulerClass_twistCore_neg_one` and
  `chernClass_one_eq_complexEulerClass`).

## Decisions

### The route for $S^{4k}$: the complexified tangent bundle

Let $T=TS^{4k}$ with a complex structure $J$, and $T_J$ its complex
bundle, of rank $2k$.

1. $T\oplus\underline{\mathbb R}\cong\underline{E}$ over the sphere, by
   $(v,t)\mapsto d\iota(v)+t\,x$ at $x$, with Tau Ceti's
   `TauCeti.sphereTangentEquiv` (the derivative of the inclusion is an
   isometry of $T_xS^m$ onto $x^\perp$).
2. Complexification commutes with sums and takes trivial bundles to
   trivial ones, so $T_{\mathbb C}\oplus\underline{\mathbb C}$ is
   trivial; by the Whitney formula `totalChernClass_prod` and
   `totalChernClass_trivial`, $c(T_{\mathbb C})=1$. The complexification
   is Tau Ceti's bundle `fun x ↦ ℂ ⊗[ℝ] T x`
   (`Topology/VectorBundle/Complexification.lean`).
3. For a complex structure, $\mathbb C\otimes_{\mathbb R}T\cong
   T_J\oplus\overline{T_J}$, complex-linearly, by
   $z\otimes v\mapsto(zv,\bar zv)$, where $\overline{T_J}$ is Tau Ceti's
   `TauCeti.ConjugateBundle` (`Topology/VectorBundle/Conjugate.lean`).
4. Since $H^{j}(S^{4k};\mathbb Z)=0$ for $0<j<4k$ (Tau Ceti's
   `TopCat.isZero_singularCohomology_topCatSphere_of_ne`, through the
   homeomorphism of `Geometry/Manifold/Instances/TopCatSphere.lean`),
   the Whitney formula in degree $4k$ (`chernClass_prod`) leaves
   $c_{2k}(T_{\mathbb C})=c_{2k}(T_J)+c_{2k}(\overline{T_J})$. Both are top
   classes, so Euler classes (`chernClass_finrank_eq_complexEulerClass`),
   and Tau Ceti's `TauCeti.complexEulerClass_conjugateBundle` gives
   $e(\overline{T_J})=(-1)^{2k}e(T_J)=e(T_J)$. Hence $2e(T_J)=0$.
5. But $\langle e(T_J),[S^{4k}]\rangle=\chi(S^{4k})=2$, by
   `evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType` and Tau Ceti's
   `TauCeti.eulerChar_sphere`, after identifying the complex Euler class
   with the real one of the oriented tangent bundle, as Tau Ceti's
   `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass` does for complex
   manifolds. So $\langle 2e(T_J),[S^{4k}]\rangle=4\ne0$: a contradiction,
   with no need to know that $H^{4k}(S^{4k};\mathbb Z)$ is torsion free.

No Pontryagin class is defined: the argument uses only Chern classes of
$T_{\mathbb C}$, which is what Pontryagin classes would be built from.
Chern classes of conjugate bundles in general degrees are not needed
either, since on $S^{4k}$ only the top class survives.

### The route for $S^{4k+2}$, $k\ge2$: Bott integrality

The design chooses Bott's integrality theorem, through the surjective
half of the Bott periodicity theorem, as in Hatcher [Hatcher2017], §2.1
and Chapter 4, and not Borel–Serre's argument with Steenrod reduced powers.
The reasons:

- Borel–Serre need the mod $p$ reduced powers $P^i$ on singular
  cohomology, with naturality, the Cartan formula and $P^1x=x^p$ in
  degree two. Neither library has them (Tau Ceti has only the cup square
  of a degree-one class mod two, `Cohomology/Cup/SquareModTwo.lean`), and
  their construction (by equivariant cochains on $X^p$) shares nothing
  with what the library has.
- The K-theory route uses what the libraries have: the Chern classes and
  their Whitney formula, tensor products of line bundles
  (`chernClass_one_tensorProduct`), Tau Ceti's homotopy invariance of
  bundles (`TauCeti.exists_continuousLinearEquiv_cylinder`,
  `Topology/VectorBundle/HomotopyInvariance.lean`), Tau Ceti's Newton
  polynomials (`TauCeti.newtonMvPolynomial`, with the identity
  `TauCeti.X_mul_derivative_chernSeries`), and Tau Ceti's bundle cores
  `TauCeti.FiniteRankBundleCore` with their split Grothendieck ring
  `TauCeti.SplitK0`.
- Only the surjectivity of $K(X)\otimes K(S^2)\to K(X\times S^2)$ is
  needed, not its injectivity: this is the shorter half of Hatcher's proof
  (clutching, Laurent and linear clutching functions, and the splitting of
  a linear one).

The statement proved is: for a complex vector bundle $V$ of any rank over
$S^{2m}$, $m\ge1$, and any orientation,
$(m-1)!\mid\langle c_m(V),[S^{2m}]\rangle$. For $V=T_J$ the left side is
$\chi(S^{2m})=2$ (as in step 5 above), so $m\le3$. This also excludes
$S^{4k}$ for $k\ge2$, but the route above is kept for all $k$, since it is
much shorter and $S^4$ needs it.

The proof of integrality:

1. **Newton classes.** $s_j(V)$ is $s_j$ of Newton's power sums evaluated
   at the Chern classes of $V$ (Tau Ceti's `TauCeti.newtonMvPolynomial`),
   so that $s_j(V)=\sum x_i^j$ for Chern roots. It is additive,
   $s_j(V\oplus W)=s_j(V)+s_j(W)$ over a compact base: from the Whitney
   formula, since the generating series of the $s_j$ is the logarithmic
   derivative of the total Chern class (`X_mul_derivative_chernSeries`),
   and a logarithmic derivative turns products into sums. It vanishes on
   trivial bundles for $j\ge1$, is natural and iso-invariant, and is
   $c_1(L)^j$ on a line bundle. If every cup product of two classes of
   positive even degree with sum $2j$ vanishes (as on $S^{2m}$ for $j=m$),
   then $s_j=(-1)^{j-1}j\,c_j$, by Newton's identity
   (the coefficient of $t^j$ in `X_mul_derivative_chernSeries`).
2. **K-theory.** $K(X)$ is the split Grothendieck group of the category
   of complex bundle cores over $X$, whose biproduct is the Whitney sum.
   Every additive, iso-invariant invariant factors through it; so $s_j$
   becomes a homomorphism $K(X)\to H^{2j}(X;\mathbb Z)$ for compact $X$.
3. **The product theorem, surjective half.** For compact Hausdorff $X$,
   $K(X\times\mathbb CP^1)$ is generated by the classes $[p^*A]$ and
   $[p^*A\otimes q^*H]$ for bundles $A$ over $X$ [Hatcher2017, §2.1,
   proof of Theorem 2.2, the surjectivity]. By induction over the factors,
   $K((\mathbb CP^1)^m)$ is generated by the classes of the line bundles
   $L_T=\bigotimes_{i\in T}\mathrm{pr}_i^*H$, for $T\subseteq\{1,\dots,m\}$.
4. **Computation on $(\mathbb CP^1)^m$.** With $y_i=c_1(\mathrm{pr}_i^*H)$,
   $y_i^2=\mathrm{pr}_i^*(y^2)=0$ since $H^4(\mathbb CP^1)=0$, so
   $s_m(L_T)=(\sum_{i\in T}y_i)^m$ is $m!\,y_1\cdots y_m$ for
   $T=\{1,\dots,m\}$ and $0$ otherwise. Hence $s_m$ of every bundle over
   $(\mathbb CP^1)^m$ is an integer multiple of $m!\,y_1\cdots y_m$.
5. **Back to the sphere.** A collapse map
   $\kappa:(\mathbb CP^1)^m\to S^{2m}$ (through the smash product, built
   from $\mathbb CP^1\cong S^2$ and the collapse $S^a\times S^b\to
   S^{a+b}$) satisfies $\kappa^*u=\pm\langle u,[S^{2m}]\rangle\,y_1\cdots
   y_m$ for every $u\in H^{2m}(S^{2m};\mathbb Z)$, with a sign that does
   not depend on $u$, and $y_1\cdots y_m$ has infinite order. With step 1
   on $S^{2m}$, $\kappa^*s_m(V)=(-1)^{m-1}m\,\kappa^*c_m(V)$, and step 4
   gives $m\langle c_m(V),[S^{2m}]\rangle\in m!\,\mathbb Z$.

### Files and the folder of the sphere

`DESIGN.md` put the theorem in
`Geometry/Manifold/Instances/Sphere/AlmostComplex.lean`.
That would make `Instances/Sphere.lean` a sibling of a folder
`Instances/Sphere/`, which `AGENTS.md` forbids, and so a move of
`Instances/Sphere.lean` to `Instances/Sphere/Basic.lean` with every import
of it. The theorem is about almost complex structures, so it goes beside
the library's other files on them instead:
`Geometry/Symplectic/Manifold/AlmostComplex/Sphere.lean`. No file moves.
`DESIGN.md` is corrected to name this file.

## Files

### `Topology/VectorBundle/Complex/ChernClass/Newton.lean`

- `Bundle.newtonClass G E j : (TopCat.of B).integralCohomology (2 * j)`,
  the degree-$2j$ component of `MvPolynomial.aeval` of
  `TauCeti.newtonMvPolynomial ℤ (finrank ℂ G) j` at the Chern classes
  $c_1,\dots,c_n$ in `EvenIntegralCohomology`, with `newtonClass_def`.
- `newtonClass_zero` (the rank), `newtonClass_pullback`,
  `newtonClass_congr` (as `chernClass_congr`), `newtonClass_trivial`
  ($0$ for $j\ne0$), `newtonClass_of_finrank_eq_one` ($c_1^j$, as a power
  in `EvenIntegralCohomology`).
- `newtonClass_prod`: over a compact base,
  $s_j(E_1\oplus E_2)=s_j(E_1)+s_j(E_2)$, from `chernClass_prod` and
  `TauCeti.X_mul_derivative_chernSeries`.
- `newtonClass_eq_of_cup_eq_zero`: if $j\ge1$ and every cup product of
  classes of degrees $2a,2b>0$ with $a+b=j$ vanishes, then
  $s_j(E)=(-1)^{j-1}j\,c_j(E)$.

### `Topology/VectorBundle/Complexification/Basic.lean`

The complexification of real bundles as a functor on what the part uses,
for finite-dimensional models, with Tau Ceti's instances of
`Topology/VectorBundle/Complexification.lean` (scope
`TauCeti.Complexification`):

- `complexificationProdHomeomorph`: the complexification of `E₁ ×ᵇ E₂`
  is the direct sum of the complexifications, by a homeomorphism of total
  spaces that is complex-linear on each fibre.
- `complexificationTrivialHomeomorph`: the complexification of
  `Bundle.Trivial B F` is `Bundle.Trivial B (Complexification F)`.
- `complexificationMapHomeomorph`: a homeomorphism of total spaces that is
  real-linear on fibres complexifies to one that is complex-linear.
- `Bundle.totalChernClass_complexification_eq_one`: over a compact base,
  if $E\oplus\underline{\mathbb R}^r$ is trivial, then
  $c(E_{\mathbb C})=1$.

### `Topology/VectorBundle/Complexification/ComplexStructure.lean`

For `J : TauCeti.Bundle.ContinuousComplexStructure F V`:
`TauCeti.Bundle.ContinuousComplexStructure.complexificationHomeomorph`,
the homeomorphism from the complexification of `V` to
`J.Fiber ×ᵇ TauCeti.ConjugateBundle J.Fiber`, $z\otimes v\mapsto
(zv,\bar zv)$, complex-linear on each fibre, with its value on pure
tensors (`complexificationHomeomorph_tmul`).

### `Geometry/Manifold/VectorBundle/Tangent/Sphere.lean`

- `sphereTangentProdHomeomorph`: the homeomorphism from the total space of
  `TangentSpace (𝓡 m) ×ᵇ Bundle.Trivial _ ℝ` over `sphere (0 : E) 1` to
  that of `Bundle.Trivial (sphere (0 : E) 1) E`, $(v,t)\mapsto
  d\iota(v)+t\,x$, real-linear on each fibre, from Tau Ceti's
  `TauCeti.sphereTangentEquiv` and the continuity of the tangent map of
  the inclusion.

### `Topology/VectorBundle/Complex/KTheory/Basic.lean`

The part defines no category of bundles and no K-group of its own.
Bundles are Tau Ceti's `TauCeti.FiniteRankBundleCore ℂ X`
(`Topology/VectorBundle/FiniteRank/`), with isomorphisms from fibrewise
equivalences (`isoOfContinuousEquiv`), `trivial`, the Whitney sum as the
biproduct (`whitneySum`), `pullbackFunctor` and `tensor`. $K(X)$ is
`TauCeti.SplitK0 (FiniteRankBundleCore ℂ X)`
(`CategoryTheory/GrothendieckGroup/Split.lean`), with `SplitK0.of`,
`of_congr`, `of_biprod`, `exists_eq_sub`, `lift` and `lift_unique`. Since
the cores form a monoidal preadditive category
(`Topology/VectorBundle/FiniteRank/Monoidal.lean`), it is a commutative
ring (`CategoryTheory/GrothendieckGroup/Monoidal/Basic.lean`) with
`of_mul_of`, $[A][D]=[A\otimes D]$, so tensoring with a line bundle is
multiplication by its class; pullback along `f` is the ring homomorphism
`SplitK0.mapRingHom (pullbackFunctor f)`. The Chern classes of a core `A`
are those of `A.core.Fiber`, with model `Fin A.rank → ℂ`. Tau Ceti's
`TauCeti.TopologicalKZero`, the split Grothendieck group of variable-rank
atlases, is not used: atlases have neither a tensor product nor Chern
classes.

The file has:

- `Bundle.newtonClassInvariant j`, a `SplitK0.AdditiveInvariant` of
  `FiniteRankBundleCore ℂ X` with values in $H^{2j}(X;\mathbb Z)$, for
  compact `X`, sending `A` to `newtonClass (Fin A.rank → ℂ) A.core.Fiber j`:
  invariant under isomorphism by `newtonClass_congr` with the library's
  `isoFiberEquiv`, and additive on `whitneySum` by `newtonClass_prod` with
  Tau Ceti's `whitneySumTotalSpaceHomeomorph`.
- `Bundle.newtonClassHom j`, its `SplitK0.lift`, with `newtonClassHom_of`
  and `newtonClassHom_pullback`, its compatibility with
  `SplitK0.mapRingHom (pullbackFunctor f)`.

### `Topology/VectorBundle/FiniteRank/Clutching.lean`

The clutching construction over $X\times\mathbb CP^1$ [Hatcher2017, §2.1]:
$\mathbb CP^1$ is covered by the closed discs $|z|\le1$ and $|z|\ge1$ of
the affine chart and $\infty$, meeting in the circle. For a core
`E : FiniteRankBundleCore ℂ X` and a continuous family $f$ of
automorphisms of $E$ over $X\times S^1$, `FiniteRankBundleCore.clutching E f` is the
core in `FiniteRankBundleCore ℂ (X × ℙ ℂ (Fin 2 → ℂ))` obtained from
$p^*E$ on the two discs, glued by $f$ along the circle, on the cover by
slightly larger open discs and the trivializations of $E$. API:
`clutching_one` ($p^*E$), `nonempty_iso_clutching_of_homotopic`
(clutchings by homotopic families are isomorphic), `clutching_whitneySum`
(block-diagonal families), `clutching_tensor` (for a line bundle with its
clutching), and `clutching_z`: the tautological line is the clutching of
$\underline{\mathbb C}$ by $z$ (or $z^{-1}$, as the charts give).

### `Topology/VectorBundle/Complex/KTheory/ProductSphere.lean`

The surjective half of the product theorem [Hatcher2017, §2.1]:

- every bundle over $X\times\mathbb CP^1$, $X$ compact Hausdorff, is a
  clutching of its restriction to $X\times\{1\}$
  (`exists_iso_clutching`), by Tau Ceti's
  `TauCeti.exists_continuousLinearEquiv_cylinder` on each disc;
- `exists_iso_clutching_laurent`: the clutching function may be taken a
  Laurent polynomial $\sum_{|i|\le N}a_i(x)z^i$, by uniform approximation
  on fibres (Fejér sums in a finite atlas) and since nearby clutching
  functions are homotopic;
- `TauCeti.FiniteRankBundleCore.exists_linear_clutching_iso_of_fiberMap_eq_sum`,
  in `Topology/VectorBundle/FiniteRank/PolynomialClutching.lean`: a
  polynomial clutching function of degree
  $\le N$ becomes linear on $(N+1)E$ (Hatcher's matrix), and
  `of_clutching_linear`: for a linear one $a(x)z+b(x)$, $E$ splits as
  $E_+\oplus E_-$ by the spectral projection
  $\frac1{2\pi i}\oint(w-T)^{-1}dw$ (Mathlib's `circleIntegral`), giving
  $[E_+\otimes H^{\pm1}]+[E_-]$ in $K$;
- `Bundle.closure_of_pullback_fst_union_mul_eq_top`: the additive group
  $K(X\times\mathbb CP^1)$ is generated by the classes $[p^*A]$ and their
  products with $[q^*H]$, using $[H^{-1}]=2-[H]$
  (`TauCeti.SplitK0.of_clutching_circleZPowIso_one`). Here $L_m$ is the
  line clutched from $\underline{\mathbb C}$ by $u\mapsto u^m$
  (`circleZPowIso X m`), so $H^{-1}=L_1$; the relation comes from
  $L_m\oplus L_n\cong L_{m+n}\oplus L_0$
  (`TauCeti.FiniteRankBundleCore.whitneySum_clutching_circleZPowIso`, by
  `nonempty_iso_clutching_of_homotopic`), which gives
  $[L_m]=1+m(1-[H])$ (`TauCeti.SplitK0.of_clutching_circleZPowIso`).

### `Topology/VectorBundle/Complex/KTheory/ProjectiveLinePow.lean`

- `Bundle.closure_range_of_tensorTautological_eq_top`:
  $K((\mathbb CP^1)^m)$, for `Fin m → ℙ ℂ (Fin 2 → ℂ)`, is generated by the classes of the
  $L_T$, by induction on `m` through `Fin.snoc`.
- `newtonClassHom_mem_zmultiples`: $s_m$ of every class is a multiple of
  $m!\,y_1\cdots y_m$.

### `AlgebraicTopology/Cohomology/Sphere/Collapse.lean`

The collapse $\kappa:S^a\times S^b\to S^{a+b}$ that factors through the
smash product, for unit spheres of inner product spaces, and its effect
on integral cohomology in degree $a+b$: the pull-back of a class is its
evaluation times the cross product of the generators, up to one sign;
from Tau Ceti's Künneth and slant products for $S^{d+1}\times Y$
(`Cohomology/Sphere/Product.lean`,
`TopCat.singularCohomologyKunneth_sphere_bijective`) and the local degree
of $\kappa$ at a point off the wedge. Its iterate
$(\mathbb CP^1)^m\to S^{2m}$, through Tau Ceti's homeomorphism of
$\mathbb CP^1$ with $S^2$, and that $y_1\cdots y_m$ has infinite order.

### `Topology/VectorBundle/Complex/ChernClass/SphereIntegrality.lean`

- `Bundle.factorial_dvd_evalFundamentalClass_chernClass_sphere`: for a
  complex vector bundle `V` over `sphere (0 : E) 1` with
  `finrank ℝ E = 2 * m + 1`, `m ≠ 0`, and an orientation `o`,
  `((m - 1)! : ℤ) ∣ ⟨c_m(V), [S^{2m}]_o⟩`.

### `Geometry/Symplectic/Manifold/AlmostComplex/Sphere.lean`

- `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_sphere`:
  for $J$ on $TS^{2m}$, $\langle c_m(J.Fiber),[S^{2m}]_J\rangle=2$.
- `SymplecticGeometry.isEmpty_continuousComplexStructure_sphere_four_mul`:
  for `k ≠ 0`, no continuous complex structure on the tangent bundle of
  `sphere (0 : E) 1` with `finrank ℝ E = 4 * k + 1`.
- `TauCeti.Bundle.ContinuousComplexStructure.isEmpty_sphere_four_mul_add_two`:
  the same for `finrank ℝ E = 4 * k + 3` and `2 ≤ k`.
- `TauCeti.Bundle.ContinuousComplexStructure.isEmpty_sphere`: for
  `finrank ℝ E = 2 * n + 1` with `n ≠ 0`, `n ≠ 1`, `n ≠ 3`.
- `TauCeti.SmoothAlmostComplexStructure.isEmpty_sphere`: the smooth
  corollary, `IsEmpty (SmoothAlmostComplexStructure (𝓡 (2 * n))
  (sphere (0 : E) 1))` under the same hypotheses; this is what
  *Symplectic sums*' `Pointwise.lean` uses.

## What the part uses

- *Chern classes* (merged): `chernClass`, `totalChernClass`,
  `chernClass_prod`, `totalChernClass_prod`, `chernClass_pullback`,
  `chernClass_congr`, `totalChernClass_trivial`,
  `chernClass_finrank_eq_complexEulerClass`,
  `chernClass_one_eq_complexEulerClass`, `chernClass_one_tensorProduct`,
  `Projectivization.hyperplaneClass`.
- The library's `Geometry/Manifold/Orientation/EulerCharacteristic.lean`
  (`evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`) and
  `Geometry/Manifold/VectorBundle/ComplexStructure.lean`.
- Tau Ceti: `TauCeti.eulerChar_sphere`, `TauCeti.sphereTangentEquiv`,
  `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass` (as a pattern),
  the complexification and conjugate bundles with
  `TauCeti.complexEulerClass_conjugateBundle`,
  `TauCeti.Bundle.ContinuousComplexStructure`, the sphere cohomology of
  `AlgebraicTopology/Cohomology/Sphere/`, homotopy invariance of bundles,
  tensor products of bundles, `TauCeti.newtonMvPolynomial` and
  `TauCeti.X_mul_derivative_chernSeries`, `TauCeti.FiniteRankBundleCore`
  with its Whitney sums, pullbacks and tensor products, and
  `TauCeti.SplitK0` with its ring structure.
- The library's `Topology/VectorBundle/FiniteRank/` (`isoFiberEquiv`,
  `tensorFiberEquiv`, `ofBundleOfFinrankEqIso`).
- Mathlib: `VectorBundleCore`,
  `circleIntegral`, `MvPolynomial.psum_eq_mul_esymm_sub_sum`.

It waits for no part.

## Building issues

In this order. All are sub-issues of #3283, *Build the part Almost complex
spheres*. Sizes are estimates in lines.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Newton classes of complex bundles | `ChernClass/Newton.lean` | — | 300 |
| 2 | Complexification: sums, trivial bundles, $c(E_{\mathbb C})=1$ for stably trivial $E$ | `Complexification/Basic.lean` | — | 350 |
| 3 | Complexification of a bundle with a complex structure | `Complexification/ComplexStructure.lean` | — | 250 |
| 4 | Tangent bundle of the sphere plus a trivial line | `Tangent/Sphere.lean` | — | 200 |
| 5 | $\langle c_m(T_J),[S^{2m}]\rangle=2$, and no structure on $S^{4k}$ | `AlmostComplex/Sphere.lean` | 2, 3, 4 | 300 |
| 6 | Newton classes as a homomorphism on the split Grothendieck group of bundle cores | `KTheory/Basic.lean` | 1 | 250 |
| 7 | The clutching construction over $X\times\mathbb CP^1$ | `FiniteRank/Clutching.lean` | — | 500 |
| 8 | Every bundle is a clutching; Laurent clutching functions | `KTheory/ProductSphere.lean` | 7 | 450 |
| 9 | Linear clutching, its splitting, and the surjective product theorem | `KTheory/ProductSphere.lean` | 8 | 500 |
| 10 | $K((\mathbb CP^1)^m)$ and its Newton classes | `KTheory/ProjectiveLinePow.lean` | 6, 9 | 300 |
| 11 | The collapse map to $S^{2m}$ in cohomology | `Sphere/Collapse.lean` | — | 400 |
| 12 | Bott integrality on spheres | `ChernClass/SphereIntegrality.lean` | 10, 11 | 200 |
| 13 | No structure on $S^{4k+2}$, $k\ge2$, and the theorem for $S^{2n}$ | `AlmostComplex/Sphere.lean` | 5, 12 | 150 |

Issues 1 to 4, 7 and 11 can start at once. The $S^{4k}$ case is done with
issue 5; *Symplectic sums*' `Pointwise.lean` waits for issue 13.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd
  ed.][McDuffSalamon2017], Exercise 4.1.9.
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (the
  product theorem and its proof by clutching functions) and Chapter 4 (the
  Chern character, Bott's integrality on spheres and the spheres with
  almost complex structures).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of
  Mathematics Studies 76, Princeton (1974), §14 (the conjugate bundle),
  §15 (complexification) and §16 (Newton's polynomials).
* M. F. Atiyah, R. Bott, *On the periodicity theorem for complex vector
  bundles*, Acta Math. 112 (1964), 229–247.
* A. Borel, J.-P. Serre, *Groupes de Lie et puissances réduites de
  Steenrod*, Amer. J. Math. 75 (1953), 409–448 (the other route, not
  taken).
