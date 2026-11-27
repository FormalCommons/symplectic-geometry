# Compatible symplectic forms

This is the detailed design of part 49 of `DESIGN.md`, *Compatible
symplectic forms*. It covers three milestones of
`atlas/symplectic-fibrations.md`: *Thurston's theorem on symplectic
fibrations* ([McDuffSalamon2017], Theorem 6.1.4, after [Thurston1976]),
*Chern class criterion for compatible symplectic forms* (Lemma 6.1.7 and
Corollary 6.1.8 there) and *Symplectic forms on surface bundles with fibre
genus different from one* (Theorem 6.2.2 there), the last by the page's
elementary route through families of area forms.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. Statements about Mathlib, Tau Ceti and the library were checked
against the versions pinned when this file was written (Tau Ceti
`c9d170eed5a8`).

## Setting and notation

- **Manifolds.** Real manifolds modelled on finite-dimensional spaces, with
  boundaryless models, Hausdorff and σ-compact, smooth (`∞`). $M$ is
  modelled on `IM`, $B$ on `IB`, the fibre $F$ on `IF`. The map
  `π : M → B` is smooth. Compactness of $M$ is assumed only where a
  statement needs it (step 2 of Thurston's theorem and the milestones that
  use it); then $B$ and $F$ are compact too, as the page says.
- **Atlases and fibre forms.** These are *Symplectic fibrations*'
  as the conventions *Fibrations* and *Fibre forms* of `DESIGN.md`
  describe them. In `Geometry/Manifold/FiberBundle/MapFiber.lean`: an
  atlas `A` of `π` with fibre $F$ (`TauCeti.MapFiber.Atlas`), smooth in
  the sense of `A.IsContMDiff`, and for a chart `e` of `A` and
  `b ∈ e.baseSet` the fibre inclusion `e.fiberInclusionMap hb`, written
  $j_{e,b}:F\to M$, $v\mapsto e^{-1}(b,v)$. In
  `Geometry/Manifold/FiberBundle/StructureGroup.lean`: structure groups,
  so that symplectic atlases for $(F,\sigma)$ are those with structure
  group `TauCeti.SmoothForm.diffeomorphStabilizer σ`, and oriented atlases
  for an orientation of $F$ those with structure group
  `Diffeomorph.orientationPreservingSubgroup`. In
  `Geometry/Manifold/FiberBundle/RestrictsTo.lean`: the predicate that a
  two-form $\tau$ on $M$ *restricts to the fibre forms*, $j_{e,b}^*\tau=\sigma$
  for every chart and base point. In
  `Geometry/Symplectic/Fibration/Basic.lean`: compatible symplectic forms; and
  compatibility of a symplectic form with an oriented atlas and an
  orientation of $B$. This file uses these
  notions under the names that *Symplectic fibrations*' design gives them,
  and names below only its own declarations. Where this file writes
  "restricts to the fibre forms of `A`", the Lean statement uses that
  predicate.
- **Forms and cohomology.** Two-forms are Tau Ceti's `SmoothTwoForm`;
  symplectic forms satisfy `TauCeti.SmoothTwoForm.IsSymplectic`. Cohomology
  is `TauCeti.deRhamCohomology I M k`, with classes
  `TauCeti.deRhamCohomology.mk` of closed forms and pull-backs
  `TauCeti.deRhamCohomology.map f hf k`. For a closed $\tau$ write $[\tau]$.
- **Surfaces.** A closed surface is $F$ modelled on `𝓡 2`, compact,
  connected, with an orientation `o : Manifold.Orientation (𝓡 2) F (Fin 2)`.
  Its genus is Tau Ceti's `TauCeti.surfaceGenus F`, and integrals of top
  forms are `integralTopForm o`, as in the merged *First Chern number*.

## Decisions

The paragraph *The design file decides* of part 49 asks for two things.

- **The real first Chern class over a general base.** It is built in three
  layers, each a definition with its own API:
  1. for a principal `Circle`-bundle, the class
     `realFirstChernClass IB P` of *Minimal coupling*
     (`Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean`,
     #2348), $-(2\pi)^{-1}$ times the class of the curvature of any
     connection form. This part adds its naturality under equivariant maps
     of circle bundles;
  2. for a smooth complex vector bundle, given as a real bundle with a
     smooth complex structure `J : ContMDiffComplexStructure I ∞ F V`, the
     class `ContMDiffComplexStructure.realFirstChernClass J`, which is
     `realFirstChernClass` of the unit circle bundle of the determinant
     line $\Lambda^{\mathrm{top}}_{\mathbb C}(V,J)$ for a Hermitian metric
     on it. This is the Chern–Weil class for the determinant line, as the
     review of #2280 asked, and not a second Chern–Weil theory with
     $\mathfrak u(n)$-valued curvature;
  3. for a nondegenerate two-form `ω` on a real bundle,
     `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass`, the class of
     any complex structure that `ω` tames, as the library's integral
     `Bundle.symplecticChernNumber` (`ChernNumber/Basic.lean`) chooses one;
     and, on the tangent bundle, `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass`,
     beside the integral `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernClass`.

  The determinant line is Tau Ceti's `TauCeti.DetBundle`
  (`Topology/VectorBundle/Determinant.lean` of Tau Ceti),
  which is only a topological bundle today; this part makes it a smooth
  one. The vertical bundle $\mathrm{Ver}=\ker d\pi$ gets the symplectic
  structure $\tau|_{\mathrm{Ver}}$ of any form $\tau$ that restricts to
  the fibre forms; it does not depend on $\tau$.

  **Comparison with the integral class.** The class is compared with the
  integral `TauCeti.firstChernClass` over a
  closed oriented surface, where both give numbers: the integral of the de
  Rham class is the Chern number (`chernNumber_eq_integral_curvature`,
  merged). Over a general base the comparison would say that Tau Ceti's
  `TauCeti.deRhamHom IM M 2` sends the de Rham class to the image of the
  integral class in $H^2(M;\mathbb R)$. That needs Chern–Weil theory for
  the Euler class in singular cohomology over an arbitrary base, which
  neither library has; no milestone needs it, so this part does not build
  it, as *Minimal coupling*'s design already decided for circle bundles.
  The page itself uses only the real class.
- **The hypothesis $c_1(TF)=\lambda[\sigma]$.** For a symplectic form `σ`
  on $F$ with `hσ : σ.IsSymplectic`, it reads
  `hσ.isNondegenerate.realFirstChernClass = λ • [σ]` in
  `TauCeti.deRhamCohomology IF F 2`, with `λ ≠ 0`. For a closed surface
  oriented by `σ`, `realFirstChernClass_tangent_eq_of_surface` below gives
  it with $\lambda=(2-2g)/\int_F\sigma$.

Two further choices:

- **Thurston's theorem in two files.** Step 1 of the page's proof, the
  closed extension of the fibre forms, needs neither compactness nor a base
  form, and is used by *Coupling forms* only through Thurston's theorem; it
  goes in `ClosedExtension.lean`, and step 2 with the milestone in
  `Thurston.lean`, so that two issues do not write one file. The
  equivalence "for some, equivalently every $b$" of the milestone is proved
  in `ClosedExtension.lean`, for a connected base.
- **Moser's argument with a parameter.** The merged
  `Geometry/Symplectic/Moser/Family.lean` has Moser's argument with a
  parameter in $[0,1]$, relative to a compact set on which the primitives
  vanish. The surface case needs it on a closed fibre, with no vanishing
  condition, and with the parameter in an open set of the base. So this
  part adds the closed-manifold form with a parameter in any manifold, in a
  file of its own, `Geometry/Symplectic/Moser/Parameter.lean`.

## Departures from `DESIGN.md`

This pull request corrects part 49 and the conventions of `DESIGN.md`:

- Step 1 of Thurston's theorem moves from `Thurston.lean` to
  `ClosedExtension.lean`. `ChernClass.lean` keeps the vertical bundle, its
  class and the criterion, and `Surface.lean` the surface milestone; the
  real Chern classes of bundles, the surface formula and the reduction to a
  symplectic atlas go in the files of *Files* below.
- The real first Chern class is compared with the integral class over closed
  oriented surfaces only, as above, not over a general base.
- The part also builds on *Minimal coupling*'s `RealChernClass.lean`
  (#2348), and on the merged *Smooth families*' `GoodCover.lean`, which
  issue 9 below generalizes to a manifold parameter.
- The parametric Moser argument is the new `Moser/Parameter.lean`, not the
  merged `Moser/Family.lean`; and the departure *Proof routes on
  `atlas/symplectic-fibrations.md`* now says that the surface case runs
  Moser's argument with a parameter in the base, which the parallel
  transport route avoids only for the first milestone of the page.

## Files

| File | Contents |
|---|---|
| `Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean` | (of *Minimal coupling*) naturality of `realFirstChernClass` |
| `Geometry/Manifold/VectorBundle/Determinant.lean` | the determinant line of a smooth complex bundle as a smooth line bundle, with a Hermitian metric |
| `Geometry/Manifold/VectorBundle/ChernNumber/RealChernClass.lean` | the real first Chern class of a smooth complex vector bundle |
| `Geometry/Manifold/VectorBundle/Symplectic/RealChernClass.lean` | the real class of a bundle with a nondegenerate two-form; surfaces |
| `Geometry/Manifold/DeRham/SmoothFamily/GoodCover.lean` | (of *Smooth families*) smooth families of primitives over a manifold parameter |
| `Geometry/Symplectic/Moser/Parameter.lean` | Moser stability on a closed manifold with a parameter in a manifold |
| `Geometry/Symplectic/Fibration/ClosedExtension.lean` | closed extensions of the fibre forms (step 1); the cohomological condition |
| `Geometry/Symplectic/Fibration/Thurston.lean` | step 2 and Thurston's theorem |
| `Geometry/Symplectic/Fibration/ChernClass.lean` | the vertical bundle, its real first Chern class, the criterion |
| `Geometry/Symplectic/Fibration/AreaForm.lean` | a symplectic atlas for an oriented fibration with closed surface fibre |
| `Geometry/Symplectic/Fibration/Surface.lean` | the surface milestone, with compatibility with the orientation |

### Naturality in `FiberBundle/Principal/RealChernClass.lean`

Added to *Minimal coupling*'s file, which #2403 merged. For principal
`Circle`-bundles $Q\to B'$ and $P\to B$ as in that file, a smooth
$f:B'\to B$ and a smooth map $\Phi$ of total spaces with
$\pi_P\circ\Phi=f\circ\pi_Q$ and $\Phi(q\cdot z)=\Phi(q)\cdot z$:

- `IsCircleConnectionForm.mpullback (hα) (hΦ …)`: $\Phi^*\alpha$ is a
  connection form on $Q$. Equivariance makes $d\Phi$ carry the fundamental
  field of `circleLieGenerator` to that of $P$, and $\Phi^*\alpha$
  invariant.
- `IsCircleConnectionForm.curvature_mpullback`: its curvature is
  $f^*F_\alpha$, since both pull back to $d\Phi^*\alpha$ along $\pi_Q$ and
  `π_Q^*` is injective on forms (a submersion).
- `realFirstChernClass_map`: `realFirstChernClass IB' Q =
  deRhamCohomology.map f hf 2 (realFirstChernClass IB P)`. A special case
  with $f=\mathrm{id}$ is invariance under isomorphisms of circle bundles.

About 150 lines.

### `Geometry/Manifold/VectorBundle/Determinant.lean`

For a smooth real vector bundle `V` over `M` with finite-dimensional model
and a smooth complex structure `J` (so that `J.toContinuousComplexStructure.Fiber`
is a complex bundle), the determinant line `TauCeti.DetBundle ℂ G _`:

- an instance `ContMDiffVectorBundle ∞` on it: its coordinate changes are
  determinants of the smooth coordinate changes of `V`, smooth since `det`
  is polynomial;
- the smoothness of `TauCeti.DetBundle.congrModelHomeomorph`: a smooth
  fibrewise complex-linear isomorphism of such bundles (for instance
  `Tames.exists_complex_bundleEquiv`) induces a smooth isomorphism of
  determinant lines, and the pull-back isomorphism
  `TauCeti.DetBundle.pullbackHomeomorph` is smooth;
- `exists_hermitianMetric_detBundle`: the determinant line has a smooth
  Hermitian metric in the form taken by `Hermitian/CircleBundle.lean`
  (`circleBundleDiffeomorph`, `contMDiffFiberBundle_circleFiber`): a smooth
  real metric that multiplication by `Complex.I` preserves, from Tau Ceti's
  `TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I`;
- `TauCeti.DetBundle.lineHomeomorph` is smooth for a line bundle.

About 300 lines. The coordinate changes of `TauCeti.DetBundle` are the
determinants of those of `V` (`TauCeti.DetBundle.coordChangeL_trivialization`),
so their smoothness follows from that of `V`'s.

### `Geometry/Manifold/VectorBundle/ChernNumber/RealChernClass.lean`

Over a base `M` as in *Setting*, for `J : ContMDiffComplexStructure I ∞ F V`:

- `ContMDiffComplexStructure.realFirstChernClass J : TauCeti.deRhamCohomology I M 2`,
  `realFirstChernClass` of the unit circle bundle of the determinant line
  for the metric that `exists_hermitianMetric_detBundle` chooses; with
  `realFirstChernClass_def`.
- `realFirstChernClass_eq_of_metric`: any smooth Hermitian metric on the
  determinant line gives the same class. Normalization $v\mapsto v/|v|_{g'}$
  is an equivariant map of circle bundles over the identity
  (`realFirstChernClass_map`).
- `realFirstChernClass_pushforward`: a smooth complex-linear isomorphism
  of bundles does not change the class.
- `realFirstChernClass_pullback`: for a smooth `f`, the class of
  `J.pullback f hf` is `deRhamCohomology.map f hf 2` of the class of `J`
  (the pull-back of the determinant line and of its metric, and the
  bundle map over `f`).
- `realFirstChernClass_eq_of_finrank_eq_one`: for a line bundle with a
  smooth Hermitian metric, the class is `realFirstChernClass` of its own
  unit circle bundle (through the smooth `TauCeti.DetBundle.lineHomeomorph`).
- `integralTopForm_realFirstChernClass`: over a closed surface with
  orientation `o`, the integral of any closed representative of the class
  of `J` is the Chern number `chernNumber` of `J.toContinuousComplexStructure.Fiber`
  (by `realFirstChernClass_eq_of_finrank_eq_one` in rank one, through the
  determinant line in general, and `chernNumber_eq_integral_curvature`).
  This is the comparison with the integral class.

About 400 lines.

### `Geometry/Manifold/VectorBundle/Symplectic/RealChernClass.lean`

- `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass (h)`, the class of
  the complex structure `h.polarComplexStructure g` for a chosen bundle
  metric `g`, with `_def`.
- `realFirstChernClass_eq_of_tames`: every smooth complex structure tamed
  by `ω` gives this class (`Tames.exists_complex_bundleEquiv` and
  `realFirstChernClass_pushforward`).
- `realFirstChernClass_pullback` and `realFirstChernClass_pushforward` for
  forms: the class of the pull-back form along a smooth map, and of the form
  transported by a smooth isomorphism of bundles that carries one form to
  the other.
- On the tangent bundle: `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass`,
  through `ContMDiffTwoForm.tangentEquiv`, and
  `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass_mpullback`: a
  diffeomorphism $\varphi$ with $\varphi^*\sigma'=\sigma$ carries one class
  to the other.
- `realFirstChernClass_tangent_eq_of_surface`: on a closed connected
  surface, for a symplectic form `σ` inducing the orientation `o`
  (`hσ.volumeOrientation … = o`),
  `hσ.realFirstChernClass = ((2 - 2 * surfaceGenus F) / integralTopForm o σ) • [σ]`.
  Proof: top-degree de Rham cohomology of a closed connected oriented
  surface is detected by the integral
  (`mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`, merged),
  the integral of the left side is the symplectic Chern number
  (`integralTopForm_realFirstChernClass`), and that is $2-2g$
  (`Bundle.symplecticChernNumber_tangent`, merged). The integral of `σ` is
  positive.

About 300 lines.

### Smooth families over a manifold parameter

As first merged, *Smooth families* stated its parametric results for
families over the unit interval only: `PreservesSmoothFamilies`
(`DifferentialForm/SmoothFamily/Map.lean`) quantified over families
`unitInterval → D`, and so did the Mayer–Vietoris steps of
`DeRham/SmoothFamily/MayerVietoris.lean` and
`exists_isSmoothFamily_mextDerivₗ_eq` (`DeRham/SmoothFamily/GoodCover.lean`).
The reduction in `AreaForm.lean` needs primitives of a family over a ball
of the base, on a closed fibre, which is not contractible, so
`IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq` does not
apply. Issue 9 below is a refactor of those files:

- `PreservesSmoothFamilies T` quantifies over smooth families over every
  smooth parameter manifold `N` with a model `J`
  (boundary allowed, so that the unit interval is a case), in universes
  (of `N`, its model and its model space) that the definition takes as
  parameters; its closure lemmas, the
  homotopy operator's and the Mayer–Vietoris steps are proved slice by
  slice and carry over;
- `exists_isSmoothFamily_mextDerivₗ_eq` takes a family `η : N → SmoothForm I M ℝ (k + 1)`
  with `IsSmoothFamily J η`, and gives `α : N → SmoothForm I M ℝ k` with
  `IsSmoothFamily J α`; the milestone *Smooth families of primitives*
  stays `exists_primitiveMap_of_hasFiniteGoodCover`, with the stronger
  `PreservesSmoothFamilies`.

Every use is updated in the same pull request, and
`design/smooth-families.md` where it states these declarations for the
unit interval. The fallback of a predicate for one given parameter model
was not needed: the generalized `PreservesSmoothFamilies` takes the
universes as parameters.

### `Geometry/Symplectic/Moser/Parameter.lean`

On a closed manifold `N` (compact, boundaryless), with a parameter manifold
`P` (model `IP`, any):

- `TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_mextDeriv_eq_sub`:
  let `ω₀` be a closed two-form on `N`, `σ` a two-form and `β` a one-form on
  `P × N` with slices $\sigma_p$, $\beta_p$, such that
  $d\beta_p=\sigma_p-\omega_0$ for every $p$ and every
  $\omega_0+s(\sigma_p-\omega_0)$, $s\in[0,1]$, is nondegenerate. Then there
  is a diffeomorphism $\hat\chi$ of $P\times N$ of the form
  $(p,x)\mapsto(p,\chi_p(x))$ with $\chi_p^*\sigma_p=\omega_0$ for every
  $p$, and $\chi_p=\mathrm{id}$ where $\beta_p=0$.

  Proof: the Moser fields of the segments, for $(p,s)\in P\times\mathbb R$,
  are the merged `moserField` of one form on $(P\times\mathbb R)\times N$
  (no cutoff is needed on a compact `N`); their flows are complete and
  jointly smooth by the merged `TauCeti.contMDiff_timeDependentFlowOf_param`
  (`Geometry/Manifold/Flow/TimeDependent.lean`), and the time-one maps are
  $\chi_p$. The inverse family is the flow backwards. The argument follows
  the merged `exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`
  and `TauCeti.SmoothForm.IsClosed.exists_isotopy_mpullback_eq`, which the
  module docstring credits.

About 300 lines. It uses only merged files and Tau Ceti.

### `Geometry/Symplectic/Fibration/ClosedExtension.lean`

For a symplectic atlas `A` of `π` for $(F,\sigma)$, with no compactness:

- `exists_isClosed_restricts_of_map_eq` (step 1): if a class
  `a : deRhamCohomology IM M 2` satisfies `map (j e b) _ 2 a = [σ]` for
  every chart `e` of `A` and `b ∈ e.baseSet`, there is a closed $\tau$
  that restricts to the fibre forms of `A` with $[\tau]=a$. Proof as on the
  page: cover $B$ by chart balls inside base sets, which are smoothly
  contractible; on $\pi^{-1}(U)\cong U\times F$ the fibre embedding is a
  homotopy equivalence, so homotopy invariance
  (`TauCeti.deRhamCohomology.map_eq_of_homotopy`) makes
  $e^*\mathrm{pr}_F^*\sigma-\tau_0$ exact there, $=d\lambda_U$; glue the
  $d((\rho_U\circ\pi)\lambda_U)$ with a smooth partition of unity on $B$
  (`SmoothPartitionOfUnity`), locally finite.
- `map_eq_of_restricts`: conversely, if a closed $\tau$ restricts to the
  fibre forms, `a = [τ]` satisfies the hypothesis. In particular for a
  compatible symplectic form.
- `forall_map_eq_of_map_eq`: over a connected base, if the hypothesis holds
  for one chart and one base point, it holds for all. At one point two
  charts differ by a symplectomorphism of $F$, which fixes $[\sigma]$; over
  a base set the embeddings $j_{e,b}$ are homotopic along paths in a ball;
  the set of good points is open and closed.
- `exists_isClosed_restricts_iff`: the two directions together: a closed
  extension of the fibre forms exists if and only if such a class does.

Statements are in degree 2 with $\sigma$ closed (it is symplectic). About
450 lines; if it grows, the chart-independence lemma goes first in the same
issue as a public lemma about fibre embeddings.

### `Geometry/Symplectic/Fibration/Thurston.lean`

For `M` compact:

- `exists_forall_le_isSymplectic_add_smul_mpullback` (step 2): if a closed
  $\tau$ restricts to the fibre forms and `β` is a symplectic form on `B`,
  there is $K_0$ such that $\tau+K\pi^*\beta$ is symplectic for every
  $K\ge K_0$. Pointwise, $\mathrm{Hor}_x=\mathrm{Ver}_x^{\tau}$ is a
  complement of $\mathrm{Ver}_x$ (linear algebra: $\tau$ is nondegenerate on
  $\mathrm{Ver}_x$), the form is block diagonal for
  $\mathrm{Hor}\oplus\mathrm{Ver}$, and on $\mathrm{Hor}$ it is
  $\tau|_{\mathrm{Hor}}+K\beta$ read through $d\pi$. Nondegeneracy of
  $K^{-1}\tau|_{\mathrm{Hor}}+\beta$ is open in $(x,K^{-1})$ and holds at
  $K^{-1}=0$; compactness of $M$ gives one $K_0$. The form restricts to the
  fibre forms since $j_{e,b}^*\pi^*\beta=0$.
- `exists_isSymplectic_restricts_mk_eq` (milestone): for `M` compact, `B`
  connected with a symplectic form `β`, a symplectic atlas `A` and a class
  `a` with `map (j e b) _ 2 a = [σ]` for **one** chart `e` and `b ∈ e.baseSet`,
  there is $K_0$ such that for every $K\ge K_0$ there is a symplectic form
  compatible with `A` whose class is `a + K • [π^*β]`. Milestone line:
  *Thurston's theorem on symplectic fibrations*.

About 300 lines.

### `Geometry/Symplectic/Fibration/ChernClass.lean`

For a symplectic atlas `A` for $(F,\sigma)$:

- the vertical bundle `fun x ↦ LinearMap.ker (mfderiv IM IB π x)` as a
  smooth subbundle of `TM`, by Tau Ceti's
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`: images
  of coordinate frames of `TF` under $d(e^{-1})$ are local frames, unless
  *Symplectic fibrations* builds it first;
- `verticalForm A`, the restriction to $\mathrm{Ver}$ of a connection
  two-form of `A` (*Symplectic fibrations*' existence of connection
  two-forms), with `isNondegenerate_verticalForm`, and
  `verticalForm_eq`: every form that restricts to the fibre forms has this
  restriction to $\mathrm{Ver}$;
- `realFirstChernClass_vertical A : deRhamCohomology IM M 2`, the class of
  `isNondegenerate_verticalForm` (layer 3 above), with `_def`;
- `map_realFirstChernClass_vertical`: for a chart `e` and `b ∈ e.baseSet`,
  `map (j e b) _ 2 (realFirstChernClass_vertical A) = hσ.realFirstChernClass`.
  The differential of $j_{e,b}$ is an isomorphism from `TF` onto the
  pull-back of $\mathrm{Ver}$ that carries $\sigma$ to the pull-back of
  `verticalForm A`; then `realFirstChernClass_pullback` and
  `realFirstChernClass_pushforward` for forms;
- `map_inv_smul_realFirstChernClass_vertical` (milestone): if
  `hσ.isNondegenerate.realFirstChernClass = λ • [σ]` with `λ ≠ 0`, then
  `a := λ⁻¹ • realFirstChernClass_vertical A` satisfies
  `map (j e b) _ 2 a = [σ]` for every chart and base point; and
  `exists_isSymplectic_compatible_of_realFirstChernClass_eq`: if moreover
  `M` is compact and `B` compact, connected and symplectic, a compatible
  symplectic form exists (`exists_isSymplectic_restricts_mk_eq`). The first
  carries the milestone line *Chern class criterion for compatible
  symplectic forms*; the second's docstring says that it is the
  consequence the milestone states.

About 350 lines.

### `Geometry/Symplectic/Fibration/AreaForm.lean`

For an oriented atlas `A` of `π` with closed connected surface fibre
$(F,o)$:

- `exists_restricts_isPositive_area`: a two-form $\tau$ on $M$ whose
  restrictions $j_{e,b}^*\tau$ are area forms inducing `o`, of integral
  one. Fix such a form $\sigma_0$ on $F$ (a top form inducing `o`, from Tau
  Ceti's `TauCeti.exists_topForm_of_orientation`, rescaled) and glue $e^*\mathrm{pr}_F^*\sigma_0$ with a partition of unity
  on $B$. Coordinate changes preserve `o`, so they preserve positivity and
  the integral, and positive forms of integral one are a convex set.
- `exists_symplecticAtlas_of_oriented` (the reduction): `π` has a symplectic
  atlas for $(F,\sigma_0)$, with the same base sets near each point, whose
  charts preserve the orientation, and for which $\tau$ restricts to the
  fibre forms. Over a chart ball $U$ inside a base set of `e`, the slices
  $\sigma_b=j_{e,b}^*\tau$ have the integral of $\sigma_0$, so
  $\sigma_b-\sigma_0$ is exact; a smooth family of primitives over $U$ is
  `exists_isSmoothFamily_mextDerivₗ_eq` with the manifold parameter $U$
  of issue 9 (a closed manifold has a finite good cover); segments of
  positive area forms stay positive, hence nondegenerate; `Moser/Parameter.lean` gives $\hat\chi$ on $U\times F$,
  and the new chart is $e$ followed by $\hat\chi^{-1}$.

About 400 lines.

### `Geometry/Symplectic/Fibration/Surface.lean`

- `exists_isSymplectic_compatible_oriented` (milestone): let $F$ be a closed
  connected surface with orientation `o` and `surfaceGenus F ≠ 1`, `M`
  compact, `B` compact and connected with a symplectic form `β`, and `A` an
  oriented atlas of `π` with fibre $(F,o)$. Then `M` has a symplectic form
  compatible with `A`, `o` and the orientation of `B` induced by `β`, in the
  sense of *Symplectic fibrations*' `Basic.lean`. Milestone line:
  *Symplectic forms on surface bundles with fibre genus different from one*.

  Proof: `exists_symplecticAtlas_of_oriented` gives a symplectic atlas for
  $(F,\sigma_0)$; `realFirstChernClass_tangent_eq_of_surface` gives
  $c_1(TF)=(2-2g)[\sigma_0]$ with $2-2g\ne0$; the criterion of
  `ChernClass.lean` and step 1 give a closed $\tau$ restricting to
  $\sigma_0$ on the fibres, positive there; and $\omega_K=\tau+K\pi^*\beta$
  for large $K$. Compatibility with the orientation of $M$: in the block
  form of step 2, the top power of $\omega_K$ on a basis made of a lift of
  a $\beta$-oriented basis of $T_bB$ and an `o`-oriented basis of the fibre
  has the sign of $(K^{-1}\tau|_{\mathrm{Hor}}+\beta)^n\wedge\sigma_0$,
  which is positive for large $K$, again uniformly by compactness. So this
  file needs from `Thurston.lean` the form $\tau+K\pi^*\beta$ itself, which
  step 2 states, and not only the milestone.
- `surfaceGenus_ne_one` is a hypothesis that cannot be dropped: the page's
  Hopf surface is the counterexample, which is not built here.

About 250 lines.

## Issues

Each issue is a few hundred lines, in an order where each comes after the
ones it waits for.

1. **Naturality of the real first Chern class of a circle bundle**
   (`FiberBundle/Principal/RealChernClass.lean`). Waits for nothing.
2. **The smooth determinant line** (`VectorBundle/Determinant.lean`).
   Waits for nothing.
3. **The real first Chern class of a complex vector bundle**
   (`VectorBundle/ChernNumber/RealChernClass.lean`). Waits for 1 and 2.
4. **The real Chern class of a bundle with a nondegenerate two-form**
   (`VectorBundle/Symplectic/RealChernClass.lean`). Waits for 3.
5. **Moser stability with a parameter** (`Moser/Parameter.lean`). Waits
   for nothing.
6. **Closed extensions of the fibre forms**
   (`Fibration/ClosedExtension.lean`). Waits for *Symplectic fibrations*'
   `Basic.lean`.
7. **Thurston's theorem** (`Fibration/Thurston.lean`). Waits for 6.
8. **The Chern class criterion** (`Fibration/ChernClass.lean`). Waits for
   4, 7 and *Symplectic fibrations*' `HorizontalDistribution.lean`
   (existence of connection two-forms).
9. **Smooth families of primitives over a manifold parameter**
   (`DifferentialForm/SmoothFamily/Map.lean`, `DeRham/SmoothFamily/`).
   Waits for nothing.
10. **Symplectic atlases of oriented surface fibrations**
    (`Fibration/AreaForm.lean`). Waits for 5, 9 and *Symplectic
    fibrations*' `Basic.lean`.
11. **Surface bundles of genus different from one**
    (`Fibration/Surface.lean`). Waits for 8 and 10.

Issues 1, 2, 5 and 9 can start at once.

## Uses

- *Symplectic fibrations*: `MapFiber.lean` (smooth atlases, fibre
  inclusions), `StructureGroup.lean` (symplectic and oriented atlases),
  `RestrictsTo.lean` (the restriction predicate), `Basic.lean`
  (compatibility, compatibility with an orientation) and
  `HorizontalDistribution.lean` (existence of connection two-forms).
- *Minimal coupling*: `realFirstChernClass` (#2348).
- Merged files of *First Chern number*: circle connection forms and their
  curvature, `chernNumber_eq_integral_curvature`,
  `Bundle.symplecticChernNumber_tangent`, the Hermitian circle bundle
  (`Hermitian/CircleBundle.lean`), top-degree Poincaré duality.
- Merged files of *Symplectic vector bundles*: two-forms and complex
  structures on bundles, `polarComplexStructure`,
  `Tames.exists_complex_bundleEquiv`, pull-backs; Tau Ceti's `TauCeti.DetBundle`.
- Merged files of *Moser isotopy* and *Smooth families*: `moserField`,
  the time extensions, and `PreservesSmoothFamilies` and
  `exists_isSmoothFamily_mextDerivₗ_eq` as issue 9 generalizes them.
- Tau Ceti: de Rham cohomology and its homotopy invariance, smooth
  subbundles from local frames, finite-rank bundle cores and their
  determinant, top forms of an orientation, `surfaceGenus`.
- Mathlib: `SmoothPartitionOfUnity`, `Manifold.Orientation`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §2.7 (first Chern class), Theorem 6.1.4, Lemma 6.1.7, Corollary 6.1.8
  and Theorem 6.2.2.
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and
  Multiplicity Diagrams*][GuilleminLermanSternberg1996], §1.5 (weak
  coupling).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of
  Mathematics Studies 76, Princeton (1974), §14 (the first Chern class
  through the determinant line).
