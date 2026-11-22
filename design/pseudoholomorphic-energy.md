# Energy of pseudoholomorphic curves

The detailed design of part 30 of `DESIGN.md`, *Energy of pseudoholomorphic
curves*. It proves the milestone *Energy identity for J-holomorphic curves*
of `atlas/almost-complex-structures.md`, and settles the question that
`DESIGN.md` leaves to this file: how $\int_\Sigma u^*\omega$ is compared with
the pairing of $[\omega]$ with $u_*[\Sigma]$.

Sources: McDuff–Salamon [McDuffSalamon2017], §4.5, equation (4.5.4) and the
paragraph after it; for the pointwise computation and the tame case Wendl
[Wendl2010] (equation (2.6), Definition 2.18, Proposition 2.19) and
McDuff–Salamon [McDuffSalamon2012], §2.2. For the topological side: J. M.
Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 16 and 18
(integration of top forms, smooth chains and the smoothing theorem), and
A. Hatcher, *Algebraic Topology*, §§2.1 and 3.3 (the class of a simplex,
local orientations and fundamental classes along compact sets).

All declarations of Tau Ceti and Mathlib named below were checked against the
pinned versions (Tau Ceti `v4.37.0-rc1`, see `lakefile.toml`), except those
said to be on Tau Ceti's main branch, which were checked against its commit
`464618e8a5`. Paths of Tau Ceti files are relative to
`.lake/packages/TauCeti/TauCeti/`.

## What there is, and what is missing

- **Pointwise energy on the standard line**
  (`Geometry/Symplectic/Manifold/Energy.lean`): for `F : ℝ × ℝ →ₗ[ℝ] T_xM`,
  `TauCeti.SmoothTwoForm.stdComplexLineEnergyDensity ω J x F`
  $=\omega(F\partial_s,JF\partial_s)+\omega(F\partial_t,JF\partial_t)$, the
  Wirtinger identity
  `TauCeti.SmoothTwoForm.Invariant.stdComplexLineEnergyDensity_sub_two_mul_twoForm`
  ($e(F)-2\omega(F\partial_s,F\partial_t)=\omega(v,Jv)$ with
  $v=F\partial_s+JF\partial_t$, for $J$-invariant $\omega$), and the
  tameness lemmas `Tames.stdComplexLineEnergyDensity_nonneg`, `_eq_zero_iff`.
  The integrated energy there, `stdComplexLineEnergy`, lives on
  $\mathbb R^2$ with a measure; the pinned version has no energy of a map
  from a closed surface.
- **The energy of a map from a surface, on Tau Ceti's main branch**
  (`Geometry/Symplectic/Manifold/Energy/Surface.lean`, added after the pin
  in commit `464618e8a5`), in `TauCeti.SmoothTwoForm`:
  `energyForm ω J j u : RoughForm I' C ℝ 2`, the polarized two-term form
  $c\mapsto\tfrac12\bigl(\omega(du\,jv,J\,du\,w)-\omega(du\,jw,J\,du\,v)\bigr)$,
  with `energyForm_apply` (`@[simp]`), `energyForm_apply_frame`,
  `energyForm_apply_frame_eq_stdComplexLineEnergyDensity` and
  `energyForm_eq_mpullback_of_isPseudoholomorphicAt`;
  `Tames.energyForm_apply_frame_nonneg`, `_pos`; the pointwise Wirtinger
  inequality and its equality case
  (`Compatible.mpullback_apply_frame_le_energyForm_apply_frame`,
  `Compatible.energyForm_apply_frame_eq_mpullback_apply_frame_iff`);
  `isSmoothForm_energyForm` (continuity for a `C¹` map);
  `energy ω J j o u := integralTopForm o (ω.energyForm J j u)` with
  `energy_def`; `energy_eq_integralTopForm_mpullback` (for
  `∀ c, IsPseudoholomorphicAt j J u c`, the energy is
  `integralTopForm o (mpullback I' I u ω.val)`); `Tames.energy_nonneg`,
  `Tames.energy_eq_zero_iff` and `Tames.apply_eq_of_energy_eq_zero`;
  `Compatible.integralTopForm_mpullback_le_energy` and
  `Compatible.energy_eq_integralTopForm_mpullback_iff` (the Wirtinger
  inequality on compact surfaces, with its equality case);
  `energyForm_comp_apply`, `energy_comp_diffeomorph` and
  `energy_comp_eq_degree_mul`. The same commit adds
  `SmoothBundleForm.contMDiffAt_eval₂`
  (`Geometry/Manifold/DifferentialForm/Smooth.lean`) and
  `Diffeomorph.mfderiv_ne_zero` (`Geometry/Manifold/Diffeomorph/Basic.lean`),
  which the file uses, and gives `SmoothAlmostComplexStructure.complexFrame`
  the hypothesis `finrank ℝ (TangentSpace I c) = 2` in place of the pinned
  orientation `o`. Everything else it imports is pinned (Decision 8).
- **The Cauchy–Riemann operator, linearly**
  (`LinearAlgebra/Complex/LinearPart.lean`):
  `TauCeti.complexAntilinearPart J J' F` $=\tfrac12(F+J'\circ F\circ J)$ for
  linear endomorphisms `J`, `J'` and a linear map `F`, with
  `TauCeti.isComplexLinear_iff_complexAntilinearPart_eq_zero`. With
  `J := j c`, `J' := J (u c)` and `F := mfderiv I' I u c` this is the page's
  $\bar\partial_J(u)$ at `c`. The part defines no operator of its own.
- **Pseudoholomorphic maps** (`Geometry/Symplectic/Manifold/JHolomorphic.lean`):
  `TauCeti.IsPseudoholomorphicAt j J u c`, `IsPseudoholomorphic`,
  `IsPseudoholomorphicAt.mfderiv_apply_commute`,
  `IsPseudoholomorphicAt.mfderiv_isComplexLinear`.
- **Surfaces with an almost complex structure**
  (`Geometry/Symplectic/Manifold/AlmostComplex/Orientation.lean`):
  `TauCeti.SmoothAlmostComplexStructure.complexFrame` (the basis $(e,je)$ of
  a tangent plane), `apply_basis_nonneg_of_forall_nonneg` and
  `integralTopForm_pos_of_forall_nonneg` (a continuous top form that is
  $\ge0$ on every frame $(e,je)$ and $>0$ on one has positive integral). The
  orientation of a surface by $j$ is not a definition there: statements take
  `o : Manifold.Orientation I' C (Fin 2)` and the hypothesis that every basis
  `b` with `b 1 = j c (b 0)` has orientation `o.orientationAt c`. The part
  does the same.
- **Integration** (`Geometry/Manifold/DifferentialForm/Integration/`):
  `TauCeti.integralTopForm o φ` for a rough top form, with
  `IsSmoothForm.integrableTopForm`, `integralTopForm_add_of_compactSpace`,
  `integralTopForm_smul`, `integralTopForm_nonneg`, `integralTopForm_pos`;
  and, in `Geometry/Symplectic/Manifold/CurvePairing.lean`,
  `TauCeti.integralTopForm_mpullback_nonneg` (only $\ge0$).
- **Smooth chains** (`Geometry/Manifold/SmoothSingular/`): `SmoothSimplex`,
  `SmoothSimplex.integral`, the cochain `TauCeti.integrationCochain` with
  Stokes' theorem (`d_comp_integrationCochain`), the de Rham map
  `deRhamCohomology.integration` into smooth singular cohomology, the
  smoothing theorem (`smoothSingularHomologyIso`,
  `quasiIso_chainComplexMap_smoothSingularSubcomplex_ι_opens`, for every
  open subset of a Hausdorff σ-compact manifold), and
  `TauCeti.SmoothSimplex.integral_eq_integralTopForm` (`TopForm.lean`): a
  top form supported in the image of a simplex that is, near
  $\Delta^p$, an orientation-preserving open embedding $g$ has the same
  integral over the simplex as over the manifold.
- **Fundamental classes** (`AlgebraicTopology/Singular/LocalHomology/`):
  `TauCeti.HomologicalOrientation` with `fundamentalClass`,
  `fundamentalClassOn` (the class along a compact set) and their uniqueness
  lemmas `eq_fundamentalClass`, `eq_fundamentalClassOn`;
  `mapFundamentalClass`, `evalFundamentalClass`; and the passage from a
  smooth orientation, `TauCeti.Manifold.Orientation.toHomologicalOrientation`
  (`Orientation/Smooth.lean`), with `toHomologicalOrientation_neg`.

Missing, even on Tau Ceti's main branch: the first display of the milestone
for maps that are not pseudoholomorphic (the $\bar\partial$ term), the
reading of the energy through an area form and its independence of it, and
any link between `integralTopForm` and fundamental classes. On Tau Ceti's main branch
(after the pin), `Geometry/Manifold/SmoothSingular/Period.lean` pairs de Rham
classes with integral *smooth* singular homology
(`deRhamCohomology.smoothHomologyPeriod`, built on a version of
`integrationCochain` generalized to integer coefficients) and
`SingularCohomology.lean` adds the de Rham homomorphism `deRhamHom` into
real singular cohomology. The comparison with fundamental classes is a target
of Tau Ceti's roadmap that no one has started.

## Decisions

1. **The energy integrand is a top form that does not see the area form.**
   For a linear map $L:T_c\Sigma\to T_xM$ let
   $b(v,w)=\omega_x(Lv,J_xLw)$ and

   $$\varepsilon_L(v,w)=\tfrac14\bigl(b(jv,w)+b(w,jv)-b(v,jw)-b(jw,v)\bigr).$$

   This is alternating for every $\omega$ and $J$, and on a frame
   $\varepsilon_L(e,je)=\tfrac12\bigl(b(e,e)+b(je,je)\bigr)$, which is half
   of `stdComplexLineEnergyDensity` of $(a,s)\mapsto L(ae+s\,je)$. For a
   compatible pair it is $\tfrac12(\lvert Le\rvert^2+\lvert Lje\rvert^2)$ in
   $g_J$. If $\mathrm{dvol}_\Sigma$ is positive on frames, the squared norm
   of $L$ for the metric $\mathrm{dvol}_\Sigma(\cdot,j\cdot)$ is
   $\lvert L\rvert^2=(b(e,e)+b(je,je))/\mathrm{dvol}_\Sigma(e,je)$ for any
   $e\ne0$, so $\tfrac12\lvert L\rvert^2\,\mathrm{dvol}_\Sigma=\varepsilon_L$
   as top forms. The page's integrand is therefore $\varepsilon_{du}$, and
   independence of the area form is a pointwise identity. The energy is
   Tau Ceti main's `energy`, the integral of its `energyForm`, and the
   page's $\tfrac12\int\lvert du\rvert^2\mathrm{dvol}_\Sigma$ is proved equal
   to it for every admissible area form. Tau Ceti's form
   $\tfrac12\bigl(b(jv,w)-b(jw,v)\bigr)$ and the four-term
   $\varepsilon_{du}$ are both alternating and agree on a frame $(e,je)$,
   where each is $\tfrac12\bigl(b(e,e)+b(je,je)\bigr)$; on a plane they are
   therefore equal (`energyForm_apply_eq_energyDensity`, by
   `SmoothAlmostComplexStructure.topForm_ext`). On a source of another
   dimension they differ, and only the four-term form is defined for a
   linear map rather than for a map of manifolds. So the library keeps
   `energyDensity` for the pointwise statements that Tau Ceti lacks (the
   squared norm and the $\bar\partial$ identity, with `normSq` and
   `Energy/Metric.lean`, which are merged), and passes to Tau Ceti's form
   by that lemma; it defines no energy form of its own.
2. **The pointwise identity is an identity of top forms.** For
   $J$-invariant $\omega$,
   $\varepsilon_L=2\,\varepsilon_{\bar\partial L}+L^*\omega_x$ with
   $\bar\partial L$ = `complexAntilinearPart`. Both sides are top forms on a
   plane, so they agree once they agree on one frame $(e,je)$, where this is
   the Wirtinger identity. Integrated, it gives the first display of
   the milestone; no orientation hypothesis is needed for it, only for signs
   (nonnegativity, positivity).
3. **An area form compatible with the orientation is a taming form.** With
   the orientation hypothesis on `o`, a two-form on the surface is positive
   on positively oriented bases exactly when it is positive on every frame
   $(e,je)$, which is Tau Ceti's `dvol.Tames j`. The statements take
   `hdvol : dvol.Tames j`; no new predicate.
4. **Regularity.** Integrals are added only for integrable forms. Tau Ceti
   main's `isSmoothForm_energyForm` says that the energy form of a $C^1$ map
   is a continuous form (`IsSmoothForm I' 0`). The forms
   $c\mapsto\varepsilon_{\bar\partial(du_c)}$ and
   $c\mapsto\lvert du_c\rvert^2\mathrm{dvol}_\Sigma$ are then continuous by
   the identities of Decisions 1 and 2, since $u^*\omega$ is smooth.
5. **The pairing with homology.** For a closed two-form, $\langle[\omega],A\rangle$
   for $A\in H_2(M;\mathbb Z)$ (Tau Ceti's model of integral singular
   homology, the type of `mapFundamentalClass`) is the integral of $\omega$
   over a smooth integral cycle representing $A$, which exists and is
   unique up to smooth boundaries by the smoothing theorem. The part needs
   this map only through two properties: its value on such a cycle, and
   naturality under smooth maps. It is
   `TauCeti.deRhamCohomology.singularHomologyPeriod` below, unless Tau Ceti
   has a map with these properties by the time its issue starts (its
   main-branch `smoothHomologyPeriod` composed with the smoothing
   isomorphism would be one; it cannot be brought over under its Tau Ceti
   name, since it rests on a generalization of the pinned
   `integrationCochain`).
6. **The comparison with the fundamental class, and its sign.** The library
   proves that for a closed oriented surface $\Sigma$ and a smooth top form
   $\varphi$, $\int_\Sigma\varphi=\langle[\varphi],[\Sigma]\rangle$, where the
   local orientations of $[\Sigma]$ are the classes of positively oriented
   simplices, as in Hatcher. The proof is local (route under
   `FundamentalClass.lean`). Tau Ceti's `toHomologicalOrientation` selects
   its local orientations through radial projection and an orthonormal-basis
   generator of the sphere, not through simplices; Tau Ceti's own roadmap
   records that in dimension one this is the class of a *decreasing* path,
   the negative of the simplex convention. So the issue that proves the
   local lemma first determines, in dimension two, the sign
   $s\in\{1,-1\}$ with $[\text{positive simplex}]=s\cdot$(Tau Ceti's local
   orientation). The homology statements then use `o.toHomologicalOrientation`
   if $s=1$ and `(-o).toHomologicalOrientation` if $s=-1$, and that issue
   records the outcome in this file. Outcome: $s=-1$
   (`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`, in
   `LocalHomology/Orientation/StdSimplex.lean`), so the homology statements
   use `(-o).toHomologicalOrientation`. The comparison is proved for surfaces
   only: the milestone needs nothing more, and only the local lemma depends
   on the dimension. Tau Ceti's roadmap plans the general statement; when
   it arrives, the library's surface case becomes a corollary to be
   replaced in a refactor.
7. **Relative cycles without a relative smoothing theorem.** The local step
   needs: if a smooth cycle $z$ and a smooth chain $\sigma$ with boundary in
   an open $U$ have the same class in the continuous relative homology
   $H_2(M,U)$, then $z-\sigma=\partial b+c$ with $b$ smooth and $c$ a smooth
   chain in $U$. This follows from the absolute smoothing theorem for $M$
   and for $U$ (both pinned): through the relative chains of the pairs of
   simplicial sets of smooth and of continuous simplices, and Tau Ceti's
   `SSetPair.quasiIso_chainComplexMap`; it is one lemma.
8. **Tau Ceti main's energy is copied now.** Waiting for a move of Tau Ceti
   would block issue 3 and the milestone for an unknown time, and defining
   the library's own `energyForm` and `energy` would clash by name with Tau
   Ceti at the next move. Everything that Tau Ceti's
   `Energy/Surface.lean` imports is pinned, and checking the file against the
   pin leaves three gaps: `SmoothBundleForm.contMDiffAt_eval₂` and
   `Diffeomorph.mfderiv_ne_zero`, which the same commit adds to other Tau
   Ceti files, and the hypothesis of the pinned `complexFrame` (an
   orientation, where the file has only `finrank = 2`). So, as *Files* in
   `AGENTS.md` says, the part copies the whole file to
   `SymplecticGeometry/Geometry/Symplectic/Manifold/Energy/Surface.lean`
   with Tau Ceti's header, and the two lemmas to the `FromTauCeti.lean`
   siblings of the library's `DifferentialForm/Smooth.lean` and
   `Diffeomorph/Basic.lean`. The one change to a proof is in
   `energyForm_eq_mpullback_of_isPseudoholomorphicAt`, which builds the frame
   $(e,je)$ as a basis from the pinned
   `TauCeti.AlmostComplexStructure.linearIndependent_pair` instead of calling
   `complexFrame`; the module docstring records it. A move of Tau Ceti past
   `464618e8a5` deletes the three files.

## Conventions

- **Target.** `I : ModelWithCorners ℝ E H`, `[IsManifold I ∞ M]`,
  `ω : TauCeti.SmoothTwoForm I M`, `J : TauCeti.SmoothAlmostComplexStructure I M`;
  the milestone assumes `ω.Compatible J`. The homology statements add
  `[FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]` and `M : Type`.
- **Surface.** `C` (the letter `Σ` is a token) with
  `I' : ModelWithCorners ℝ E' H'`, `[FiniteDimensional ℝ E']`,
  `[IsManifold I' ∞ C]`, `j : SmoothAlmostComplexStructure I' C`. The pointwise
  lemmas of `Density.lean` take only `h2 : finrank ℝ E' = 2`; where signs or
  integration need it, statements take
  `o : Manifold.Orientation I' C (Fin 2)` (which fixes the dimension, by
  `o.finrank_tangentSpace_eq`) and, where signs matter, the hypothesis
  `ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) → b.orientation = o.orientationAt c`
  of `integralTopForm_mpullback_nonneg`. *Closed* is `[CompactSpace C]`; the
  identities hold on compact surfaces with boundary too. The homology
  statements take the model `𝓘(ℝ, E')` with `hE' : finrank ℝ E' = 2`,
  `[ChartedSpace E' C] [T2Space C] [CompactSpace C]` and `C : Type`, as
  `toHomologicalOrientation` and `fundamentalClass` need.
- **Maps.** `u : C → M` with `hu : ContMDiff I' I ∞ u`; the regularity lemma
  needs only `ContMDiff I' I 1 u`.
- **Namespaces.** The densities and the energy are about the target form, as
  Tau Ceti's `stdComplexLineEnergyDensity` is, and go in
  `TauCeti.SmoothTwoForm` (dot notation `ω.energyForm J j u`). The general
  lemmas go in the namespaces of the Tau Ceti notions they are about.

## Files

| File | Contents |
|---|---|
| `Geometry/Symplectic/JHolomorphic/Energy/Density.lean` | the pointwise density $\varepsilon_L$, the squared norm, the pointwise identity |
| `LinearAlgebra/Complex/EnergyDensity.lean` | the same for a linear map between vector spaces, from which `Density.lean` reads its statements |
| `Geometry/Symplectic/Manifold/AlmostComplex/TopForm.lean` | top forms on a tangent plane of an almost complex surface: equality and ratios read on one frame $(e,je)$, without an orientation |
| `LinearAlgebra/Complex/TopForm.lean` | the same on a real plane with a complex structure |
| `Geometry/Symplectic/JHolomorphic/Energy/Metric.lean` | the squared norm read in $g_J$ |
| `Geometry/Symplectic/Manifold/Energy/Surface.lean` | Tau Ceti main's file of that path, copied with Tau Ceti's header (Decision 8): the energy form and its continuity, the energy, the pseudoholomorphic case, positivity, the Wirtinger inequality |
| `Geometry/Manifold/DifferentialForm/Smooth/FromTauCeti.lean` | Tau Ceti main's `SmoothBundleForm.contMDiffAt_eval₂`, for the file above |
| `Geometry/Manifold/Diffeomorph/Basic/FromTauCeti.lean` | Tau Ceti main's `Diffeomorph.mfderiv_ne_zero`, for the file above |
| `Geometry/Symplectic/JHolomorphic/Energy/Surface.lean` | Tau Ceti's energy form read through `energyDensity`, the energy through an area form, the integrated identity, zero energy and local constancy |
| `AlgebraicTopology/SimplicialSet/Homology/RestrictScalars.lean` | the change of coefficients on simplicial chains along a restriction of scalars, `SSet.restrictScalarsChainMap` |
| `Geometry/Manifold/SmoothSingular/SingularPeriod.lean` | the pairing of de Rham classes with integral singular homology |
| `Geometry/Manifold/SmoothSingular/RelativeCycle.lean` | the relative step of Decision 7 |
| `AlgebraicTopology/SimplicialSet/Homology/RelativeClass.lean` | the relative class of a simplex whose faces lie in the subcomplex of a pair of simplicial sets, `SSetPair.relClass` |
| `AlgebraicTopology/SimplicialSet/Homology/One.lean` | naturality of the class of a closed $1$-simplex under maps of simplicial sets, `SSet.ιHomology₁_homologyMap` |
| `AlgebraicTopology/Singular/RelativeClass.lean` | the relative class of a singular simplex whose faces lie in the subspace, `TopPair.relClass` |
| `AlgebraicTopology/Singular/LocalHomology/Orientation/StdSimplex.lean` | the class of the standard $2$-simplex in the local homology of $\mathbb R^2$ at an interior point, and the sign $s$ of Decision 6 |
| `AlgebraicTopology/Singular/LocalHomology/Orientation/Simplex.lean` | the class of a positively oriented simplex in local homology, in dimension two |
| `Geometry/Manifold/DeRham/FundamentalClass.lean` | $\int_\Sigma\varphi=\langle[\varphi],[\Sigma]\rangle$ on closed oriented surfaces |
| `Geometry/Symplectic/JHolomorphic/Energy/Homology.lean` | topological invariance, minimality, the milestone |

The `Energy/` folder sits beside Tau Ceti's folder of the same name, as
`DESIGN.md` says; the copy of Tau Ceti's file is in that folder of Tau
Ceti's, under `Manifold/`. The files outside it are general manifold topology or linear algebra
and are placed by topic.

## Definitions and their API

### `Energy/Density.lean`

For `c : C`, `x : M` and `L : TangentSpace I' c →ₗ[ℝ] TangentSpace I x`
(linear suffices, the source being finite-dimensional), each statement read
from that of `LinearAlgebra/Complex/EnergyDensity.lean`, which it imports,
for `ω x`, `J x`, `j c` and `dvol c`:

- `TauCeti.SmoothTwoForm.energyDensity (ω : SmoothTwoForm I M) (J) (j) (L) :
  TangentSpace I' c [⋀^Fin 2]→L[ℝ] ℝ`, the form $\varepsilon_L$ of Decision 1.
  API: `energyDensity_apply` (the four-term formula on `![v, w]`),
  `energyDensity_apply_complexFrame` (on `![e, j c e]` it is
  $\tfrac12(\omega(Le,JLe)+\omega(Lje,JLje))$), `energyDensity_zero`
  (`@[simp]`), `energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity`
  (half of Tau Ceti's density of $(a,s)\mapsto L(ae+s\,je)$; the issue looks
  for that linear map in Tau Ceti before defining it),
  `Tames.energyDensity_apply_complexFrame_nonneg` and
  `Tames.energyDensity_apply_complexFrame_eq_zero_iff` (zero exactly when
  `L e = 0 ∧ L (j c e) = 0`).
- `TauCeti.SmoothTwoForm.normSq (ω) (J) (j) (dvol : SmoothTwoForm I' C) (L) : ℝ`,
  the squared norm of `L` for the metric $\mathrm{dvol}(\cdot,j\cdot)$ on the
  source and $\omega(\cdot,J\cdot)$ on the target:
  $(\omega(Le,JLe)+\omega(Lje,JLje))/\mathrm{dvol}(e,je)$ for a nonzero `e`
  chosen once (and `0` on a zero tangent space). API: `normSq_eq` (the same
  formula for *every* nonzero `e`, on a plane; it holds because numerator and
  denominator are values of the top forms $2\varepsilon_L$ and
  $\mathrm{dvol}$ on the same frame), `normSq_smul_eq_two_smul_energyDensity`
  (`normSq • dvol c = 2 • energyDensity L` when `dvol c ≠ 0`, which on
  a plane is being nonzero on frames), `normSq_nonneg` under tameness of both forms.
- `Invariant.energyDensity_eq_two_smul_add` (Decision 2): for
  `ω.Invariant J`, `ω.energyDensity J j L = 2 • ω.energyDensity J j
  (complexAntilinearPart (j c) (J x) L) + (ω x).compContinuousLinearMap L`
  (for `L : TangentSpace I' c →L[ℝ] TangentSpace I x`, with the linear maps of
  `j c`, `J x` and `L` coerced as needed).

### `LinearAlgebra/Complex/EnergyDensity.lean`

The same statements for vector spaces, in the namespace `AlternatingMap`:
for `ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ`, which may be degenerate, complex structures
`J : AlmostComplexStructure V` and `j : AlmostComplexStructure W`, and
`L : W →ₗ[ℝ] V`. The definitions are `AlternatingMap.energyDensity ω J j L`
and `AlternatingMap.energyNormSq ω J j dvol L`. Tameness and invariance are
hypotheses on `ω` (`∀ v, v ≠ 0 → 0 < ω ![v, J v]`,
`∀ v w, ω ![J v, J w] = ω ![v, w]`), and planes are `finrank ℝ W = 2`. The
identity `AlternatingMap.energyDensity_eq_two_smul_add` is proved on a frame
$(e,je)$, by `TauCeti.AlmostComplexStructure.alternatingMap_ext` of
`LinearAlgebra/Complex/TopForm.lean` (a top form is its value on a basis times
the determinant, `AlternatingMap.eq_smul_basis_det`), with the Wirtinger
identity, which Tau Ceti proves for nondegenerate forms only. The lemmas of
`Manifold/AlmostComplex/TopForm.lean` are those of
`LinearAlgebra/Complex/TopForm.lean` at `j c`.

### `Energy/Metric.lean`

- `TauCeti.SmoothTwoForm.Compatible.normSq_eq_inner`: for `hc : ω.Compatible J`
  and `e` with `dvol (e, j e) = 1` (a unit vector for the domain metric), on a plane
  (`Module.finrank ℝ E' = 2`, as for `normSq_eq`),
  `normSq = hc.metric.inner x (L e) (L e) + hc.metric.inner x (L (j e)) (L (j e))`,
  from `Compatible.metric_inner` of *Almost complex manifolds*' `Metric.lean`.
  This is the page's reading of $\lvert\eta\rvert^2$ through a unit vector, in
  the metric $g_J$ as a Riemannian metric. Separate from `Density.lean` so
  that only this file waits for `Metric.lean`.

### `Manifold/Energy/Surface.lean` (from Tau Ceti main)

The declarations listed under *What there is* for this file, with Tau
Ceti's names, statements and namespace `TauCeti.SmoothTwoForm`. The part
uses in particular `energyForm`, `energyForm_apply`,
`isSmoothForm_energyForm`, `energy`, `energy_def`,
`energy_eq_integralTopForm_mpullback` (the pseudoholomorphic case),
`Tames.energy_nonneg`, `Tames.energy_eq_zero_iff` (for compact `C`, `ho`,
`ω.Tames J` and `hu : ContMDiff I' I 1 u`,
`ω.energy J j o u = 0 ↔ ∀ c, mfderiv I' I u c = 0`) and
`Compatible.integralTopForm_mpullback_le_energy`. The copy changes only the
proof of `energyForm_eq_mpullback_of_isPseudoholomorphicAt` (Decision 8).
The two supporting lemmas go in the `FromTauCeti.lean` files of *Files*.
Tau Ceti states the pullback as `mpullback I' I u ω.val`, and so does the
rest of this design.

### `JHolomorphic/Energy/Surface.lean`

It imports the copy above and `Energy/Density.lean`, and defines nothing.

- `energyForm_apply_eq_energyDensity`: on a plane (`h2 : finrank ℝ E' = 2`),
  `ω.energyForm J j u c = ω.energyDensity J j (mfderiv I' I u c).toLinearMap`.
  Both sides agree on a frame by `energyForm_apply_frame_eq_stdComplexLineEnergyDensity`
  and `energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity`, hence
  everywhere by `SmoothAlmostComplexStructure.topForm_ext` (Decision 1).
- `energy_eq_half_integralTopForm_normSq`: for `hdvol : dvol.Tames j`,
  `ω.energy J j o u = 1 / 2 * integralTopForm o (fun c ↦ ω.normSq J j dvol (mfderiv I' I u c) • dvol c)`.
  This is the independence of the area form: the left side has none.
- `Invariant.energy_eq_integralTopForm_add`: for `ω.Invariant J`, compact `C`
  and `hdvol`,
  `ω.energy J j o u = integralTopForm o (fun c ↦ ω.normSq J j dvol (complexAntilinearPart … (mfderiv I' I u c)) • dvol c) + integralTopForm o (mpullback I' I u ω.val)`.
- `Tames.energy_eq_zero_iff_isLocallyConstant`: for compact `C`, `ho`,
  `ω.Tames J` and `hu`, `ω.energy J j o u = 0 ↔ IsLocallyConstant u`, from
  Tau Ceti's `Tames.energy_eq_zero_iff`,
  `MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero`
  (`Geometry/Manifold/MFDeriv/Constancy.lean`) and its converse. Tau Ceti's
  `Tames.apply_eq_of_energy_eq_zero` is the connected case; the milestone
  speaks of local constancy.
- `Compatible.energy_identity`: the analytic half of the milestone, the
  conjunction, for compact `C`, `hc : ω.Compatible J` and every `dvol` taming
  `j`, of the first display (in the form of
  `Invariant.energy_eq_integralTopForm_add` with the left side written
  through `energy_eq_half_integralTopForm_normSq`), the pseudoholomorphic
  case, and the independence of `dvol`. No milestone line; the milestone is
  in `Homology.lean`.

### `SmoothSingular/SingularPeriod.lean`

- `TauCeti.deRhamCohomology.singularHomologyPeriod : deRhamCohomology I M p →ₗ[ℝ]
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (ModuleCat.of ℤ (ULift ℤ))).obj (TopCat.of M) →+ ℝ)`
  (the name avoids Tau Ceti's degree-one `deRhamCohomology.homologyPeriod`).
  Built from the inverse of `smoothSingularHomologyIso I M (ModuleCat.of ℤ (ULift ℤ)) p`
  and the integral of a closed form over smooth integral chains, which on a
  chain $\sum n_i\sigma_i$ is $\sum n_i\int_{\sigma_i}\varphi$ (Tau Ceti's real
  `integrationCochain` after the change of coefficients $\mathbb Z\to\mathbb R$,
  or `SmoothSimplex.integral` summed directly), well defined by Stokes'
  theorem for chains. API: `singularHomologyPeriod_mk_apply_smoothCycle` (on
  the image of the class of a smooth integral cycle it is the integral over
  the cycle; the exact form of the cycle's class is the issue's), and
  `singularHomologyPeriod_map` ($\langle f^*c,A\rangle=\langle c,f_*A\rangle$
  for smooth `f`, from `integrationCochain_naturality` and the naturality of
  the smoothing isomorphism, `smoothSingularHomologyIso_inv_naturality`).
  The issue first checks whether Tau Ceti has such a map since the pin
  (Decision 5).

### `SmoothSingular/RelativeCycle.lean`

- The lemma of Decision 7, for an open `U : Opens M` of a Hausdorff
  σ-compact `M`: a smooth chain `w` whose boundary
  is a smooth chain of `U`, and which is zero in the continuous relative
  homology of `(M, U)`, is `∂ b + c` with `b` a smooth chain of `M` and `c` a
  smooth chain of `U`. Name `TauCeti.exists_smoothSingular_eq_d_add`. It is
  stated on elements, for any coefficient module `R : ModuleCat.{u} k`: the
  vanishing in relative homology is the hypothesis that, as a continuous
  chain, `w = ∂ B + A` with `A` a chain of `U` (the chain-level meaning of
  vanishing in the relative chains of `TopPair`), so issue 8 passes from
  the classes it compares to such a decomposition. Proof: the inclusion of
  smooth into continuous simplices is a morphism from the pair of smooth
  simplices of `(M, U)` to that of continuous ones, a quasi-isomorphism on
  relative chains by smoothing for `U` and for `M` and
  `SSetPair.quasiIso_chainComplexMap`; the image of `w` in the smooth
  relative chains is a cycle that bounds continuously, hence smoothly, and
  lifting that bound gives `b`.

### `LocalHomology/Orientation/Simplex.lean`

- For a smooth 2-simplex `σ : SmoothSimplex 𝓘(ℝ, E') C 2` given near
  `fullSimplex 2` by an open embedding `g` that is orientation preserving
  from `Manifold.Orientation.euclideanSpace 2` to `o` (the hypotheses of
  `SmoothSimplex.integral_eq_integralTopForm`), and a compact `K` inside
  `g '' interior (fullSimplex 2)`: `σ` is a relative cycle of
  `(C, C ∖ K)`, and its class is the fundamental class along `K` of the
  correctly signed homological orientation (Decision 6):
  `SmoothSimplex.relativeClass_eq_fundamentalClassOn`, the class being
  `TopPair.relClass` of the underlying singular simplex, from
  `AlgebraicTopology/Singular/RelativeClass.lean` (it defines no class of its
  own). By `eq_fundamentalClassOn` it suffices to
  compute the local image at each point of `K`; by the change-of-chart sign
  rule (`OpenPartialHomeomorph.localHomologyMap_restrict_localOrientationOfOrientedChart`)
  and translation invariance this reduces to one affine simplex around `0`
  in $\mathbb R^2$ with its standard orientation, where the connecting
  morphism takes the simplex to its boundary loop, and Tau Ceti's explicit
  description of the circle (`AlgebraicTopology/Singular/Sphere.lean`: the
  connecting morphism of the two-arc cover sends its generator to
  `[-x] - [x]`) fixes the sign $s$.
- The issue records $s$ in this file and in this section, and from then on
  "the correctly signed homological orientation" means
  `o.toHomologicalOrientation hE'` if $s=1$ and
  `(-o).toHomologicalOrientation hE'` if $s=-1$. If $s=-1$, it also opens an
  issue, labelled `proposed`, for the parts that compare integrals of forms
  with Tau Ceti's fundamental classes (at present *First Chern number*'s
  Chern–Weil formula).
- Recorded: $s=-1$. For `p` in the interior of `fullSimplex 2`, the class
  of the standard simplex in $H_2(\mathbb R^2,\mathbb R^2\setminus\{p\})$ is
  minus the local orientation at `p` of
  `(Manifold.Orientation.euclideanSpace 2).toHomologicalOrientation`
  (`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`, and
  `TopPair.relClass_fullSimplex_eq_neg_localOrientationOfOrientedChart` for
  the identity chart), in `LocalHomology/Orientation/StdSimplex.lean`. So the
  correctly signed homological orientation is
  `(-o).toHomologicalOrientation hE'`. `StdSimplex.lean` imports
  `LinearAlgebra/Complex/Orientation.lean` and
  `AlgebraicTopology/Singular/LocalHomology/Orientation/Smooth.lean` of part
  *First Chern number*.

### `DeRham/FundamentalClass.lean`

- `TauCeti.Manifold.Orientation.integralTopForm_eq_singularHomologyPeriod`
  (the name follows the orientation used): for a closed surface `C` as in
  *Conventions*, oriented by `o`, and a smooth two-form `φ` (closed, by
  `mextDeriv_eq_zero_of_finrank_le`),
  `integralTopForm o φ = deRhamCohomology.singularHomologyPeriod (mk φ) (oₕ.fundamentalClass hE')`
  with `oₕ` the correctly signed homological orientation. Route: every
  point has a positively oriented simplex chart (a chart, a linear
  equivalence of `E'` with $\mathbb R^2$ matching `o` at the point, and a
  small affine simplex around it); a smooth partition of unity subordinate to
  the interiors of finitely many of them splits `φ` into forms `ρᵢ • φ`
  supported in compact sets `Kᵢ`; both sides are additive in `φ`. For one
  piece choose a smooth integral cycle `z` representing the fundamental
  class (smoothing). Its image in $H_2(C,C\setminus K_i)$ is the class along
  `Kᵢ` (Tau Ceti), so is that of the simplex `σᵢ` (`Simplex.lean`), and the
  relative step gives `z - σᵢ = ∂ b + c` with `c` in `C ∖ Kᵢ`. Hence
  $\int_z\rho_i\varphi=\int_{\sigma_i}\rho_i\varphi$ (Stokes for `b`, and
  `ρᵢ • φ` vanishes on `c`), which is `integralTopForm o (ρᵢ • φ)` by
  `SmoothSimplex.integral_eq_integralTopForm`.

### `Energy/Homology.lean`

With `oₕ` as above, `A` an integral class of $H_2(M)$, `hω : ω` closed, and
`hA : oₕ.mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A` ("$u$ represents
$A$"):

- `integralTopForm_mpullback_eq_singularHomologyPeriod`:
  `integralTopForm o (mpullback I' I u ω.val) = singularHomologyPeriod (mk ω) A`,
  from `FundamentalClass.lean` for `u^* ω` and `singularHomologyPeriod_map`.
- `energy_eq_singularHomologyPeriod`: for `∀ c, IsPseudoholomorphicAt j J u c`,
  `ω.energy J j o u = singularHomologyPeriod (mk ω) A`.
- `Compatible.energy_le_energy`: for `hc`, `ho`, pseudoholomorphic `u` and
  any smooth `v : C → M` representing the same `A`,
  `ω.energy J j o u ≤ ω.energy J j o v` (both areas are the period of `A`,
  and Tau Ceti's `Compatible.integralTopForm_mpullback_le_energy` bounds
  that of `v` by its energy).
- `singularHomologyPeriod_pos`: for `hc`, `ho` and pseudoholomorphic `u`
  that is not locally constant, `0 < singularHomologyPeriod (mk ω) A`.
- **Milestone** `Compatible.energy_identity_and_homology`: the conjunction of
  `Compatible.energy_identity` and, for closed `ω`, the three statements
  above. Milestone: *Energy identity for J-holomorphic curves*.

## Main results

| Result | Lean name | File |
|---|---|---|
| pointwise identity | `TauCeti.SmoothTwoForm.Invariant.energyDensity_eq_two_smul_add` | `Density.lean` |
| independence of the area form | `TauCeti.SmoothTwoForm.energy_eq_half_integralTopForm_normSq` | `Surface.lean` |
| integrated identity | `TauCeti.SmoothTwoForm.Invariant.energy_eq_integralTopForm_add` | `Surface.lean` |
| pseudoholomorphic case | `TauCeti.SmoothTwoForm.energy_eq_integralTopForm_mpullback` (Tau Ceti main) | `Manifold/Energy/Surface.lean` |
| zero energy | `TauCeti.SmoothTwoForm.Tames.energy_eq_zero_iff_isLocallyConstant` | `Surface.lean` |
| integration against $[\Sigma]$ | `TauCeti.Manifold.Orientation.integralTopForm_eq_singularHomologyPeriod` | `DeRham/FundamentalClass.lean` |
| the milestone | `TauCeti.SmoothTwoForm.Compatible.energy_identity_and_homology` | `Homology.lean` |

The tame case of the page's notes (the symmetrized metric) is not a
milestone. The densities are defined for any `ω` and `J`, and the
pseudoholomorphic case and positivity need only `Tames`, so it costs nothing
later.

## What it uses

- From *Almost complex manifolds*: `Metric.lean` (`Compatible.metric`,
  `Compatible.metric_inner`), for `Energy/Metric.lean` only.
- From Tau Ceti: the declarations of *What there is*; those of its main
  branch through the copies of Decision 8.
- From Mathlib: `SmoothPartitionOfUnity`,
  `AlternatingMap.eq_smul_basis_det`, `IsLocallyConstant`.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **Energy densities.** `Energy/Density.lean`, all of it, with
   `Manifold/AlmostComplex/TopForm.lean`, which it imports. About 350
   lines. No blockers.
2. **Tau Ceti main's energy of a map from a surface.** The copy of
   Decision 8: `Manifold/Energy/Surface.lean` and the two `FromTauCeti.lean`
   files. About 550 lines, nearly all copied. No blockers. If a move of Tau
   Ceti past `464618e8a5` comes first, the issue has nothing left to do.
3. **The energy and its identity.** `JHolomorphic/Energy/Surface.lean`, all
   of it, with `Compatible.energy_identity`. About 250 lines. Blocked by 2.
4. **The squared norm in the metric of a compatible pair.**
   `Energy/Metric.lean`. About 80 lines. Blocked by 1 and #860.
5. **Periods of closed forms on integral singular homology.**
   `SmoothSingular/SingularPeriod.lean`, with the change of coefficients on
   chains in `SimplicialSet/Homology/RestrictScalars.lean`. About 300 lines.
   No blockers.
6. **Relative cycles and smooth chains.** `SmoothSingular/RelativeCycle.lean`.
   About 250 lines. No blockers.
7. **Positively oriented simplices in local homology.**
   `LocalHomology/Orientation/Simplex.lean`, with the sign of Decision 6
   recorded here. About 400 lines. No blockers.
8. **Integration against the fundamental class of a surface.**
   `DeRham/FundamentalClass.lean`. About 350 lines. Blocked by 5, 6 and 7.
9. **Topological invariance, and the milestone.** `Energy/Homology.lean`.
   About 200 lines. Blocked by 3 and 8.

Issues 1, 5, 6 and 7 can start at once. Before starting, 5–8 check whether
Tau Ceti has done their work since the pin; if a move of Tau Ceti brings it,
the issue uses it instead and this file is updated.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §4.5, equation (4.5.4) and the paragraph after it.
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.][McDuffSalamon2012],
  §2.2.
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  equation (2.6), Definition 2.18, Proposition 2.19.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in
  Mathematics 218, Springer, 2013, Chapters 16 and 18.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002,
  §2.1 and §3.3.
