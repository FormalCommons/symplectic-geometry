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

The declarations and files of Tau Ceti named under *What there is* were
checked against the pinned Tau Ceti `c9d170eed5a8` (see `lakefile.toml`).
The rest of the file was written against Tau Ceti `v4.37.0-rc1` and its
later commit `464618e8a5`, both of which `c9d170eed5a8` contains. Paths of
Tau Ceti files are relative to `.lake/packages/TauCeti/TauCeti/`.

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
  $\mathbb R^2$ with a measure; the energy of a map from a closed surface
  is in the file of the next item.
- **The energy of a map from a surface**
  (`Geometry/Symplectic/Manifold/Energy/Surface.lean`, added in Tau Ceti's
  commit `464618e8a5` and pinned since the move to `c9d170eed5a8`, #2025),
  in `TauCeti.SmoothTwoForm`:
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
  the hypothesis `finrank ℝ (TangentSpace I c) = 2` in place of an
  orientation `o`.
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

Missing at the pin: the first display of the milestone for maps that are
not pseudoholomorphic (the $\bar\partial$ term), the reading of the energy
through an area form and its independence of it, and the comparison
$\int_\Sigma\varphi=\langle[\varphi],[\Sigma]\rangle$ of `integralTopForm`
with the pairing against a fundamental class. Tau Ceti's one result that
involves both is the degree formula
`TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_degree_toHomologicalOrientation_mul`
(`Geometry/Manifold/Degree/Homological.lean`), which does not give that
comparison. Pinned since the move to `c9d170eed5a8` (#2025),
`Geometry/Manifold/SmoothSingular/Period.lean` pairs de Rham
classes with integral *smooth* singular homology
(`deRhamCohomology.smoothHomologyPeriod`, built on a version of
`integrationCochain` generalized to integer coefficients) and
`SingularCohomology.lean` adds the de Rham homomorphism `deRhamHom` into
real singular cohomology.

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
   Tau Ceti's `energy`, the integral of its `energyForm`, and the
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
4. **Regularity.** Integrals are added only for integrable forms. Tau Ceti's
   `isSmoothForm_energyForm` says that the energy form of a $C^1$ map
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
   naturality under smooth maps. It is Tau Ceti's
   `closedFormHomologyPeriod φ`, on `H₂(M; ℤ)` with coefficients the ring
   `ℤ`; since `mapFundamentalClass` has coefficients `ULift ℤ`, a class `A`
   is read in it as `(uliftIntHomologyIso (TopCat.of M) 2).hom.hom A`. The
   two properties are `closedFormHomologyPeriod_homologyMap_ι_homologyπ`
   and `closedFormHomologyPeriod_mpullback` (with
   `homologyMap_comp_uliftIntHomologyIso_hom`).
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
7. **Relative cycles from Tau Ceti's relative smoothing theorem.** The local
   step needs: if a smooth cycle $z$ and a smooth chain $\sigma$ with boundary
   in an open $U$ have the same class in the continuous relative homology
   $H_2(M,U)$, then $z-\sigma=\partial b+c$ with $b$ smooth and $c$ a smooth
   chain in $U$. This follows from Tau Ceti's relative smoothing theorem in
   `TauCeti/Geometry/Manifold/SmoothSingular/Relative.lean`: the pair
   `TauCeti.smoothSingularPair`, its inclusion `TauCeti.smoothSingularPairι`
   into the pair of continuous simplices, and the instance
   `TauCeti.quasiIso_chainComplexMap_smoothSingularPairι`; it is one lemma.
8. **Tau Ceti's energy is used as it is.** The energy of a map from a
   surface is Tau Ceti's `Energy/Surface.lean`, and the library defines no
   `energyForm` or `energy` of its own. Before the pinned version had that
   file, issue 2 copied it, through its section on compact surfaces, with
   `SmoothBundleForm.contMDiffAt_eval₂`, as *Files* in `AGENTS.md` says,
   rather than block issue 3 and the milestone on a move of Tau Ceti. The
   move to `c9d170eed5a8` (#2025) deleted both copies, and the library uses
   Tau Ceti's declarations.

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
| `LinearAlgebra/Complex/StdComplexLine.lean` | the images of `stdComplexLineReal` and `stdComplexLineImag` under `(a, s) ↦ a • v + s • w`, used by `Density.lean` |
| `Geometry/Symplectic/Manifold/AlmostComplex/TopForm.lean` | top forms on a tangent plane of an almost complex surface: equality and ratios read on one frame $(e,je)$, without an orientation |
| `LinearAlgebra/Complex/TopForm.lean` | the same on a real plane with a complex structure |
| `Geometry/Symplectic/JHolomorphic/Energy/Metric.lean` | the squared norm read in $g_J$ |
| `Geometry/Symplectic/JHolomorphic/Energy/Surface.lean` | Tau Ceti's energy form read through `energyDensity`, the energy through an area form, the integrated identity, zero energy and local constancy |
| `Geometry/Manifold/MFDeriv/Constancy.lean` | a locally constant map has zero differential, `IsLocallyConstant.mfderiv_eq_zero`, for the file above |
| `AlgebraicTopology/SimplicialSet/Homology/RestrictScalars.lean` | the change of coefficients on simplicial chains along a restriction of scalars, `SSet.restrictScalarsChainMap`, and its isomorphism form `SSet.restrictScalarsChainIso` |
| `Geometry/Manifold/SmoothSingular/RelativeCycle.lean` | the relative step of Decision 7 |
| `AlgebraicTopology/SimplicialSet/Homology/RelativeClass.lean` | the relative class of a simplex whose faces lie in the subcomplex of a pair of simplicial sets, `SSetPair.relClass` |
| `AlgebraicTopology/SimplicialSet/Homology/One.lean` | naturality of the class of a closed $1$-simplex under maps of simplicial sets, `SSet.ιHomology₁_homologyMap` |
| `AlgebraicTopology/Singular/RelativeClass.lean` | the relative class of a singular simplex whose faces lie in the subspace, `TopPair.relClass` |
| `AlgebraicTopology/Singular/LocalHomology/Orientation/StdSimplex.lean` | the class of the standard $2$-simplex in the local homology of $\mathbb R^2$ at an interior point, and the sign $s$ of Decision 6 |
| `AlgebraicTopology/Singular/LocalHomology/Orientation/Simplex.lean` | the class of a positively oriented simplex in local homology, in dimension two |
| `Geometry/Manifold/DeRham/FundamentalClass.lean` | $\int_\Sigma\varphi=\langle[\varphi],[\Sigma]\rangle$ on closed oriented surfaces |
| `Geometry/Manifold/Orientation/Preserving.lean` | a map of a real normed space with positive Jacobian determinant preserves orientation, for the file above |
| `Geometry/Symplectic/JHolomorphic/Energy/Homology.lean` | topological invariance, minimality, the milestone |

The `Energy/` folder sits beside Tau Ceti's folder of the same name, as
`DESIGN.md` says. The files outside it are general manifold topology or linear algebra
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
  from Tau Ceti's `Compatible.metric_inner`.
  This is the page's reading of $\lvert\eta\rvert^2$ through a unit vector, in
  the metric $g_J$ as a Riemannian metric. Separate from `Density.lean` so
  that only this file waits for `Metric.lean`.

### Tau Ceti's `Manifold/Energy/Surface.lean`

The declarations listed under *What there is* for this file, in the
namespace `TauCeti.SmoothTwoForm` (Decision 8). The part
uses in particular `energyForm`, `energyForm_apply`,
`isSmoothForm_energyForm`, `energy`, `energy_def`,
`energy_eq_integralTopForm_mpullback` (the pseudoholomorphic case),
`Tames.energy_nonneg`, `Tames.energy_eq_zero_iff` (for compact `C`, `ho`,
`ω.Tames J` and `hu : ContMDiff I' I 1 u`,
`ω.energy J j o u = 0 ↔ ∀ c, mfderiv I' I u c = 0`) and
`Compatible.integralTopForm_mpullback_le_energy`. Tau Ceti states the
pullback as `mpullback I' I u ω.val`, and so does the rest of this design.

### `JHolomorphic/Energy/Surface.lean`

It imports Tau Ceti's `Manifold/Energy/Surface.lean`, and
`Energy/Density.lean`, `Manifold/AlmostComplex/TopForm.lean` and
`Geometry/Manifold/MFDeriv/Constancy.lean`, and defines nothing.

- `energyForm_apply_eq_energyDensity`: on a plane (`h2 : finrank ℝ E' = 2`),
  `ω.energyForm J j u c = ω.energyDensity J j (mfderiv I' I u c).toLinearMap`.
  Both sides agree on a frame by `energyForm_apply_frame_eq_stdComplexLineEnergyDensity`
  and `energyDensity_apply_complexFrame_eq_stdComplexLineEnergyDensity`, hence
  everywhere by `SmoothAlmostComplexStructure.topForm_ext` (Decision 1).
- `energy_eq_half_integralTopForm_normSq`: for `hdvol : dvol.Tames j`,
  `ω.energy J j o u = 1 / 2 * integralTopForm o (fun c ↦ ω.normSq J j dvol (mfderiv I' I u c).toLinearMap • dvol.val c)`.
  This is the independence of the area form: the left side has none.
- `Invariant.energy_eq_integralTopForm_add`: for `ω.Invariant J`, compact `C`,
  `hdvol` and `hu : ContMDiff I' I 1 u`,
  `ω.energy J j o u = integralTopForm o (fun c ↦ ω.normSq J j dvol (complexAntilinearPart … (mfderiv I' I u c).toLinearMap) • dvol.val c) + integralTopForm o (mpullback I' I u ω.val)`.
- `Tames.energy_eq_zero_iff_isLocallyConstant`: for compact `C`, `ho`,
  `ω.Tames J` and `hu`, `ω.energy J j o u = 0 ↔ IsLocallyConstant u`, from
  Tau Ceti's `Tames.energy_eq_zero_iff`,
  `MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero`
  (`Geometry/Manifold/MFDeriv/Constancy.lean`) and its converse
  `IsLocallyConstant.mfderiv_eq_zero` (the library's file of the same path). Tau Ceti's
  `Tames.apply_eq_of_energy_eq_zero` is the connected case; the milestone
  speaks of local constancy.
- `Compatible.energy_identity`: the analytic half of the milestone, the
  conjunction, for compact `C`, `hc : ω.Compatible J`, `hu : ContMDiff I' I 1 u`
  and every `dvol` taming `j`, of the first display (in the form of
  `Invariant.energy_eq_integralTopForm_add` with the left side written
  through `energy_eq_half_integralTopForm_normSq`), the pseudoholomorphic
  case, and the independence of `dvol`. No milestone line; the milestone is
  in `Homology.lean`.

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
  the classes it compares to such a decomposition. Proof: Tau Ceti's
  `TauCeti.smoothSingularPairι` maps `TauCeti.smoothSingularPair` to the
  pair of continuous simplices of `(M, U)`, and is a quasi-isomorphism on
  relative chains (`TauCeti.quasiIso_chainComplexMap_smoothSingularPairι`);
  the image of `w` in the smooth
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
  compute the local image at each point of `K`. There `g`, read on `U`, and
  the inclusion of `U` into $\mathbb R^2$ preserve orientation, so they carry
  local orientations to local orientations
  (`TauCeti.Manifold.Orientation.localHomologyMap_toHomologicalOrientation`,
  in `Orientation/Smooth.lean` of part *First Chern number*, from Tau Ceti's
  `localIndex_toHomologicalOrientation`), and this reduces to the standard
  simplex of `StdSimplex.lean`, which fixes the sign $s$.
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
  `LinearAlgebra/Complex/Orientation.lean`,
  `AlgebraicTopology/Singular/LocalHomology/Orientation/Plane.lean` and
  `AlgebraicTopology/Singular/LocalHomology/Orientation/Smooth.lean` of part
  *First Chern number*.

### `DeRham/FundamentalClass.lean`

- `TauCeti.Manifold.Orientation.integralTopForm_eq_closedFormHomologyPeriod`
  (the name follows the orientation used): for a closed surface `C` as in
  *Conventions*, oriented by `o`, and `φ : closedForms 𝓘(ℝ, E') C 2` (every two-form
  is closed, by `mextDeriv_eq_zero_of_finrank_le`),
  `integralTopForm o φ.val.val = closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of C) 2).hom.hom (oₕ.fundamentalClass hE'))`
  with `oₕ` the correctly signed homological orientation. Route: every
  point has a positively oriented simplex chart (the inverse of an oriented
  chart, `exists_partialDiffeomorph_isOrientationPreservingAt` of Tau Ceti, and a
  small affine simplex in its target); a smooth partition of unity subordinate to
  the interiors of finitely many of them splits `φ` into forms `ρᵢ • φ`
  supported in compact sets `Kᵢ`; both sides are additive in `φ`. For one
  piece choose a smooth integral cycle `z` representing the fundamental
  class (smoothing). Its image in $H_2(C,C\setminus K_i)$ is the class along
  `Kᵢ` (Tau Ceti), so is that of the simplex `σᵢ` (`Simplex.lean`), and the
  relative step gives `z - σᵢ = ∂ b + c` with `c` in `C ∖ Kᵢ`. Hence
  $\int_z\rho_i\varphi=\int_{\sigma_i}\rho_i\varphi$ (Stokes for `b`, and
  `ρᵢ • φ` vanishes on `c`), which is `integralTopForm o (ρᵢ • φ)` by
  `SmoothSimplex.integral_eq_integralTopForm`.
- `TauCeti.Manifold.Orientation.integralTopForm_mpullback_eq_closedFormHomologyPeriod`:
  for `hE'`, `o`, `φ : closedForms I M 2` and smooth `u : C → M`,
  `integralTopForm o (mpullback I' I u φ.val.val) = closedFormHomologyPeriod φ ((uliftIntHomologyIso (TopCat.of M) 2).hom.hom (oₕ.mapFundamentalClass hE' ⟨u, hu.continuous⟩))`,
  from the previous result for `u^* φ`, `closedFormHomologyPeriod_mpullback`
  and `homologyMap_comp_uliftIntHomologyIso_hom`.

### `Energy/Homology.lean`

With `oₕ` as above, `A` an integral class of $H_2(M)$, `hω : ω` closed, and
`hA : oₕ.mapFundamentalClass hE' ⟨u, hu.continuous⟩ = A` ("$u$ represents
$A$"), with `Aℤ = (uliftIntHomologyIso (TopCat.of M) 2).hom.hom A` its class with
coefficients the ring `ℤ`:

- `energy_eq_closedFormHomologyPeriod`: for `∀ c, IsPseudoholomorphicAt j J u c`,
  `ω.energy J j o u = closedFormHomologyPeriod ⟨ω, hω⟩ Aℤ`.
- `Compatible.energy_le_energy`: for `hc`, `ho`, pseudoholomorphic `u` and
  any smooth `v : C → M` representing the same `A`,
  `ω.energy J j o u ≤ ω.energy J j o v` (both areas are the period of `A`,
  and Tau Ceti's `Compatible.integralTopForm_mpullback_le_energy` bounds
  that of `v` by its energy).
- `Tames.closedFormHomologyPeriod_pos`: for `ω.Tames J` (a compatible pair
  gives it), `ho` and pseudoholomorphic `u`
  that is not locally constant, `0 < closedFormHomologyPeriod ⟨ω, hω⟩ Aℤ`.
- **Milestone** `Compatible.energy_identity_and_homology`: the conjunction of
  `Compatible.energy_identity` and, for closed `ω`,
  `energy_eq_closedFormHomologyPeriod`, `Compatible.energy_le_energy` and
  `Tames.closedFormHomologyPeriod_pos`, with the energy written as in
  `Compatible.energy_identity`, through
  `energy_eq_half_integralTopForm_normSq`. Milestone: *Energy identity for
  J-holomorphic curves*.

## Main results

| Result | Lean name | File |
|---|---|---|
| pointwise identity | `TauCeti.SmoothTwoForm.Invariant.energyDensity_eq_two_smul_add` | `Density.lean` |
| independence of the area form | `TauCeti.SmoothTwoForm.energy_eq_half_integralTopForm_normSq` | `JHolomorphic/Energy/Surface.lean` |
| integrated identity | `TauCeti.SmoothTwoForm.Invariant.energy_eq_integralTopForm_add` | `JHolomorphic/Energy/Surface.lean` |
| pseudoholomorphic case | `TauCeti.SmoothTwoForm.energy_eq_integralTopForm_mpullback` (Tau Ceti) | Tau Ceti's `Manifold/Energy/Surface.lean` |
| zero energy | `TauCeti.SmoothTwoForm.Tames.energy_eq_zero_iff_isLocallyConstant` | `JHolomorphic/Energy/Surface.lean` |
| integration against $[\Sigma]$ | `TauCeti.Manifold.Orientation.integralTopForm_eq_closedFormHomologyPeriod` | `DeRham/FundamentalClass.lean` |
| the milestone | `TauCeti.SmoothTwoForm.Compatible.energy_identity_and_homology` | `Homology.lean` |

The tame case of the page's notes (the symmetrized metric) is not a
milestone. The densities are defined for any `ω` and `J`, and the
pseudoholomorphic case and positivity need only `Tames`, so it costs nothing
later.

## What it uses

- From Tau Ceti: `Compatible.metric` and `Compatible.metric_inner`
  (`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/CompatibleMetric.lean`), for `Energy/Metric.lean` only.
- From Tau Ceti: the declarations of *What there is*, its
  `Manifold/Energy/Surface.lean` included (Decision 8).
- From Mathlib: `SmoothPartitionOfUnity`,
  `AlternatingMap.eq_smul_basis_det`, `IsLocallyConstant`.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **Energy densities.** `Energy/Density.lean`, all of it, with
   `Manifold/AlmostComplex/TopForm.lean`, which it imports. About 350
   lines. No blockers.
2. **Tau Ceti main's energy of a map from a surface.** The copy of
   Decision 8: `Manifold/Energy/Surface.lean` and the `FromTauCeti.lean`
   file. About 550 lines, nearly all copied. No blockers. The move to
   `c9d170eed5a8` (#2025) deleted these copies.
3. **The energy and its identity.** `JHolomorphic/Energy/Surface.lean`, all
   of it, with `Compatible.energy_identity`. About 250 lines. Blocked by 2.
4. **The squared norm in the metric of a compatible pair.**
   `Energy/Metric.lean`. About 80 lines. Blocked by 1 and #860.
5. **Periods of closed forms on integral singular homology.**
   `SmoothSingular/SingularPeriod.lean`, with the change of coefficients on
   chains in `SimplicialSet/Homology/RestrictScalars.lean`. About 300 lines.
   No blockers. Tau Ceti's `closedFormHomologyPeriod` has since replaced
   `SingularPeriod.lean`, which was deleted (#2211).
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
