# Kähler stability

This is the detailed design of part 44 of `DESIGN.md`, *Kähler stability*.
It proves two milestones of `atlas/symplectic-group-actions.md`, the
*Kempf–Ness correspondence* and the *Hilbert–Mumford numerical criteria*,
following McDuff–Salamon [McDuffSalamon2017], §5.7 (equations
(5.7.2)–(5.7.4) and Theorem 5.7.2), and Georgoulas–Robbin–Salamon
[GeorgoulasRobbinSalamon2021] (arXiv v2: Lemma 2.1, Theorems 4.1 and 4.3,
Definition 7.1, Theorem 7.3, Theorems 12.2, 12.5 and 12.6). The convergence
of the gradient flow of $\tfrac12\|\mu\|^2$ follows Lerman (E. Lerman,
*Gradient flow of the norm squared of a moment map*, Enseign. Math. 51
(2005), 117–127), whose proof needs a Łojasiewicz inequality and a local
normal form; for the normal form, Marle (C.-M. Marle, *Modèle d'action
hamiltonienne d'un groupe de Lie sur une variété symplectique*, Rend. Sem.
Mat. Univ. Politec. Torino 43 (1985)) and Guillemin–Sternberg
[GuilleminSternberg1990]; for the semialgebraic Łojasiewicz inequality,
Bochnak–Coste–Roy (*Real Algebraic Geometry*, Springer, 1998, §2.5–2.6).

Paths of new files are under `SymplecticGeometry/`, Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`, and the Tau Ceti declarations
named below were checked against the pinned version `c9d170eed5a8`. The
statements below fix the mathematics and the names; the building issues
may adjust implicit arguments and instance arguments to what elaborates.

## Setting and conventions

- `G` is a Lie group over `I : ModelWithCorners ℝ E H` (`[LieGroup I ∞ G]`,
  `E` finite-dimensional, no boundary), compact and connected; its Lie
  algebra is `𝔤 := GroupLieAlgebra I G` and its exponential
  `mulInvariantExp`.
- `M` is a manifold over `I' : ModelWithCorners ℝ E' H'`, compact,
  connected, without boundary, with `σ : TauCeti.SmoothTwoForm I' M`,
  `J : TauCeti.SmoothAlmostComplexStructure I' M` and `σ.IsKahler J`. The
  metric is $g_J(v,w)=\sigma(v,Jw)$, installed as a local
  `RiemannianBundle` instance through Tau Ceti's `Compatible.metric`, as
  `DESIGN.md` says under *Almost complex structures, Kähler manifolds and
  characteristic classes*. `tendsto_limitPoint` takes `I' = 𝓘(ℝ, E')`, the
  model of Tau Ceti's Morse–Bott theorems on components of a moment map.
- `G` acts smoothly (`[MulAction G M] [ContMDiffSMul I I' ∞ G M]`) and each
  `g • ·` preserves `σ` and `J`; these are hypotheses, not a predicate, as
  `DESIGN.md` says for symplectic actions.
- **Sign.** `μ : M → Module.Dual ℝ 𝔤` is the page's moment map, so the
  hypothesis is `σ.IsEquivariantMomentMap (fun x ↦ -μ x)` (*Group actions,
  moment maps and periods* in `DESIGN.md`). With it,
  $\operatorname{grad}\langle\mu,\xi\rangle=-JX_\xi$ (this follows from
  $g_J(v,w)=\sigma(v,Jw)$ and $d\langle\mu,\xi\rangle=-\iota_{X_\xi}\sigma$),
  so $t\mapsto\langle\mu(\exp(it\xi)p),\xi\rangle$ is antitone with
  derivative $-|X_\xi|^2$. This fixes every sign of both milestones as the
  page states them: semistability is $w_\mu\le0$, stability $w_\mu<0$.
- **Inner product.** `B : LinearMap.BilinForm ℝ 𝔤`, symmetric, positive
  definite and `Ad`-invariant, as
  `TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`
  gives it, already on `GroupLieAlgebra I G`, the tangent space `E` at `1`
  on which `IsEquivariantMomentMap` and `Lie.adjointRepresentation` live
  (as a continuous bilinear map, invariant under
  `adjointContinuousLinearMap`). `B` gives $\mu^\sharp(x)\in\mathfrak g$
  (`B.toDual` inverted on `μ x`) and $\|\mu(x)\|^2=B(\mu^\sharp x,\mu^\sharp x)$,
  in `MomentMap/NormSq.lean`.
- **No holomorphic charts.** The proofs use only that `σ` is closed and
  that `J` is compatible with it, together with the infinitesimal
  holomorphicity $X_{i\xi}=JX_\xi$ of the complexified action. The
  integrability of `J`, and Tau Ceti's condition $N_J=0$, are never used.
  The statements still take `σ.IsKahler J`, as the page does, so the
  *Kähler* bullet of `DESIGN.md` needs no added hypothesis.

## Decisions

1. **$G^{\mathbb C}$ is data with hypotheses.** Neither Mathlib nor Tau
   Ceti constructs the complexification of a compact Lie group: Tau Ceti
   has its Lie algebra for $\mathrm U(n)$, $\mathrm{SU}(n)$ and
   $\mathrm{SO}(n)$ (`Geometry/Lie/Subgroup/Complexification.lean`) and the
   faithful unitary embedding of a compact Lie group
   (`TauCeti.Lie.exists_injective_contMDiffMonoidMorphism_matrixUnitarySubgroup`),
   but no group $G\exp(i\mathfrak g)$. Constructing one, a closed subgroup
   of $\mathrm{GL}(n,\mathbb C)$, would need Chevalley's algebraicity
   theorem, which the milestones do not use. So the part has a structure
   `LieComplexification I G IC Gc` with the following fields. `Gc` is a
   real Lie group over `IC`, and `toHom` is an injective
   `ContMDiffMonoidMorphism` from `G` to `Gc`. Its derivative at `1`,
   `C.lieMap`, is a definition and not a field: Tau Ceti's
   `ContMDiffMonoidMorphism.groupLieAlgebraLieHom`, with `map_lieExp` for
   its exponential (`Geometry/Lie/Functor.lean`). Then
   `cplx` is a `TauCeti.AlmostComplexStructure` on `GroupLieAlgebra IC Gc`
   that commutes with each `ad` (a complex Lie algebra). The range of
   `lieMap` is `TauCeti.IsMaximalTotallyReal` for `cplx`, so that it and
   the range of `cplx ∘ lieMap` are complementary. Finally there is
   `polar : (E × G) ≃ₘ⟮_, IC⟯ Gc`, with `𝔤` read as its model space `E` (the
   tangent space has no charted-space instance), a diffeomorphism with
   `polar (ξ, u) = mulInvariantExp (cplx (lieMap ξ)) * toHom u`. All the
   milestones' conclusions are about $\Phi_p$, $\mu$ and orbits, and none of
   these fields is one of them, as the review of #2250 asks. The complex
   manifold structure of $G^{\mathbb C}$ is not needed: the proofs use only
   the complex structure of its Lie algebra and the polar decomposition.
   The structure has an example: `Circle` in `ℂˣ`, with `cplx`
   multiplication by `I` and `polar (ξ, u) = exp (I * lieMap ξ) * u`
   (Mathlib's `Complex.exp`, `Circle`), which is `exp (-t) * u` where
   `lieMap ξ = t I`.
2. **The holomorphic extension of the action** is a predicate
   `IsComplexifiedAction C J` on
   `[MulAction Gc M] [ContMDiffSMul IC I' ∞ Gc M]`. It says that
   `C.toHom u • x = u • x`, and that, with Tau Ceti's
   `TauCeti.fundamentalVectorField`,
   `fundamentalVectorField (C.cplx (C.lieMap ξ)) x = J x (fundamentalVectorField (C.lieMap ξ) x)`
   for all `ξ` and `x`. This is the page's "extends holomorphically",
   read at the level of fundamental vector fields; the proofs need nothing
   more. Its example is the action of `ℂˣ` on `ℂ` by multiplication, which
   extends the rotation action of `Circle` through the example of
   decision 1, with `J` multiplication by `I`.
3. **Geodesics and the quotient.** The decomposition is
   $G^{\mathbb C}=\exp(i\mathfrak g)G$ (`polar`), so $G^{\mathbb C}/G$ is the
   space of cosets $gG$. "Descends to $G^{\mathbb C}/G$" is the
   invariance $\Phi_p(gu)=\Phi_p(g)$ for $u\in G$, with the induced
   function on `Gc ⧸ C.toHom.range` through `Quotient.lift`.
   "Convex along geodesics" is that
   `t ↦ Φ_p (g * mulInvariantExp (t • C.cplx (C.lieMap ξ)))` is `ConvexOn ℝ univ`
   for every `g` and `ξ`, the form in which [GeorgoulasRobbinSalamon2021]
   uses it; no Riemannian metric on $G^{\mathbb C}/G$ is defined. The
   left-trivialized derivative $g^{-1}\widehat g$ is
   `mfderiv IC IC (g⁻¹ * ·) g ĝ`, in the Lie algebra `TangentSpace IC 1`,
   and `C.im : GroupLieAlgebra IC Gc →ₗ[ℝ] 𝔤` is the component along
   `cplx ∘ lieMap` of the decomposition of decision 1.
4. **The Łojasiewicz inequality is proved here, by Lerman's route.** Tau
   Ceti has convergence of a gradient trajectory given the inequality on a
   normed space (`IsIntegralCurveOn.exists_tendsto_atTop_of_lojasiewicz`), its
   Morse–Bott case on manifolds
   (`Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`), Tarski–Seidenberg
   (`TauCeti.HasSemialgebraicProjections ℝ`, `Geometry/RealAlgebraic/CAD/Existence.lean`)
   with semialgebraic sets and functions (`Geometry/RealAlgebraic/Semialgebraic/`),
   and the linear part of the local normal form, the symplectic slice
   (`Geometry/Symplectic/Hamiltonian/MomentMap/Slice.lean`). It has no
   Łojasiewicz inequality for analytic or polynomial functions. The
   inequality for $f=\tfrac12\|\mu\|^2$ needs only the polynomial case:
   in the Marle–Guillemin–Sternberg model $G\times_H(\mathfrak m^*\times V)$
   of a neighbourhood of an orbit, $\mu[g,\eta,v]=\operatorname{Ad}^*_g(\tau+\eta+\mu_V(v))$
   with $\mu_V$ quadratic, so, $B$ being invariant, $f$ is a polynomial in
   $(\eta,v)$ composed with a submersion. So the part proves:
   (a) the curve selection lemma for semialgebraic sets over `ℝ`, and the
   growth of a one-variable semialgebraic function near `0`; (b) the
   gradient inequality for real polynomials,
   $|P(x)-P(x_0)|^\theta\le c\,|\nabla P(x)|$ near $x_0$ with
   $\theta\in[\tfrac12,1)$; (c) the local normal form in the weak form that
   (d) needs: near every point, a chart of $M$ in which $\|\mu\|^2$ is a
   polynomial in some of the coordinates; (d) the inequality for $f$ on
   $M$; (e) convergence on a Riemannian manifold, which is Tau Ceti's
   `tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`. The analytic inequality is not
   needed and is not proved.
5. **The limit points $p^+_\xi$** for $\xi\in\Lambda$ do not need (d): the
   orbit $t\mapsto\exp(it\xi)p$ is the negative gradient flow of
   $\langle\mu,\xi\rangle$, which is Morse–Bott for a circle action (Tau
   Ceti's `MomentMap/MorseBott.lean`,
   `exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace`),
   so Tau Ceti's Morse–Bott inequality `exists_mul_abs_sub_le_norm_mgradient_sq`
   with (e) gives the limit; issue 11 takes it from Tau Ceti's
   `Morse/Bott/ExponentialConvergence.lean`. The weights $w_\mu(p,\xi)$ exist for every
   $\xi$, by monotonicity and compactness of $M$.
6. **Home.** The complexification is Lie theory, so it is
   `Geometry/Lie/Complexification.lean`, beside Tau Ceti's folder
   `Geometry/Lie/Subgroup/` (Tau Ceti has no file of that name there). The
   Kähler files cannot go in `Geometry/Symplectic/Manifold/Kahler/`, since
   Tau Ceti has the file `Geometry/Symplectic/Manifold/Kahler.lean` (where
   `IsKahler` is) and the library's own merged `Manifold/Kahler.lean` has
   that path too (*Files do not clash with Tau Ceti's*, `DESIGN.md`). They
   are moment-map theory and go in Tau Ceti's folder
   `Geometry/Symplectic/Hamiltonian/MomentMap/`, under `KempfNess/` and
   `HilbertMumford.lean`. This replaces the folder `Geometry/Symplectic/Kahler/`
   that `DESIGN.md` first gave, and `DESIGN.md` now names these files.
7. **The moment limit theorem uses no moment-weight inequality.** The
   proof of [GeorgoulasRobbinSalamon2021] (arXiv v2, Theorem 6.4)
   compares two flow lines $g,\tilde g$ of $\Phi_p$ in $G^{\mathbb C}$, from
   $1$ and from any $g_0$. It uses that their distance in $G^{\mathbb C}/G$
   does not increase (Lemma A.2), and Ness's uniqueness theorem for
   critical points of $\|\mu\|^2$ in one $G^{\mathbb C}$-orbit (Theorem 6.3),
   by the second proof given there, due to Calabi–Chen, which uses the
   same lemma. Neither step uses weights,
   so the moment-weight inequality stays in issue 12 and the build order
   does not change. With no metric on $G^{\mathbb C}/G$, the distance is
   replaced by the polar radius: for $a=\exp(i\eta)u$ (`C.polar.symm a`),
   the number $B(\eta,\eta)$. Its derivative along a curve is a Gauss
   lemma for the polar decomposition, proved from Tau Ceti's derivative of
   the exponential (`LeftInvariantDerivation.hasMFDerivAt_lieExp`,
   `Geometry/Lie/Exponential/Derivative/Formula.lean`) and the
   $\operatorname{ad}$-invariance of $B$
   (`TauCeti.Lie.lieInvariant_iff_adjoint_invariant`). The geodesic from
   $g$ to $\tilde g$ is $s\mapsto g\exp(is\eta)$, and its two end slopes are
   given by `hasDerivAt_kempfNessFunction_geodesic`, so the monotonicity
   is `antitone_moment_expI` and needs no second variation.

## Files

- `Geometry/Lie/Complexification.lean`: `LieComplexification`, its API
  (`expI`, `im`, `re`, `lieMap_re_add_cplx_lieMap_im`, `polar_apply`,
  `connectedSpace` from connectedness of `G`, `toHom` a closed embedding),
  the circle example, and the Gauss lemma of decision 7.
- `Geometry/RealAlgebraic/Semialgebraic/CurveSelection.lean`: decision 4 (a).
- `Analysis/Calculus/Lojasiewicz/Polynomial.lean`: decision 4 (b), in Tau
  Ceti's folder `Analysis/Calculus/Lojasiewicz/`.
- `Geometry/Manifold/Riemannian/Gradient/Lojasiewicz.lean`: decision 4 (e).
- `Geometry/Symplectic/Hamiltonian/MomentMap/LocalNormalForm.lean`:
  decision 4 (c).
- `Geometry/Symplectic/Hamiltonian/MomentMap/NormSq.lean`: $\mu^\sharp$
  and $\|\mu\|^2$, for any Lie group and any map `μ`.
- In `Geometry/Symplectic/Hamiltonian/MomentMap/KempfNess/`:
  `Basic.lean` (`IsComplexifiedAction`, the stability predicates, the
  gradient of $\langle\mu,\xi\rangle$ and the
  derivative along $\exp(it\xi)$), `Function.lean` ($\Phi_p$ and the
  first half of the milestone), `NormSquare.lean` (the gradient flow of
  $f$, its Łojasiewicz inequality, convergence, Ness's uniqueness theorem
  and the moment limit), and
  `Stability.lean` (the boundedness and properness criteria and the
  milestone).
- `Geometry/Symplectic/Hamiltonian/MomentMap/HilbertMumford.lean`:
  weights, limit points, the slope identity, the moment-weight inequality
  and the criteria.

## Definitions and their API

All in `SymplecticGeometry`, with `C : LieComplexification I G IC Gc`.

- `C.expI ξ := mulInvariantExp (C.cplx (C.lieMap ξ))`, with `expI_zero`,
  `expI_add_smul` for `s t : ℝ`
  (`expI ((s + t) • ξ) = expI (s • ξ) * expI (t • ξ)`), and
  `C.toHom u * C.expI ξ * (C.toHom u)⁻¹ = C.expI (Ad u ξ)` for connected `G`.
- `IsComplexifiedAction C J` (decision 2), with
  `IsComplexifiedAction.fundamentalVectorField_cplx` and
  `isMIntegralCurve_expI_smul` (the velocity of $t\mapsto\exp(it\xi)p$ is
  $JX_\xi$ at the moving point).
- `momentSharp B hB μ x : 𝔤` and `momentNormSq B hB μ x : ℝ`, with
  `B (momentSharp …) ξ = μ x ξ`, `momentNormSq_nonneg`,
  `momentNormSq_eq_zero_iff`, invariance under `G`, and smoothness.
- `IsSemistable C μ p : Prop` ($\exists x\in\overline{G^{\mathbb C}p}$ with
  $\mu(x)=0$), `IsPolystable C μ p` ($\exists x\in G^{\mathbb C}p$ with
  $\mu(x)=0$), `IsStable C μ p` (polystable and
  `DiscreteTopology (MulAction.stabilizer Gc p)`), each with its `_iff`
  lemma, invariance along `Gc`-orbits, and
  `IsStable.isPolystable`, `IsPolystable.isSemistable`; and
  `polystableLocus C μ : SubMulAction Gc M`.
- `kempfNessFunction C μ p : Gc → ℝ`, written $\Phi_p$, defined through
  `polar`: `Φ_p (expI ξ * toHom u) = ∫ t in 0..1, μ (expI (-(t • ξ)) • p) ξ`,
  with `kempfNessFunction_polar` as its defining lemma.
- `momentWeight C μ p ξ : ℝ`, the limit of `μ (C.expI (t • ξ) • p) ξ` as
  `t → ∞` (`limUnder atTop`), with `tendsto_momentWeight`, and
  `limitPoint C p ξ : M`, with `tendsto_limitPoint` for every `ξ`.
- `nonzeroPeriods I G : Set 𝔤 := {ξ | ξ ≠ 0 ∧ mulInvariantExp ξ = 1}`,
  written $\Lambda$, invariant under `Ad` and under positive integer
  multiples, in `Geometry/Lie/Exponential/Periods.lean`.

## Main results

### `Geometry/Lie/Complexification.lean` (the polar radius)

For connected `G` and a symmetric `Ad`-invariant `B`, so that `B` is also
`ad`-invariant (`TauCeti.Lie.lieInvariant_iff_adjoint_invariant`):

- `polar_symm_inv`: if `C.polar.symm a = (η, u)` then
  `C.polar.symm a⁻¹ = (-Ad u⁻¹ η, u⁻¹)`, from `toHom_mul_expI_mul_inv`.
- `hasDerivAt_polar_symm_fst_comp` (the Gauss lemma): for a curve
  `a : ℝ → Gc` differentiable at `t`, with `(η, u) = C.polar.symm (a t)`,
  `s ↦ B (C.polar.symm (a s)).1 (C.polar.symm (a s)).1` has at `t` the
  derivative `2 * B (Ad u⁻¹ η) (C.im (a⁻¹ ȧ))`, where `a⁻¹ ȧ` is
  `mfderiv IC IC ((a t)⁻¹ * ·) (a t) (Manifold.curveVelocity IC a t)`. Proof:
  differentiate `a = expI η * toHom u`, with `η` and `u` differentiable at `t`
  because `polar` is a diffeomorphism. By
  `LeftInvariantDerivation.hasMFDerivAt_lieExp` (with
  `lieExp_eq_mulInvariantExp`), the imaginary part of
  $a^{-1}\dot a$ is $\operatorname{Ad}_{u^{-1}}S\dot\eta$, where $S$ is the
  even part of the series $(1-e^{-z})/z$ at $z=\operatorname{ad}_{i\eta}$,
  a power series in $\operatorname{ad}_\eta^2$. It is $B$-symmetric and
  fixes $\eta$, so $B(\eta,S\dot\eta)=B(\eta,\dot\eta)$.

### `KempfNess/Basic.lean`

- `hasDerivAt_moment_expI`: the derivative of
  `t ↦ μ (C.expI (t • ξ) • p) ξ` is `-‖X_ξ‖²` at the moving point, so the
  function is antitone (`antitone_moment_expI`).
- `mgradient_moment_apply`: `mgradient (fun x ↦ μ x ξ) = -J X_ξ`.

### `KempfNess/Function.lean` (first half of the Kempf–Ness milestone)

- `contMDiff_kempfNessFunction`; `mfderiv_kempfNessFunction`:
  `mfderiv IC 𝓘(ℝ) (Φ_p) g ĝ = μ (g⁻¹ • p) (C.im (mfderiv IC IC (g⁻¹ * ·) g ĝ))`;
  `kempfNessFunction_toHom : Φ_p (C.toHom u) = 0`.
- `existsUnique_kempfNessFunction`: the unique smooth function with these
  two properties is $\Phi_p$ (uniqueness from connectedness of `Gc`).
- `kempfNessFunction_mul_toHom : Φ_p (g * C.toHom u) = Φ_p g`, and the
  induced function on `Gc ⧸ C.toHom.range`.
- `hasDerivAt_deriv_kempfNessFunction_geodesic`: the second derivative of
  `t ↦ Φ_p (g * C.expI (t • ξ))` is $|X_\xi(\exp(-it\xi)g^{-1}p)|^2$;
  `convexOn_kempfNessFunction_geodesic`.
- `mfderiv_kempfNessFunction_eq_zero_iff : mfderiv … Φ_p g = 0 ↔ μ (g⁻¹ • p) = 0`.
- `isPolystable_iff_exists_mfderiv_kempfNessFunction_eq_zero`.
- `exists_smul_eq_of_moment_eq_zero`: if $x,y\in G^{\mathbb C}p$ and
  $\mu(x)=\mu(y)=0$ then $y=u\cdot x$ for some $u\in G$ ($\langle\mu,\xi\rangle$
  decreases along $\exp(it\xi)$, strictly off the stabilizer directions), and
  `bijective_zeroLevelOrbit_polystableOrbit`: the map from the `G`-orbits
  of `TauCeti`'s `levelSubMulAction` at `0` to the `Gc`-orbits of
  `polystableLocus C μ` induced by the inclusion is bijective. This
  includes the clause that a polystable orbit meets $\mu^{-1}(0)$ in a
  single $G$-orbit, which the review of #2250 asked for.

### `KempfNess/NormSquare.lean`

- `mgradient_momentNormSq`: $\operatorname{grad}\|\mu\|^2(x)=-2JX_{\mu^\sharp(x)}(x)$.
- `exists_mem_orbit_maximalIntegralCurve`: the negative gradient flow of
  `momentNormSq` stays in the $G^{\mathbb C}$-orbit of its start, as $g(t)^{-1}p$ for
  the solution of $g^{-1}\dot g=-2i\mu^\sharp(g^{-1}p)$ in `Gc` with $g(0)=1$, at
  every time, and $\frac{d}{dt}\Phi_p(g(t))=-2\|\mu(g(t)^{-1}p)\|^2$.
- `exists_lojasiewicz_momentNormSq`: decision 4 (d), for any Hamiltonian
  action of a compact group with an equivariant moment map (not only
  Kähler).
- `tendsto_maximalIntegralCurve_momentNormSq`: the flow converges to a
  critical point of $\|\mu\|^2$.

The moment limit theorem follows, by decision 7, in this order. A *flow
curve* from `p` on a set `s` of times is a `g : ℝ → Gc` with
left-trivialized derivative
`-2 • C.cplx (C.lieMap (momentSharp B hB μ ((g t)⁻¹ • p)))` on `s`
(`HasLeftTrivializedDerivOn`), as `exists_mem_orbit_maximalIntegralCurve`
gives it on `univ`; the flow there is that
of `momentNormSq`, which is $\|\mu\|^2$ and not $f$, hence the factor 2.
This is a hypothesis of the statements below, not a definition.

- `hasDerivAt_polar_symm_fst_inv_mul`: for flow curves `g` and `g̃` from
  `p`, with `(η t, u t) = C.polar.symm ((g t)⁻¹ * g̃ t)` and
  `x t = (g t)⁻¹ • p`, the function `t ↦ B (η t) (η t)` has at each
  `t` of which `s` is a neighbourhood the derivative
  `4 * (μ (x t) (η t) - μ (C.expI (-η t) • x t) (η t))`. Proof:
  `hasDerivAt_polar_symm_fst_comp`, applied to `g̃ t` as a right factor
  and, through `polar_symm_inv`, to `g t` as a left factor, together with
  `apply_momentSharp` and the equivariance `moment_toHom_smul`, using
  `C.expI (-η t) • x t = C.toHom (u t) • (g̃ t)⁻¹ • p`. The two terms are
  the end slopes at `s = 0` and `s = 1` of
  `s ↦ Φ_p (g t * C.expI (s • η t))`.
- `antitoneOn_polar_symm_fst_inv_mul`: so `t ↦ B (η t) (η t)` is
  antitone on `s` for convex `s`, such as `Set.Ici 0`, by
  `antitone_moment_expI`.
- `exists_smul_eq_of_mgradient_momentNormSq_eq_zero` (Ness's uniqueness
  theorem): if `y = g₀⁻¹ • x` and `mgradient I' (momentNormSq B hB μ)`
  vanishes at `x` and at `y`, then `y = u • x` for some `u : G`. Proof (the
  Calabi–Chen proof of [GeorgoulasRobbinSalamon2021], Theorem 6.3): a
  critical point `x` has $X_{\mu^\sharp(x)}(x)=0$ (`mgradient_momentNormSq`),
  hence $X_{i\mu^\sharp(x)}(x)=JX_{\mu^\sharp(x)}(x)=0$, so `C.expI (s • momentSharp B hB μ x)`
  fixes `x` (`mulInvariantExp_smul_smul_eq_iff`, for the action of `Gc`).
  So `g t = C.expI (-(2 * t) • momentSharp B hB μ x)` and
  `g̃ t = g₀ * C.expI (-(2 * t) • momentSharp B hB μ y)` are flow curves
  from `x`, with `(g t)⁻¹ • x = x` and `(g̃ t)⁻¹ • x = y`, and
  `y = C.toHom (u t)⁻¹ • C.expI (-η t) • x`. The function `N t = B (η t) (η t)` is
  antitone and nonnegative, with derivative `4 * F (η t, u t)` for
  `F (η, u) = μ x η - μ (C.expI (-η) • x) η`. The pairs `(η, u)` with
  `B η η ≤ N 0` and `y = C.toHom u⁻¹ • C.expI (-η) • x` form a compact set
  (`B` is positive definite on a finite-dimensional space and `G` is
  compact) that contains `(η t, u t)` for `t ≥ 0`, and `F` takes its maximum
  on it at some `(η∞, u∞)`. The maximum is `0`, since otherwise `N` would
  decrease at a rate bounded below and become negative. Then
  `μ x η∞ = μ (C.expI (-η∞) • x) η∞`, so `C.expI (-η∞)` fixes `x`
  (`expI_smul_eq_self_of_moment_apply_le`, applied to `-η∞`), and
  `y = C.toHom u∞⁻¹ • x`. This generalizes `exists_smul_eq_of_moment_eq_zero`.
- `momentNormSq_limit_eq_iInf` (the moment limit theorem): for the limit
  `x∞` of the flow from `p`,
  `momentNormSq B hB μ x∞ = ⨅ g : Gc, momentNormSq B hB μ (g • p)`. Both
  norms are those of `B`. Proof: `≥`, because the flow stays in the orbit
  (`exists_mem_orbit_maximalIntegralCurve`) and `momentNormSq` is
  continuous. `≤`: fix `g₀`. Let `g` be the flow curve from `p` and `g'`
  the one from `g₀⁻¹ • p`, and put `g̃ = g₀ * g'`, a flow curve from `p`
  with `(g̃ t)⁻¹ • p = x̃ t`, the flow from `g₀⁻¹ • p`. By
  `antitoneOn_polar_symm_fst_inv_mul`, `η` is bounded, so along a sequence
  `η tₙ → η∞` and `u tₙ → u∞`. Then
  `x̃∞ = C.toHom u∞⁻¹ • C.expI (-η∞) • x∞`. The two limits are critical points
  in one `Gc`-orbit, so by Ness's theorem and `momentNormSq_smul`,
  `momentNormSq x∞ = momentNormSq x̃∞`. This is at most
  `momentNormSq (g₀⁻¹ • p)`, because `momentNormSq` decreases along its
  negative gradient flow (`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`).
- `exists_smul_limit_eq_of_mem_orbit`: the same argument shows that the
  `G`-orbit of `x∞` depends only on the `Gc`-orbit of `p`: the limit of the
  flow from `g₀ • p` is `u • x∞` for some `u : G`.

### `KempfNess/Stability.lean`

- `isSemistable_iff_bddBelow_kempfNessFunction`.
- `isStable_iff_bddBelow_and_isProperMap_kempfNessFunction`.
- `kempfNess`: the milestone, the conjunction of the existence and
  uniqueness of $\Phi_p$, its descent and convexity, its critical points,
  the three characterizations and the bijection of orbit sets, in the
  setting above, without the invariance of `J` under `G` and the
  connectedness of `M`, which it does not use. Milestone: *Kempf–Ness
  correspondence*.

### `HilbertMumford.lean`

- `momentWeight_le`: $w_\mu(p,\xi)\le\langle\mu(p),\xi\rangle$, and
  `tendsto_limitPoint` for every `ξ`.
- `tendsto_deriv_kempfNessFunction`: the slope identity, the limit of the
  derivative of $t\mapsto\Phi_p(\exp(-it\xi))$ is $-w_\mu(p,\xi)$.
- `momentWeight_le_mul_norm`: the moment-weight inequality,
  $w_\mu(p,\xi)\le\|\xi\|\,\|\mu(gp)\|$ for $\xi\in\Lambda$ and $g\in G^{\mathbb C}$,
  with both norms those of `B`: `√(B ξ ξ)` and `√(momentNormSq B hB μ (g • p))`.
- `exists_momentWeight_pos_of_not_isSemistable`: a destabilizing
  $\xi\in\Lambda$, by the route of *The destabilizing direction* below.
- `isSemistable_iff_momentWeight_nonpos`,
  `isPolystable_iff_isSemistable_and_limitPoint_mem_orbit`,
  `isStable_iff_momentWeight_neg`, and `hilbertMumford`, their
  conjunction. Milestone: *Hilbert–Mumford numerical criteria*. The
  quantifiers range over all of `nonzeroPeriods I G`, as the page says.

Edge cases: `G` trivial has $\Lambda=\emptyset$, and every point is
stable, since $\mathfrak g^*=0$; `M` is nonempty, being connected.

### The destabilizing direction

The route needs a direction of positive weight, not one of maximal weight,
so it avoids the generalized Kempf existence theorem of
[GeorgoulasRobbinSalamon2021] (arXiv v2, Theorem 10.4) and its geodesics in
$G^{\mathbb C}/G$, on which the design puts no metric. It follows the
argument of Lemma 10.5 there along the flow of `momentNormSq`, and
Theorem 11.1 there for continuity, whose inequality reverses under the
*Sign* bullet. Norms are those of `B`, written $|\xi|=\sqrt{B(\xi,\xi)}$.
For `ξ`, write `𝔞 ξ` for the set `{ζ | ∀ ζ', ⁅ζ', ξ⁆ = 0 → ⁅ζ', ζ⁆ = 0}`:
a subspace that contains `ξ`. Its elements commute pairwise: each
commutes with `ξ`, so lies in the centralizer of `ξ`, and so commutes
with every element of `𝔞 ξ`. It is a set in the statements below; a
proof that needs it as a `Submodule` builds it there.

- `sqrt_polar_symm_fst_le_add_mul` (`Geometry/Lie/Complexification.lean`,
  with the polar radius): for connected `G`, a symmetric `Ad`-invariant `B`,
  a curve `a` with `HasLeftTrivializedDerivOn a v univ` and
  `√(B (C.im (v t)) (C.im (v t))) ≤ K` for all `t`, the polar radius
  `√(B η η)` of `a t`, for `(η, u) = C.polar.symm (a t)`, is at most that of
  `a 0` plus `K * t` for `t ≥ 0`. Proof: `hasDerivAt_polar_symm_fst_comp`,
  Cauchy–Schwarz for `B` and `Ad`-invariance bound the derivative of
  `B η η` by `2 * K * √(B η η)`; compare with the boundary
  `(√(B η₀ η₀) + (K + ε) * t + ε) ^ 2` by
  `image_le_of_deriv_right_lt_deriv_boundary` and let `ε → 0`. The
  moment-weight inequality uses it too, for
  `a t = g * C.expI (-(t • ξ))` and `K = √(B ξ ξ)`; whichever of the two
  building issues comes first proves it.
- `hasDerivAt_moment_apply_expI` (`KempfNess/Basic.lean`): the derivative
  of `s ↦ μ (C.expI (s • η) • p) ξ` at `t` is the negative of the inner
  product of `X_ξ` and `X_η` at the moving point, from
  `mgradient_moment_apply` and `isMIntegralCurve_expI_smul`, as in
  `hasDerivAt_moment_expI`, its case `η = ξ`.
- `momentWeight_smul` (`HilbertMumford.lean`): for `0 < c`,
  `momentWeight C μ p (c • ξ) = c * momentWeight C μ p ξ`, by
  `expI_smul` and the change of time `t ↦ c * t` in `tendsto_momentWeight`.
- `momentWeight_expI_smul_of_lie_eq_zero`: if `⁅η, ξ⁆ = 0` then
  `momentWeight C μ (C.expI η • p) ξ = momentWeight C μ p ξ`. Proof:
  `C.expI η` and `C.expI (t • ξ)` commute (`commute_lieExp_of_lie_eq_zero`
  in `Gc`, since `C.cplx` and `C.lieMap` preserve brackets up to sign:
  `cplx_lie_cplx`), so the limit point moves to
  `C.expI η • limitPoint C p ξ`. The limit point is a critical point of
  `x ↦ μ x ξ` (`limitPoint_mem_criticalPoints`), so `X_ξ` vanishes there
  (`mgradient_moment_apply`), and every `C.expI (t • ξ)` fixes it
  (`expI_smul_smul_eq_self_iff`). They commute with `C.expI (s • η)`, so
  they also fix each `C.expI (s • η) • limitPoint C p ξ`, where `X_ξ`
  vanishes too. By `hasDerivAt_moment_apply_expI`,
  `s ↦ μ (C.expI (s • η) • limitPoint C p ξ) ξ` is then constant, and
  `momentWeight_eq_moment_limitPoint` concludes.
- `continuousOn_momentWeight`: for a submodule `𝔞` of pairwise commuting
  elements, `momentWeight C μ p` is continuous on `𝔞`. Proof: let `K` be the
  closure of `{C.expI η • p | η ∈ 𝔞}`, compact since `M` is. For `ξ ∈ 𝔞`,
  `momentWeight C μ p ξ` is the infimum of `μ y ξ` over `y ∈ K`: it is
  attained at `limitPoint C p ξ ∈ K` (`tendsto_limitPoint`,
  `momentWeight_eq_moment_limitPoint`), and it is at most `μ y ξ` for
  `y = C.expI η • p` by `momentWeight_le` and
  `momentWeight_expI_smul_of_lie_eq_zero`, hence for `y ∈ K` by continuity.
  The map `(y, ξ) ↦ μ y ξ` is continuous (`𝔤` is finite-dimensional), so
  `IsCompact.continuous_sInf` gives continuity.
- `exists_pow_mem_of_mem_nhds_one` (`Topology/Algebra/Group/Recurrence.lean`,
  with its additive version): in a compact topological group, every
  neighbourhood of `1` contains `g ^ n` for some `n > 0`. Proof: the powers
  `g ^ n` have a cluster point, so two of them, `g ^ k` and `g ^ l` with
  `k < l`, lie in one translate `x * W` of a neighbourhood `W` with
  `W⁻¹ * W ⊆ V`. No such lemma turned up in Mathlib or Tau Ceti at the
  pinned versions; its building issue searches again first.
- `mem_closure_smul_nonzeroPeriods` (`Geometry/Lie/Exponential/Periods.lean`):
  for compact `G` and `ξ ≠ 0`, `ξ` lies in the closure of the positive
  multiples `c • λ` of the elements `λ ∈ nonzeroPeriods I G ∩ 𝔞 ξ`. Proof,
  with an `Ad`-invariant `B` from
  `TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`:
  given `δ` with `0 < δ < |ξ|` and the `B`-ball of radius `δ` inside the
  source of `mulInvariantExpOpenPartialHomeomorph` and inside a set on
  which `mulInvariantExp` is injective
  (`exists_injOn_mulInvariantExp_modelSpace`), its image is a neighbourhood
  of `1`, so by `exists_pow_mem_of_mem_nhds_one` some `m ≥ 1` has
  `mulInvariantExp (m • ξ) = mulInvariantExp η` with `|η| < δ`. For `ζ'`
  commuting with `ξ`, `h = mulInvariantExp (s • ζ')` commutes with
  `mulInvariantExp (m • ξ)` (`commute_lieExp_of_lie_eq_zero`), so
  `conj_lieExp` (with `lieExp_eq_mulInvariantExp`) and injectivity on the
  `Ad`-invariant ball give `Ad h η = η`, and `hasDerivAt_Ad_lieExp_smul_apply_zero` gives
  `⁅ζ', η⁆ = 0`. So `η ∈ 𝔞 ξ`, in particular `⁅ξ, η⁆ = 0`, and
  `λ = m • ξ - η` has `mulInvariantExp λ = 1`
  (`lieExp_add_of_lie_eq_zero`), lies in `𝔞 ξ`, is nonzero because
  `|m • ξ| ≥ |ξ| > δ > |η|`, and `|ξ - m⁻¹ • λ| = |η| / m < δ`. The
  route through Tau Ceti's tori (`isTorus_closedOneParameterSubgroup`,
  `Exponential/CommutativeGroup/Kronecker.lean`) would need the Lie algebra
  of the closed subgroup inside `𝔤` and its exponential, which this route
  does not.
- `isSemistable_of_iInf_momentNormSq_smul_eq_zero` (`KempfNess/Stability.lean`,
  the converse of `IsSemistable.iInf_momentNormSq_smul_eq_zero`): in the
  setting of `momentNormSq_limit_eq_iInf`, if
  `⨅ g : Gc, momentNormSq B hB μ (g • p) = 0` then `p` is semistable: the
  limit of the flow (`tendsto_maximalIntegralCurve_momentNormSq`) lies in
  the closure of the orbit (`exists_mem_orbit_maximalIntegralCurve`), and
  `momentNormSq_limit_eq_iInf` and `momentNormSq_eq_zero_iff` make it a
  zero of `μ`. The proof of
  `isSemistable_iff_bddBelow_kempfNessFunction` has this step inline; the
  building issue moves it here.
- `exists_momentWeight_pos_of_iInf_momentNormSq_pos` (`HilbertMumford.lean`):
  in that setting, if `0 < m²` for `m² := ⨅ g : Gc, momentNormSq B hB μ (g • p)`,
  some `ξ` with `B ξ ξ = 1` has `0 < momentWeight C μ p ξ`. Proof: take
  the flow curve `g` of `exists_mem_orbit_maximalIntegralCurve`, so
  `Φ_p (g t) ≤ -2 * m² * t` for `t ≥ 0` (`Φ_p 1 = 0` by
  `kempfNessFunction_toHom`), and let `r t` be the polar radius
  of `g t`, with `g t = C.expI (r t • ζ t) * C.toHom (u t)` and
  `B (ζ t) (ζ t) = 1` when `r t > 0` (`expI_mul_toHom_polar_symm`). Let `L`
  be the maximum of `√(momentNormSq B hB μ)` on `M`; `L ≥ m > 0`.
  1. `r t ≤ 2 * L * t`, by `sqrt_polar_symm_fst_le_add_mul`, since the
     imaginary part of the left-trivialized derivative is
     `-2 • momentSharp B hB μ ((g t)⁻¹ • p)` (`im_cplx_lieMap`).
  2. `r t ≥ 2 * m² * t / √(momentNormSq B hB μ p)`, by
     `kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le` at `g = 1`; so
     `r t → ∞`.
  3. The `ζ t` lie on the unit sphere of `B`, which is compact, so
     `ζ (t n) → ζ₀` along a sequence `t n → ∞`.
  4. `s ↦ Φ_p (C.expI (s • ζ))` is convex
     (`convexOn_kempfNessFunction_geodesic` at `g = 1`) and vanishes at `0`,
     and `Φ_p (g t) = Φ_p (C.expI (r t • ζ t))` by
     `kempfNessFunction_mul_toHom`. So for `0 < s ≤ r (t n)`,
     `Φ_p (C.expI (s • ζ (t n))) / s ≤ Φ_p (g (t n)) / r (t n) ≤ -m² / L`
     by 1. Letting `n → ∞` (`contMDiff_kempfNessFunction`),
     `Φ_p (C.expI (s • ζ₀)) ≤ -(m² / L) * s` for every `s ≥ 0`.
  5. By the slope identity `tendsto_deriv_kempfNessFunction` at `-ζ₀`, the
     derivative of `s ↦ Φ_p (C.expI (s • ζ₀))` tends to
     `-momentWeight C μ p (-ζ₀)`. A derivative that tends to `D` bounds the
     growth (`Convex.mul_sub_le_image_sub_of_le_deriv`), so
     `Φ_p (C.expI (s • ζ₀)) / s → D`, and
     `momentWeight C μ p (-ζ₀) ≥ m² / L > 0`. Take `ξ = -ζ₀`.
- `exists_momentWeight_pos_of_not_isSemistable`: if `p` is not semistable,
  some `λ ∈ nonzeroPeriods I G` has `0 < momentWeight C μ p λ`. Proof:
  `isSemistable_of_iInf_momentNormSq_smul_eq_zero` and
  `momentNormSq_nonneg` give `0 < m²`, and
  `exists_momentWeight_pos_of_iInf_momentNormSq_pos` a unit `ξ` of
  positive weight. The weight is continuous at `ξ` on `𝔞 ξ`
  (`continuousOn_momentWeight`), so it is positive on a neighbourhood of
  `ξ` in `𝔞 ξ`, which contains some `c • λ` with `c > 0` and
  `λ ∈ nonzeroPeriods I G ∩ 𝔞 ξ` (`mem_closure_smul_nonzeroPeriods`).
  Then `momentWeight_smul` gives `0 < momentWeight C μ p λ`.
- `isSemistable_iff_momentWeight_nonpos` is this together with
  `IsSemistable.momentWeight_nonpos`, which the slope identity gives.

## What it uses

- From Tau Ceti: `TauCeti.SmoothTwoForm.IsKahler` and `Compatible.metric`;
  `IsEquivariantMomentMap`, `levelSubMulAction`; `fundamentalVectorField`;
  `mulInvariantExp`;
  `TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`;
  `mgradient` and `maximalIntegralCurve`
  (`Geometry/Manifold/Riemannian/Gradient/`);
  `tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`; the Morse–Bott
  results named in decision 5; the semialgebraic geometry and the
  symplectic slice named in decision 4; for the destabilizing direction,
  `mulInvariantExpOpenPartialHomeomorph` and
  `exists_injOn_mulInvariantExp_modelSpace`
  (`Geometry/Lie/Exponential/LocalInverse.lean`),
  `commute_lieExp_of_lie_eq_zero` and `lieExp_add_of_lie_eq_zero`
  (`Geometry/Lie/Adjoint/Exponential/Formula.lean`), `conj_lieExp` and
  `hasDerivAt_Ad_lieExp_smul_apply_zero`.
- From Mathlib: `IsCompact.continuous_sInf` (`Topology/Order/Compact.lean`)
  and the comparison lemmas of `Analysis/Calculus/MeanValue.lean`.
- From other parts: none on `main` is needed. The local normal form (c)
  is not Tau Ceti's weight chart of part 37 (*Equivariant normal forms*),
  which holds only at fixed points; it generalizes it along orbits.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **The complexification.** `Geometry/Lie/Complexification.lean`, with
   the circle example. No blockers.
2. **The complexified action and the stability predicates.**
   `KempfNess/Basic.lean`. Blocked by 1.
3. **The Kempf–Ness function.** `KempfNess/Function.lean` up to
   convexity and critical points. Blocked by 2.
4. **The polystable orbits.** The rest of `KempfNess/Function.lean`: one
   $G$-orbit in each, and the bijection of orbit sets. Blocked by 3.
5. **Curve selection.** `Semialgebraic/CurveSelection.lean`. No blockers.
6. **The polynomial Łojasiewicz inequality.**
   `Lojasiewicz/Polynomial.lean`. Blocked by 5.
7. **Łojasiewicz convergence on manifolds.**
   `Gradient/Lojasiewicz.lean`. No blockers.
8. **The local normal form of a moment map.** `MomentMap/LocalNormalForm.lean`.
   No blockers. If it exceeds a thousand lines, its issue splits the
   equivariant tubular neighbourhood of an orbit from the moment map in
   the model.
9. **The gradient flow of $\|\mu\|^2$.** `KempfNess/NormSquare.lean`, and
   the Gauss lemma of decision 7 in `Geometry/Lie/Complexification.lean`.
   Blocked by 3, 6, 7 and 8. The moment limit theorem comes last, after
   the steps that *Main results* lists before it, in that order; it does
   not use the moment-weight inequality of issue 12.
10. **The criteria, and the Kempf–Ness milestone.**
    `KempfNess/Stability.lean`. Blocked by 4 and 9.
11. **Weights and limit points.** The first two items of
    `HilbertMumford.lean`. Blocked by 3 and 7.
12. **Destabilizing directions, and the second milestone.**
    The rest of `HilbertMumford.lean`, from the moment-weight inequality on. Blocked by 10 and 11.
    The destabilizing direction is these issues, in this order:
    1. `sqrt_polar_symm_fst_le_add_mul`, unless the moment-weight
       inequality has proved it. No blockers.
    2. `hasDerivAt_moment_apply_expI`, `momentWeight_smul`,
       `momentWeight_expI_smul_of_lie_eq_zero` and
       `continuousOn_momentWeight`. No blockers.
    3. `exists_pow_mem_of_mem_nhds_one` and
       `mem_closure_smul_nonzeroPeriods`. No blockers.
    4. `isSemistable_of_iInf_momentNormSq_smul_eq_zero` and
       `exists_momentWeight_pos_of_iInf_momentNormSq_pos`. Blocked by 12.1
       and by the slope identity (#7892).
    5. `exists_momentWeight_pos_of_not_isSemistable` and
       `isSemistable_iff_momentWeight_nonpos`. Blocked by 12.2, 12.3 and
       12.4.

Issues 1, 5, 7 and 8 can start at once; the Kempf–Ness milestone
(issue 10) comes before the Hilbert–Mumford one (issue 12).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.7, equations (5.7.2)–(5.7.4) and Theorem 5.7.2.
* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight
  Inequality and the Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021],
  arXiv v2, Lemma 2.1, Theorems 4.1, 4.3, 7.3, 12.2, 12.5 and 12.6, and
  Definition 7.1.
* [V. Guillemin and S. Sternberg][GuilleminSternberg1990], for the local
  normal form.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign.
  Math. 51 (2005), 117–127.
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une
  variété symplectique*, Rend. Sem. Mat. Univ. Politec. Torino 43 (1985),
  227–251.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*,
  Springer, 1998, §2.5–2.6.
