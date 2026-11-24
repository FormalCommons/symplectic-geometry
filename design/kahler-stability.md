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
  characteristic classes*.
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
  definite and `Ad`-invariant, as `TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`
  gives it. That theorem is stated on `LeftInvariantDerivation I G`, with
  Tau Ceti's `continuousAdjointRepresentation`; `KempfNess/Basic.lean`
  carries it to `GroupLieAlgebra I G`, the tangent space `E` at `1` on which
  `IsEquivariantMomentMap` and `Lie.adjointRepresentation` live, along
  Tau Ceti's public `leftInvariantDerivationLinearIsometryEquivModelVectorSpace`
  (both representations are `adjointContinuousLinearMap`, read on either
  side). `B` gives $\mu^\sharp(x)\in\mathfrak g$
  (`B.toDual` inverted on `μ x`) and $\|\mu(x)\|^2=B(\mu^\sharp x,\mu^\sharp x)$.
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
   `cplx` is a real-linear map on `GroupLieAlgebra IC Gc` with square
   `-1` that commutes with each `ad` (a complex Lie algebra). The ranges of
   `lieMap` and of `cplx ∘ lieMap` are complementary. Finally there is
   `polar : 𝔤 × G ≃ₘ⟮_, IC⟯ Gc`, a diffeomorphism with
   `polar (ξ, u) = mulInvariantExp (cplx (lieMap ξ)) * toHom u`. All the
   milestones' conclusions are about $\Phi_p$, $\mu$ and orbits, and none of
   these fields is one of them, as the review of #2250 asks. The complex
   manifold structure of $G^{\mathbb C}$ is not needed: the proofs use only
   the complex structure of its Lie algebra and the polar decomposition.
   The structure has an example: `Circle` in `ℂˣ`, with
   `polar (t, u) = exp t * u` (Mathlib's `Complex.exp`, `Circle`).
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
   `tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`, taken
   from its main branch at `07c8b6b1f5ff`. The analytic inequality is not
   needed and is not proved.
5. **The limit points $p^+_\xi$** for $\xi\in\Lambda$ do not need (d): the
   orbit $t\mapsto\exp(it\xi)p$ is the negative gradient flow of
   $\langle\mu,\xi\rangle$, which is Morse–Bott for a circle action (Tau
   Ceti's `MomentMap/MorseBott.lean`,
   `exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace`),
   so Tau Ceti's Morse–Bott inequality `exists_mul_abs_sub_le_norm_mgradient_sq`
   with (e) gives the limit. Until the library moves to a Tau Ceti commit
   at or after `07c8b6b1f5ff`, that inequality's file
   `Morse/Bott/ExponentialConvergence.lean` and (e) cannot be imported
   together, since (e) rests on copies from Tau Ceti main that clash with
   the pinned `Morse/ExponentialConvergence.lean`; building issue 11 waits
   for #2450, which removes the clash by that move or by copying what it
   needs from main's Bott file. The weights $w_\mu(p,\xi)$ exist for every
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

## Files

- `Geometry/Lie/Complexification.lean`: `LieComplexification`, its API
  (`expI`, `im`, `re`, `lieMap_re_add_cplx_lieMap_im`, `polar_apply`,
  `connectedSpace` from connectedness of `G`, `toHom` a closed embedding),
  and the circle example.
- `Geometry/RealAlgebraic/Semialgebraic/CurveSelection.lean`: decision 4 (a).
- `Analysis/Calculus/Lojasiewicz/Polynomial.lean`: decision 4 (b), in Tau
  Ceti's folder `Analysis/Calculus/Lojasiewicz/`.
- `Geometry/Manifold/Riemannian/Gradient/Lojasiewicz.lean`: decision 4 (e).
- `Geometry/Symplectic/Hamiltonian/MomentMap/LocalNormalForm.lean`:
  decision 4 (c).
- In `Geometry/Symplectic/Hamiltonian/MomentMap/KempfNess/`:
  `Basic.lean` (`IsComplexifiedAction`, $\mu^\sharp$ and $\|\mu\|^2$, the
  stability predicates, the gradient of $\langle\mu,\xi\rangle$ and the
  derivative along $\exp(it\xi)$), `Function.lean` ($\Phi_p$ and the
  first half of the milestone), `NormSquare.lean` (the gradient flow of
  $f$, its Łojasiewicz inequality, convergence and the moment limit), and
  `Stability.lean` (the boundedness and properness criteria and the
  milestone).
- `Geometry/Symplectic/Hamiltonian/MomentMap/HilbertMumford.lean`: $\Lambda$,
  weights, limit points, the slope identity, the moment-weight inequality
  and the criteria.

## Definitions and their API

All in `SymplecticGeometry`, with `C : LieComplexification I G IC Gc`.

- `C.expI ξ := mulInvariantExp (C.cplx (C.lieMap ξ))`, with `expI_zero`,
  `expI_add_smul` for `s t : ℝ`
  (`expI ((s + t) • ξ) = expI (s • ξ) * expI (t • ξ)`), and
  `C.toHom u * C.expI ξ * (C.toHom u)⁻¹ = C.expI (Ad u ξ)`.
- `IsComplexifiedAction C J` (decision 2), with
  `IsComplexifiedAction.fundamentalVectorField_cplx` and
  `fundamentalVectorField_expI` (the velocity of $t\mapsto\exp(it\xi)p$ is
  $JX_\xi$ at the moving point).
- `momentSharp B hB μ x : 𝔤` and `momentNormSq B μ x : ℝ`, with
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
  `limitPoint C p ξ : M`, with `tendsto_limitPoint` for `ξ ∈ Λ`.
- `integralLattice I G : Set 𝔤 := {ξ | ξ ≠ 0 ∧ mulInvariantExp ξ = 1}`,
  written $\Lambda$, invariant under `Ad` and under positive integer
  multiples.

## Main results

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
  $\mu(x)=\mu(y)=0$ then $y=u\cdot x$ for some $u\in G$ (strict convexity
  along geodesics off the stabilizer directions), and
  `bijective_zeroLevelOrbit_polystableOrbit`: the map from the `G`-orbits
  of `TauCeti`'s `levelSubMulAction` at `0` to the `Gc`-orbits of
  `polystableLocus C μ` induced by the inclusion is bijective. This
  includes the clause that a polystable orbit meets $\mu^{-1}(0)$ in a
  single $G$-orbit, which the review of #2250 asked for.

### `KempfNess/NormSquare.lean`

- `mgradient_momentNormSq`: $\operatorname{grad}f(x)=-JX_{\mu^\sharp(x)}(x)$.
- `exists_mem_orbit_maximalIntegralCurve`: the negative gradient flow of
  $f$ stays in the $G^{\mathbb C}$-orbit of its start, as $g(t)^{-1}p$ for
  the solution of $g^{-1}\dot g=-i\mu^\sharp(g^{-1}p)$ in `Gc`, and
  $\frac{d}{dt}\Phi_p(g(t))=-\|\mu(g(t)^{-1}p)\|^2$.
- `exists_lojasiewicz_momentNormSq`: decision 4 (d), for any Hamiltonian
  action of a compact group with an equivariant moment map (not only
  Kähler).
- `tendsto_maximalIntegralCurve_momentNormSq` and
  `momentNormSq_limit_eq_iInf` (the moment limit theorem): the flow
  converges, and $\|\mu(x_\infty)\|=\inf_{g\in G^{\mathbb C}}\|\mu(gp)\|$.

### `KempfNess/Stability.lean`

- `isSemistable_iff_bddBelow_kempfNessFunction`.
- `isStable_iff_bddBelow_and_isProperMap_kempfNessFunction`.
- `kempfNess`: the milestone, the conjunction of the existence and
  uniqueness of $\Phi_p$, its descent and convexity, its critical points,
  the three characterizations and the bijection of orbit sets, in the
  setting above. Milestone: *Kempf–Ness correspondence*.

### `HilbertMumford.lean`

- `momentWeight_le`: $w_\mu(p,\xi)\le\langle\mu(p),\xi\rangle$, and
  `tendsto_limitPoint` for `ξ ∈ integralLattice I G`.
- `tendsto_deriv_kempfNessFunction`: the slope identity, the limit of the
  derivative of $t\mapsto\Phi_p(\exp(-it\xi))$ is $-w_\mu(p,\xi)$.
- `momentWeight_le_mul_norm`: the moment-weight inequality,
  $w_\mu(p,\xi)\le\|\xi\|\,\|\mu(gp)\|$ for $\xi\in\Lambda$ and $g\in G^{\mathbb C}$.
- `exists_momentWeight_pos_of_not_isSemistable`: a destabilizing
  $\xi\in\Lambda$ (the limit of the flow of $f$, and continuity of
  weights for torus actions).
- `isSemistable_iff_momentWeight_nonpos`,
  `isPolystable_iff_isSemistable_and_limitPoint_mem_orbit`,
  `isStable_iff_momentWeight_neg`, and `hilbertMumford`, their
  conjunction. Milestone: *Hilbert–Mumford numerical criteria*. The
  quantifiers range over all of `integralLattice I G`, as the page says.

Edge cases: `G` trivial has $\Lambda=\emptyset$, and every point is
stable, since $\mathfrak g^*=0$; `M` is nonempty, being connected.

## What it uses

- From Tau Ceti: `TauCeti.SmoothTwoForm.IsKahler` and `Compatible.metric`;
  `IsEquivariantMomentMap`, `levelSubMulAction`; `fundamentalVectorField`;
  `mulInvariantExp`; `TauCeti.Lie.exists_isSymm_bilinForm_Ad_invariant`;
  `mgradient` and `maximalIntegralCurve`
  (`Geometry/Manifold/Riemannian/Gradient/`);
  `tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`; the Morse–Bott
  results named in decision 5; the semialgebraic geometry and the
  symplectic slice named in decision 4.
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
9. **The gradient flow of $\|\mu\|^2$.** `KempfNess/NormSquare.lean`.
   Blocked by 3, 6, 7 and 8.
10. **The criteria, and the Kempf–Ness milestone.**
    `KempfNess/Stability.lean`. Blocked by 4 and 9.
11. **Weights and limit points.** The first two items of
    `HilbertMumford.lean`. Blocked by 3 and 7.
12. **Destabilizing directions, and the second milestone.**
    The rest of `HilbertMumford.lean`, from the moment-weight inequality on. Blocked by 10 and 11.

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
