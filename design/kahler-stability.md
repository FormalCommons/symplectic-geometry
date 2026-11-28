# Kähler stability

This is the detailed design of part 44 of `DESIGN.md`, *Kähler stability*.
It proves two milestones of `atlas/symplectic-group-actions.md`, the
*Kempf–Ness correspondence* and the *Hilbert–Mumford numerical criteria*,
following McDuff–Salamon [McDuffSalamon2017], §5.7 (equations
(5.7.2)–(5.7.4) and Theorem 5.7.2), and Georgoulas–Robbin–Salamon
[GeorgoulasRobbinSalamon2021] (arXiv v2: Lemmas 2.1, 2.3 and 8.4,
Theorems 4.1 and 4.3, Definition 7.1, Theorems 7.2, 7.3 and 8.5, Theorems
12.2, 12.4, 12.5 and 12.6). The convergence
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
- **Holomorphic charts in one step only.** Except for the sufficiency half
  of the polystable criterion, the proofs use only that `σ` is closed and
  that `J` is compatible with it, together with the infinitesimal
  holomorphicity $X_{i\xi}=JX_\xi$ of the complexified action. Those
  proofs never use the integrability of `J`, nor Tau Ceti's condition $N_J=0$,
  and their statements take `σ.IsKahler J`, as the page does. The sufficiency
  half of the polystable criterion needs holomorphic coordinates at a
  zero of $\mu$ ([GeorgoulasRobbinSalamon2021], arXiv v2, Theorem 12.5),
  so `exists_mem_nonzeroPeriods_tendsto_expI_smul` and every statement
  that uses it (`isPolystable_of_isSemistable_of_limitPoint_mem_orbit`,
  `isStable_of_momentWeight_neg`, the polystable and stable criteria and
  `hilbertMumford`) also take `hJi : J.IsIntegrable`, the predicate
  `TauCeti.SmoothAlmostComplexStructure.IsIntegrable` of
  `Geometry/Manifold/Complex/Integrable.lean`. This is the hypothesis that
  the *Kähler* bullet of `DESIGN.md` lets this file add; the book's Kähler
  manifolds are integrable, and a proof of the Newlander–Nirenberg theorem
  would remove it without changing the statements. No chart-free route is
  known: without charts, a direction of weight `0` need not be a period,
  and nothing shows that its limit point leaves the orbit (#8248).

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
6. **Home.** The complexification is Lie theory, so it is in
   the folder `Geometry/Lie/Complexification/`, beside Tau Ceti's folder
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
8. **Parabolic subgroups without weights outside $\mathfrak g$.**
   [GeorgoulasRobbinSalamon2021] (arXiv v2, Theorem 5.3, Lemma 7.5,
   Appendices D and E) move weights across $G^{\mathbb C}$ by extending
   $w_\mu$ to the $G^{\mathbb C}$-conjugates $g\xi g^{-1}$ of elements of
   $\mathfrak g$, and by writing each conjugate as $q\xi' q^{-1}$ with $q$ in
   the parabolic subgroup $P(\xi')$ (Theorem D.4, proved inside
   $\mathrm{GL}(n,\mathbb C)$). The criteria need less. They use only
   (i) that $w_\mu(qx,\xi)=w_\mu(x,\xi)$, and that $p^+_\xi$ is moved by an
   element of $G^{\mathbb C}$ when $x$ is replaced by $qx$, for $q\in P(\xi)$;
   (ii) the decomposition $G^{\mathbb C}=P(\xi)G$ (Theorem D.3); and (iii) the
   equivariance $w_\mu(ux,\operatorname{Ad}_u\xi)=w_\mu(x,\xi)$ for $u\in G$.
   So the part defines no weight along a direction outside $\mathfrak g$, and
   proves neither Theorem 5.3 in its general form nor Theorem D.4. $P(\xi)$ is
   defined by the convergence of $\exp(it\xi)\,g\,\exp(-it\xi)$, which needs
   only `expI`, and (ii) is proved from `polar`, `cplx` and `lieMap` by
   an open-and-closed argument on the connected group $G^{\mathbb C}$, which,
   like Appendix E, avoids the structure theory of Lie groups. It uses the
   eigenspaces of $\operatorname{ad}(i\xi)$, an operator that is symmetric for
   an inner product built from `B`. *How the criteria use them*, under
   `HilbertMumford.lean` below, shows how (i)–(iii) give the steps of the
   criteria that the source proves with Theorems 5.3 and D.4.

## Files

- `Geometry/Lie/Complexification/Basic.lean`: `LieComplexification`, its
  API (`im`, `re`, `lieMap_re_add_cplx_lieMap_im`, `connectedSpace` from
  connectedness of `G`).
- `Geometry/Lie/Complexification/Polar.lean`: `expI`, `polar_apply`,
  `toHom` a closed embedding, the circle example, and the Gauss lemma of
  decision 7.
- `Geometry/Lie/Subgroup/Parabolic.lean`: the parabolic subgroup
  `C.parabolic ξ` of decision 8, its Lie subspace, and
  $G^{\mathbb C}=P(\xi)G$. Tau Ceti's folder `Geometry/Lie/Subgroup/` has no
  file of that name, and the files of `Complexification/` keep their paths.
- `Geometry/RealAlgebraic/Semialgebraic/CurveSelection.lean`: decision 4 (a).
- `Analysis/Calculus/Lojasiewicz/Polynomial.lean`: decision 4 (b), in Tau
  Ceti's folder `Analysis/Calculus/Lojasiewicz/`.
- `Geometry/Manifold/Riemannian/Gradient/Lojasiewicz.lean`: decision 4 (e).
- `Geometry/Symplectic/Hamiltonian/MomentMap/LocalNormalForm.lean`:
  decision 4 (c).
- `Geometry/Symplectic/Hamiltonian/MomentMap/NormSq.lean`: $\mu^\sharp$,
  and what $\|\mu\|^2$ needs beyond Tau Ceti's `MomentMap/NormSq.lean`, for
  any Lie group and any map `μ`.
- In `Geometry/Symplectic/Hamiltonian/MomentMap/KempfNess/`:
  `Basic.lean` (`IsComplexifiedAction`, the stability predicates, the
  gradient of $\langle\mu,\xi\rangle$ and the
  derivative along $\exp(it\xi)$), `Function.lean` ($\Phi_p$ and the
  first half of the milestone), `NormSquare.lean` (the gradient flow of
  $f$, its Łojasiewicz inequality, convergence, Ness's uniqueness theorem
  and the moment limit), and
  `Stability.lean` (the boundedness and properness criteria and the
  milestone); for the local criterion at a zero of $\mu$, the one step
  that uses `hJi`, `Stabilizer.lean`, `HolomorphicChart.lean`,
  `Projective.lean` and `HolomorphicSlice.lean`; and
  `NumericalCriterion.lean` (the sufficiency halves of the polystable and
  stable criteria, the three criteria and the Hilbert–Mumford milestone).
- `Geometry/Symplectic/Hamiltonian/MomentMap/HilbertMumford.lean`:
  weights, limit points, the slope identity, the moment-weight inequality,
  the semistable criterion and the necessity halves of the others.

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
- `momentSharp B hB μ x`, in any finite-dimensional real vector space (here
  `𝔤`), with `B (momentSharp …) ξ = μ x ξ`. The norm
  square is Tau Ceti's `momentNormSq μ (B.toDual hB).symm x : ℝ`, with its
  invariance under `G` and smoothness; here `momentNormSq_nonneg` and
  `momentNormSq_eq_zero_iff`.
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
- `C.parabolic ξ : Subgroup Gc` (decision 8), the `g` for which
  `t ↦ C.expI (t • ξ) * g * C.expI (-(t • ξ))` has a limit as `t → ∞`, with
  `mem_parabolic_iff`; `C.parabolicLimit ξ : C.parabolic ξ →* Gc`, that
  limit (`limUnder atTop`; `Gc` is Hausdorff by `IC.t2Space_of_lieGroup`), with
  `tendsto_parabolicLimit`; and `C.parabolicSubspace ξ`, the submodule of
  `GroupLieAlgebra IC Gc` of the `x` for which
  `t ↦ tangentAd (C.expI (t • ξ)) x` converges. Edge cases:
  `parabolic_zero : C.parabolic 0 = ⊤`, and in the circle example of
  decision 1, where `Gc` is commutative, every `C.parabolic ξ` is `⊤`.
- `nonzeroPeriods I G : Set 𝔤 := {ξ | ξ ≠ 0 ∧ mulInvariantExp ξ = 1}`,
  written $\Lambda$, invariant under `Ad` and under positive integer
  multiples, in `Geometry/Lie/Exponential/Periods.lean`.

## Main results

### `Geometry/Lie/Complexification/Polar.lean` (the polar radius)

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

### `Geometry/Lie/Subgroup/Parabolic.lean` (decision 8)

Here `G` is compact and connected and `E` finite-dimensional, as in the
setting; the proofs choose `B` with
`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant`,
so no statement takes it.

- `C.parabolic ξ` is a subgroup: the conjugate of `g * h` is the product
  of the conjugates (insert `C.expI (-(t • ξ)) * C.expI (t • ξ) = 1`, from
  `expI_add_smul`), and that of `g⁻¹` the inverse, so limits multiply
  (`Filter.Tendsto.mul`, `Filter.Tendsto.inv`). Then
  `map_mul` for the homomorphism `C.parabolicLimit ξ`, and
  `expI_mul_parabolicLimit_mul_expI_neg : C.expI (s • ξ) * C.parabolicLimit ξ q * C.expI (-(s • ξ)) = C.parabolicLimit ξ q`
  (the conjugates are those at time `t + s`), so the limit commutes with
  every `C.expI (s • ξ)`.
- `tangentAd_expI_smul`: `tangentAd (C.expI (t • ξ))` is
  `NormedSpace.exp (t • A)` for `A := ad (C.cplx (C.lieMap ξ))`, by Tau
  Ceti's `TauCeti.Lie.tangentAd_mulInvariantExp_apply`
  (`Geometry/Lie/Adjoint/Exponential/Formula.lean`). So
  `C.parabolicSubspace ξ` is the sum of the eigenspaces of `A` with
  eigenvalue `≤ 0`, once `A` is diagonalizable with real eigenvalues
  (next item).
- `isSelfAdjoint_ad_cplx_lieMap` (`Geometry/Lie/Complexification/Basic.lean`): for the form
  `Bc x y := B (C.re x) (C.re y) + B (C.im x) (C.im y)`, symmetric and
  positive definite because `lieMap_re_add_cplx_lieMap_im` splits
  `GroupLieAlgebra IC Gc`, the operator `A` is `Bc`-symmetric. Proof: by
  `cplx_lie'`, `re_lie`, `im_lie`, `re_lieMap`, `im_lieMap` and the values of
  `re` and `im` on `cplx`, `C.re (A x) = -⁅ξ, C.im x⁆` and
  `C.im (A x) = ⁅ξ, C.re x⁆`; then the `ad`-invariance of `B`
  (`TauCeti.Lie.lieInvariant_iff_adjoint_invariant`) gives
  `Bc (A x) y = Bc x (A y)`. Then Tau Ceti's
  `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top`
  (`Analysis/InnerProductSpace/Spectral/Relative.lean`), for the positive
  definite form `Bc`, spans the Lie algebra of `Gc` by eigenspaces of `A`.
- `parabolicSubspace_sup_range_lieMap : C.parabolicSubspace ξ ⊔ LinearMap.range C.lieMap.toLinearMap = ⊤`.
  Proof: the conjugation `τ x := C.lieMap (C.re x) - C.cplx (C.lieMap (C.im x))`
  anticommutes with `A` (by the same formulas), so it maps the eigenspace
  of `λ` to that of `-λ`. For `x` in the eigenspace of `λ > 0`,
  `x = 2 • C.lieMap (C.re x) - τ x` with `τ x` in the eigenspace of `-λ`;
  the other eigenspaces lie in `C.parabolicSubspace ξ`.
- `mulInvariantExp_mem_parabolic`: for `x ∈ C.parabolicSubspace ξ`,
  `mulInvariantExp x ∈ C.parabolic ξ`, by `TauCeti.Lie.conj_mulInvariantExp`
  (`Geometry/Lie/Adjoint/Exponential/Basic.lean`) and continuity of
  `mulInvariantExp`. With `toHom_mulInvariantExp`, the map
  `F (x, y) := mulInvariantExp (x : EC) * C.toHom (mulInvariantExp y)` on
  `C.parabolicSubspace ξ × E` takes values in the set
  `S := C.parabolic ξ * Set.range C.toHom`.
- `parabolic_mul_range_toHom_mem_nhds_one : S ∈ 𝓝 1`. In the logarithm
  chart `mulInvariantLogChart` of Tau Ceti's
  `Geometry/Lie/Exponential/LocalInverse.lean`, whose derivative at `1` is
  the identity (`hasFDerivAt_mulInvariantLogChart_one`), the map `F` is
  strictly differentiable at `0` with derivative `(x, y) ↦ x + C.lieMap y`,
  which is onto by `parabolicSubspace_sup_range_lieMap`. Mathlib's
  `HasStrictFDerivAt.map_nhds_eq_of_surj`
  (`Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`) then makes the
  image of `F` a neighbourhood of `1`.
- `parabolic_mul_range_toHom_eq_univ : (C.parabolic ξ : Set Gc) * Set.range C.toHom = Set.univ`
  (Theorem D.3), with the two forms used below,
  `exists_mem_parabolic_mul_toHom : ∃ q ∈ C.parabolic ξ, ∃ u, g = q * C.toHom u`
  and `exists_toHom_mul_mem_parabolic : ∃ u, ∃ q ∈ C.parabolic ξ, g = C.toHom u * q`
  (the first applied to `g⁻¹`). Proof: `S` is open, since for
  `g = q * C.toHom u` and a neighbourhood `V ⊆ S` of `1`, the neighbourhood
  `q • V • C.toHom u` of `g` lies in `S`. `S` is closed: for `k` in
  `closure (C.parabolic ξ)`, the neighbourhood `k * V⁻¹` of `k` meets
  `C.parabolic ξ`, so `k ∈ C.parabolic ξ * V ⊆ S`; hence
  `S = closure (C.parabolic ξ) * Set.range C.toHom`, closed by Mathlib's
  `IsClosed.mul_right_of_isCompact` (`Topology/Algebra/Group/Pointwise.lean`),
  since `G` is compact. `Gc` is connected (`C.connectedSpace`) and `S` is
  nonempty.

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
  theorem): if `y = g₀⁻¹ • x` and `mgradient I' (momentNormSq μ (B.toDual hB).symm)`
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
  `momentNormSq μ (B.toDual hB).symm x∞ = ⨅ g : Gc, momentNormSq μ (B.toDual hB).symm (g • p)`. Both
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
  $w_\mu(p,\xi)\le\|\xi\|\,\|\mu(gp)\|$ for every $\xi\in\mathfrak g$ (in particular
  $\xi\in\Lambda$) and $g\in G^{\mathbb C}$,
  with both norms those of `B`: `√(B ξ ξ)` and `√(momentNormSq μ (B.toDual hB).symm (g • p))`.
- `momentWeight_toHom_smul : momentWeight C μ (C.toHom u • x) (Ad u ξ) = momentWeight C μ x ξ`
  and `limitPoint_toHom_smul : limitPoint C (C.toHom u • x) (Ad u ξ) = C.toHom u • limitPoint C x ξ`,
  from `toHom_mul_expI_mul_inv` and `moment_toHom_smul` (decision 8 (iii)).
- `limitPoint_smul_of_mem_parabolic`: for `q ∈ C.parabolic ξ`,
  `limitPoint C (q • x) ξ = C.parabolicLimit ξ q • limitPoint C x ξ`, since
  `C.expI (t • ξ) • q • x` is the conjugate of `q` at time `t` acting on
  `C.expI (t • ξ) • x`; by continuity of the action of `Gc` and
  `limitPoint_eq_of_tendsto`.
- `tendsto_kempfNessFunction_expI_neg_smul_div`:
  `Φ_p (C.expI (-(s • ξ))) / s → -momentWeight C μ p ξ` as `s → ∞`. By
  `kempfNessFunction_expI` the quotient is
  `-∫ t in 0..1, μ (C.expI ((t * s) • ξ) • p) ξ`, and dominated convergence
  (`intervalIntegral.tendsto_integral_filter_of_dominated_convergence`, with
  the bound from compactness of `M`) and `tendsto_momentWeight` give the
  limit. It does not use the slope identity.
- `abs_kempfNessFunction_expI_mul_toHom_le`: if `√(momentNormSq μ (B.toDual hB).symm y) ≤ L`
  for all `y`, then `|Φ_p (C.expI η * C.toHom u)| ≤ L * √(B η η)` for every
  `p`, from `kempfNessFunction_expI_mul_toHom` and
  `abs_apply_le_sqrt_momentNormSq_mul_sqrt`.
- `momentWeight_smul_of_mem_parabolic`: for `q ∈ C.parabolic ξ`,
  `momentWeight C μ (q • x) ξ = momentWeight C μ x ξ` (decision 8 (i)).
  Proof: by `kempfNessFunction_mul`,
  `Φ_{q • x} (C.expI (-(s • ξ))) = Φ_x (C.expI (-(s • ξ)) * k s) - Φ_x q⁻¹`
  with `k s := C.expI (s • ξ) * q⁻¹ * C.expI (-(s • ξ))`, and, again by
  `kempfNessFunction_mul`, `Φ_x (C.expI (-(s • ξ)) * k s)` differs from
  `Φ_x (C.expI (-(s • ξ)))` by `Φ_y (k s)` for some `y`. As `k s` converges,
  its polar radius (through the continuous `C.polar.symm`) is bounded, so
  the difference is bounded by the previous item; divide by `s` and apply
  `tendsto_kempfNessFunction_expI_neg_smul_div` twice.

*How the criteria use them.* The necessity halves and the sufficiency
half of the stable criterion go through the following lemmas, in
`HilbertMumford.lean` unless another file is named; the sufficiency half
of the polystable criterion,
`isPolystable_of_isSemistable_of_limitPoint_mem_orbit`, is given after
them, under *Sufficiency for polystability*. Let `Ad` be `Lie.tangentAd`.

- `momentWeight_eq_moment_iff`: `momentWeight C μ x ξ = μ x ξ` exactly
  when `C.expI (t • ξ) • x = x` for every `t`, in the setting of
  `momentWeight_le`. Forward: for `t ≥ 0`,
  `μ x (t • ξ) = t * momentWeight C μ x ξ ≤ μ (C.expI (t • ξ) • x) (t • ξ)`
  by `momentWeight_le_moment_expI_smul`, so
  `expI_smul_eq_self_of_moment_apply_le`, applied to `t • ξ`, fixes `x`;
  for `t < 0`, apply `C.expI (t • ξ)` to the case `-t` (`expI_add_smul`).
  Backward: the function in `tendsto_momentWeight` is then constant
  (`tendsto_nhds_unique`). Fixed points of all `C.expI (t • ξ)` are the
  zeros of `X_ξ` (`expI_smul_smul_eq_self_iff`).
- `exists_momentWeight_smul_eq_moment_of_forall_expI_smul_eq`: if every
  `C.expI (t • λ)` fixes `x`, then for each `g : Gc` some `u : G` has
  `momentWeight C μ (g • x) (Ad u λ) = μ x λ`. Proof: write
  `g = C.toHom u * q` with `q ∈ C.parabolic λ`
  (`exists_toHom_mul_mem_parabolic`); then
  `momentWeight_toHom_smul`, `momentWeight_smul_of_mem_parabolic` and
  `momentWeight_eq_moment_iff` give
  `momentWeight C μ (g • x) (Ad u λ) = momentWeight C μ (q • x) λ = momentWeight C μ x λ = μ x λ`.
- `IsPolystable.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero`:
  if `p` is polystable and `momentWeight C μ p ξ = 0`, there are
  `q ∈ C.parabolic ξ` and `x` with `μ x = 0`,
  `∀ t : ℝ, C.expI (t • ξ) • x = x` and `p = q • x`. Proof: take `g` with
  `μ (g • p) = 0` (`isPolystable_iff_exists_smul`) and write
  `g⁻¹ = q * C.toHom u` with `q ∈ C.parabolic ξ`
  (`exists_mem_parabolic_mul_toHom`); put `x = C.toHom u • g • p`, so that
  `p = q • x` and `μ x = 0` (`moment_toHom_smul`). By
  `momentWeight_smul_of_mem_parabolic`,
  `momentWeight C μ x ξ = 0 = μ x ξ`, and `momentWeight_eq_moment_iff`
  concludes. It holds for every `ξ`, not only for periods.
- `IsPolystable.limitPoint_mem_orbit` (the necessity half of the polystable
  criterion), in the setting of `tendsto_limitPoint`: if `p` is polystable
  and `momentWeight C μ p ξ = 0`, then `limitPoint C p ξ ∈ MulAction.orbit Gc p`.
  With `q` and `x` from the previous item, `limitPoint C x ξ = x`
  (`limitPoint_eq_of_tendsto` for the constant curve), so
  `limitPoint C p ξ = C.parabolicLimit ξ q • x`
  (`limitPoint_smul_of_mem_parabolic`), and `x = q⁻¹ • p`. Its
  semistability part is `IsPolystable.isSemistable`.
- `IsStable.momentWeight_neg` (the necessity half of the stable criterion):
  if `p` is stable and `ξ ≠ 0`, then `momentWeight C μ p ξ < 0`. The weight
  is `≤ 0` by `IsSemistable.momentWeight_nonpos`. If it were `0`, take `q`
  and `x` as above: `X_ξ` vanishes at `x` (`expI_smul_smul_eq_self_iff`),
  and the stabilizer of `x` in `Gc` is discrete, since that of `p` is and
  `x = q⁻¹ • p` (`MulAction.discreteTopology_stabilizer_smul_iff`). As
  `μ x = 0`, `IsComplexifiedAction.discreteTopology_stabilizer_iff_of_moment_eq_zero`
  then gives `ξ = 0`. That lemma, already in `KempfNess/Basic.lean`, is
  how a trivial isotropy algebra of a zero of `μ` in `G` gives a discrete
  stabilizer in `Gc`, and back; no path in the stabilizer is needed.
- `exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le`
  (`Geometry/Lie/Exponential/Periods.lean`): for compact `G` and `ξ ≠ 0`,
  some `λ ∈ nonzeroPeriods I G` has
  `closedOneParameterSubgroup λ ≤ closedOneParameterSubgroup ξ`. Proof:
  `T := closedOneParameterSubgroup ξ` is a torus
  (`isTorus_closedOneParameterSubgroup`), not `⊥` because some
  `mulInvariantExp (t • ξ) ≠ 1` (`forall_mulInvariantExp_smul_eq_one_iff`),
  so it has an element `k ≠ 1` with `k ^ 2 = 1`
  (`IsTorus.exists_sq_eq_one_ne_one`), which is `lieExp X` for some `X` in
  the Lie algebra of `T` (`IsTorus.image_lieExp_lieSubalgebraOfSubgroup`).
  Let `λ` be twice the image of `X` in `𝔤` (`lieExp_eq_mulInvariantExp`):
  `mulInvariantExp λ = k ^ 2 = 1` (`mulInvariantExp_nsmul`), `λ ≠ 0` since
  `k ≠ 1`, and every `mulInvariantExp (t • λ)` lies in `T`
  (`mem_lieSubalgebraOfSubgroup`, `T` being closed), so
  `closedOneParameterSubgroup_le` gives the inclusion. This is how a
  nonzero element of an isotropy algebra gives a nonzero period in it, by
  `mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le`; it needs no
  Lie algebra of the stabilizer, and the approximation of
  `mem_closure_smul_nonzeroPeriods` would not do, since its periods need
  not fix the point.
- `isStable_of_momentWeight_neg` (`KempfNess/NumericalCriterion.lean`;
  the sufficiency half of the stable criterion), with `hJi`: if `momentWeight C μ p λ < 0` for every
  `λ ∈ nonzeroPeriods I G`, then `p` is stable. It is semistable
  (`isSemistable_iff_momentWeight_nonpos`), so polystable by
  `isPolystable_of_isSemistable_of_limitPoint_mem_orbit`, whose condition
  holds vacuously; take `g` with `μ (g • p) = 0` and put `y = g • p`. By
  `isStable_smul_iff` and `isStable_of_moment_eq_zero`, it is enough that
  the stabilizer of `y` is discrete, that is, by
  `IsComplexifiedAction.discreteTopology_stabilizer_iff_of_moment_eq_zero`,
  that `X_ξ y = 0` only for `ξ = 0`. If `ξ ≠ 0` had `X_ξ y = 0`, the
  previous item and
  `mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le` would give
  `λ ∈ nonzeroPeriods I G` with `X_λ y = 0`, so every `C.expI (t • λ)` fixes
  `y` (`expI_smul_smul_eq_self_iff`), and
  `exists_momentWeight_smul_eq_moment_of_forall_expI_smul_eq` at `g⁻¹` some
  `u` with `momentWeight C μ p (Ad u λ) = μ y λ = 0`. But
  `Ad u λ ∈ nonzeroPeriods I G` (`tangentAd_mem_nonzeroPeriods`), whose
  weight is negative.
- `exists_momentWeight_pos_of_not_isSemistable`: a destabilizing
  $\xi\in\Lambda$, by the route of *The destabilizing direction* below.
- `isSemistable_iff_momentWeight_nonpos`; and, in
  `KempfNess/NumericalCriterion.lean`,
  `isPolystable_iff_isSemistable_and_limitPoint_mem_orbit`, from
  `IsPolystable.isSemistable`, `IsPolystable.limitPoint_mem_orbit` and
  `isPolystable_of_isSemistable_of_limitPoint_mem_orbit`; and
  `isStable_iff_momentWeight_neg`, from `IsStable.momentWeight_neg` and
  `isStable_of_momentWeight_neg`. The quantifiers range over all of
  `nonzeroPeriods I G`, as the page says, and the polystable criterion
  keeps the restriction to those `ξ` with `momentWeight C μ p ξ = 0`.
  The polystable and stable criteria take `hJi`.
- `hilbertMumford` (`KempfNess/NumericalCriterion.lean`): the milestone,
  in the setting of `tendsto_limitPoint`
  with the hypotheses of `kempfNess`, the invariance of `J` under `G` and
  `hJi`. For every `p`: for each
  `ξ ∈ nonzeroPeriods I G`, `t ↦ μ (C.expI (t • ξ) • p) ξ` tends to
  `momentWeight C μ p ξ` and `t ↦ C.expI (t • ξ) • p` to `limitPoint C p ξ`
  (`tendsto_momentWeight`, `tendsto_limitPoint`); and the three criteria
  above, as a conjunction. Milestone: *Hilbert–Mumford numerical
  criteria*.

Edge cases: `G` trivial has $\Lambda=\emptyset$, and every point is
stable, since $\mathfrak g^*=0$; `M` is nonempty, being connected.

### Sufficiency for polystability

This follows [GeorgoulasRobbinSalamon2021] (arXiv v2, Theorem 12.5, Steps
1–7), with the holomorphic part gathered into one lemma at a zero of
$\mu$. Let `p` be semistable and not polystable, and let `x` be the limit
of the negative gradient flow of `momentNormSq` from `p`
(`tendsto_maximalIntegralCurve_momentNormSq`). The flow stays in
`MulAction.orbit Gc p` (`exists_mem_orbit_maximalIntegralCurve`), so `x`
lies in its closure. By `momentNormSq_limit_eq_iInf`, `isSemistable_iff`
and the continuity of `momentNormSq`, `momentNormSq … x = 0`, so `μ x = 0`
(`momentNormSq_eq_zero_iff`); and `x ∉ MulAction.orbit Gc p`, since
otherwise `p` would be polystable (`isPolystable_iff`). This is
Theorem 7.2 there. The local criterion takes this `x`, and not any zero
of `μ` in the closure of the orbit, because its proof follows the flow
into the chart.

- `exists_mem_nonzeroPeriods_tendsto_expI_smul`
  (`KempfNess/HolomorphicSlice.lean`), the local criterion: in the setting
  of `tendsto_limitPoint`, with the hypotheses of `kempfNess`, the
  invariance of `J` under `G` and `hJi`, if the negative gradient flow of
  `momentNormSq μ (B.toDual hB).symm` from `p` tends to `x`, `μ x = 0`
  and `x ∉ MulAction.orbit Gc p`, then there are
  `y ∈ MulAction.orbit Gc p` and `λ ∈ nonzeroPeriods I G` with
  `Tendsto (fun t ↦ C.expI (t • λ) • y) atTop (𝓝 x)`. Edge case: for `G`
  trivial the orbit is `{p}`, closed, so the hypotheses cannot hold. The
  route, with `H` the stabilizer of `x` in `G` and `H₀` its identity
  component, is given under *The local criterion* below. It needs no
  holomorphic slice theorem: the flow itself, written in a chart at `x`
  as an orbit point times a point of a linear slice, carries the slice
  coordinate along one orbit of the complexification of `H₀` (Steps 2–4
  of the source).
- `exists_momentWeight_eq_zero_limitPoint_not_mem_orbit`
  (`HilbertMumford.lean`), steps 6–7 of the source: in the setting of
  `tendsto_limitPoint`, if `y ∈ MulAction.orbit Gc p`,
  `λ ∈ nonzeroPeriods I G`, `C.expI (t • λ) • y → x` as `t → ∞`, `μ x = 0`
  and `x ∉ MulAction.orbit Gc p`, then some `ξ ∈ nonzeroPeriods I G` has
  `momentWeight C μ p ξ = 0` and `limitPoint C p ξ ∉ MulAction.orbit Gc p`.
  Proof: `momentWeight C μ y λ = μ x λ = 0` (`tendsto_momentWeight`,
  continuity of `μ`, `tendsto_nhds_unique`) and `limitPoint C y λ = x`
  (`limitPoint_eq_of_tendsto`). Write `p = g • y` and
  `g = C.toHom u * q` with `q ∈ C.parabolic λ`
  (`exists_toHom_mul_mem_parabolic`). By `momentWeight_smul_of_mem_parabolic`,
  `limitPoint_smul_of_mem_parabolic`, `momentWeight_toHom_smul` and
  `limitPoint_toHom_smul`, `ξ = Ad u λ` has weight `0` at `p` and limit
  point `C.toHom u • C.parabolicLimit λ q • x`, which lies in the orbit of
  `x`, disjoint from that of `p`; and `ξ ∈ nonzeroPeriods I G`
  (`tangentAd_mem_nonzeroPeriods`). It does not use `hJi`.
- `isPolystable_of_isSemistable_of_limitPoint_mem_orbit`
  (`KempfNess/NumericalCriterion.lean`): in the setting of
  `tendsto_limitPoint`, with the hypotheses of `kempfNess`, the invariance
  of `J` under `G` and `hJi`, if `p` is semistable and
  `limitPoint C p ξ ∈ MulAction.orbit Gc p` for every
  `ξ ∈ nonzeroPeriods I G` with `momentWeight C μ p ξ = 0`, then `p` is
  polystable. Otherwise take `x` as above; the two previous items give a
  `ξ` that contradicts the hypothesis.

### The local criterion

The proof of `exists_mem_nonzeroPeriods_tendsto_expI_smul` follows Steps
1–5 of [GeorgoulasRobbinSalamon2021] (arXiv v2, proof of Theorem 12.5),
with their Lemma 2.3 for the stabilizer and Theorem 12.4 (with Lemma 8.4
and Theorem 8.5) for the linear case. Fix `x` as in the statement, so
`μ x = 0`; `H = MulAction.stabilizer G x` is closed in the compact `G`,
hence compact. Write `𝔥 ⊆ 𝔤` for the isotropy algebra of `x`, the `ξ`
with `X_ξ x = 0`, which is the Lie algebra of `H` and of `H₀`
(`TauCeti.Lie.lieSubalgebraOfSubgroup_ambientConnectedComponentOfOne_stabilizer`),
and `𝔤c_x` for the `Z` in the Lie algebra of `Gc` with `X_Z x = 0`. Since
`μ x = 0`,
`IsComplexifiedAction.fundamentalVectorField_eq_zero_iff_of_moment_eq_zero`
makes `𝔤c_x` the sum of `C.lieMap 𝔥` and `C.cplx (C.lieMap 𝔥)`. The
files below go in `Geometry/Symplectic/Hamiltonian/MomentMap/KempfNess/`.
`HilbertMumford.lean` imports none of them, and they import it only where
they use the semistable criterion, so the two halves do not import each
other.

**`KempfNess/Stabilizer.lean`** (the complexified stabilizer, Step 1 of
the source, first half).

- `polar_symm_mem_stabilizer_iff_of_moment_eq_zero`: if `μ x = 0`, then
  `g ∈ MulAction.stabilizer Gc x` exactly when, for
  `(η, u) = C.polar.symm g`, `X_η x = 0` and `u ∈ H` (Lemma 2.3 of the
  source). Backward: `C.expI η` fixes `x` (`expI_smul_smul_eq_self_iff`).
  Forward: `y = C.toHom u • x` has `μ y = 0` (`moment_toHom_smul`) and
  `C.expI η • y = x`; `t ↦ μ (C.expI (t • η) • y) η` is antitone
  (`antitone_moment_expI`) and vanishes at `t = 0` and `t = 1`, so it is
  constant there, `X_η` vanishes along the curve (`hasDerivAt_moment_expI`),
  the curve is constant, and `y = x`.
- `mem_stabilizer_of_hasLeftTrivializedDerivOn`: a curve `k : ℝ → Gc`
  on an interval `s` with `k t₀ = 1` and left-trivialized derivative in
  `𝔤c_x` on `s` takes values in the identity component `Gc₀` of
  `MulAction.stabilizer Gc x` (Tau Ceti's
  `Subgroup.ambientConnectedComponentOfOne`). The curve `t ↦ k t • x` has
  derivative `mfderiv (k t • ·) x (X_ζ x) = 0`, so it is constant, and
  `k` is a connected curve through `1` in the stabilizer.
- `stabilizerComplexification C hx : LieComplexification I₀ H₀ IC₀ Gc₀`,
  with `H₀` and `Gc₀` the identity components of the stabilizers of `x`
  in `G` and `Gc`, closed subgroups made Lie groups by
  `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` (`I₀`, `IC₀` their
  models). Its `toHom` is `C.toHom` restricted (it maps `H₀` into `Gc₀`,
  being continuous and `H₀` connected); `cplx` is `C.cplx` on the Lie
  algebra of `Gc₀`, read as `𝔤c_x` through
  `EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype_eq_isotropy`
  (`Geometry/Lie/Subgroup/IdentityComponent.lean`); and `polar` is
  `C.polar` restricted to `𝔥 × H₀`. By the first item, `C.polar` maps
  `𝔥 × H` onto the stabilizer of `x` in `Gc`, so, being a
  homeomorphism, it maps the component `𝔥 × H₀` of `(0, 1)` onto `Gc₀`.
  `H₀` is compact and connected, so the setting holds for it.
- `stabilizerComplexification_expI` and `mem_nonzeroPeriods_of_stabilizer`:
  through the inclusion of Lie algebras, the `expI` of
  `stabilizerComplexification C hx` is that of `C`, and a nonzero period of
  `H₀` is one of `G` (`EmbeddedLieSubgroupData.coe_mulInvariantExp`,
  `EmbeddedLieSubgroupData.injective_groupLieAlgebraMap_subtype`). These
  replace the passage from `H exp(i𝔥)` to its identity component: the
  curve of Step 4 starts at `1`, so it never leaves `Gc₀`.

**`KempfNess/HolomorphicChart.lean`** (Step 1, second half; the only use
of `hJi` besides the statements that pass it on).

- `exists_equivariant_holomorphic_chart`: with `hJi`, `J` invariant under
  `G` and `H` compact, there is an `OpenPartialHomeomorph M E'` `e`, smooth
  with smooth inverse, with `e x = 0`, derivative the identity at `x`,
  `H`-invariant source, `e (h • z) = mfderiv I' I' (h • ·) x (e z)` for
  `h ∈ H`, and `J` constant in it:
  `mfderiv e z (J z v) = J x (mfderiv e z v)` on its source. Proof: take a
  chart in which `J` is constant (`isIntegrable_iff_mfderiv`), composed
  with a linear map so that its derivative at `x` is the identity and its
  constant structure is `J x`, and average it over the Haar measure of `H`
  as Tau Ceti's `TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`
  (`Geometry/Manifold/GroupAction/EquivariantSlice.lean`) does for smooth
  charts, which already gives `H` the Lie group structure of the closed
  subgroup theorem. The average keeps `J` constant because each `h ∈ H` is
  `J`-holomorphic near `x`, by the invariance of `J`; that `dh_x` is
  `J`-linear would not be enough. The averaging lemma that Tau Ceti's
  proof uses is private there, so this file proves the step it needs
  (differentiation under the integral sign of a family of maps with
  `J x`-linear derivatives) and credits Tau Ceti's theorem.
- `fundamentalVectorField_chart_symm`: for `ξ, η ∈ 𝔥`,
  `Z = C.lieMap ξ + C.cplx (C.lieMap η)` and `v` in the target of `e`,
  `X_Z (e.symm v) = mfderiv (e.symm) v (A ξ v + J x (A η v))`, where `A ξ`
  is the derivative at `0` of `t ↦ mfderiv (mulInvariantExp (t • ξ) • ·) x`,
  a `J x`-linear map, skew for `g_J` at `x`. For `η = 0` this is the
  derivative of the equivariance at `h = mulInvariantExp (t • ξ)`
  (equation (12.5) of the source); for `ξ = 0`, `X_{iη} = J X_η` and `J`
  is constant in `e`.
- `expI_smul_chart_symm`: if `NormedSpace.exp (s • (J x ∘ A λ)) v` lies in
  the target of `e` for `s ∈ [0, t]`, then
  `C.expI (t • λ) • e.symm v = e.symm (NormedSpace.exp (t • (J x ∘ A λ)) v)`:
  both are integral curves of `X_{iλ}` from `e.symm v`
  (`isMIntegralCurve_expI_smul`, the previous item), so they agree.

**`KempfNess/Projective.lean`** (the linear case, Theorem 12.4 of the
source). Here `C : LieComplexification I G IC Gc` is any complexification
in the setting, `V = Fin (n + 1) → ℂ` with the Hermitian product of
`EuclideanSpace`, and `ρ : Gc →* Matrix.GeneralLinearGroup (Fin (n + 1)) ℂ`
is smooth, unitary on `C.toHom` (`Matrix.unitaryGroup`), and complex in
its derivative: `dρ (C.cplx Z) = Complex.I • dρ Z`.

- The action of `Gc` on `ℙ ℂ V` through `ρ` (Tau Ceti's
  `Projectivization.mapDiffeomorph` at the linear equivalence `ρ g`), with the
  library's `fubiniStudyForm n` and `ofComplexManifold`; the invariance of
  both under `G` (`mpullback_unitary_fubiniStudyForm`); and
  `isComplexifiedAction_projectivization`. The fundamental vector field of
  `ξ` at `[y]` is the image of `dρ ξ • y` under the differential of the
  projection, which identifies it with the generator of Tau Ceti's
  `TauCeti.ComplexProjectiveSpace.unitaryAction` at `dρ ξ`, an
  identification Tau Ceti leaves open.
- `projectivizationMoment ρ : ℙ ℂ V → Module.Dual ℝ 𝔤`, a constant multiple
  of Tau Ceti's `TauCeti.ComplexProjectiveSpace.unitaryMomentMap` composed
  with `dρ` and `diffeomorphProjectivization`, and
  `isEquivariantMomentMap_neg_projectivizationMoment` for the *Sign*
  convention. It is transported from `isMomentMap_unitaryMomentMap` and
  `unitaryMomentMap_smul`, not derived again; the constant comes from
  `fubiniStudyForm n` being `π` times the pull-back of Tau Ceti's form, for
  which `unitaryMomentMap` is a moment map of `-2π` times it.
- `kempfNessFunction_projectivization_mk`: for `v ≠ 0`,
  `Φ_[v] g = c * (Real.log ‖ρ g' v‖ ^ 2 - Real.log ‖v‖ ^ 2)` with `c > 0`
  and `g'` equal to `g` or `g⁻¹` as the *Sign* bullet decides, by
  `existsUnique_kempfNessFunction`; and
  `not_isSemistable_projectivization_mk`: if `0` lies in the closure of
  `{ρ g v | g}`, `[v]` is not semistable
  (`isSemistable_iff_bddBelow_kempfNessFunction`) (Theorem 8.5 there).
- `tendsto_smul_zero_of_momentWeight_pos`: if
  `momentWeight C (projectivizationMoment ρ) [v] λ > 0`, then `v` lies in
  the sum of the eigenspaces of one sign of the Hermitian matrix
  `-Complex.I • dρ λ`, so `ρ (C.expI (t • λ')) v → 0` with antitone norm,
  for `λ'` equal to `λ` or `-λ` as the sign decides (Lemma 8.4 there).
  The moment along `C.expI (t • λ)` is a weighted mean of the eigenvalues
  of the components of `v`, with weights `exp (2 t a) ‖v_a‖ ^ 2`.
- `exists_mem_nonzeroPeriods_tendsto_smul_zero` (Theorem 12.4 there): if
  `v ≠ 0` and `0` lies in the closure of `{ρ g v | g}`, some
  `λ ∈ nonzeroPeriods I G` has `ρ (C.expI (t • λ)) v → 0` as `t → ∞`
  with antitone norm. By the previous two items and
  `isSemistable_iff_momentWeight_nonpos` for `ℙ ℂ V`, which is compact,
  connected and modelled on `𝓘(ℝ, Fin n → ℂ)`, as `tendsto_limitPoint`
  needs; `nonzeroPeriods` is closed under negation.

**`KempfNess/HolomorphicSlice.lean`** (Steps 2–5 of the source). Let `e` be
the chart of `exists_equivariant_holomorphic_chart`, and `T ⊆ E'` the
complex orbit tangent space `{X_Z x | Z}`, which is the `g_J`-orthogonal
sum of `{X_ξ x | ξ}` and its image under `J x`: the two are orthogonal
because the orbit of a zero of `μ` is isotropic (Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_inf_orthogonal`).

- `slice`: the `g_J`-orthogonal complement `S` of `T` at `x`, a
  `J x`-invariant subspace, invariant under `A ξ` and under
  `mfderiv (h • ·) x` for `ξ ∈ 𝔥` and `h ∈ H` (equation (12.6) of the
  source: `A ξ (X_η x) = X_⁅ξ, η⁆ x`, and `A ξ` is skew). Tau Ceti's
  symplectic slice `SymplecticSlice` is `W^σ ⧸ W` with `W` the real orbit
  tangent space, and `J x` does not preserve `W^σ`; `S` maps
  isomorphically onto it, `H`-equivariantly, but the steps below need a
  `J x`-invariant subspace of `E'`, so they use `S`.
- `ker_sliceOperator_eq` (Step 2): for `v ∈ S` near `0`, the kernel of
  `(Z, w) ↦ X_Z (e.symm v) - mfderiv e.symm v w` on the Lie algebra of
  `Gc` times `S` is `{(C.lieMap ξ + C.cplx (C.lieMap η), A ξ v + J x (A η v)) | ξ, η ∈ 𝔥}`.
  This set lies in the kernel by `fundamentalVectorField_chart_symm`; the
  operator is onto at `v = 0`, so near it, and the kernel then has the
  dimension `2 dim 𝔥` of this set.
- `exists_eventually_eq_expI_mul_smul_chart_symm` (Step 3): with `𝔥ᗮ` the
  `B`-orthogonal complement of `𝔥`, the map
  `(α, β, v) ↦ C.expI α * C.toHom (mulInvariantExp β) • e.symm v` on
  `𝔥ᗮ × 𝔥ᗮ × S` has bijective derivative at `0`, so it is a local
  diffeomorphism there (`HasStrictFDerivAt.toOpenPartialHomeomorph`), and
  the flow from `p`, which tends to `x`, is eventually
  `C.expI (α t) * C.toHom (mulInvariantExp (β t)) • e.symm (v t)` with
  `α, β, v` differentiable and `v t` near `0`.
- `exists_mem_stabilizer_slice_eq` (Step 4): with `g` the flow curve of
  `exists_mem_orbit_maximalIntegralCurve`, `h t` the element
  `C.expI (α t) * C.toHom (mulInvariantExp (β t))` and
  `k t = (h t₀)⁻¹ * (g t₀)⁻¹ * g t * h t`, one has
  `e.symm (v t) = (k t)⁻¹ • e.symm (v t₀)` for `t ≥ t₀`. Differentiating,
  `ker_sliceOperator_eq` puts the left-trivialized derivative of `k` in
  `𝔤c_x`, so `k t ∈ Gc₀` (`mem_stabilizer_of_hasLeftTrivializedDerivOn`),
  and `v t = ρ (k t)⁻¹ (v t₀)`, where `ρ` is the tangent representation
  `g ↦ mfderiv (g • ·) x` of `Gc₀` on `S` (Tau Ceti's
  `tangentRepresentation`): both sides solve the same linear equation
  (`ODE_solution_unique_of_mem_Icc`). `ρ` preserves `S` and is
  `J x`-linear, since by `polar_symm_mem_stabilizer_iff_of_moment_eq_zero`
  every element of `Gc₀` is `C.expI η * C.toHom u` with `η ∈ 𝔥` and
  `u ∈ H₀`, and `ρ (C.expI η)` is `NormedSpace.exp (J x ∘ A η)` by
  `expI_smul_chart_symm`. In an orthonormal basis of `S` for the
  Hermitian product of `g_J` and `J x`, `ρ` is a representation of
  `stabilizerComplexification C hx` as `Projective.lean` takes it.
- The local criterion (Step 5): `v t₀ ≠ 0`, since otherwise
  `x ∈ MulAction.orbit Gc p`; `v t → 0` lies in the `Gc₀`-orbit of `v t₀`,
  so `exists_mem_nonzeroPeriods_tendsto_smul_zero` gives a period `λ` of
  `H₀` with `ρ (expI (t • λ)) (v t₀) → 0` and antitone norm. The curve
  stays in the ball of `S` where `e.symm` is defined, so by
  `expI_smul_chart_symm`, `C.expI (t • λ) • e.symm (v t₀) → e.symm 0 = x`,
  with `e.symm (v t₀) = (h t₀)⁻¹ • (g t₀)⁻¹ • p` in the orbit of `p`, and
  `λ ∈ nonzeroPeriods I G` (`mem_nonzeroPeriods_of_stabilizer`).

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

- `sqrt_polar_symm_fst_le_add_mul` (`Geometry/Lie/Complexification/Polar.lean`,
  with the polar radius): for connected `G`, a symmetric, nonnegative, `Ad`-invariant `B`,
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
  `⨅ g : Gc, momentNormSq μ (B.toDual hB).symm (g • p) = 0` then `p` is semistable: the
  limit of the flow (`tendsto_maximalIntegralCurve_momentNormSq`) lies in
  the closure of the orbit (`exists_mem_orbit_maximalIntegralCurve`), and
  `momentNormSq_limit_eq_iInf` and `momentNormSq_eq_zero_iff` make it a
  zero of `μ`. The proof of
  `isSemistable_iff_bddBelow_kempfNessFunction` has this step inline; the
  building issue moves it here.
- `exists_momentWeight_pos_of_iInf_momentNormSq_pos` (`HilbertMumford.lean`):
  in that setting, if `0 < m²` for `m² := ⨅ g : Gc, momentNormSq μ (B.toDual hB).symm (g • p)`,
  some `ξ` with `B ξ ξ = 1` has `0 < momentWeight C μ p ξ`. Proof: take
  the flow curve `g` of `exists_mem_orbit_maximalIntegralCurve`, so
  `Φ_p (g t) ≤ -2 * m² * t` for `t ≥ 0` (`Φ_p 1 = 0` by
  `kempfNessFunction_toHom`), and let `r t` be the polar radius
  of `g t`, with `g t = C.expI (r t • ζ t) * C.toHom (u t)` and
  `B (ζ t) (ζ t) = 1` when `r t > 0` (`expI_mul_toHom_polar_symm`). Let `L`
  be the maximum of `√(momentNormSq μ (B.toDual hB).symm)` on `M`; `L ≥ m > 0`.
  1. `r t ≤ 2 * L * t`, by `sqrt_polar_symm_fst_le_add_mul`, since the
     imaginary part of the left-trivialized derivative is
     `-2 • momentSharp B hB μ ((g t)⁻¹ • p)` (`im_cplx_lieMap`).
  2. `r t ≥ 2 * m² * t / √(momentNormSq μ (B.toDual hB).symm p)`, by
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
  `hasDerivAt_Ad_lieExp_smul_apply_zero`; for the criteria, checked at the
  pinned version `0aaa80fd07b7`, `isTorus_closedOneParameterSubgroup`,
  `closedOneParameterSubgroup_le`, `forall_mulInvariantExp_smul_eq_one_iff`
  and `mulInvariantExp_nsmul` (`Geometry/Lie/Subgroup/OneParameter.lean`,
  `Geometry/Lie/Exponential/`), `IsTorus.exists_sq_eq_one_ne_one` and
  `IsTorus.image_lieExp_lieSubalgebraOfSubgroup`
  (`Geometry/Lie/Subgroup/Torus.lean`), `mem_lieSubalgebraOfSubgroup`
  (`Geometry/Lie/Subgroup/LieAlgebra.lean`) and
  `mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le`
  (`Geometry/Lie/Subgroup/Stabilizer.lean`); for decision 8,
  `TauCeti.Lie.tangentAd_mulInvariantExp_apply`,
  `TauCeti.Lie.conj_mulInvariantExp`,
  `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top` and
  `mulInvariantLogChart`; for the
  local criterion, `TauCeti.exists_equivariant_contMDiff_chart_of_isCompact_stabilizer`,
  `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`,
  `Subgroup.ambientConnectedComponentOfOne`, `tangentRepresentation`,
  `TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_inf_orthogonal`,
  `Projectivization.mapDiffeomorph`,
  `TauCeti.ComplexProjectiveSpace.unitaryMomentMap`,
  `unitaryMomentMap_smul`, `isMomentMap_unitaryMomentMap` and
  `unitaryAction`, checked at `0aaa80fd07b7`.
- From Mathlib: `IsCompact.continuous_sInf` (`Topology/Order/Compact.lean`)
  and the comparison lemmas of `Analysis/Calculus/MeanValue.lean`; for
  decision 8, `HasStrictFDerivAt.map_nhds_eq_of_surj`,
  `IsClosed.mul_right_of_isCompact`
  and dominated convergence for interval integrals; for the local
  criterion, `HasStrictFDerivAt.toOpenPartialHomeomorph` and
  `ODE_solution_unique_of_mem_Icc`.
- From other parts, only merged files: for the local criterion of
  *Sufficiency for polystability*, `IsIntegrable` from
  `Geometry/Manifold/Complex/Integrable.lean` (*Nijenhuis tensor*) and the
  Fubini–Study form of `Geometry/Manifold/Projectivization/FubiniStudy/`
  (*Complex projective space*), and
  `Geometry/Lie/Subgroup/IdentityComponent.lean`. The local normal form (c)
  is not Tau Ceti's weight chart of part 37 (*Equivariant normal forms*),
  which holds only at fixed points; it generalizes it along orbits.

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **The complexification.** `Geometry/Lie/Complexification/`, with
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
   the Gauss lemma of decision 7 in `Geometry/Lie/Complexification/Polar.lean`.
   Blocked by 3, 6, 7 and 8. The moment limit theorem comes last, after
   the steps that *Main results* lists before it, in that order; it does
   not use the moment-weight inequality of issue 12.
10. **The criteria, and the Kempf–Ness milestone.**
    `KempfNess/Stability.lean`. Blocked by 4 and 9.
11. **Weights and limit points.** The first two items of
    `HilbertMumford.lean`. Blocked by 3 and 7.
12. **Destabilizing directions, and the second milestone.**
    The rest of `HilbertMumford.lean`, from the moment-weight inequality on,
    and the files of the local criterion and `KempfNess/NumericalCriterion.lean`.
    Blocked by 10 and 11;
    its polystable and stable criteria are also blocked by 14 and 15.
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

    The polystable and stable criteria are these issues, in this order:
    6. `exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le`, in
       `Geometry/Lie/Exponential/Periods.lean`. No blockers.
    7. `momentWeight_eq_moment_iff`,
       `exists_momentWeight_smul_eq_moment_of_forall_expI_smul_eq`,
       `IsPolystable.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero`,
       `IsPolystable.limitPoint_mem_orbit` and `IsStable.momentWeight_neg`.
       Blocked by 14 and 15.

    The sufficiency half of the polystable criterion is these issues, in
    this order:
    8. `exists_momentWeight_eq_zero_limitPoint_not_mem_orbit`. Blocked by
       14 and 15.
    9. `exists_mem_nonzeroPeriods_tendsto_expI_smul`, by the route of
       *The local criterion*, in these issues, in this order:
       1. `polar_symm_mem_stabilizer_iff_of_moment_eq_zero` and
          `mem_stabilizer_of_hasLeftTrivializedDerivOn`, in
          `KempfNess/Stabilizer.lean`. No blockers.
       2. `stabilizerComplexification`, `stabilizerComplexification_expI`
          and `mem_nonzeroPeriods_of_stabilizer`. Blocked by 12.9.1.
       3. `KempfNess/HolomorphicChart.lean`:
          `exists_equivariant_holomorphic_chart`,
          `fundamentalVectorField_chart_symm` and `expI_smul_chart_symm`.
          No blockers.
       4. The complexified action on `ℙ ℂ V` from `ρ`,
          `isComplexifiedAction_projectivization`, `projectivizationMoment`
          and `isEquivariantMomentMap_neg_projectivizationMoment`, in
          `KempfNess/Projective.lean`. No blockers.
       5. `kempfNessFunction_projectivization_mk`,
          `not_isSemistable_projectivization_mk`,
          `tendsto_smul_zero_of_momentWeight_pos` and
          `exists_mem_nonzeroPeriods_tendsto_smul_zero`. Blocked by 12.9.4
          and by 12.5.
       6. `slice`, `ker_sliceOperator_eq` and
          `exists_eventually_eq_expI_mul_smul_chart_symm`, in
          `KempfNess/HolomorphicSlice.lean`. Blocked by 12.9.3.
       7. `exists_mem_stabilizer_slice_eq` with the representation of
          `Gc₀` on the slice, and `exists_mem_nonzeroPeriods_tendsto_expI_smul`.
          Blocked by 12.9.2, 12.9.5 and 12.9.6.
    10. `isPolystable_of_isSemistable_of_limitPoint_mem_orbit`, in
        `KempfNess/NumericalCriterion.lean`. Blocked by 12.8 and 12.9.7.

    The last issue, `isStable_of_momentWeight_neg`, the polystable and
    stable criteria and `hilbertMumford`, in
    `KempfNess/NumericalCriterion.lean`, is blocked by 12.5, 12.6, 12.7
    and 12.10.
13. **The parabolic subgroup.** `Geometry/Lie/Subgroup/Parabolic.lean`:
    `C.parabolic ξ`, `C.parabolicLimit ξ` and `C.parabolicSubspace ξ` with
    their API, `tangentAd_expI_smul`, `isSelfAdjoint_ad_cplx_lieMap` (in
    `Complexification/Basic.lean`),
    `parabolicSubspace_sup_range_lieMap` and `mulInvariantExp_mem_parabolic`.
    Blocked by 1.
14. **$G^{\mathbb C}=P(\xi)G$.** The rest of `Parabolic.lean`, from
    `parabolic_mul_range_toHom_mem_nhds_one` on. Blocked by 13.
15. **Weights under the parabolic subgroup.** In `HilbertMumford.lean`,
    the items of *Main results* from `momentWeight_toHom_smul` to
    `momentWeight_smul_of_mem_parabolic`. Blocked by 11 and 13.

Issues 1, 5, 7 and 8 can start at once; the Kempf–Ness milestone
(issue 10) comes before the Hilbert–Mumford one (issue 12).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §5.7, equations (5.7.2)–(5.7.4) and Theorem 5.7.2.
* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight
  Inequality and the Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021],
  arXiv v2, Lemmas 2.1, 2.3, 7.5 and 8.4, Theorems 4.1, 4.3, 5.3, 7.2,
  7.3, 8.5, 12.2, 12.4, 12.5 and 12.6, Definition 7.1, and Appendices D and E.
* [V. Guillemin and S. Sternberg][GuilleminSternberg1990], for the local
  normal form.
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign.
  Math. 51 (2005), 117–127.
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une
  variété symplectique*, Rend. Sem. Mat. Univ. Politec. Torino 43 (1985),
  227–251.
* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*,
  Springer, 1998, §2.5–2.6.
