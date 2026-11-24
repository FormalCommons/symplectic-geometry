# Flux homomorphism

The detailed design of part 52 of `DESIGN.md`, *Flux homomorphism*. The
part has no milestone of its own. It proves results from McDuff–Salamon
[McDuffSalamon2017], §10.2, that *Coupling forms* and *Hamiltonian
fibrations* (page `atlas/symplectic-fibrations.md`) use:

- Theorem 10.2.5: on a closed symplectic manifold, a symplectic isotopy
  with zero flux ends at a Hamiltonian diffeomorphism, and is homotopic
  with fixed ends to a Hamiltonian isotopy. So the kernel of Tau Ceti's
  endpoint flux is $\mathrm{Ham}$.
- The countability of the flux group $\Gamma_\sigma$ (the paragraph after
  Definition 10.2.9).
- Proposition 10.2.12: a smooth path of Hamiltonian diffeomorphisms is a
  Hamiltonian isotopy.

All declarations of Tau Ceti and Mathlib named below were checked against
the pinned Tau Ceti `c9d170eed5a8` and its Mathlib. Paths of Tau Ceti files
are relative to `.lake/packages/TauCeti/TauCeti/`, and paths of the
library's files relative to `SymplecticGeometry/`.

## What there is, and what is missing

Below, `σ : TauCeti.closedForms J M 2` is a closed two-form on a manifold
`M` modelled on `J : ModelWithCorners ℝ E H`.

- **Flux** (`Geometry/Symplectic/Flux.lean` and `Flux/`):
  `TauCeti.Diffeotopy.fluxForm`, `flux` (with the page's sign, the de Rham class
  $[\int_0^1\phi_t^*\iota_{X_t}\sigma\,dt]$),
  `Homotopic.flux_eq`, `flux_trans` (`(Φ.trans Ψ).flux = Ψ.flux + Φ.flux`),
  `flux_symm`, `flux_reparam`, `flux_concat`; `flux_eq_mk_eulerianFluxForm`
  (`Flux/Eulerian.lean`: the flux is the class of
  $\int_0^1\iota_{X_t}\sigma\,dt$); `flux_globalFlowDiffeotopyAlong`,
  `exists_flux_eq` (`Flux/Flow.lean`); `flux_orderedGlobalFlowDiffeotopy`
  and `exists_homotopy_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`
  (`Flux/OrderedFlow.lean`: for symplectic fields $Y_i$ and time functions
  $A_i$ with $A_i(0)=0$, the ordered flow
  $\psi^{Y_0}_{A_0(t)}\circ\dots\circ\psi^{Y_{k-1}}_{A_{k-1}(t)}$ has flux
  $\sum_iA_i(1)[\iota_{Y_i}\sigma]$, and when every $A_i(1)=0$ it is a
  loop homotopic to the constant one relative to both ends, through maps
  preserving $\sigma$).
- **Flux and swept areas** (`Flux/Sweep.lean`):
  `TauCeti.Diffeotopy.sweep` ($(t,s)\mapsto\phi_t(c(s))$),
  `pathIntegral_fluxForm_eq_rectangleIntegral` and
  `period_flux_ofMul_eq_rectangleIntegral` (the period of the flux on a
  `C¹` loop is the $\sigma$-area swept by the loop).
- **Flux group and endpoint flux** (`Flux/Endpoint.lean`):
  `TauCeti.fluxGroup σ` (fluxes of diffeotopies that preserve `σ` at every
  time and end at the identity: smooth loops, no topology on the
  diffeomorphism group), `flux_mem_fluxGroup`,
  `flux_sub_flux_mem_fluxGroup`, `TauCeti.endpointFlux σ` on
  `TauCeti.SmoothForm.isotopyStabilizer σ`, `endpointFlux_apply`,
  `mem_ker_endpointFlux_iff` (the kernel is the set of endpoints of
  zero-flux paths), `endpointFlux_surjective`.
- **Hamiltonian diffeotopies** (`Flux/Hamiltonian.lean`):
  `TauCeti.Diffeotopy.IsHamiltonian`, `IsHamiltonian.flux_eq_zero`,
  `TauCeti.SmoothForm.hamiltonianGroup`, `hamiltonianGroup_le_isotopyStabilizer`
  and `TauCeti.hamiltonianGroup_subgroupOf_le_ker_endpointFlux` (one
  inclusion of the kernel statement).
- **Diffeotopies** (`Geometry/Diffeomorphism/Diffeotopy/`): `reparam`,
  `reparam_homotopic`, `Homotopic` with `Homotopic.trans`,
  `Homotopic.trans_congr`, `Homotopic.symm_congr`; `velocity`
  (`Velocity.lean`); `orderedGlobalFlowDiffeotopy` (`OrderedFlow.lean`).
- **Period coordinates** (`Geometry/Manifold/DeRham/FiniteDimensional.lean`):
  the instance `FiniteDimensional ℝ (deRhamCohomology I M 1)` for a compact
  boundaryless `M`; the integral classes `periodHomologyClass`, with
  `homologyPeriods_periodHomologyClass_bijective`; `periodDualBasis`,
  `periodDualForm`, `classCoordinates` with `classCoordinates_eq_zero_iff`
  and `sub_sum_classCoordinates_smul_periodDualForm_mem_exactForms`.
- **Periods** (`Geometry/Manifold/DeRham/Period.lean`,
  `DeRham/HomologyPeriod.lean`, `SmoothSingular/Period.lean`):
  `deRhamCohomology.period` with `period_injective` (connected `M`),
  `homologyPeriodHom` with `homologyPeriodHom_loopClass` and
  `homologyPeriodHom_hurewicz₁`, and `closedFormHomologyPeriod φ` (the
  periods of a closed `p`-form on `H_p(M; ℤ)`, through the smoothing
  isomorphism); smooth representatives of path classes,
  `Path.exists_homotopic_contMDiff_extend` (`Geometry/Manifold/SmoothApprox.lean`).
- **Finiteness of homology**: `TauCeti.FiniteCWType.of_isManifold` and
  `finite_singularHomology_of_finiteCWType`
  (`AlgebraicTopology/Cellular/EulerCharacteristic/FiniteCWType.lean`):
  the integral singular homology of a compact boundaryless manifold is
  finitely generated in each degree.
- **Smooth simplices** (`Geometry/Manifold/SmoothSingular/Integral.lean`):
  `SmoothSimplex.integral_eq_setIntegral_mpullback` (the integral over a
  simplex computed from a map on $\mathbb R^p$ agreeing with it on the
  simplex) and `integral_δ` (faces).
- **The library**: `TauCeti.Diffeotopy.smoothVelocity`
  (`Geometry/Diffeomorphism/Diffeotopy/Velocity.lean`);
  `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`
  (`Geometry/Symplectic/Flux/Hamiltonian.lean`); smooth dependence of
  periods on a parameter, `IsSmoothFamily.contMDiff_homologyPeriodHom`
  (`Geometry/Manifold/DeRham/HomologyPeriod.lean`).

Missing, and built here: fluxes of the initial pieces of a diffeotopy;
Theorem 10.2.5 and the kernel of the endpoint flux; the identification of
rectangle integrals over doubly periodic maps with periods on
$H_2(M;\mathbb Z)$; the countability of $\Gamma_\sigma$; and Proposition
10.2.12.

## Decisions

These settle the questions that `DESIGN.md` leaves to this file.

1. **Setting.** All statements are about Tau Ceti's `Diffeotopy J ∞ M`,
   `fluxGroup`, `endpointFlux` and `hamiltonianGroup`, with no topology on
   the diffeomorphism group, as `DESIGN.md` says under *Flux and
   cohomology*. The flux is Tau Ceti's, with the page's sign. A closed
   manifold is `[CompactSpace M] [T2Space M] [J.Boundaryless]
   [FiniteDimensional ℝ E]`. Each statement takes only the hypotheses its
   proof uses: Theorem 10.2.5 and Proposition 10.2.12 need a symplectic
   `σ` but not a connected `M`, and the countability needs only a closed
   `σ`.

2. **Initial pieces of a diffeotopy.** For `T : unitInterval`,
   `Φ.truncate T` is the diffeotopy $t\mapsto\phi_{Tt}$, the
   reparametrization `Φ.reparam` along $s\mapsto Ts$. Its flux is the flux
   of $\phi$ up to time $T$; in period coordinates it is
   $\int_0^T\langle[\iota_{X_t}\sigma],c_i\rangle\,dt$ (from
   `flux_eq_mk_eulerianFluxForm`, with velocity $T\,X_{Tt}$). This is how
   Theorem 10.2.5 and Proposition 10.2.12 differentiate a flux in time. A
   diffeotopy that preserves `σ` at every time is Hamiltonian as soon as
   all its initial pieces have zero flux: the integrands then vanish, so
   every $\iota_{X_t}\sigma$ is exact, which is the library's criterion
   `isHamiltonian_iff_forall_interiorₗ_velocity_mem_exactForms`.

3. **The proof of Theorem 10.2.5** is McDuff–Salamon's, in Tau Ceti's
   terms. Let `Φ` preserve `σ` at every time, with zero flux. First
   replace `Φ` by its reparametrization along a smooth transition function
   that is constant near both ends (`reparam`, `reparam_homotopic`,
   `flux_reparam`); then its velocity vanishes near both ends. Take the
   period-dual forms $\theta_i$ (`periodDualForm`) and symplectic fields
   $Y_i$ with $\iota_{Y_i}\sigma=\theta_i$
   (`IsNondegenerate.interiorClass_surjective`), complete since `M` is
   compact. Let $g_i(t)$ be the $i$-th class coordinate of
   $\iota_{X_t}\sigma$ and $A_i(t)=\int_0^tg_i$; these are smooth on
   $\mathbb R$ once $g_i$ is extended by zero, and $A_i(1)=0$ because the
   flux is zero. Let $\theta$ be the ordered flow of the $Y_i$ with times
   $A_i$ (`orderedGlobalFlowDiffeotopy`) and $\Psi=$ `Φ.trans θ.symm`,
   that is $\theta_t^{-1}\circ\phi_t$. The initial pieces of $\theta$ are
   ordered flows with times $A_i(Tt)$, so by `flux_trans`, `flux_symm`
   and `flux_orderedGlobalFlowDiffeotopy` every initial piece of $\Psi$ has
   zero flux, and $\Psi$ is Hamiltonian by Decision 2. Since every
   $A_i(1)=0$, $\theta$ ends at the identity, so $\Psi$ ends where `Φ`
   does. And $\theta$ is homotopic to the constant diffeotopy relative to
   both ends (`exists_homotopy_orderedGlobalFlowDiffeotopy_mem_diffeomorphStabilizer`),
   so `Φ` is homotopic to $\Psi$ (`Homotopic.trans_congr`).
   The homotopy is stated with Tau Ceti's `Diffeotopy.Homotopic`, which
   does not ask that the intermediate maps preserve `σ`. The construction
   gives that as well, but nothing downstream uses it.

4. **The route to countability is through periods, not the Weinstein
   chart.** McDuff–Salamon argue that $\mathrm{Symp}_0$ is locally
   contractible, by Weinstein's chart of the diagonal, so that
   $\pi_1(\mathrm{Symp}_0)$ is countable. That needs a topology on the
   symplectomorphism group, local
   contractibility in it, and a comparison of its continuous loops with
   the smooth loops that define `TauCeti.fluxGroup`. The library takes a
   shorter route that works with smooth loops directly and for every
   closed `σ`. Let `Φ` be a loop and $\gamma$ a smooth loop. The period of
   the flux of `Φ` on $\gamma$ is the $\sigma$-area of the swept map
   $(t,s)\mapsto\phi_t(\gamma(s))$ (`period_flux_ofMul_eq_rectangleIntegral`).
   Since `Φ` is a loop, this map is doubly periodic on the unit square. So
   it is a torus, and the area is the period of `σ` on an integral class
   of $H_2(M;\mathbb Z)$. That group is finitely generated, so these
   periods form a countable set $P_\sigma$. In the period coordinates of
   `homologyPeriods_periodHomologyClass_bijective`, $\Gamma_\sigma$ maps
   into $P_\sigma^b$, which is countable. The comparison of the swept area
   with a period uses the two-simplex 2-cycle of the square: cut the
   square along a diagonal into two affine simplices. Their integrals add
   up to the rectangle integral, and on a doubly periodic map their edges
   cancel in pairs. This is the content of McDuff–Salamon's description
   of the flux by swept cylinders, equation (10.2.2) with Lemma 10.2.1.
   The Lagrangian neighbourhood theorem of *Symplectic neighbourhoods* is
   not used, so the part no longer builds on that part.

5. **`Family.lean` is kept; Proposition 10.2.19 is not built.** *Coupling
   forms* uses only `Family.lean`: Proposition 10.2.12, for the
   equivalence of Hamiltonian holonomy and Hamiltonian curvature
   (`design/coupling-forms.md`). *Hamiltonian fibrations* uses
   `Kernel.lean` and `Family.lean` (`design/hamiltonian-fibrations.md`).
   Its route for 3 ⇒ 1 shifts the connection by closed one-forms of the
   base and does not need Proposition 10.2.19, and no other part uses that
   proposition, so this part has no file for it.

6. **The proof of Proposition 10.2.12** goes through the countability. If
   every $\phi_t$ lies in $\mathrm{Ham}$, the flux of each initial piece
   lies in $\Gamma_\sigma$. It differs by an element of $\Gamma_\sigma$
   from the zero flux of a Hamiltonian path to $\phi_T$
   (`flux_sub_flux_mem_fluxGroup`). In period coordinates it is continuous
   in $T$ (Decision 2), and it takes values in a countable set and is $0$
   at $T=0$, so it is $0$ for all $T$. Decision 2 then makes the path
   Hamiltonian.

## Files

New files of the library, with the topic of each:

- `Geometry/Diffeomorphism/Diffeotopy/Truncate.lean`: `Diffeotopy.truncate`
  and its API, including the truncations of `trans`, `symm` and
  `orderedGlobalFlowDiffeotopy`, and the velocity of a truncation.
- `Geometry/Manifold/SmoothSingular/Rectangle.lean`: rectangle integrals of
  closed two-forms over doubly periodic maps are periods on
  $H_2(M;\mathbb Z)$; the periods of a closed form on a compact
  boundaryless manifold form a countable set.
- `Geometry/Symplectic/Flux/Kernel.lean`: fluxes of initial pieces, the
  Hamiltonian criterion of Decision 2, Theorem 10.2.5 and the kernel of the
  endpoint flux.
- `Geometry/Symplectic/Flux/Countable.lean`: periods of fluxes of loops,
  and the countability of $\Gamma_\sigma$.
- `Geometry/Symplectic/Flux/Family.lean`: Proposition 10.2.12.

All declarations are about Tau Ceti's notions, so they are in the `TauCeti`
namespace (`TauCeti.Diffeotopy` for those that dot notation on a diffeotopy
finds), as `AGENTS.md` asks.

## Definitions and their API

- `TauCeti.Diffeotopy.truncate (Φ : Diffeotopy J ∞ M) (T : unitInterval) :
  Diffeotopy J ∞ M`, defined as `Φ.reparam` along $s\mapsto Ts$, with
  `truncate_def`, `truncate_apply` (`Φ.truncate T (t, x) = Φ (T * t, x)`,
  `@[simp]`), `timeSlice_truncate`, `final_truncate`
  (`(Φ.truncate T).final = Φ.timeSlice T`), `truncate_one`,
  `truncate_zero` (`= refl`), `truncate_trans`, `truncate_symm`,
  `truncate_orderedGlobalFlowDiffeotopy` (the ordered flow with times
  $t\mapsto A_i(Tt)$), and `velocity_truncate`
  ($T\cdot X_{Tt}$, with `smoothVelocity_truncate`).

No other definition is added: the flux group, the endpoint flux and
$\mathrm{Ham}$ are Tau Ceti's.

## Main results

Throughout, `[FiniteDimensional ℝ E] [J.Boundaryless] [T2Space M]
[CompactSpace M]` unless said otherwise, and `σ : closedForms J M 2`.

`Kernel.lean`:

- `TauCeti.Diffeotopy.homologyPeriod_flux_truncate`: for `Φ` preserving
  `σ` at every time and an integral class $c\in H_1(M;\mathbb Z)$,
  `deRhamCohomology.homologyPeriod ((Φ.truncate T).flux σ _) c` is the
  integral over $[0,T]$ of the period (`homologyPeriodHom`) of
  `σ.interiorₗ (Φ.smoothVelocity t)` on $c$. No compactness.
- `TauCeti.Diffeotopy.isHamiltonian_of_forall_flux_truncate_eq_zero`: `Φ`
  preserving `σ` at every time, with `(Φ.truncate T).flux σ _ = 0` for
  every `T`, is `IsHamiltonian σ`.
- `TauCeti.Diffeotopy.exists_isHamiltonian_homotopic_of_flux_eq_zero`
  (Theorem 10.2.5): for `σ` nondegenerate and `Φ` preserving `σ` at every
  time with `Φ.flux σ _ = 0`, there is `Ψ` with `Ψ.IsHamiltonian σ.val`
  and `Φ.Homotopic Ψ` (so `Ψ.final = Φ.final`, by `Homotopic.final_eq`).
- `TauCeti.Diffeotopy.final_mem_hamiltonianGroup_of_flux_eq_zero`: the
  same hypotheses give `Φ.final ∈ SmoothForm.hamiltonianGroup σ.val`.
- `TauCeti.ker_endpointFlux`: for `σ` nondegenerate,
  `(endpointFlux σ).ker = (SmoothForm.hamiltonianGroup σ.val).subgroupOf
  (SmoothForm.isotopyStabilizer σ.val)`, from `mem_ker_endpointFlux_iff`
  and `hamiltonianGroup_subgroupOf_le_ker_endpointFlux`.

`Rectangle.lean` (`[FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]`):

- `TauCeti.rectangleIntegral_mem_range_closedFormHomologyPeriod`: for
  `u : ℝ × ℝ → M` smooth on the unit square with `u (0, s) = u (1, s)` and
  `u (t, 0) = u (t, 1)` for `s, t ∈ [0, 1]`,
  `rectangleIntegral σ.val.val u (0, 0) (1, 1) ∈
  Set.range (closedFormHomologyPeriod σ)`. The smoothness hypothesis is
  the one that `Diffeotopy.sweep` satisfies (`contMDiffOn_sweep`, smooth
  within the strip $[0,1]\times\mathbb R$).
- `TauCeti.countable_range_closedFormHomologyPeriod`: for a compact
  boundaryless `M` and `φ : closedForms J M p`,
  `(Set.range (closedFormHomologyPeriod φ)).Countable`.

`Countable.lean`:

- `TauCeti.Diffeotopy.period_flux_mem_range_closedFormHomologyPeriod`: for
  `Φ` with `Φ.final = 1`, every `x` and every `g : FundamentalGroup M x`,
  `deRhamCohomology.period x (Φ.flux σ _) (Additive.ofMul g) ∈
  Set.range (closedFormHomologyPeriod σ)`. The slices of `Φ` need not
  preserve `σ`.
- `TauCeti.countable_fluxGroup`: `(fluxGroup σ : Set (deRhamCohomology J M 1)).Countable`.
  If the passage from loop classes to all of $H_1(M;\mathbb Z)$ needs it,
  the statement may take `[ConnectedSpace M]` and use `period_injective`
  in place of the period coordinates; the fibres of the page are
  connected.

`Family.lean`:

- `TauCeti.Diffeotopy.isHamiltonian_of_forall_timeSlice_mem_hamiltonianGroup`
  (Proposition 10.2.12): for `σ` nondegenerate and
  `∀ t, Φ.timeSlice t ∈ SmoothForm.hamiltonianGroup σ.val`,
  `Φ.IsHamiltonian σ.val`.

## What it uses

- From Tau Ceti and Mathlib: the declarations listed under *What there is*.
- From the library, merged: *Hamiltonian flows*
  (`Diffeotopy/Velocity.lean`, `Flux/Hamiltonian.lean`) and
  `DeRham/HomologyPeriod.lean`. Nothing of *Symplectic neighbourhoods*
  (Decision 4).
- Used by: *Coupling forms* (`Family.lean`) and *Hamiltonian
  fibrations* (`Kernel.lean`, and `Family.lean` with what it builds on).

## Building issues

Each is a few hundred lines; each is blocked by the issues it names.

1. **Truncations of diffeotopies.** `Diffeotopy/Truncate.lean`, all of
   it. About 250 lines. No blockers.
2. **Fluxes of initial pieces and the Hamiltonian criterion.** In
   `Kernel.lean`: `homologyPeriod_flux_truncate` and
   `isHamiltonian_of_forall_flux_truncate_eq_zero`. About 250 lines.
   Blocked by 1.
3. **Theorem 10.2.5 and the kernel of the endpoint flux.** In
   `Kernel.lean`: `exists_isHamiltonian_homotopic_of_flux_eq_zero`,
   `final_mem_hamiltonianGroup_of_flux_eq_zero` and `ker_endpointFlux`.
   About 350 lines. Blocked by 2.
4. **Rectangle integrals as periods.** `SmoothSingular/Rectangle.lean`,
   all of it. About 350 lines. No blockers.
5. **The flux group is countable.** `Countable.lean`. About 200 lines.
   Blocked by 4.
6. **Smooth paths in $\mathrm{Ham}$.** `Family.lean`. About 200 lines.
   Blocked by 2 and 5.

Issues 1 and 4 can start at once. *Coupling forms* waits for 6;
*Hamiltonian fibrations* waits for 3 and 6.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §10.2: equation (10.2.1), Lemma 10.2.1 and equation (10.2.2), Theorem
  10.2.5, Definition 10.2.9 and the paragraph after it, and Proposition
  10.2.12.
* A. Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer,
  1997, Chapter 3 (the flux homomorphism), which Tau Ceti's flux files also
  cite.
