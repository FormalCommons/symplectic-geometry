# Hamiltonian circle actions

This is the detailed design of part 38 of `DESIGN.md`, *Hamiltonian
circle actions*. It proves one milestone of
`atlas/symplectic-group-actions.md`, *Frankel–Ono Hamiltonianity
criterion*, following McDuff–Salamon [McDuffSalamon2017], Theorem 5.1.6
and its proof, with two changes of route that `DESIGN.md` already
announces or leaves to this file: the Poincaré dual of an orbit is
replaced by an integral identity, and the nondegeneracy of the pairing
between $H^1$ and $H^{m-1}$ comes from the Hodge theorem that the library
has (Griffiths–Harris [GriffithsHarris1978], Chapter 0, §6; Bott–Tu
[BottTu1982], §5, for the pairing).

Paths of new files are under `SymplecticGeometry/`. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`. All declarations of Tau
Ceti, Mathlib and the library named below were checked against the pinned
versions, and the statements of *Main results* were checked to elaborate
there, with the proofs left out. Throughout, `I : ModelWithCorners ℝ E H`
with `[FiniteDimensional ℝ E]`, `[IsManifold I ∞ M]`; the global results
add `[BoundarylessManifold I M] [T2Space M] [CompactSpace M]`, and
connectedness where it is said. The symplectic form is
`σ : TauCeti.SmoothTwoForm I M` (`ω` is notation once `ContDiff` is
open). A symplectic action is the hypothesis

```lean
hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
  (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) σ = σ
```

as in Tau Ceti's `mlieDerivForm_fundamentalVectorField_eq_zero`, and the
fundamental vector field of `ξ` is Tau Ceti's `fundamentalVectorField I ξ`
(*Group actions, moment maps and periods* in `DESIGN.md`).

## What there is, and what is missing

- **Hamiltonian vector fields** (Tau Ceti,
  `Geometry/Symplectic/Hamiltonian/SymplecticVectorField.lean`): the
  class `σ.interiorClass X` $=[\iota_X\sigma]$ of a symplectic vector field,
  and `interiorClass_eq_zero_iff`: it vanishes exactly when $X$ is
  Hamiltonian. `mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero`
  turns $L_X\sigma=0$ into membership, and
  `mlieDerivForm_fundamentalVectorField_eq_zero`
  (`Geometry/Manifold/GroupAction/InvariantForm.lean`) gives $L_X\sigma=0$
  for an invariant form. `mextDerivₗ_apply_fundamentalVectorField_eq_zero`
  in the same file shows how Cartan's formula is applied there.
- **Moment maps and fixed points** (Tau Ceti,
  `Geometry/Symplectic/Hamiltonian/MomentMap/`): `IsMomentMap`, and
  `IsMomentMap.criticalPoints_eq_fixedPoints_of_eq_top`
  (`Critical.lean`): the critical points of $\langle\mu,\xi\rangle$ are
  the fixed points of $G$ when the one-parameter subgroup of $\xi$ is
  dense. The library's *Lie group actions* (`GroupAction/Circle.lean`,
  #2256) gives, for the circle, the fixed points as the zeros of
  $X_{\xi_1}$; *Moment maps* (`MomentMap/WeaklyHamiltonian.lean`, #2258)
  gives a moment map once every $X_\xi$ is Hamiltonian.
- **De Rham cohomology** (Tau Ceti, `Geometry/Manifold/DeRham/`):
  `closedForms`, `exactForms`, `deRhamCohomology.mk` and `wedge`
  (`Wedge.lean`, with `wedge_mem_closedForms` and
  `wedge_mem_exactForms_of_right_mem`); `integralTopForm`, Stokes'
  theorem `integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms`
  and the pairing `poincarePairing` (`PoincarePairing/Basic.lean`), whose
  nondegeneracy Tau Ceti does not prove; `compactlySupportedForms_eq_top`
  on a compact manifold (`CompactSupport.lean`); homotopy invariance
  `deRhamCohomology.map_eq_of_homotopy` (`HomotopyInvariance.lean`); and
  `mem_exactForms_one_iff_forall_pathIntegral_eq_zero`
  (`PathIntegral.lean`): on a connected manifold a closed one-form is
  exact when its integrals along smooth loops at one point vanish.
- **Hodge theory.** The library's `Geometry/Manifold/DeRham/Hodge/Basic.lean`
  (merged) has the Hodge theorem
  `TauCeti.harmonicForms.toDeRhamCohomology_bijective` on a compact
  oriented boundaryless Riemannian manifold. Tau Ceti has
  `hodgeStar_mem_harmonicForms` and `harmonicForms_le_closedForms`
  (`DeRham/Harmonic.lean`), the wedge characterization
  `SmoothForm.inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar`
  (`Riemannian/HodgeStar.lean`), definiteness
  `integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff`
  (`Riemannian/Codifferential.lean`), graded commutativity
  `SmoothForm.wedge_comm`, and a smooth metric on every σ-compact manifold,
  `nonempty_contMDiffRiemannianMetric`
  (`Geometry/Manifold/VectorBundle/Riemannian/Existence.lean`).
- **Wedge powers and interior products** (Tau Ceti):
  `SmoothForm.wedgePow` (`DifferentialForm/Wedge/Smooth/Pow.lean`), with
  no lemma on closedness; the pointwise power rule
  `ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`
  (`Topology/Algebra/Module/Alternating/Wedge/Pow.lean`),
  $\iota_v(\omega^{m+1})=(m+1)\,\iota_v\omega\wedge\omega^m$; and the
  antiderivation rule `RoughForm.interior_wedge_apply`
  (`DifferentialForm/Wedge/Interior.lean`).
- **Averaging** (Tau Ceti, `DifferentialForm/Average.lean`):
  `SmoothForm.measureAverage J μ`, with `measureAverage_apply`,
  `mpullback_smul_measureAverage` (invariance for a right-invariant `μ`)
  and `IsClosed.measureAverage`. That the average of a closed form is
  cohomologous to it is missing.

## Decisions

`DESIGN.md` leaves two questions to this file, and the issue a third.

1. **Nondegeneracy of the pairing, through the Hodge theorem.** Of the two
   routes `DESIGN.md` offers, singular duality would need the comparison of
   the wedge and integration with the cup and cap products under Tau
   Ceti's de Rham–singular isomorphism, which neither library has; periods
   of closed one-forms describe $H^1$ but say nothing directly about
   $H^{m-1}$. The Hodge theorem gives it in a few steps: choose a metric;
   a closed $(m-1)$-form $\beta$ is $h+d\theta$ with $h$ harmonic; $\star h$
   is a harmonic, hence closed, one-form; and
   $\int\star h\wedge\beta=\int\star h\wedge h=\pm\int|h|^2\,\mathrm{vol}$,
   so the hypothesis forces $h=0$. The statement is at the level of forms,
   as the milestone's proof uses it, and needs no dimension hypothesis: an
   orientation indexed by `Fin m` fixes the dimension.
2. **The hypothesis on $[\omega]^{n-1}\smile-$.** It is stated as
   injectivity of `deRhamCohomology.wedge I M (2 * (n - 1)) 1 c`, where
   `c` is the class `deRhamCohomology.mk` of the closed form
   `σ.wedgePow (n - 1)`. No cast of degrees is needed, since the target
   degree $2(n-1)+1$ is never compared with $2n-1$. The plan asks for an
   isomorphism; only injectivity is used, so the milestone assumes only
   that, which is more general.
3. **The vanishing of the pairing with $\iota_X\omega\wedge\omega^{n-1}$, by
   averaging.** Proving that $\int_M\gamma(X)\,\omega^n$ vanishes
   through the average of $\gamma(X)$ over orbits, as `DESIGN.md` first
   planned, would need Fubini on $M\times S^1$ for `integralTopForm`, and
   free homotopies of orbit loops. This file averages the closed one-form
   $\gamma$ over the group instead. Its average $\bar\gamma$ is closed and
   invariant (Tau Ceti), and cohomologous to $\gamma$: each $g^*\gamma$ is,
   since $g$ is homotopic to the identity through the connected group, and
   the integral of $\bar\gamma-\gamma$ along a smooth loop is the average
   over $G$ of the integrals of $g^*\gamma-\gamma$, all zero (Fubini on the
   compact $G\times[0,1]$, for a continuous integrand). For an invariant
   closed one-form, Cartan's formula gives
   $d(\bar\gamma(X_\xi))=L_{X_\xi}\bar\gamma-\iota_{X_\xi}d\bar\gamma=0$,
   so on connected $M$ the function $\bar\gamma(X_\xi)$ is constant, and it
   vanishes at a fixed point. Since $\int\gamma\wedge\eta$ depends only on
   the class of $\gamma$ when $\eta=\iota_X\omega\wedge\omega^{n-1}$ is
   closed (Stokes), and the top-degree identity
   $\gamma\wedge\iota_X\omega\wedge\omega^{n-1}=\tfrac1n\gamma(X)\,\omega^n$
   holds pointwise, the integral is zero.

   This works for any compact path-connected Lie group, and so does the
   implication "fixed point ⇒ Hamiltonian", with #2258 assembling the
   Hamiltonians into a moment map. The file states it in that generality;
   only the converse uses the circle.

The power rule $\iota_X(\omega^n)=n\,\iota_X\omega\wedge\omega^{n-1}$, which
`DESIGN.md` placed in `CircleAction.lean`, is used only pointwise, in the
top-degree identity above, and pointwise it is Tau Ceti's
`wedgePow_succ_apply_vecCons`. No form-level version is added unless the
top-degree identity needs one; then it goes to a differential-form file,
as result 2 of `CircleAction.lean` says, holding for any two-form.

## Files

| File | Contents | Issue |
|---|---|---|
| `Geometry/Manifold/DeRham/PoincarePairing/Nondegenerate.lean` | nondegeneracy of the pairing in degrees $(1,m-1)$ | 1 |
| `Geometry/Manifold/DeRham/Wedge.lean` | closedness of wedge powers (named like Tau Ceti's file) | 1 |
| `Geometry/Manifold/DifferentialForm/Average.lean` | the average of a closed one-form is cohomologous to it (named like Tau Ceti's file) | 2 |
| `Geometry/Manifold/GroupAction/InvariantForm.lean` | an invariant closed one-form pairs each $X_\xi$ to a constant (named like Tau Ceti's file) | 2 |
| `Geometry/Symplectic/Hamiltonian/CircleAction.lean` | fixed points of Hamiltonian circle actions, the vanishing integral, the milestone | 3 |

## Main results

### `Geometry/Manifold/DeRham/PoincarePairing/Nondegenerate.lean`

```lean
theorem TauCeti.mem_exactForms_of_forall_integralTopForm_wedge_eq_zero
    [BoundarylessManifold I M] [T2Space M] [CompactSpace M] {l : ℕ}
    (o : Manifold.Orientation I M (Fin (1 + l))) {β : SmoothForm I M ℝ l}
    (hβ : β ∈ closedForms I M l)
    (h : ∀ γ ∈ closedForms I M 1,
      integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1) (β : RoughForm I M ℝ l)) = 0) :
    β ∈ exactForms I M l
```

The proof installs a metric from `nonempty_contMDiffRiemannianMetric`
with `letI`, as `DeRham/Hodge/Basic.lean`'s users do, and follows
Decision 1. The step "the integral of $\gamma\wedge\beta$ depends only on
the class of $\beta$" (and, for issue 3, of $\gamma$) is
`wedge_mem_exactForms_of_right_mem` (or `_of_left_mem`) with
`compactlySupportedForms_eq_top` and Stokes' theorem; if it takes more
than a few lines, it is a public lemma of this file.

### `Geometry/Manifold/DeRham/Wedge.lean`

```lean
theorem TauCeti.SmoothForm.wedgePow_mem_closedForms {k : ℕ} {φ : SmoothForm I M ℝ k}
    (hφ : φ ∈ closedForms I M k) (m : ℕ) : φ.wedgePow m ∈ closedForms I M (k * m)
```

By induction with `wedgePow_succ` and Tau Ceti's `wedge_mem_closedForms`.

### `Geometry/Manifold/DifferentialForm/Average.lean`

For `J : ModelWithCorners ℝ E' H'` with `[FiniteDimensional ℝ E'] [J.Boundaryless]`, a group `G`
with `[T2Space G] [CompactSpace G] [PathConnectedSpace G]
[IsManifold J ∞ G] [ContMDiffSMul J I ∞ G M]`, `[MeasurableSpace G]
[OpensMeasurableSpace G]`, and `[I.Boundaryless]` (Tau Ceti's averaging needs it):

```lean
theorem TauCeti.SmoothForm.measureAverage_sub_mem_exactForms_one [T2Space M]
    [PreconnectedSpace M] (μ : Measure G) [IsProbabilityMeasure μ]
    {γ : SmoothForm I M ℝ 1} (hγ : γ ∈ closedForms I M 1) :
    SmoothForm.measureAverage J μ γ - γ ∈ exactForms I M 1
```

with, as a public lemma, the exchange of the line integral along a smooth
curve and the average: `pathIntegral (measureAverage J μ γ) c a b` is
`∫ g, pathIntegral (mpullback (g • ·) _ γ) c a b ∂μ`. That each
$g^*\gamma-\gamma$ is exact is `deRhamCohomology.map_eq_of_homotopy`
along a path from `1` to `g` in `G`, applied as a homotopy
$M\times[0,1]\to M$. The proof is in `TauCeti.SmoothForm`, the namespace
of `measureAverage`.

### `Geometry/Manifold/GroupAction/InvariantForm.lean`

For a closed one-form `γ` invariant under every `g • ·`, and every `ξ`,
the function `fun x ↦ γ.val x ![fundamentalVectorField I ξ x]` has zero
differential, and on a preconnected `M` it is constant. Proved by
Cartan's formula `mlieDerivForm_apply_eq_mextDeriv_add` with
`mlieDerivForm_fundamentalVectorField_eq_zero`, as in the proof of Tau
Ceti's `mextDerivₗ_apply_fundamentalVectorField_eq_zero`, which it credits.
Names in Tau Ceti's style:
`TauCeti.mvfderiv_apply_fundamentalVectorField_eq_zero` and
`TauCeti.apply_fundamentalVectorField_eq_of_preconnectedSpace`.

### `Geometry/Symplectic/Hamiltonian/CircleAction.lean`

In `SymplecticGeometry`, with `attribute [local instance]
LieGroup.minSmoothness_of_isRCLikeNormedField` where the group's Lie
algebra is used, and for `G` a Lie group on a boundaryless model `J`,
`[T2Space G] [CompactSpace G] [PathConnectedSpace G] [MulAction G M]
[ContMDiffSMul J I ∞ G M]`:

1. **A Hamiltonian circle action has a fixed point.** On a compact
   nonempty `M` with `σ.IsNondegenerate`, from
   `σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ`:
   the component $\langle\mu,\xi_1\rangle$ has a maximum
   (`IsCompact.exists_isMaxOn`), which is a critical point, which is a
   zero of $X_{\xi_1}$ and so a fixed point (`GroupAction/Circle.lean`;
   or Tau Ceti's `criticalPoints_eq_fixedPoints_of_eq_top`).
   `exists_mem_fixedPoints_of_isMomentMap`.
2. **The vanishing integral.**

   ```lean
   theorem integralTopForm_wedge_interior_wedge_wedgePow_eq_zero
       [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M] {n : ℕ}
       (o : Manifold.Orientation I M (Fin (1 + (1 + 2 * n))))
       {σ : SmoothTwoForm I M} (hσ : σ.IsClosed) (hinv : …)
       {p : M} (hp : p ∈ MulAction.fixedPoints G M) (ξ : GroupLieAlgebra J G)
       {γ : SmoothForm I M ℝ 1} (hγ : γ ∈ closedForms I M 1) :
       integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1)
         (RoughForm.wedge (RoughForm.interior (k := 1) (fundamentalVectorField I ξ)
           (σ : RoughForm I M ℝ 2)) (σ.wedgePow n : RoughForm I M ℝ (2 * n)))) = 0
   ```

   By Decision 3. The top-degree identity, in dimension $2n+2$ (which the
   orientation fixes), comes from the antiderivation rule
   `RoughForm.interior_wedge_apply` applied to the $(2n+3)$-form
   $\gamma\wedge\sigma^{n+1}$, which is zero: it gives
   $\gamma\wedge\iota_X\sigma^{n+1}=\gamma(X)\,\sigma^{n+1}$, and the power
   rule turns the left side into $(n+1)\,\gamma\wedge\iota_X\sigma\wedge\sigma^n$.
   If this pointwise step is long, it is a public lemma in the library's
   `Geometry/Manifold/DifferentialForm/Wedge/Smooth/Pow.lean`, about
   `RoughForm.interior` and `SmoothForm.wedgePow` for any $X$ in top
   degree.
3. **A symplectic action with a fixed point is Hamiltonian.**

   ```lean
   theorem exists_isMomentMap_of_mem_fixedPoints
       [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
       {n : ℕ} (hn : 1 ≤ n) (hE : finrank ℝ E = 2 * n)
       {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic) (hinv : …)
       (hL : Function.Injective (deRhamCohomology.wedge I M (2 * (n - 1)) 1
         (deRhamCohomology.mk I _ ⟨σ.wedgePow (n - 1),
           SmoothForm.wedgePow_mem_closedForms
             ((mem_closedForms I σ).mpr ((SmoothForm.isClosed_def σ).1 hσ.isClosed)) _⟩)))
       {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
       ∃ μ : M → Module.Dual ℝ (GroupLieAlgebra J G),
         σ.IsMomentMap (InfinitesimalAction.fundamental J G I M) μ
   ```

   For each `ξ`, $X_\xi$ is symplectic, $\iota_{X_\xi}\sigma\wedge\sigma^{n-1}$
   is closed, and by 2 and the nondegeneracy of issue 1 (with the
   orientation of `σ`, `IsNondegenerate.volumeOrientation`, reindexed to
   `Fin (1 + (1 + 2 * (n - 1)))`) it is exact; so its class
   `wedge c [ι_{X_ξ}σ]` is zero, `hL` gives `σ.interiorClass X_ξ = 0`, and
   `interiorClass_eq_zero_iff` makes $X_\xi$ Hamiltonian. The existence
   theorem of `WeaklyHamiltonian.lean` (#2258) then gives `μ`. The
   hypotheses `hn` and `hE` are the plan's; the proof drops either if it
   does not use it.
4. **The milestone.**

   ```lean
   theorem exists_isMomentMap_iff_exists_mem_fixedPoints
       [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
       {n : ℕ} (hn : 1 ≤ n) (hE : finrank ℝ E = 2 * n)
       {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
       [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
       (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
         (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
       (hL : Function.Injective (deRhamCohomology.wedge I M (2 * (n - 1)) 1
         (deRhamCohomology.mk I _ ⟨σ.wedgePow (n - 1),
           SmoothForm.wedgePow_mem_closedForms
             ((mem_closedForms I σ).mpr ((SmoothForm.isClosed_def σ).1 hσ.isClosed)) _⟩))) :
       (∃ μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle),
           σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) (fun x ↦ -μ x)) ↔
         ∃ p : M, p ∈ MulAction.fixedPoints Circle M
   ```

   Milestone: *Frankel–Ono Hamiltonianity criterion*. The left side is the
   page's Hamiltonian action, in its sign (*Group actions, moment maps and
   periods*); in an existential the sign does not matter, as the page
   says. From 1 and 3.

## What it uses

- From *Lie group actions*: `GroupAction/Circle.lean` (#2256), for the
  fixed points of the circle as the zeros of $X_{\xi_1}$, in result 1.
- From *Moment maps*: `MomentMap/WeaklyHamiltonian.lean` (#2258), for the
  moment map in result 3.
- From *Hodge theory*: the merged `Geometry/Manifold/DeRham/Hodge/Basic.lean`.
- From Tau Ceti and Mathlib: the declarations of *What there is*.

## Building issues

Each is a few hundred lines at most; each is blocked by the issues it
names.

1. **Nondegeneracy of the pairing in degrees $(1,m-1)$, and closed wedge
   powers.** `PoincarePairing/Nondegenerate.lean` and `DeRham/Wedge.lean`.
   About 170 lines. No blockers.
2. **Invariant representatives of closed one-forms.**
   `DifferentialForm/Average.lean` and `GroupAction/InvariantForm.lean`.
   About 250 lines. No blockers.
3. **Hamiltonian circle actions, and the milestone.** `CircleAction.lean`.
   About 250 lines. Blocked by 1, 2, #2256 (`GroupAction/Circle.lean`)
   and #2258 (`MomentMap/WeaklyHamiltonian.lean`).

Issues 1 and 2 can start at once.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 5.1.6 and its proof.
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (the Hodge theorem).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5
  (the Poincaré pairing).
