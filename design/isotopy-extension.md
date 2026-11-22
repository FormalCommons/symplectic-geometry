# Isotopy extension

This is the detailed design of part 18 of `DESIGN.md`, *Isotopy extension*. It
covers the milestones *Symplectic ball extension*, *Symplectic isotopy
extension* and *Neighbourhood extension of submanifold isotopies* of
`atlas/symplectic-manifolds.md`, which follow McDuff–Salamon
[McDuffSalamon2017], §3.3 (Theorems 3.3.1 and 3.3.2, with Theorem A.2.1 and
Lemma A.2.2 of the appendix) and Exercise 3.4.20, and the corrections of
[McDuffSalamon2019Errata] to the proof of Theorem 3.3.1. The smooth isotopy
extension theorem it starts from is Hirsch's (M. Hirsch, *Differential
Topology*, Springer GTM 33, 1976, Chapter 8, Theorems 1.3 and 1.4), which Tau
Ceti proves in a reparametrized form.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. Manifolds follow *Manifolds, families and signs* of `DESIGN.md`:
`I : ModelWithCorners ℝ E H` with `[FiniteDimensional ℝ E]`,
`[I.Boundaryless]`, `[IsManifold I ∞ M]`, and `[T2Space M]`,
`[SigmaCompactSpace M]` where a statement needs them, as Tau Ceti's isotopy
extension does. The source of a family is `P` (or `Q`), over
`J : ModelWithCorners ℝ E' H'`. A symplectic form is
`ω : TauCeti.SmoothTwoForm I M` with `ω.IsSymplectic`. A family of
embeddings is a `TauCeti.SmoothIsotopy`, a family of diffeomorphisms a
`TauCeti.Diffeotopy I ∞ M`, both over `unitInterval`.

## What exists, and what the part adds

Tau Ceti has the smooth isotopy extension theorem
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`
(`Geometry/Manifold/SmoothIsotopy/Extension.lean`), but it extends the
reparametrized motion $t\mapsto F(s(t),\cdot)$, $s=$ `Real.smoothTransition`,
and since $s$ is flat at $0$ and $1$ the original times cannot be recovered
from it. It has the ambient velocity field of a motion over `ℝ` that is
constant near both ends (`TauCeti.exists_ambientVelocityField`,
`Geometry/Manifold/SmoothIsotopy/Velocity/Basic.lean`), time-dependent flows
and their diffeotopies (`TauCeti.timeDependentFlowDiffeotopy`,
`Geometry/Diffeomorphism/Diffeotopy/Flow.lean`), Moser's theorem with given
primitives (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact`,
`Geometry/Symplectic/Manifold/Moser.lean`), the relative Moser theorem for one
pair of forms
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`,
`RelativeMoser.lean`), the relative Poincaré operator of a vector bundle
(`TauCeti.vectorBundlePoincareHomotopy`,
`Geometry/Manifold/DifferentialForm/Relative/Basic.lean`, used by
`DifferentialForm/VectorBundlePoincare.lean`), tubular
neighbourhoods with their retractions and deformations
(`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`,
`TauCeti.SmoothEmbedding.exists_deformation_subset`,
`Geometry/Manifold/TubularNeighborhood/Existence.lean`), the periods of
closed one-forms on singular homology (`TauCeti.homologyPeriodHom`,
`TauCeti.deRhamCohomology.homologyPeriod`,
`TauCeti.exists_mextDeriv_eq_of_homologyPeriodHom_eq_zero`,
`Geometry/Manifold/DeRham/HomologyPeriod.lean`), and Hamiltonian diffeotopies
(`TauCeti.Diffeotopy.HasHamiltonian`, `IsHamiltonian`,
`Geometry/Symplectic/Flux/Hamiltonian.lean`).

Neighbourhood deformation retracts are Tau Ceti's NDR pairs
(`TauCeti.NDRPair`, `Topology/Homotopy/Extension/NDRPair.lean`). Neither Tau
Ceti nor Mathlib has any of the three milestones, nor an isotopy extension
that keeps the original times. The atlas's correspondence page
(`atlas/symplectic-manifolds-lean.md`, §3.3) lists only related ingredients,
the ones above. The part adds, in this order of dependence:

1. the homological shrinking lemma for the subset of an NDR pair, which the
   cohomological theorem uses;
2. smooth paths in the symplectic group;
3. families of embeddings near a compact set, and isotopy extension at every
   time;
4. velocity forms of families of symplectic embeddings, and the extension of
   such a family by the flow of an ambient (Hamiltonian) vector field;
5. Moser's argument for a family of Moser problems depending on a parameter;
6. the three milestones.

## Decisions

`DESIGN.md` leaves two questions to this file, and the route of the
submanifold theorem raises a third.

- **Symplectic embeddings of a closed ball.** The plan's closed balls
  $B(r)$ are `Metric.closedBall (0 : StdSpace (Fin n)) r`, with `stdForm` as
  a constant two-form, `(stdForm (Fin n)).constSmooth`
  (`TauCeti.SymplecticForm.constSmooth`). A map on a closed ball is smooth when
  it is smooth on an open neighbourhood of the ball, the usual reading of
  smoothness on a subset. It is not a map on the ball as a manifold with
  boundary: Mathlib gives closed balls no such structure, and the plan's
  proofs extend the maps to neighbourhoods anyway. So
  `IsSymplecticBallEmbedding ω r j`, for a total function
  `j : StdSpace (Fin n) → M`, says that `j` is smooth on an open neighbourhood
  of $B(r)$, injective on $B(r)$, and pulls `ω` back to `ω₀` at every point
  of the open ball `Metric.ball 0 r`. For `r > 0` the last condition holds on
  $B(r)$ by continuity. For `r = 0` it is empty, so an embedding of `B(0)` is
  a point with a smooth germ, and a family of embeddings of `B(0)` is a
  smooth path of centres. That is the plan's reading of the case
  $\lambda=0$, so one statement covers $\lambda\ge0$. A family is
  `IsSymplecticBallFamily ω r e`, `e : unitInterval × StdSpace (Fin n) → M`,
  jointly smooth on `univ ×ˢ U` for an open `U ⊇ B(r)`, each slice an
  `IsSymplecticBallEmbedding ω r`. The values of `j` and `e` away from the
  neighbourhood play no role.
- **How $H^1(Q;\mathbb R)$ is read.** $Q$ is a compact subset, so de Rham
  cohomology does not apply to it. The library reads its first cohomology
  through singular homology:
  $H^1(Q;\mathbb R)\cong\operatorname{Hom}(H_1(Q;\mathbb Z),\mathbb R)$ by
  the universal coefficient theorem, since $H_0$ is free (Tau Ceti's
  `TopCat.singularKronecker`, `AlgebraicTopology/Cohomology/UniversalCoefficient.lean`,
  is this isomorphism). For a class of $M$ the restriction to $Q$ is the
  period homomorphism of a closed form on the cycles of $Q$:
  `(deRhamCohomology.homologyPeriod c).comp (ContinuousMap.singularHomologyMap ℤ 1 ι)`
  for the inclusion `ι : C(Q, M)`. Then
  - *$H^1(M;\mathbb R)\to H^1(Q;\mathbb R)$ is onto* reads: every additive
    map `H₁(Q; ℤ) →+ ℝ` is the restriction of the periods of a de Rham class
    of $M$;
  - *$H^1(Q;\mathbb R)=0$* reads: `H₁(Q; ℤ) →+ ℝ` is a subsingleton.

  With $H^1_{\mathrm{dR}}(M)\cong H^1(M;\mathbb R)$ (de Rham's theorem in
  degree one, through `homologyPeriod`, which Tau Ceti proves injective) these
  are the plan's hypotheses. The library states the milestone in this
  reading. It uses only declarations of Tau Ceti and needs no comparison of
  cohomology theories. Read like this, the hypothesis is what the proof uses:
  periods on the cycles of $Q$ decide exactness on a neighbourhood of $Q$
  (see `Cohomological/Primitive.lean`). Singular homology in Tau Ceti lives
  in `TopCat.{0}`, so the theorem takes `M : Type`.
- **Neighbourhood deformation retracts.** The hypothesis is
  `Nonempty (TauCeti.NDRPair Q)`, Tau Ceti's NDR data: a control function
  vanishing exactly on `Q` and a deformation of `M` that fixes `Q` and
  carries the open set where the control is below `1` into `Q`. A compact
  `Q` with an open neighbourhood that deformation retracts onto it relative
  to `Q`, the book's notion, has such data by `TauCeti.NDRPair.ofHomotopyRel`.
  The control function it needs exists because a manifold is metrizable. So
  the library adds no predicate.
- **The route of the submanifold theorem.** The plan extends $de_t$ to
  symplectic bundle maps along $Q$, realizes them by tubular maps, and then
  runs a relative Moser argument in an auxiliary parameter. The first step
  needs symplectic complements chosen smoothly in $t$, which is where the
  review of #420 expected a $t$-dependent version of *Symplectic
  neighbourhoods*' `Tubular.lean` and the open issues #254, #266 and #269.
  This design takes a route that chooses no complements and does not use
  `Tubular.lean`. First, isotopy extension at every time gives a compactly
  supported diffeotopy $G_t$ of $M$ with $G_t\circ i=e_t$. Then the forms
  $\omega_t=G_t^*\omega$ are symplectic everywhere, and they are joined by
  Moser's argument *along $t$*. Their velocity $\partial_t\omega_t$ is
  $d\gamma_t$, with $\gamma_t$ the pull-back by $G_t$ of the contraction of
  $\omega$ with the velocity field of $G_t$. On $Q$, $i^*\gamma_t$ is the
  velocity form of $e_t$, which is closed because $e_t^*\omega$ does not
  depend on $t$. Its pull-back by a smooth retraction $r$ of a tubular
  neighbourhood onto $Q$ is therefore closed too, so subtracting it leaves a
  primitive of $\partial_t\omega_t$, and this one vanishes on $TQ$.
  The relative Moser theorem along a family (`Moser/Family.lean` below)
  then gives $\chi_t$ fixing $Q$ with
  $\chi_t^*\omega_t=\omega$ near $Q$, and $F_t=G_t\circ\chi_t$ is the wanted
  family. Nothing in this argument uses the constant rank of $i^*\omega$. So
  the library proves the theorem for every compact embedded submanifold,
  which contains the plan's statement (see *Milestones*). The part
  therefore does not wait for *Symplectic neighbourhoods* and stays at
  level 2, and none of #254, #266 and #269 blocks it.

Further choices of this design:

- **Isotopy extension at every time.** Every milestone asks that the
  extension agrees with the given family at each time $t\in[0,1]$, not at a
  reparametrized one. `Extension.lean` below gives this. It first extends
  the family past both ends of $[0,1]$, near a compact set, then makes it
  constant beyond them by a reparametrization that is the identity on
  $[0,1]$, then applies Tau Ceti's `exists_ambientVelocityField` and runs the
  flow. All three milestones and the extension lemmas of `Flow.lean` take
  their ambient diffeotopy from it. It also supplies the inverse of a family
  of open embeddings jointly smoothly: if $\Phi_t\circ k_0=k_t$ on a compact
  set, then $k_t^{-1}=k_0^{-1}\circ\Phi_t^{-1}$ there, and $\Phi^{-1}$ is
  smooth because $\Phi$ is a `Diffeotopy`.
- **Hamiltonians.** The milestones' Hamiltonian isotopies are
  `TauCeti.Diffeotopy` with `HasHamiltonian ω F` for an explicit `F`,
  read along the motion as Tau Ceti reads it, $F(x,t)=H_t(\phi_t x)$. The
  plan's compact support of $H$ throughout $[0,1]$ is the conclusion
  `∀ p, p.1 ∉ K → F p = 0` together with `∀ t, ∀ y ∉ K, Φ (t, y) = y`, for
  one compact `K`. Since $\phi_t$ preserves $K$, these say that every $H_t$
  vanishes off $K$. A symplectic isotopy is a `Diffeotopy` with
  `∀ t, Φ.timeSlice t ∈ TauCeti.SmoothForm.diffeomorphStabilizer ω`, the
  form of Tau Ceti's `isotopyStabilizer`.
- **Families of symplectic embeddings.** For
  `F : TauCeti.SmoothIsotopy f₀ f₁` from `P` to `M`, `F.IsSymplectic σ ω`
  says that every slice pulls `ω` back to `σ`. On an open subset
  `U : Opens M` the form is `ω` restricted along `Subtype.val`, as in
  `DESIGN.md`'s *Neighbourhood germs*. This is the one predicate the part
  adds on Tau Ceti's type. The atlas's correspondence page notes that
  `SmoothIsotopy` has no symplectic field, and the predicate is what each
  milestone needs.
- **Families over `ℝ` only inside proofs.** As `DESIGN.md` asks, the
  milestones and the extension theorems use families over `unitInterval`.
  The one exception is the Moser lemma along a family in `Moser/Family.lean`.
  It is a tool for proofs, and it takes its family over `ℝ` as Tau Ceti's
  Moser theorems do. A proof that runs a flow extends its
  family past both ends with *Smooth families*' time extensions
  (`ContMDiff/TimeExtension.lean` for maps and functions,
  `DifferentialForm/TimeExtension.lean` for forms), and
  then reparametrizes into an open interval where its open conditions hold.
  This gives the vector field over `ℝ` that `timeDependentFlowDiffeotopy`
  needs, the second note of the review of #420.

## Files and declarations

| File | Contents |
|---|---|
| `AlgebraicTopology/Singular/NDRPair.lean` | the homological shrinking lemma for the subset of an NDR pair |
| `Analysis/CStarAlgebra/Exponential.lean` | smoothness of `t ↦ selfAdjoint.expUnitary (t • a)` (named like Mathlib's file) |
| `Analysis/Matrix/SymplecticGroup/Connected.lean` | smooth paths in `Matrix.symplecticGroup` (named like Tau Ceti's file) |
| `Analysis/Matrix/L2OpNorm.lean` | `ContDiff` of matrix-valued maps under the ℓ² operator norm, entrywise and against the entrywise norm (named like Tau Ceti's `Analysis/Matrix/L2OpNorm.lean`) |
| `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog.lean` | smoothness of `t ↦ a ^ t` for strictly positive `a` (named like Tau Ceti's file) |
| `Geometry/Manifold/SmoothEmbedding/Neighborhood.lean` | embeddings near a compact set, uniformly in a compact parameter |
| `Geometry/Manifold/SmoothIsotopy/Extension.lean` | time extension of an isotopy past its ends, and isotopy extension at every time (named like Tau Ceti's file) |
| `Geometry/Symplectic/IsotopyExtension/Velocity.lean` | `SmoothIsotopy.IsSymplectic`, velocity forms, their closedness, the link with `HasHamiltonian` |
| `Geometry/Symplectic/IsotopyExtension/Flow.lean` | extension of a family of symplectic embeddings by an ambient symplectic or Hamiltonian flow |
| `Geometry/Symplectic/Moser/Family.lean` | Moser's argument near a compact set along a family, and with a parameter |
| `Geometry/Manifold/TubularNeighborhood/OneFormCorrection.lean` | the correction lemma: a function whose slices have differential `γ_t` along a compact submanifold where `f^* γ_t` vanishes |
| `Geometry/Manifold/DifferentialForm/VectorBundlePoincare.lean` | the relative Poincaré operator at the zero section of a vector bundle, and its fibre-scaling primitives for a family of one-forms |
| `Analysis/Calculus/DifferentialForm/Poincare.lean` | a closed form on a star-convex open set, vanishing on a compact star-convex subset, has a global primitive near it that vanishes on it (named like Tau Ceti's file) |
| `Geometry/Symplectic/IsotopyExtension/Ball/Basic.lean` | `IsSymplecticBallEmbedding`, `IsSymplecticBallFamily`, enlarging a symplectic ball |
| `Geometry/Symplectic/IsotopyExtension/Ball/Isotopy.lean` | the Hamiltonian ball extension and the milestone *Symplectic ball extension* |
| `Geometry/Manifold/DeRham/HomologyPeriod.lean` | periods of a smooth family of closed one-forms depend smoothly on the parameter |
| `Geometry/Symplectic/IsotopyExtension/Cohomological/Primitive.lean` | ambient closed forms with prescribed periods, and primitives on one neighbourhood for all times |
| `Geometry/Symplectic/IsotopyExtension/Cohomological/Basic.lean` | the milestone *Symplectic isotopy extension* |
| `Geometry/Symplectic/IsotopyExtension/Submanifold.lean` | the milestone *Neighbourhood extension of submanifold isotopies* |

`Moser/Family.lean` sits in the folder of *Moser isotopy*, beside that
part's files, because its subject is Moser's argument. It is a file of this
part, and `design/moser-isotopy.md` records it as the one exception to that
part's folder. *Moser isotopy* proves its milestone fixing a submanifold for
the linear segment between two forms, and the submanifold theorem here needs
a general family. Both parts use one cut-off Moser field, *Moser isotopy*'s
`moserField` (`Moser/Field.lean`), generalized to a family of two-forms
by #551 (see *What the part uses*). Where a Tau Ceti file has the same
name (`Extension.lean`, `Connected.lean`, `Poincare.lean`), the two merge upstream, as
`DESIGN.md`'s *Principles* allow. No folder of this part has the name of a
Tau Ceti file.

### `AlgebraicTopology/Singular/NDRPair.lean`

```lean
theorem TauCeti.NDRPair.exists_isOpen_range_singularHomologyMap_le
    {X : Type} [TopologicalSpace X] {Q U : Set X} (N : NDRPair Q) (hU : IsOpen U)
    (hQU : Q ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ ∃ (hQV : Q ⊆ V) (hVU : V ⊆ U), ∀ k : ℕ,
      LinearMap.range (ContinuousMap.singularHomologyMap ℤ k (ContinuousMap.inclusion hVU)) ≤
        LinearMap.range
          (ContinuousMap.singularHomologyMap ℤ k (ContinuousMap.inclusion (hQV.trans hVU)))
```

Every class of `V`, pushed into `U`, comes from `Q`. `V` is the set of
points where the control of `N` is below `1` and whose whole track under
the deformation stays in `U`. It is open by the tube lemma, since
`unitInterval` is compact, and it contains `Q`, which the deformation fixes.
Restricted to `V`, the deformation joins the inclusion `V → U` to a map that
factors through `Q`, and `ContinuousMap.singularHomologyMap_eq_of_homotopic`
(`AlgebraicTopology/Singular/Homotopy/Invariance.lean`) concludes. No
compactness of `Q` is needed. Expected size: 150 lines.

### `Analysis/Matrix/SymplecticGroup/Connected.lean`

```lean
theorem Matrix.exists_contDiff_path_symplecticGroup {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hA : A ∈ symplecticGroup n ℝ)
    (hB : B ∈ symplecticGroup n ℝ) :
    ∃ γ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t, γ t ∈ symplecticGroup n ℝ) ∧ γ 0 = A ∧ γ 1 = B
```

Tau Ceti's `Matrix.isPathConnected_symplecticGroup` gives only continuous
paths, and the frames along a path of centres must be smooth. The route
reduces to `A = 1` by left multiplication. It then writes `B` as its unitary
factor times its positive factor (`Units.polarUnitary`,
`SymplecticGroup.polarUnitary_mem`). The unitary factor is the realification
of `exp (I • H)` for a Hermitian `H` (`Matrix.UnitaryGroup.exists_expUnitary_eq`),
joined to `1` by `t ↦ realify (exp (t • I • H))`. The positive factor `P` is
joined to `1` by `t ↦ P ^ t`, which is symplectic by
`SymplecticGroup.rpow_mem`. The issue checks how Mathlib's continuous
functional calculus gives smoothness in `t`, for instance by writing `P ^ t`
as `exp (t • log P)`. Smoothness is stated for the entrywise norm
`Matrix.Norms.Elementwise`, as for the frames of *Maslov index*. Expected
size: 150 lines.

The general steps of the proof are public lemmas in files of their own
topics: `CFC.contDiff_const_rpow`
(`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog.lean`),
`selfAdjoint.contDiff_expUnitary_smul` (`Analysis/CStarAlgebra/Exponential.lean`),
both files of this part, and `Matrix.realifyCLM` and `SymplecticGroup.inv_mem`, which
`Connected.lean` imports from `Topology/Algebra/Matrix/Realify.lean` of
*Lagrangian Grassmannian* and `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` of
*Symplectic group*. Both of those files are merged.

### `Geometry/Manifold/SmoothEmbedding/Neighborhood.lean`

```lean
theorem TauCeti.exists_isOpen_forall_isSmoothEmbedding_of_injOn
    [J.Boundaryless] [I.Boundaryless] [T2Space P] [T2Space M]
    {G : unitInterval × P → M} {O : Set P} (hO : IsOpen O)
    (hG : ContMDiffOn ((𝓡∂ 1).prod J) I ∞ G (univ ×ˢ O)) {K : Set P} (hK : IsCompact K)
    (hKO : K ⊆ O) (hinj : ∀ t, InjOn (fun x ↦ G (t, x)) K)
    (himm : ∀ t, ∀ x ∈ K, Function.Injective (mfderiv J I (fun x ↦ G (t, x)) x)) :
    ∃ V : Opens P, K ⊆ V ∧ (V : Set P) ⊆ O ∧
      ∀ t, Manifold.IsSmoothEmbedding J I ∞ (fun x : V ↦ G (t, x))
```

Its corollary without the parameter is `TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`.
The constructor `TauCeti.SmoothIsotopy.ofForallIsSmoothEmbedding`
(`V : Opens P`, `G` jointly smooth on `unitInterval × V` with embedding
slices) gives the `SmoothIsotopy f₀ f₁` for any smooth `f₀`, `f₁` on `V`
equal to the slices at `0` and `1`, with an `_apply` lemma. Immersions are locally injective, and a locally
injective map, injective on a compact set, is injective on a neighbourhood
of it. With the parameter this is uniform, by compactness of
`unitInterval × K`. The issue first looks for the topological step stated in
general: Tau Ceti's `TauCeti.IsExactLiouvilleEmbedding.exists_isOpen_injOn`
proves it for one map. Expected size: 250 lines.

### `Geometry/Manifold/SmoothIsotopy/Extension.lean`

The main theorem is isotopy extension at every time:

```lean
theorem TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq
    [J.Boundaryless] [I.Boundaryless] [IsManifold J ∞ P] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] {f₀ f₁ : C^∞⟮J, P; I, N⟯} (F : SmoothIsotopy f₀ f₁)
    {A : Set P} (hA : IsCompact A) :
    ∃ Φ : Diffeotopy I ∞ N, ∃ K : Set N, IsCompact K ∧ (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ t, ∀ x ∈ A, Φ (t, f₀ x) = F (t, x)
```

Its statement is Tau Ceti's `exists_diffeotopy_apply_eq` without the change of
time. The steps:

1. `TauCeti.SmoothIsotopy.exists_contMDiff_extend`. There are `δ > 0`, an
   open `V ⊇ A` and a `G : ℝ × P → N`, smooth on `Ioo (-δ) (1 + δ) ×ˢ V`,
   that agrees with `F` on
   $[0,1]\times V$ and whose slices are smooth embeddings of `V` for
   $t\in(-\delta,1+\delta)$. Seeley's extension extends maps into a normed
   space, so the target is moved into one. Tau Ceti's
   `IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`, built on the
   map of Mathlib's `SmoothBumpCovering.embeddingPiTangent`, embeds a
   neighbourhood `W` of the compact track of `A` into a Euclidean space,
   with a smooth retraction of a
   neighbourhood of its image onto it
   (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`). The extension is
   *Smooth families*' `ContMDiff/TimeExtension.lean` applied to the
   composite with the embedding, followed by the retraction, for times close to $[0,1]$. The
   embedding property of the slices for those times comes from
   `SmoothEmbedding/Neighborhood.lean` again.
2. Compose with a smooth `c : ℝ → (-δ, 1 + δ)` that is the identity on
   $[0,1]$ and constant near $\pm\infty$. The result is constant beyond two
   times `a < 0 < 1 < b`, has embedding slices for every real time, and is
   `F` on $[0,1]$.
3. Tau Ceti's `TauCeti.exists_ambientVelocityField` gives a compactly
   supported smooth field `X` on `ℝ × N` with the velocity of the motion of
   `A`. Its flow, `TauCeti.timeDependentFlowDiffeotopy` (complete by
   `TauCeti.isCompleteVectorField_timeDependentSuspensionField`), is `Φ`.
   Uniqueness of integral curves gives `Φ (t, f₀ x) = F (t, x)`.

The file also has `TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`,
for `F` between manifolds of the same dimension and `h` smooth on
`unitInterval × P`: a smooth `G` on `N × unitInterval`, vanishing off a
compact set, with `G (F (t, y), t) = h (t, y)` for `y` near `A` (step 2 of
`Flow.lean`). For it, `Extension.lean` imports Tau Ceti's
`Geometry/Manifold/LocalDiffeomorph/Injective.lean`, for
`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`, and *Hamiltonian flows*'
`Geometry/Diffeomorphism/Diffeotopy/Basic.lean`.

Expected size: 450 lines. The proof adapts Tau Ceti's
`TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq`, which the module docstring
credits.

### `Geometry/Symplectic/IsotopyExtension/Velocity.lean`

For `σ : TauCeti.SmoothTwoForm J P`, `ω : TauCeti.SmoothTwoForm I M` and
`F : TauCeti.SmoothIsotopy f₀ f₁` from `P` to `M`:

```lean
/-- Every slice of `F` pulls `ω` back to `σ`. -/
def TauCeti.SmoothIsotopy.IsSymplectic (σ : SmoothTwoForm J P) (ω : SmoothTwoForm I M)
    (F : SmoothIsotopy f₀ f₁) : Prop :=
  ∀ t, TauCeti.mpullback J I (fun x ↦ F (t, x)) ω.val = σ.val

/-- The velocity forms `α_t (v) = ω (∂ₜ F (t, x), d F_t v)` of `F`, as one form on the
cylinder `unitInterval × P`: the contraction of `F^* ω` with the unit time field. -/
def TauCeti.SmoothIsotopy.velocityForm (ω : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁) :
    SmoothForm ((𝓡∂ 1).prod J) (unitInterval × P) ℝ 1
```

API:
- `isSymplectic_def`;
- `velocityForm_def`, and `velocityForm_apply` (its value on `(0, v)` at
  `(t, x)` is $\omega_{F(t,x)}(\partial_tF(t,x),dF_t\,v)$);
- `mpullback_prodMk_velocityForm` (the slice at `t`, written `α_t` below);
- `IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`: for a closed `ω`
  and a symplectic `F` every slice is closed. This is Cartan's formula for
  the closed form `F^*ω` on the cylinder, whose slices do not depend on `t`;
- `IsSymplectic.refl` (the constant isotopy `ContMDiffMap.smoothIsotopyRefl`
  of a map pulling `ω` back to `σ`), and `TauCeti.Diffeotopy.isSymplectic_smoothIsotopy`
  (the restriction `Diffeotopy.smoothIsotopy` of a diffeotopy with slices in
  `diffeomorphStabilizer ω` is symplectic). These are the examples of the
  predicate;
- `TauCeti.Diffeotopy.hasHamiltonian_iff_velocityForm`: `Φ.HasHamiltonian ω F`
  if and only if `F` is smooth and the slices of the velocity form of
  `Φ.smoothIsotopy` (the restriction of `Φ` to the identity of `M`) are the
  differentials of the `F (·, t)`. This translates between Tau
  Ceti's reading along the motion, on `M × unitInterval`, and the cylinder
  `unitInterval × M` of `SmoothIsotopy`, and is the one swap of the
  cylinder that the part needs.

Expected size: 300 lines.

### `Geometry/Symplectic/IsotopyExtension/Flow.lean`

Two extension theorems, shared by the three milestones. In both, `k` is a
`SmoothIsotopy f₀ f₁` from `P` to `(M, ω)`, with
`hd : Module.finrank ℝ E' = Module.finrank ℝ E`, so that its slices are open
embeddings, and `K ⊆ P` is compact. The proofs use only the hypothesis on the
velocity forms, so `k` need not be symplectic and the theorems take no form on
`P`; for a symplectic `k` the velocity forms are closed
(`IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`), which is how the
primitives `h` arise.

```lean
/-- A family of embeddings whose velocity forms are exact, with a smooth family of
primitives `h`, is the restriction to `K` of a compactly supported Hamiltonian
diffeotopy. -/
theorem TauCeti.SmoothIsotopy.exists_hasHamiltonian_forall_apply_eq
    (hω : ω.IsSymplectic) (k : SmoothIsotopy f₀ f₁) (hd) (hK : IsCompact K)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h)
    (hα : ∀ t, (SmoothForm.mpullback (Prod.mk t) _ (k.velocityForm ω)).val =
      mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x))) :
    ∃ (Φ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ) (L : Set M), IsCompact L ∧
      Φ.IsCompactlySupportedHamiltonian ω ∧ Φ.HasHamiltonian ω F ∧
      (∀ p, p.1 ∉ L → F p = 0) ∧
      (∀ t, ∀ y ∉ L, Φ (t, y) = y) ∧ ∀ t, ∀ x ∈ K, Φ (t, f₀ x) = k (t, x)

/-- On a compact `M`: if the velocity forms are `k_t^* β_t + d h_t` for a smooth family `β`
of closed one-forms on `M`, the family is the restriction to `K` of a symplectic
diffeotopy. -/
theorem TauCeti.SmoothIsotopy.exists_diffeotopy_mem_diffeomorphStabilizer_forall_apply_eq
    [CompactSpace M] (hω : ω.IsSymplectic) (k : SmoothIsotopy f₀ f₁) (hd) (hK : IsCompact K)
    {β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1}
    (hβ : ∀ t, mextDeriv (SmoothForm.mpullback (Prod.mk t) _ β).val = 0)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h)
    (hα : ∀ t, (SmoothForm.mpullback (Prod.mk t) _ (k.velocityForm ω)).val =
      mpullback J I (fun x ↦ k (t, x)) (SmoothForm.mpullback (Prod.mk t) _ β).val +
        mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x))) :
    ∃ Φ : Diffeotopy I ∞ M, (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer ω) ∧
      ∀ t, ∀ x ∈ K, Φ (t, f₀ x) = k (t, x)
```

(The smoothness proofs of the slices, written `_`, are
`contMDiff_const.prodMk contMDiff_id`.) Both are corollaries of
`TauCeti.SmoothIsotopy.exists_diffeotopy_interior_velocity_eq_forall_apply_eq`, for
velocity forms `k_t^* β_t + dh_t` with every `β_t` closed and vanishing off a
compact set: the first with `β = 0`, the second with that set `univ`. Its route:

1. Choose a compact neighbourhood `K'` of `K`. Isotopy extension at every
   time (`Extension.lean`) gives `Ψ` with `Ψ (t, f₀ x) = k (t, x)` on `K'`.
2. With a smooth cutoff $\chi$ on `M` that is `1` near $f_0(K)$ and supported in
   $f_0(K')$, set $G_t=(\chi\cdot h_t\circ f_0^{-1})\circ\Psi_t^{-1}$, and $0$
   off the image of $f_0$. It is smooth on `M × unitInterval`, because `Ψ⁻¹` is
   jointly smooth and $f_0$ is a local diffeomorphism, and $G_t\circ k_t=h_t$
   near `K` (`TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`, in
   `Extension.lean`).
3. `Φ` comes from `TauCeti.Diffeotopy.exists_interior_velocity_eq`, which
   this part adds to *Hamiltonian flows*' `Flux/CompactSupport.lean`, for the
   form $\beta+dG$ on `unitInterval × M`. There the forms $\beta_t+dG_t$
   are extended past both ends with
   `DifferentialForm/TimeExtension.lean`, and
   $X_t$ solves $\iota_{X_t}\omega=\beta_t+dG_t$. It is smooth
   by `TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`,
   and complete because it vanishes off a compact set. Its
   flow `timeDependentFlowDiffeotopy` is `Φ`.
4. On $k_t(K)$ the field $X_t$ is the velocity of $k$. Pulled back by $k_t$,
   both contractions are $k_t^*\beta_t+dh_t$, and $dk_t$ is
   onto (`TauCeti.SmoothIsotopy.eq_mfderiv_of_forall_eq_mpullback_prodMk_velocityForm`,
   in `Velocity.lean`). Uniqueness of solutions on `[0, 1]`
   (`TauCeti.timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq`, which this
   part adds to `Geometry/Manifold/Flow/TimeDependent.lean` of *Smooth
   families*, with `TauCeti.timeDependentFlowOf_eq_of_hasMFDerivWithinAt`)
   gives `Φ (t, f₀ x) = k (t, x)`.
5. The slices preserve `ω`, in `exists_interior_velocity_eq`, by
   `TauCeti.Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff`, since
   $\beta_t+dG_t$ is closed for $t\in[0,1]$; the time extension need not be
   closed past the ends. In the Hamiltonian case `G` generates `Φ`
   (`TauCeti.Diffeotopy.IsGeneratedBy`), so `Φ` is compactly supported Hamiltonian by
   `TauCeti.Diffeotopy.isCompactlySupportedHamiltonian_iff_isGeneratedBy`, and
   `Φ.HasHamiltonian ω (fun p ↦ G (Φ.cylinderMap p, p.2))` by
   `TauCeti.Diffeotopy.hasHamiltonian_comp_iff`.

`Flow.lean` imports, from *Hamiltonian flows*, `Diffeotopy/Velocity.lean` and
`Flux/CompactSupport.lean`.

Expected size: 450 lines.

### `Geometry/Symplectic/Moser/Family.lean`

Two forms of Moser's argument near a compact set, both with the cut-off
Moser field `moserField` of `Moser/Field.lean`, in the form for a family
of two-forms that #551 gives it, and both returning a compactly supported
`Diffeotopy`. In the first, the
family runs in the Moser time and is written over `ℝ`, as a form on
`ℝ × M` with Tau Ceti's slices and `SmoothForm.timeDeriv`
(`Geometry/Manifold/DifferentialForm/Flow/Family.lean`). Callers extend
their families over `unitInterval` with
`DifferentialForm/TimeExtension.lean`, which keeps the slices. In the second, the parameter is not a time and runs over
`unitInterval`.

*Along a family*, fixing a compact submanifold `f : SmoothEmbedding J I ∞ Q M`,
`[CompactSpace Q]`:

```lean
theorem TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv
    [I.Boundaryless] [T2Space M] [SecondCountableTopology M] (f : SmoothEmbedding J I ∞ Q M)
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2) (hσ : ∀ t ∈ Icc (0 : ℝ) 1, (σ.slice t).IsClosed)
    (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hγ : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ range f),
      (σ.timeDeriv.slice p.1).val p.2 = mextDeriv (γ.slice p.1).val p.2)
    (hγf : ∀ t ∈ Icc (0 : ℝ) 1, SmoothForm.mpullback f f.contMDiff (γ.slice t) = 0)
    (hnd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q, ((σ.slice t).bilinFormAt (f q)).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t q, Ψ (t, f q) = f q) ∧
      ∀ᶠ x in 𝓝ˢ (range f), ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (σ.slice t)).val x = (σ.slice 0).val x
```

The primitive `γ_t` vanishes on the tangent vectors of `Q`. Its correction
by $dF_t$, with $F$ the function of the correction lemma
`TauCeti.SmoothEmbedding.exists_contMDiff_mextDeriv_eq_mpullback_prodMk`
(`Geometry/Manifold/TubularNeighborhood/OneFormCorrection.lean`: the relative
Poincaré operator of `γ_t` on a tubular neighbourhood, cut off near `Q`),
makes it vanish as a full covector along `Q`. The cut-off
Moser field then vanishes on `Q`, and Moser's principle along trajectories
(`mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`)
gives the identity near `Q` for every $t\in[0,1]$. The field is
`moserField σ γ' ρ` for the corrected primitive `γ'` and a cutoff `ρ` on
`ℝ × M`. This is the argument of
*Moser isotopy*'s milestone *Relative Moser theorem fixing a submanifold*
for a general family.

*With a parameter*: Moser's argument for the linear paths $\omega_0+s\,d\beta_t$, $s\in[0,1]$, for
every value of a parameter $t\in[0,1]$, relative to a compact set:

```lean
theorem TauCeti.SmoothTwoForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
    [I.Boundaryless] [T2Space N] {ω₀ : SmoothTwoForm I N} (hω₀ : ω₀.IsClosed)
    (σ : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × N) ℝ 2)
    (β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × N) ℝ 1)
    (hβ : ∀ t, mextDeriv (β.slice t).val = (σ.slice t - ω₀).val) (hβ₀ : β.slice 0 = 0)
    {K : Set N} (hK : IsCompact K) (hβK : ∀ t, ∀ x ∈ K, (β.slice t).val x = 0)
    (hnd : ∀ t, ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1,
      ((ω₀ + s • (σ.slice t - ω₀)).bilinFormAt x).Nondegenerate) :
    ∃ χ : Diffeotopy I ∞ N, (∀ t, ∀ x ∈ K, χ (t, x) = x) ∧
      (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, χ (t, x) = x) ∧
      (∀ t, β.slice t = 0 → ∀ x, χ (t, x) = x) ∧
      ∀ᶠ x in 𝓝ˢ K, ∀ t,
        (SmoothForm.mpullback (χ.timeSlice t) (χ.timeSlice t).contMDiff (σ.slice t)).val x =
          ω₀.val x
```

Here `β.slice t` stands for the slice `SmoothForm.mpullback (Prod.mk t) _ β`
on `N`, and likewise for `σ`. *Smooth families* fixes how the slices of a
family over `unitInterval` are written; the issue uses that and adds no
definition. The hypothesis `hβ₀` makes `χ` start at the identity, so that it
is a `Diffeotopy` in the parameter `t`. The conclusion that the slices are
the identity where `β_t = 0` is what keeps the ends of a family fixed. For
each `t`, the Moser field solves
$\iota_{X_{s,t}}(\omega_0+s\,d\beta_t)=-\rho\beta_t$, with a cutoff `ρ` near
`K`, and `χ (t, ·)` is the time-one map of its flow. For each `t` this
field is `moserField` of the segment family
`SmoothForm.lineMapFamily ω₀ (σ.slice t) contDiff_id`, with `β.slice t`
constant in the Moser time, and the steps follow Tau Ceti's
`exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`, which
the module docstring credits. The file proves that this field is jointly
smooth in `t`, `s` and the point, by the argument of
`contMDiff_moserField`. For joint smoothness of the flow in `t`, the issue
extends `β` in `t` past both ends and reads the flows of the $X_{\cdot,t}$
off one flow, by `TauCeti.contMDiff_timeDependentFlowOf_param`
(`Geometry/Manifold/Flow/TimeDependent.lean`): Tau Ceti's
`contMDiffAt_flowOf_param` runs the vertical field of their suspensions
$(1,X_{s,t})$, a family over `t`, whose first component is constant. The
time-one maps, a family over `ℝ`, give the diffeotopy by
`TauCeti.Diffeotopy.ofReal`. The ball extension applies this theorem to parametric radial
primitives, which are not in this file: they are
`SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex` of
*Smooth families*' `Geometry/Manifold/DifferentialForm/SmoothFamily/Poincare.lean`,
for an open set star-convex about any centre `c` (here `0`), with the
segment from `c`. Expected size: 500 lines.

### `Geometry/Symplectic/IsotopyExtension/Ball/Basic.lean`

```lean
/-- `j` is a symplectic embedding of the closed ball `B(r)`: smooth on an open
neighbourhood of `B(r)`, injective on it, and pulling `ω` back to `ω₀` on the open ball. -/
def IsSymplecticBallEmbedding (ω : TauCeti.SmoothTwoForm I M) (r : ℝ)
    (j : StdSpace (Fin n) → M) : Prop :=
  (∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ ContMDiffOn 𝓘(ℝ, StdSpace (Fin n)) I ∞ j U) ∧
    Set.InjOn j (Metric.closedBall 0 r) ∧
    ∀ z ∈ Metric.ball 0 r,
      TauCeti.mpullback 𝓘(ℝ, StdSpace (Fin n)) I j ω.val z = (stdForm (Fin n)).constSmooth.val z

/-- A smooth family of symplectic embeddings of `B(r)`, jointly smooth near `[0, 1] × B(r)`. -/
def IsSymplecticBallFamily (ω : TauCeti.SmoothTwoForm I M) (r : ℝ)
    (e : unitInterval × StdSpace (Fin n) → M) : Prop :=
  (∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧
    ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, StdSpace (Fin n))) I ∞ e (univ ×ˢ U)) ∧
    ∀ t, IsSymplecticBallEmbedding ω r (fun z ↦ e (t, z))
```

API: `isSymplecticBallEmbedding_def`, `isSymplecticBallFamily_def`;
`IsSymplecticBallEmbedding.mpullback_eq_of_mem_closedBall` (for `0 < r`, the
pullback is `ω₀` on the closed ball, by continuity) and
`IsSymplecticBallEmbedding.injective_mfderiv` (immersion on the open ball:
if $dj_z\,v=0$ then $\omega_0(v,\cdot)=\omega(dj_z\,v,dj_z\,\cdot)=0$, so
$v=0$ by nondegeneracy of `stdForm`; on $B(r)$ for `0 < r`, with the
previous lemma);
`IsSymplecticBallEmbedding.mono` (a smaller radius);
`isSymplecticBallEmbedding_id` (the identity of `StdSpace (Fin n)` into
itself with `ω₀`: the example); `IsSymplecticBallFamily.of_path` (a smooth
path of centres `c : unitInterval → M` gives the family `fun p ↦ c p.1` of
radius `0`: the case $\lambda=0$ and an example);
`isSymplecticBallFamily_const` (a constant family).

The first half of the milestone:

```lean
theorem IsSymplecticBallEmbedding.exists_lt_isSymplecticBallEmbedding_eqOn
    (hω : ω.IsClosed) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {j : StdSpace (Fin n) → M} (hj : IsSymplecticBallEmbedding ω r₀ j) :
    ∃ r, r₀ < r ∧ ∃ j', IsSymplecticBallEmbedding ω r j' ∧
      Set.EqOn j' j (Metric.closedBall 0 r₀)
```

`j^*ω - ω₀` is closed on a ball about `0` and vanishes on $B(\lambda)$ as a
full form. Its radial primitive vanishes there too, because every segment to
`0` from a point of $B(\lambda)$ stays in it. Tau Ceti's relative Moser
theorem `exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`,
on `StdSpace (Fin n)`, with that primitive cut off away from $B(\lambda)$ and
$K=B(\lambda)$, gives `Φ` fixing
$B(\lambda)$ with `Φ^* j^* ω = ω₀` near it. The map `j' = j ∘ Φ` is injective near
$B(\lambda)$ (`SmoothEmbedding/Neighborhood.lean`), which gives `r`. The cut-off
primitive is `StarConvex.exists_contDiff_eqOn_zero_eventually_extDeriv_eq`, from
`Analysis/Calculus/DifferentialForm/Poincare.lean`, which this file imports. Expected
size: 350 lines, with the API.

### `Geometry/Symplectic/IsotopyExtension/Ball/Isotopy.lean`

```lean
theorem IsSymplecticBallFamily.exists_hasHamiltonian_extension
    [T2Space M] [SigmaCompactSpace M] (hω : ω.IsSymplectic)
    (hdim : Module.finrank ℝ E = 2 * n) {r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hr₀r : r₀ < r)
    {j₀ j₁ : StdSpace (Fin n) → M} (hj₀ : IsSymplecticBallEmbedding ω r j₀)
    (hj₁ : IsSymplecticBallEmbedding ω r j₁) {e : unitInterval × StdSpace (Fin n) → M}
    (he : IsSymplecticBallFamily ω r₀ e)
    (he₀ : ∀ z ∈ Metric.closedBall 0 r₀, e (0, z) = j₀ z)
    (he₁ : ∀ z ∈ Metric.closedBall 0 r₀, e (1, z) = j₁ z) :
    ∃ ρ, r₀ < ρ ∧ ρ < r ∧ ∃ (Φ : TauCeti.Diffeotopy I ∞ M) (F : M × unitInterval → ℝ)
      (K : Set M), IsCompact K ∧ Φ.HasHamiltonian ω F ∧ (∀ p, p.1 ∉ K → F p = 0) ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      (∀ t, ∀ z ∈ Metric.closedBall 0 r₀, Φ (t, j₀ z) = e (t, z)) ∧
      ∀ z ∈ Metric.closedBall 0 ρ, Φ.final (j₀ z) = j₁ z
```

The route keeps the times of `e` exactly:

1. *A smooth family that is right along $B(\lambda)$.* For $\lambda>0$,
   `SmoothEmbedding/Neighborhood.lean` makes `e` a `SmoothIsotopy` of an open
   ball about $B(\lambda)$. For $\lambda=0$ it is the isotopy of a point
   along the path of centres. `Extension.lean` gives `Ψ` with
   $\Psi_t\circ e_0=e_t$ on $B(\lambda)$. Then $k'_t=\Psi_t\circ j_0\circ P_t$
   is a family of embeddings of a ball $B(\rho_1)$ with $k'_0=j_0$ and
   $k'_t=e_t$ on $B(\lambda)$. Here $P_t$ is a smooth path of linear maps,
   `id` for $\lambda>0$. For $\lambda=0$ it is
   $(d\Psi_t\,dj_0(0))^{-1}L_t$, where $L_t$ are symplectic frames at the
   centre with $L_0=dj_0(0)$ and $L_1=dj_1(0)$. These are built from
   *Linear Moser* (`Geometry/Symplectic/LinearMoser.lean`, for the path of
   forms $(d\Psi_t\,dj_0(0))^*\omega$) followed by a smooth path in the
   symplectic group (`Analysis/Matrix/SymplecticGroup/Connected.lean`) that
   matches $dj_1(0)$ at $t=1$. In both cases $k_t'^*\omega=\omega_0$ along
   $B(\lambda)$ as full forms.
2. *The end $t=1$.* $g=k_1'^{-1}\circ j_1$ is the identity with derivative
   the identity along $B(\lambda)$. With $g_t=(1-t)\,\mathrm{id}+t\,g$, the
   family $k_t=k'_t\circ g_t$ is still right along $B(\lambda)$, and
   $k_0=j_0$, $k_1=j_1$ near $B(\lambda)$. For $\lambda>0$ this is the
   source's Theorem A.2.1(iii) step, which keeps both ends.
3. *Make it symplectic.* `Moser/Family.lean`, with $\beta_t$ the
   parametric radial primitive of $k_t^*\omega-\omega_0$ and
   $K=B(\lambda)$, gives $\chi_t$. Here $\beta_0=\beta_1=0$ because $j_0$ and
   $j_1$ are symplectic, so $\chi_0=\chi_1=\mathrm{id}$. The family
   $\hat k_t=k_t\circ\chi_t$ consists of symplectic embeddings of some
   $B(\rho_2)$, with $\hat k_t=e_t$ on $B(\lambda)$ and $\hat k_i=j_i$
   ($i=0,1$). The forms are compared on $\mathbb R^{2n}$, as the published
   errata correct the source.
4. *Hamiltonian.* The velocity forms of $\hat k$ are closed on a ball, and
   their parametric radial primitives $h_t$ are smooth in $(t,z)$. `Flow.lean`
   (`exists_hasHamiltonian_forall_apply_eq`, with $K=B(\rho)$ for
   $\lambda<\rho<\rho_2$) concludes.

The milestone is the conjunction of the two halves:

```lean
theorem exists_ballEmbedding_extension_and_hasHamiltonian_extension … :
    (∀ r₀, 0 < r₀ → ∀ j, IsSymplecticBallEmbedding ω r₀ j → ∃ r, r₀ < r ∧ …) ∧
      ∀ r₀ r, 0 ≤ r₀ → r₀ < r → ∀ j₀ j₁ e, … → ∃ ρ, …
```

with the conclusions of the two theorems above. Expected size: 550 lines.
If it exceeds the limit, step 1 for $\lambda=0$ (the frames) becomes an
issue of its own before it.

### `Geometry/Symplectic/IsotopyExtension/Cohomological/Primitive.lean`

Let `M : Type` be compact, `Q : Set M`, `U : Opens M` with `Q ⊆ U`, and let
`ι : C(Q, U)` and `ιM : C(Q, M)` be the inclusions. Write `H₁ X` for
`((singularChains ℤ).obj (.of X)).homology 1`.

- `exists_closedForms_periods_eq`: if every `H₁ Q →+ ℝ` is the restriction
  of the periods of a class of `H¹_dR(M)`, then for every smooth family `α`
  of closed one-forms on `U` there is a smooth family `β` of closed one-forms
  on `M` with
  `homologyPeriodHom α_t ∘ ι_* = homologyPeriodHom β_t ∘ ιM_*` for every
  `t`. Since `H¹_dR(M)` is finite-dimensional (see *What the part uses*), so
  is the space of the periods on `H₁ Q`. Fix classes whose restrictions form
  a basis, closed representatives `b_i`, and finitely many cycles `z_j` of
  `Q` on which evaluation is injective. Then $\beta_t=\sum a_i(t)b_i$, where
  the coefficients are a fixed linear function of the periods of `α_t` on
  the `z_j`. Those periods are smooth in `t`, by
  `IsSmoothFamily.contMDiff_homologyPeriodHom` in
  `Geometry/Manifold/DeRham/HomologyPeriod.lean`: each singular simplex is
  homotopic to a smooth path (Tau Ceti's `Geometry/Manifold/SmoothApprox.lean`),
  and along a smooth path the period is the change of a jointly smooth
  primitive of the pulled-back family on `ℝ`.
- `TauCeti.NDRPair.exists_forall_exact`: for NDR data on `Q` there
  is an open `V` with `Q ⊆ V ⊆ U` such that every closed one-form on `U`
  whose periods vanish on the image of `H₁ Q` is exact on `V`. This is
  `exists_isOpen_range_singularHomologyMap_le` with
  `TauCeti.exists_mextDeriv_eq_of_homologyPeriodHom_eq_zero` and
  `TauCeti.homologyPeriodHom_singularHomologyMap` for the inclusion `V → U`.
- `SmoothIsotopy.homologyPeriodHom_mpullback_eq`: for any `SmoothIsotopy`
  `φ` starting at `f₀` and a closed one-form `θ`, the periods of `φ_t^* θ`
  are those of `f₀^* θ`, and from the inclusion of `U` those of `θ`. The
  slices are homotopic to `f₀`, so
  `ContinuousMap.singularHomologyMap_eq_of_homotopic` and
  `homologyPeriodHom_singularHomologyMap` apply.
- `exists_contMDiff_primitive_of_periods`: for NDR data on `Q`, a
  `SmoothIsotopy` `φ` of `U` whose start `f₀` is the inclusion
  (`∀ x, f₀ x = x`), and smooth families `α` on `U` and `β` on `M` of closed
  one-forms with the periods equation of the first item (no compactness), the
  forms `α_t - φ_t^* β_t` are exact on `V` with a primitive `h` smooth on
  `unitInterval × V`. Issue 11 takes the velocity forms of a symplectic `φ`
  as `α`, and `β` from the first item or `β = 0`. The start is a variable
  with that equation rather than the term `⟨Subtype.val, contMDiff_subtypeVal⟩`,
  since with that term Lean finds no coercion of `φ` to a function. Exactness
  comes from the last two items. The smooth choice is *Hamiltonian flows*'
  `SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms` (see
  *What the part uses*), applied on the manifold `V`.

Expected size: 450 lines.

### `Geometry/Symplectic/IsotopyExtension/Cohomological/Basic.lean`

```lean
theorem TauCeti.SmoothIsotopy.exists_diffeotopy_mem_diffeomorphStabilizer_eqOn
    {M : Type} … [CompactSpace M] (hω : ω.IsSymplectic) {Q : Set M} (hQ : IsCompact Q)
    (hQr : Nonempty (NDRPair Q)) {U : Opens M} (hQU : Q ⊆ U)
    {f₀ f₁ : C^∞⟮I, U; I, M⟯} (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hφ : φ.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal ω) ω)
    (hsurj : ∀ f : H₁ Q →+ ℝ, ∃ c : deRhamCohomology I M 1,
      (deRhamCohomology.homologyPeriod c).comp
        (ContinuousMap.singularHomologyMap ℤ 1
          (⟨Subtype.val, continuous_subtypeVal⟩ : C(Q, M))).toAddMonoidHom = f) :
    ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ Ψ : Diffeotopy I ∞ M,
      (∀ t, Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer ω) ∧
      ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x)

theorem TauCeti.SmoothIsotopy.exists_hasHamiltonian_eqOn
    {M : Type} … [T2Space M] [SigmaCompactSpace M] (hω : ω.IsSymplectic) {Q : Set M}
    (hQ : IsCompact Q) (hQr : Nonempty (NDRPair Q)) {U : Opens M} (hQU : Q ⊆ U)
    {f₀ f₁ : C^∞⟮I, U; I, M⟯} (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hφ : φ.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal ω) ω)
    (hQ1 : Subsingleton (H₁ Q →+ ℝ)) :
    ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ (Ψ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ)
      (K : Set M), IsCompact K ∧ Ψ.HasHamiltonian ω F ∧ (∀ p, p.1 ∉ K → F p = 0) ∧
      (∀ t, ∀ y ∉ K, Ψ (t, y) = y) ∧ ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x)
```

Both start `φ` at a variable `f₀` equal to the inclusion, as
`Primitive.lean` does, since with the start written as
`⟨Subtype.val, contMDiff_subtypeVal⟩` Lean finds no coercion of `φ` to a
function and `φ (t, x)` does not elaborate.
The first is `Flow.lean`'s symplectic theorem with `K` a compact neighbourhood
of `Q` in `V`, and `β`, `h` from `Primitive.lean`. The second takes `β = 0`.
Its periods vanish by `hQ1`, so it needs no compactness of `M`, only the
compact support that `Flow.lean`'s Hamiltonian theorem provides. The
milestone is the conjunction, under the plan's hypotheses (compact `M`):

```lean
theorem TauCeti.SmoothIsotopy.exists_symplectic_extension_and_hamiltonian_extension … :
    (hsurj-statement → ∃ N Ψ, …) ∧ (Subsingleton (H₁ Q →+ ℝ) → ∃ N Ψ F K, …)
```

Expected size: 250 lines.

### `Geometry/Symplectic/IsotopyExtension/Submanifold.lean`

```lean
theorem TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [J.Boundaryless] [CompactSpace Q]
    (hω : ω.IsSymplectic) (i : SmoothEmbedding J I ∞ Q M) {f₁ : C^∞⟮J, Q; I, M⟯}
    (e : SmoothIsotopy i.toContMDiffMap f₁)
    (he : ∀ t, TauCeti.mpullback J I (fun q ↦ e (t, q)) ω.val = TauCeti.mpullback J I i ω.val) :
    ∃ (U : Opens M) (hU : Set.range i ⊆ U) (g₀ g₁ : C^∞⟮I, U; I, M⟯) (_ : ∀ x, g₀ x = x)
      (F : SmoothIsotopy g₀ g₁),
      F.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal ω) ω ∧
      ∀ t q, F (t, ⟨i q, hU ⟨q, rfl⟩⟩) = e (t, q)
```

The start `g₀` of `F` is the inclusion of `U`, given by its equation for the
same reason as in `Cohomological/Basic.lean`.
The route is the third decision: `Extension.lean` gives `G` with
$G_t\circ i=e_t$. The family $\omega_t=G_t^*\omega$ has velocity $d\gamma_t$,
with $\gamma_t$ the velocity form of the restriction of `G` to the identity
(`Velocity.lean`).
The form $\gamma_t-r^*(i^*\gamma_t)$, for the retraction `r` of
`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`, vanishes on `TQ`.
The relative Moser theorem along a family of `Moser/Family.lean`, applied to
the extensions of $\omega_t$ and of this primitive past both ends, gives
$\chi_t$, and
$F_t=G_t\circ\chi_t$ on the neighbourhood it provides. Expected size: 350
lines.

## Milestones

| Milestone | Theorem | File |
|---|---|---|
| *Symplectic ball extension* | `exists_ballEmbedding_extension_and_hasHamiltonian_extension` | `IsotopyExtension/Ball/Isotopy.lean` |
| *Symplectic isotopy extension* | `TauCeti.SmoothIsotopy.exists_symplectic_extension_and_hamiltonian_extension` | `IsotopyExtension/Cohomological/Basic.lean` |
| *Neighbourhood extension of submanifold isotopies* | `TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq` | `IsotopyExtension/Submanifold.lean` |

Each holds with the plan's hypotheses, read as the decisions say, or with
fewer:

- *Symplectic ball extension* drops connectedness of `M`, which the proof
  does not use: everything happens in the component of the balls. It adds
  Hausdorffness and σ-compactness, as Tau Ceti's isotopy extension does. The
  dimension $2n$ of `M` is `Module.finrank ℝ E = 2 * n`, and the case
  $\lambda=0$ is the same statement (first decision).
- *Symplectic isotopy extension*: its Hamiltonian half does not need `M`
  compact. The milestone theorem keeps the plan's compactness for both
  halves and the separate theorem drops it.
- *Neighbourhood extension of submanifold isotopies* drops the hypothesis
  that $i^*\omega$ has constant rank (third decision). The statement is about
  every compact embedded submanifold, so it contains the symplectic,
  isotropic, Lagrangian and coisotropic cases that the plan names. If the
  building issue finds a step that needs constant rank after all, it adds
  the plan's hypothesis (the kernels of $i^*\omega$ have the same dimension at
  all points) and records the reason in this file.

The statements include the degenerate cases (`n = 0`, `Q` empty, radius
`0`), and none needs an entry in `ERRATA.md`. The source corrections that the plan
records for the proof of Theorem 3.3.1 (the endpoint case of A.2.1, the
radius $0$, and the forms on $\mathbb R^{2n}$) concern the proof route, which
this design already follows. `Ball/Isotopy.lean` cites
[McDuffSalamon2019Errata] for the last of them.

## What the part uses

- *Standard model* (merged): `StdSpace`, `stdForm`, the Euclidean norm of
  `StdSpace` for the balls.
- *Linear Moser* (merged): `Geometry/Symplectic/LinearMoser.lean`, for the
  frames along a path of centres.
- *Smooth families* (`design/smooth-families.md`, merged): Seeley's
  extension in the time variable, of maps in
  `Geometry/Manifold/ContMDiff/TimeExtension.lean` (used by `Extension.lean`)
  and of forms on `unitInterval × M` in
  `Geometry/Manifold/DifferentialForm/TimeExtension.lean` (used by
  `Moser/Family.lean`, and by `Flow.lean` through *Hamiltonian flows*'
  `Flux/CompactSupport.lean`); the reparametrization of time
  `exists_contDiff_eqOn_id_Icc_mem_Ioo` in
  `Analysis/SpecialFunctions/SmoothTransition.lean` (used by
  `Extension.lean`); the parametric radial primitives
  `exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex` in
  `Geometry/Manifold/DifferentialForm/SmoothFamily/Poincare.lean`
  (used by `Ball/Isotopy.lean`); the homotopy operator on smooth families
  `SymplecticGeometry.IsSmoothFamily.homotopyOperator` in
  `Geometry/Manifold/DifferentialForm/SmoothFamily/HomotopyOperator.lean`
  (used by `DifferentialForm/VectorBundlePoincare.lean`); and the
  instance
  `FiniteDimensional ℝ (deRhamCohomology I M k)` for a compact boundaryless
  `M`, which `Geometry/Manifold/DeRham/SmoothFamily/GoodCover.lean` derives
  from `hasFiniteGoodCover_of_compactSpace` (used by
  `Cohomological/Primitive.lean`, which also imports `Geometry/Manifold/DeRham/Map.lean`
  for `TauCeti.SmoothForm.mpullback_mem_closedForms`). The part does not use the splittings and
  `contMDiff_repr_mk_of_hasFiniteGoodCover`: the periods are smooth in `t`
  as line integrals. Its flows are Tau Ceti's `timeDependentFlowDiffeotopy`,
  already a `Diffeotopy`, except in `Moser/Family.lean`, which imports the
  bridge `Diffeotopy/Real.lean` for `TauCeti.Diffeotopy.ofReal` and
  `Geometry/Manifold/Flow/TimeDependent.lean` for
  `TauCeti.contMDiff_timeDependentFlowOf_param`, a lemma this part adds
  there.
- *Hamiltonian flows*: in `DeRham/FamilyPrimitive.lean`, the smooth primitive of a
  smooth family of exact one-forms over $[0,1]$, which that part's design
  (`design/hamiltonian-flows.md`, Decision 4) builds on chart balls and glues
  over the components. This part needs it on any manifold, so that it
  applies on an open subset (`Cohomological/Primitive.lean`). This pull
  request records it in `design/hamiltonian-flows.md` as the public lemma
  `SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms`, part of
  that part's building issue 5. It also uses the predicate
  `TauCeti.Diffeotopy.IsCompactlySupportedHamiltonian` of
  `Flux/CompactSupport.lean`, through
  `isCompactlySupportedHamiltonian_iff_isGeneratedBy` (step 5 of `Flow.lean`),
  and states the compact support of `exists_hasHamiltonian_forall_apply_eq`
  with it; and the flow `TauCeti.Diffeotopy.exists_interior_velocity_eq`,
  which this part adds to that file (step 3 of `Flow.lean`).
  `IsotopyExtension/Velocity.lean` also imports three files of that part:
  `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean`, for the derivatives
  of the motion of a diffeotopy; `Geometry/Manifold/Instances/Icc.lean`,
  for the unit tangent vector of `unitInterval`; and
  `Geometry/Manifold/MFDeriv/Prod.lean`, for derivatives on products.
  `Moser/Family.lean` imports `Geometry/Diffeomorphism/Diffeotopy/Velocity.lean`
  too, for the slices of the Moser diffeotopy.
- *Contact geometry*: the merged
  `Geometry/Manifold/DifferentialForm/LieDeriv.lean`, whose
  `TauCeti.mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero`
  `IsotopyExtension/Velocity.lean` uses for the closedness of the velocity
  forms, and `Geometry/Manifold/DifferentialForm/Flow/Family.lean`, whose
  `TauCeti.SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily`
  `Moser/Family.lean` uses for the velocity of a segment of forms.
- *Moser isotopy*: `Moser/Field.lean`, whose `moserField` (#506) is
  the cut-off Moser field of both theorems of `Moser/Family.lean`. That
  design planned it for the linear segment between two forms with a fixed
  primitive. #551 generalizes it to a smooth family of two-forms
  over a parameter manifold with a time-dependent primitive, the segment being the family
  `SmoothForm.lineMapFamily σ₀ σ₁ contDiff_id`, and this pull request records
  that choice in `design/moser-isotopy.md`. So the library adapts Tau Ceti's
  private field of `RelativeMoser.lean` once. `Moser/Family.lean` also imports
  `Geometry/Symplectic/Manifold/Family.lean`, for the openness of the set
  where the slices of a family are nondegenerate, and `Moser/Isotopy.lean`
  derives its theorem fixing a submanifold from the family theorem of
  `Moser/Family.lean`.
  `IsotopyExtension/Ball/Basic.lean` also imports
  `Geometry/Symplectic/Manifold/TwoForm.lean`, for
  `TauCeti.SmoothTwoForm.injective_mfderiv_of_mpullback_apply_eq` (a map
  pulling a form back to a nondegenerate one is an immersion), which the
  pull request of `Ball/Basic.lean` adds there, and
  `Geometry/Symplectic/Manifold/Family.lean`, for
  `TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_add_smul_sub_of_eq` (the
  segment between two forms that agree at a point is constant there), which
  that pull request also adds.
- Tau Ceti, besides the declarations named above:
  `TauCeti.SmoothIsotopy` with `timeSlice`, `ContMDiffMap.smoothIsotopyRefl`;
  `TauCeti.Diffeotopy` with `timeSlice`, `final`, `trans`, `symm`,
  `smoothIsotopy`, `exists_extend_of_isCompact`;
  `TauCeti.SmoothForm.diffeomorphStabilizer`, `isotopyStabilizer`;
  `Manifold.IsSmoothEmbedding`, `isSmoothEmbedding_diffeomorph_comp`;
  `TauCeti.SymplecticForm.constSmooth`;
  `TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`;
  `TauCeti.timeDependentFlowOf`, `timeDependentFlowOf_eq_self_of_forall_eq_zero`;
  `TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem`
  (Moser's principle along trajectories, for the relative statements);
  `TauCeti.pathClassIntegral`,
  `TauCeti.pathClassIntegral_mk_eq_pathIntegral`;
  `TauCeti.homologyPeriodHom_singularHomologyMap`,
  `ContinuousMap.singularHomologyMap_eq_of_homotopic`; `TauCeti.NDRPair`,
  `TauCeti.NDRPair.ofHomotopyRel`;
  `Matrix.isPathConnected_symplecticGroup` (whose smooth version this part
  adds), `Units.polarUnitary`, `SymplecticGroup.polarUnitary_mem`,
  `SymplecticGroup.rpow_mem`, `Matrix.UnitaryGroup.exists_expUnitary_eq`.
- Mathlib: `SmoothBumpCovering.embeddingPiTangent`, `Real.smoothTransition`,
  `ContinuousMap.HomotopyRel`, `Metric.closedBall`, `Metric.ball`.

Mathlib and Tau Ceti were searched, at the pinned versions, for isotopy
extension without a change of time, neighbourhood deformation retracts (Tau
Ceti's NDR pairs are the one hit, and the part uses them), symplectic
families of embeddings and their velocity forms, symplectic ball embeddings,
smooth paths in the symplectic group, parametric Moser theorems and the
three milestones. They have only the ingredients listed above.

## Building issues

In this order; each is blocked by the ones listed. All are sub-issues of
#474, *Build the part Isotopy extension*. Sizes are estimates. "S14" and
"S15" stand for the issues of *Smooth families* and *Hamiltonian flows* that
build the files named, as their design files list them.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Singular homology near the subset of an NDR pair | `AlgebraicTopology/Singular/NDRPair.lean` | — | 150 |
| 2 | Smooth paths in the symplectic group | `Analysis/Matrix/SymplecticGroup/Connected.lean` | — | 150 |
| 3 | Embeddings near a compact set | `Geometry/Manifold/SmoothEmbedding/Neighborhood.lean` | — | 250 |
| 4 | Isotopy extension at every time | `Geometry/Manifold/SmoothIsotopy/Extension.lean` | 3; S14 (`ContMDiff/TimeExtension.lean`) | 450 |
| 5 | Velocity forms of symplectic isotopies | `IsotopyExtension/Velocity.lean` | — | 300 |
| 6 | Extension by symplectic and Hamiltonian flows | `IsotopyExtension/Flow.lean` | 4, 5; S14 (both `TimeExtension.lean` files); S15 (`Flux/Hamiltonian.lean`, `Flux/CompactSupport.lean`) | 450 |
| 7 | Moser's argument along a family and with a parameter | `Moser/Family.lean` | S14 (`DifferentialForm/TimeExtension.lean`); #506 and #551 (`moserField` for a family) | 550 |
| 8 | Symplectic ball embeddings and their enlargement | `IsotopyExtension/Ball/Basic.lean` | 3 | 350 |
| 9 | The symplectic ball extension | `IsotopyExtension/Ball/Isotopy.lean` | 2, 4, 6, 7, 8 | 550 |
| 10 | Closed forms with prescribed periods, and uniform primitives | `IsotopyExtension/Cohomological/Primitive.lean` | 1, 5; S14 (`DeRham/SmoothFamily/GoodCover.lean`, the `FiniteDimensional` instance); S15 (`DeRham/FamilyPrimitive.lean`) | 450 |
| 11 | The symplectic isotopy extension | `IsotopyExtension/Cohomological/Basic.lean` | 6, 10 | 250 |
| 12 | Neighbourhood extension of submanifold isotopies | `IsotopyExtension/Submanifold.lean` | 4, 5, 7 | 350 |

Issues 1, 2, 3 and 5 can start at once. The milestones are proved in issues 9
(*Symplectic ball extension*), 11 (*Symplectic isotopy extension*) and 12
(*Neighbourhood extension of submanifold isotopies*). Issue 9 is the largest.
If it exceeds the size limit, its first step for radius $0$ (the frames along
the path of centres) becomes an issue of its own between 8 and 9.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.3 (Theorems 3.3.1 and 3.3.2), Exercise 3.4.20, Appendix A.2 (Theorem
  A.2.1, Lemma A.2.2).
* [D. McDuff, D. Salamon, errata to *Introduction to Symplectic Topology*][McDuffSalamon2019Errata],
  p. 114.
* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33,
  Springer, 1976, Chapter 8, §1 (isotopy extension).
* R. T. Seeley, *Extension of C^∞ functions defined in a half space*,
  Proceedings of the American Mathematical Society 15 (1964), 625–626.
