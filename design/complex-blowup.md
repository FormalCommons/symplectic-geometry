# Complex blowup

This is the detailed design of part 59 of `DESIGN.md`, *Complex blowup*. It
serves four milestones: *Tautological line bundle and the exceptional
divisor*, *Complex blowup at a point* and *Blowup as a connected sum with
the reversed projective space* of `atlas/constructing-symplectic-manifolds.md`,
and *First Chern class of a blowup at a point* of
`auxiliary/connected-sums-and-blowups.md`. The first statement of the third
milestone, the independence of the connected sum, is *Connected sums*'
(part 57) and is not repeated here.

Sources: McDuff–Salamon [McDuffSalamon2017], §7.1 (the definition (7.1.1),
Lemma 7.1.1, Exercise 7.1.2, Lemma 7.1.3, Exercise 7.1.4 and (7.1.31));
Griffiths–Harris [GriffithsHarris1978], Chapter 1, §4 (the blowup of a
point, its charts, and the line bundle of a divisor); Schnell [Schnell2024],
Lemma 23.5 (the canonical bundle of a blowup by the Jacobian of the blowdown
in a chart).

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, Tau Ceti `0651fdbae946` and the Mathlib it pins. Tau Ceti
paths are relative to `.lake/packages/TauCeti/TauCeti/`, and paths of new
files are under `SymplecticGeometry/`.

## Setting and conventions

- **Dimension.** The page's complex dimension $n\ge1$ is `n + 1` in Lean,
  for `n : ℕ`. The model space is `E := Fin (n + 1) → ℂ`, the exceptional
  divisor is `ℙ ℂ (Fin (n + 1) → ℂ)`, which is Tau Ceti's complex manifold
  (`Projectivization.instChartedSpace`, `Projectivization.instIsManifold`,
  model `𝓘(ℂ, Fin n → ℂ)`, `Geometry/Manifold/Instances/Projectivization.lean`),
  and the library's tautological line `Projectivization.Tautological` and
  `tautologicalTwistCoreEquiv` are stated for exactly this space. So
  $n\ge1$ needs no hypothesis, the page's case $n=1$ is `n = 0`, the page's
  "for $n\ge2$" is `1 ≤ n`, and the page's coefficient $n-1$ is `n`.
- **Complex manifolds** are as in `DESIGN.md`: charted on `E` with
  `IsManifold 𝓘(ℂ, E) ω`. Holomorphic maps are `MDifferentiable`, and
  Tau Ceti's `MDifferentiable.contMDiff` (`Geometry/Manifold/Complex/Analytic.lean`)
  makes them `ContMDiff` at every regularity. A biholomorphism is Mathlib's
  `Diffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E') X Y ω`. A complex manifold is a smooth real
  one by Tau Ceti's `IsManifold.restrictScalars_of_ne_zero`, with
  `IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero` for its charts.
- **Holomorphic charts at the centre.** A chart of the blowup is built from
  an `OpenPartialHomeomorph M E` that sends $p_0$ to $0$. The library bundles
  this as a structure (`BlowupChart`, in `Basic.lean`) and states membership
  in a maximal atlas, real or complex, as a hypothesis where it is used.
- **Orientations.** A complex manifold carries Tau Ceti's
  `TauCeti.complexManifoldOrientation`, reindexed by the library's
  `Geometry/Manifold/Complex/Orientation.lean`; $\overline{\mathbb CP}{}^n$
  is `ℙ ℂ (Fin (n + 2) → ℂ)` with its negative, as `DESIGN.md` says.
- **Classes.** $c_1$ is the library's `SymplecticGeometry.Bundle.firstChernClass`
  (`Topology/VectorBundle/Complex/FirstChernClass.lean`) of the complex
  tangent bundle `(J.toContMDiff ⊤).toContinuousComplexStructure.Fiber`, as
  in `design/adjunction.md`; $h$ is `Projectivization.hyperplaneClass`; $e$
  is the class $d_Z$ of *Poincaré duals of submanifolds*, in the coefficient
  ring that `design/poincare-duals.md` fixes. Where that ring is not the one
  of `firstChernClass`, `ExceptionalClass.lean` states $e$ also in the
  latter through that design's comparison, and the Chern class formula uses
  that form.

## Decisions

`DESIGN.md` leaves two questions to this file; the review that wrote the
part into `DESIGN.md` added two about `CanonicalBundle.lean`.

### The projectivized tangent space at the centre

The blowup of `M` at `p₀` along a chart `c : BlowupChart M p₀` is glued
from two pieces with Tau Ceti's gluing of manifolds,
`Geometry/Manifold/Gluing/GlueData.lean`, as the library's
`Geometry/Manifold/Gluing/CapDiscs/` already does:

```
def Blowup.glueData (c : BlowupChart M p₀) : TopCat.GlueData := TopCat.GlueData.mk' …
def Blowup (c : BlowupChart M p₀) : Type := (Blowup.glueData c).toGlueData.glued
```

The index type is `Bool`. The piece `false` is the open set
`{x : M | x ≠ p₀}`, and the piece `true` is the open set
`blowdown ⁻¹' c.target` of `BlowupModel n`. They overlap in
`{x | x ≠ p₀} ∩ c.source` and in `blowdown ⁻¹' (c.target \ {0})`, glued
by $\pi^{-1}\circ\phi$ and its inverse $\phi^{-1}\circ\pi$, which are
`blowdownDiffeomorph n` composed with `c` restricted. `M : Type`, since
the pieces of a `TopCat.GlueData` share one universe and the model is in
`Type`. Each piece and each overlap is an open subset of a manifold charted
on `E` and carries its atlas, so the glued space gets Tau Ceti's
`TopCat.GlueData.chartedSpace`; its charts are those of `M` away from
$p_0$, and the charts `blowupModelChart i ∘ c.lift` of the model, where
`c.lift` is $\tilde\phi$, the inverse of the second canonical map.

The exceptional divisor $Z$ is the image of the zero section of the model
under the second canonical map, so it is Tau Ceti's complex manifold
`ℙ ℂ E` itself, and no manifold structure on `ℙ ℂ (TangentSpace I p₀)` is
needed: Tau Ceti has charts only on `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, and
`TangentSpace` is a def that instance search does not unfold. The point
`ℓ` of $Z$ stands for the line $d\phi(p_0)^{-1}\ell$ of $T_{p_0}M$. The
type depends on `c` so that its instances do; two charts give blowups
related by `Blowup.chartChange` (below), which is the identity off $Z$ and
$\ell\mapsto[d(\phi'\circ\phi^{-1})(0)\ell]$ on $Z$. The page's description
of $Z$ as the lines of $T_{p_0}M$ is the bijection
`Blowup.directionEquiv c : ℙ ℂ (TangentSpace 𝓘(ℂ, E) p₀) ≃ ℙ ℂ E`,
Mathlib's `Projectivization.map` of `mfderiv` of the chart at $p_0$; the
milestone uses it to state the value of $\tilde\phi$ on $Z$ for every chart.

The gluing is compatible, `TopCat.GlueData.IsCompatible`, over `ℂ` at `ω`
when `c` is in the complex maximal atlas of a complex manifold, and over `ℝ`
at `∞` when `c` is in the real maximal atlas of a smooth manifold charted
on `E`: the inclusions of the overlaps are inclusions of open subsets, and
the transitions are the restrictions of `blowdownDiffeomorph n` and of `c`,
which is a local diffeomorphism by its membership in the maximal atlas. So
one construction gives the complex blowup and the smooth blowup that
*Symplectic blowup* needs, and Tau Ceti's API gives the rest:
`IsCompatible.isManifold` the instances, `IsCompatible.partialDiffeomorphι`
and `IsCompatible.isLocalDiffeomorph_ι` the pieces as open submanifolds,
`IsCompatible.contMDiff_iff` and `IsCompatible.isLocalDiffeomorph_iff` the
maps out of the blowup, such as $\pi_M$, `t2Space_iff_forall_nhds` and
`secondCountableTopology` the topology, and
`TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv`
(`Geometry/Manifold/Gluing/Basic.lean`) the uniqueness of the structure.

### The almost complex blowup

For a smooth manifold `M` charted on `E`, with
`J : TauCeti.SmoothAlmostComplexStructure 𝓘(ℝ, E) M` and a chart `c` in the
real maximal atlas that is $J$-holomorphic on its source
(`hJ : ∀ x ∈ c.source, mfderiv … c x ∘L J x = (Complex.I • ·) ∘L mfderiv … c x`),
the structure $\tilde J$ on `Blowup c` is glued from two pieces that agree
on the overlap:

- off $Z$, Tau Ceti's `SmoothAlmostComplexStructure.localPullback`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Descent.lean`) of $J$ along
  $\pi_M$, which is a local diffeomorphism there;
- on the domain of `c.lift`, the pull-back along it of Tau Ceti's
  `SmoothAlmostComplexStructure.ofComplexManifold` of the model
  (`Geometry/Manifold/Complex/AlmostComplexStructure.lean`).

They agree where both are defined because the chart is $J$-holomorphic.
The hypothesis `hJ` says that $J$ is integrable near $p_0$, through a chart
that proves it; it is what *Symplectic blowup*'s normalized charts give
(Definition 7.1.17), and it is the form the Chern class milestone needs.
The file states that $d\pi_M$ is complex linear for $\tilde J$ and $J$ off
$Z$, that the charts `blowupModelChart i ∘ c.lift` are $\tilde J$-holomorphic,
so $\tilde J$ is integrable near $Z$ (the library's
`SmoothAlmostComplexStructure.IsIntegrable`, `Geometry/Manifold/Complex/Integrable.lean`,
on the open set), and that for a complex manifold $\tilde J$ is
`ofComplexManifold` of the complex blowup.

### The line bundle of the divisor and the canonical bundle

Neither library has the line bundle $\mathcal O(D)$ of a smooth complex
hypersurface, nor uses one; both have what it needs. The design builds it
once, in a general file, `Geometry/Manifold/Complex/Hypersurface/LineBundle.lean`,
as a `VectorBundleCore ℂ X ℂ ι` in the pattern of Tau Ceti's
`signedPointTwistCore` (`Geometry/Manifold/VectorBundle/Holomorphic/PointTwist/Basic.lean`):
from a family of local defining functions $f_i$ on an open cover, holomorphic,
with holomorphic, nowhere vanishing transition functions $g_{ij}$ on overlaps,
$f_i = g_{ij} f_j$ and $g_{ij}g_{jk} = g_{ik}$, the coordinate changes of
$\mathcal O(kD)$ are $g_{ji}^k$. It is a holomorphic line bundle in
Mathlib's sense, `ContMDiffVectorBundle ω`, which is the model the
canonical bundle has: Tau Ceti's `TauCeti.CanonicalBundle`
(`Geometry/Manifold/VectorBundle/Cotangent/Canonical.lean`) is Mathlib's
bundle of alternating maps, holomorphic by
`ContMDiffVectorBundle.continuousAlternatingMap`. The pull-back is Mathlib's
`Bundle.Pullback` with `ContMDiffVectorBundle.pullback`, and the tensor
product is Tau Ceti's `ContMDiffVectorBundle.tensorProduct`
(`Geometry/Manifold/VectorBundle/TensorProduct.lean`). Tau Ceti's sheaf
model (`Geometry/Manifold/Complex/StructureSheaf/LineBundle/`) and its
Picard group of bundle cores (`ContMDiffPicardGroup`) are not used: the
statement is an isomorphism of bundles, not of classes.

The defining functions of the blowup's divisor are explicit: the coordinate
`w i` in the chart `blowupModelChart i ∘ c.lift`, and `1` off $Z$. The
restriction of $\mathcal O(D)$ to $D$ and the normal bundle are not
compared: the canonical-bundle identity does not need it, and the normal
bundle of $Z$ is already identified with $L$ in `Tautological.lean`.

## Files

All in `Geometry/Manifold/Complex/Blowup/`, except the general file on
$\mathcal O(D)$. `DESIGN.md` first gave the identification with the
tautological line to `Model.lean`, the lifts of curves to `Basic.lean` and
$\mathcal O(E)$ to `CanonicalBundle.lean`; they are split off here, so that
each issue is a few hundred lines, and `DESIGN.md` is updated to match.

| File | Contents | Issue |
|---|---|---|
| `Blowup/Model.lean` | the incidence set, its charts, projections and exceptional divisor | 1 |
| `Blowup/Tautological.lean` | the model as the total space of $L$, and the normal bundle of $Z$ | 2 |
| `Blowup/Lift.lean` | lifts of biholomorphisms fixing $0$ and of curves through $0$ | 3 |
| `Blowup/Basic.lean` | the blowup of a manifold at a point along a chart | 4 |
| `Blowup/Curve.lean` | lifts of holomorphic curves, and the milestone | 5 |
| `Blowup/AlmostComplex.lean` | the almost complex blowup | 6 |
| `Blowup/SelfIntersection.lean` | $Z\cdot Z=-1$ for complex dimension two | 7 |
| `Blowup/ConnectedSum.lean` | $\widetilde M\cong M\#\overline{\mathbb CP}{}^n$ | 8 |
| `Blowup/ExceptionalClass.lean` | the class $e$ and its restrictions | 9 |
| `Blowup/ChernClass.lean` | $c_1(T\widetilde M)=\pi^*c_1(TM)-(n-1)e$ | 10 |
| `Hypersurface/LineBundle.lean` | the line bundle $\mathcal O(kD)$ of a smooth hypersurface | 11 |
| `Blowup/CanonicalBundle.lean` | $K_{\widetilde M}\cong\pi^*K_M\otimes\mathcal O((n-1)E)$ | 12 |

### `Blowup/Model.lean`

Namespace `SymplecticGeometry`, for `n : ℕ` and `E := Fin (n + 1) → ℂ`.

- `BlowupModel n`, the subtype of `ℙ ℂ E × E` of pairs `(ℓ, z)` with
  `z ∈ ℓ.submodule`, with `mem_blowupModel_iff`. Its topology is the subspace
  topology; it is closed (`isClosed_blowupModel`).
- `BlowupModel.pr` and `BlowupModel.blowdown` ($\mathrm{pr}$ and $\pi$),
  the two projections, with `@[simp]` lemmas on `⟨(ℓ, z), h⟩`.
- `blowupModelChart i : OpenPartialHomeomorph (BlowupModel n) E`, for
  `i : Fin (n + 1)`, on the pairs with `ℓ` in Tau Ceti's `affineOpen i`:
  the value `w` has `w i = z i` and, for `j ≠ i`, `w j = v j / v i` for any
  `v` spanning `ℓ`; the inverse sends `w` to
  `(mk (update w i 1), w i • update w i 1)`. These are the book's charts of
  Exercise 7.1.2 (i), indexed by `Fin (n + 1)` with no reindexing. Lemmas:
  `blowupModelChart_apply`, `blowupModelChart_symm_apply`,
  `blowupModelChart_source`, `blowupModelChart_target` (all of `E`), and the
  blowdown in the chart, `blowdown_blowupModelChart_symm_apply`:
  $z_i=w_i$, $z_j=w_iw_j$.
- The instances `ChartedSpace E (BlowupModel n)`, with `chartAt` the chart
  at the index Tau Ceti's charts of `ℙ ℂ E` use, and
  `IsManifold 𝓘(ℂ, E) r (BlowupModel n)` for every `r : ℕ∞ω`: the transition from chart `i` to
  chart `k` is $w'_k=w_iw_k$, $w'_j=v_j/w_k$ ($v=$`update w i 1`), analytic
  where $w_k\neq0$. `T2Space` and `SecondCountableTopology` from the
  subspace.
- `isMAnalyticSubmanifold_blowupModel`: the set is a complex submanifold
  of the product, Tau Ceti's `TauCeti.IsMAnalyticSubmanifold` of dimension
  `n + 1` (`Geometry/Manifold/AnalyticSubmanifold/Basic.lean`), and
  `contMDiff_blowupModel_val`, with the charts above: the inclusion is
  holomorphic.
- `contMDiff_pr`, `contMDiff_blowdown`.
- `BlowupModel.exceptionalDivisor n`, the set `{p | p.blowdown = 0}`, with
  `exceptionalDivisor_eq_range`: it is the image of `ℓ ↦ (ℓ, 0)`, the map
  `BlowupModel.zeroSection`.
- `blowdownDiffeomorph n`: $\pi$ as a biholomorphism from the complement of
  the divisor onto `{z : E | z ≠ 0}`, both as open subsets, with inverse
  `z ↦ (mk z, z)`; `coe_blowdownDiffeomorph`, `blowdownDiffeomorph_symm_apply`.

### `Blowup/Tautological.lean`

- `blowupModelTotalSpaceDiffeomorph n`, a biholomorphism from the total
  space of Tau Ceti's `(Projectivization.twistCore (-1)).Fiber` over `ℙ ℂ E`
  (model `𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ, ℂ)`) onto `BlowupModel n`, sending
  `⟨ℓ, a⟩` to `(ℓ, (tautologicalTwistCoreEquiv ℓ).symm a)`; in the chart `i`
  of each side it is $(\ell,a)\mapsto$ (affine coordinates of $\ell$, $a$
  at the place `i`), so both directions are analytic. Lemmas: under it
  `pr` is the bundle projection (`pr_blowupModelTotalSpaceDiffeomorph`) and
  the zero section goes to `zeroSection` (`…_zero`).
- `zeroSectionEmbedding n`, `zeroSection` as Tau Ceti's
  `TauCeti.SmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, E) ω`, with range the
  exceptional divisor.
- `normalSpaceZeroSectionEquiv n ℓ`, the complex-linear isomorphism from
  Tau Ceti's `SmoothEmbedding.NormalSpace` of `zeroSectionEmbedding n` at
  `ℓ` onto `Tautological ℂ E ℓ`, induced by the differential of `blowdown`,
  whose kernel at `(ℓ, 0)` is the tangent image of the zero section and whose
  image is `ℓ`; and its continuity on total spaces, in Tau Ceti's local
  normal bundle structure (`normalSpaceFiberBundle`,
  `normalSpaceVectorBundle`, with the defining functions
  `SmoothEmbedding.DefiningFunctions`). This is the page's $\nu_Z\cong L$.
  The real form, for the complex normal structure of
  `design/adjunction.md`'s `contMDiffNormalComplexStructure`, is stated as
  well, since `SelfIntersection.lean` needs it.
- First half of the milestone *Tautological line bundle and the exceptional
  divisor*: the docstrings of `blowupModelTotalSpaceDiffeomorph`,
  `blowdownDiffeomorph` and `normalSpaceZeroSectionEquiv` say which part each
  states; $c_1(L)=-h$ is the merged `complexEulerClass_twistCore_neg_one`
  and is not restated.

### `Blowup/Lift.lean`

Namespace `SymplecticGeometry.BlowupModel`. Exercise 7.1.2 (ii) and (iii),
in coordinates.

- `exists_analytic_mul_self` (in `Analysis/Analytic/`, if neither library
  has it; the issue searches by statement first): an analytic map
  $\psi$ on a ball about $0$ with $\psi(0)=0$ is $\psi(z)=A(z)z$ with $A$
  analytic into `E →L[ℂ] E` and $A(0)=d\psi(0)$, by
  $A(z)=\int_0^1d\psi(tz)\,dt$ (Hadamard's lemma).
- `liftMap ψ`: for $\psi$ holomorphic on an open `U ∋ 0` with
  $\psi(0)=0$ and $d\psi(0)$ invertible, the map on
  `blowdown ⁻¹' U` that is `(mk (ψ z), ψ z)` off $Z$ and
  `(map (dψ 0) ℓ, 0)` on $Z$. In the chart `i` it is
  $(w)\mapsto([A(z)v],\psi(z))$ with $z=w_iv$, which is analytic at
  $w_i=0$ as well; so `contMDiffOn_liftMap`. `blowdown_liftMap`:
  $\pi\circ\tilde\psi=\psi\circ\pi$, and `liftMap_zeroSection`.
- `liftPartialDiffeomorph ψ`: for $\psi$ an analytic `OpenPartialHomeomorph`
  of `E` with analytic inverse, fixing $0$, the lift is a biholomorphism of
  `blowdown ⁻¹' ψ.source` onto `blowdown ⁻¹' ψ.target`, with inverse the lift
  of $\psi^{-1}$, by the chain rule at $0$ and uniqueness;
  `eqOn_liftMap_of_blowdown_comp`: a continuous map with
  $\pi\circ\tilde\psi=\psi\circ\pi$ equals the lift, since both agree on the
  dense complement of $Z$ and the model is Hausdorff.
- `curveLift u`: for $u$ analytic from an open set of `ℂ` to `E`, with an
  isolated zero at `t₀` of order $k$ (Mathlib's `analyticOrderAt`, with
  `AnalyticAt.analyticOrderAt_eq_natCast`, so $u(t)=(t-t_0)^kg(t)$ with
  $g(t_0)\ne0$), the lift `(mk (g t), u t)` near `t₀`;
  `analyticAt_curveLift`, `blowdown_curveLift`, and `curveLift_apply_self`:
  its value at `t₀` is the line of the first nonvanishing derivative of
  $u$, `iteratedDeriv k u t₀` (`analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`).

### `Blowup/Basic.lean`

Namespace `SymplecticGeometry`, for `M : Type` with `[TopologicalSpace M]
[ChartedSpace E M]` and `p₀ : M`.

- `BlowupChart M p₀`, a structure: an `OpenPartialHomeomorph M E`
  (`toOpenPartialHomeomorph`, with a coercion) with `mem_source : p₀ ∈ source`
  and `map_center : toOpenPartialHomeomorph p₀ = 0`; `@[ext]`.
- `Blowup.glueData c` and `Blowup c` as in *Decisions*, with
  `glueData_U_false`, `glueData_U_true`, `glueData_V` and `glueData_t_apply`
  for its pieces, overlaps and transitions; the canonical maps
  `Blowup.inl c : {x : M // x ≠ p₀} → Blowup c` and
  `Blowup.inr c : blowdown ⁻¹' c.target → Blowup c`, with `range_inl`,
  `range_inr`, `inl_eq_inr_iff` (through `TopCat.GlueData.ι_eq_iff_rel`)
  and `range_inl_union_range_inr`; `Blowup.divisor c ℓ`, `inr` of
  `zeroSection ℓ`, and `Blowup.exceptionalDivisor c`, its range, with
  `mem_exceptionalDivisor_iff`.
- `Blowup.lift c : Blowup c → BlowupModel n` ($\tilde\phi$), the inverse
  of `inr` on its range followed by the inclusion, with `lift_inr`, and
  `lift_inl`: for `x ∈ c.source` it is `(mk (c x), c x)`.
- The topology and the atlas are the glued ones, `TopCat.GlueData.chartedSpace`
  as an instance `ChartedSpace E (Blowup c)`; `isOpen_range_inl`,
  `isClosed_exceptionalDivisor`, `isOpenEmbedding_inl`, `isOpenEmbedding_inr`
  (Mathlib's `TopCat.GlueData.ι_isOpenEmbedding`). `SecondCountableTopology`
  when `M` has it, by Tau Ceti's `TopCat.GlueData.secondCountableTopology`,
  and `T2Space` when `M` has it, by `TopCat.GlueData.t2Space_iff_forall_nhds`:
  a point `x` of the first piece outside `c.source` and a point of $Z$ have
  neighbourhoods `A` and `blowdown ⁻¹' c '' B` with `B` a neighbourhood of
  $p_0$ whose closure misses `A`.
- `Blowup.isCompatible_complex` and `Blowup.isCompatible_real`: with
  `c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M`, resp.
  the real atlas at `∞`, the gluing is `TopCat.GlueData.IsCompatible` over
  `𝓘(ℂ, E)` at `ω`, resp. `𝓘(ℝ, E)` at `∞`, by `blowdownDiffeomorph n` and
  the chart. The instances `IsManifold 𝓘(ℂ, E) ω (Blowup c)` and
  `IsManifold 𝓘(ℝ, E) ∞ (Blowup c)`, under the corresponding
  `[Fact (c.toOpenPartialHomeomorph ∈ …)]`, are `IsCompatible.isManifold`;
  `isLocalDiffeomorph_inl` and `isLocalDiffeomorph_inr` are
  `IsCompatible.isLocalDiffeomorph_ι`.
- `Blowup.blowdown c` ($\pi_M$), Tau Ceti's
  `TopCat.GlueData.IsCompatible.descContMDiffMap` of the inclusion on the
  first piece and `c.symm ∘ BlowupModel.blowdown` on the second, with the
  `@[simp]` lemmas `blowdown_inl`, `blowdown_inr`, and `contMDiff_blowdown`;
  `blowdownDiffeomorph c`: a biholomorphism (resp. diffeomorphism) from the
  complement of $Z$, the range of `inl`, onto `{x | x ≠ p₀}`, as open
  subsets, the inverse of `IsCompatible.partialDiffeomorphι` of the first
  piece.
- `Blowup.divisorEmbedding c`, `Blowup.divisor c` as a `TauCeti.SmoothEmbedding
  𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, E) ω (ℙ ℂ E) (Blowup c)` ($\tilde\iota$), `inr`
  composed with the model's `zeroSectionEmbedding n`, and the real one.
- `Blowup.liftChart c φ`: for any `φ : BlowupChart M p₀` in the same maximal
  atlas, $\tilde\phi$ of `φ` on `Blowup c`, `liftMap` of
  `φ ∘ c.symm` composed with `c.lift`; `liftChart_inl`, and `liftChart_inr`:
  on `ℓ` it is `(map (d(φ ∘ c⁻¹)(0)) ℓ, 0)`, which under
  `directionEquiv` is the page's $([d\phi(p_0)v],0)$.
  `liftChart_mem_maximalAtlas`: it is a holomorphic chart, a biholomorphism
  from `blowdown ⁻¹' φ.source` onto the open set `blowdown ⁻¹' φ.target` of
  the model, by `liftPartialDiffeomorph` and
  `IsCompatible.isLocalDiffeomorph_iff`.
- `Blowup.chartChange c c'`, the biholomorphism `Blowup c ≃ Blowup c'` for
  two charts of the same atlas: `descContMDiffMap` of `inl c'` on the first
  piece and, on the second, of `inr c'` of `liftMap` of `c' ∘ c.symm` over
  the source of `c' ∘ c.symm` and `inl c'` of `c.symm ∘ blowdown` off $Z$,
  which agree where both are defined. It is a local biholomorphism by
  `IsCompatible.isLocalDiffeomorph_iff` and `liftPartialDiffeomorph`, and
  bijective with inverse the same map for `c'` and `c`, so a biholomorphism
  by Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`. Tau Ceti's
  `IsCompatible.gluedDiffeomorph` does not apply, since the lift is defined
  only over the source of `c' ∘ c.symm` and not on the whole second piece.
  `chartChange_inl`, `chartChange_inr`, `blowdown_chartChange`.
- `Blowup.exists_diffeomorph_coe_eq_of_blowdown` (uniqueness): if `X` is a complex
  manifold and `e : X ≃ Blowup c` is a bijection such that `blowdown ∘ e`
  is holomorphic and biholomorphic off `e ⁻¹' Z`, and
  `c.lift ∘ e` is a biholomorphism onto its image near `e ⁻¹' Z`, then `e`
  is a biholomorphism. The hypotheses say that `e.symm ∘ inl` and
  `e.symm ∘ inr` are local biholomorphisms, so `e` is Tau Ceti's
  `TauCeti.diffeomorphOfForallIsLocalDiffeomorphEquiv`. This is the page's
  uniqueness of the structure, stated on structures carried by another type,
  so that no two instances meet on one type.

### `Blowup/Curve.lean`

For a connected Riemann surface `Σ` (`[ChartedSpace ℂ Σ]
[IsManifold 𝓘(ℂ) ω Σ] [ConnectedSpace Σ] [T2Space Σ]`) and `[T2Space M]`.

- `MDifferentiable.isClosed_discrete_preimage` (in a general file of
  `Geometry/Manifold/Complex/`, unless either library has it): the preimage
  of a point under a nonconstant holomorphic map from a connected Riemann
  surface is discrete, from Mathlib's
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` in charts and
  connectedness.
- `Blowup.curveLift c u hu`: the lift of a nonconstant holomorphic
  `u : Σ → M`, equal to `inl ∘ u` off `u ⁻¹' {p₀}` and to `BlowupModel.curveLift`
  read through `c.lift` near each point of it; `mdifferentiable_curveLift`,
  `blowdown_curveLift`, and `curveLift_unique`, by density of the
  complement of the discrete set and the Hausdorff property.
- **Milestone** `Blowup.complexBlowup`, for a complex manifold `M`, `p₀` and
  `c` in the complex atlas: the conjunction of `contMDiff_blowdown`,
  `blowdownDiffeomorph`, the charts (for every holomorphic chart `φ` with
  `φ p₀ = 0`, `liftChart c φ` is in the maximal atlas of `Blowup c`, with
  target `blowdown ⁻¹' φ.target` in the model, and value
  `(map (mfderiv φ p₀) v, 0)` at `(directionEquiv c).symm`-images), that
  `divisorEmbedding` is a holomorphic embedding, and the existence and
  uniqueness of lifts of nonconstant curves; and the uniqueness of the
  structure as `exists_diffeomorph_coe_eq_of_blowdown`, which the docstring names. Its
  docstring ends with the line Milestone: *Complex blowup at a point*.

### `Blowup/AlmostComplex.lean`

For `M` charted on `E` with `IsManifold 𝓘(ℝ, E) ∞ M`, `J`, `c` in the real
atlas and `hJ` as in *Decisions*.

- `Blowup.almostComplexStructure c J hJ : SmoothAlmostComplexStructure
  𝓘(ℝ, E) (Blowup c)`, glued as in *Decisions*, with
  `almostComplexStructure_apply_inl` (through `localPullback_apply`) and
  `almostComplexStructure_lift` (on the domain of `c.lift`);
  `mfderiv_blowdown_comp_almostComplexStructure`: $d\pi_M\tilde J=J\,d\pi_M$
  off $Z$; `isIntegrable_on`: the charts `blowupModelChart i ∘ c.lift` are
  $\tilde J$-holomorphic; and
  `almostComplexStructure_eq_ofComplexManifold` for a complex `M`.

### `Blowup/SelfIntersection.lean`

For `n = 1` (the page's complex dimension two).

- `selfIntersectionNumber_zeroSection`: the exceptional divisor of
  `BlowupModel 1` has self-intersection $-1$, *Adjunction*'s
  `TauCeti.SmoothEmbedding.selfIntersectionNumber` of `zeroSectionEmbedding 1`,
  re-modelled on `𝓡 2` with the library's `Remodel`
  (`Geometry/Manifold/ModelTransport/Remodel.lean`), for
  `ofComplexManifold` and the complex orientation of `ℙ ℂ (Fin 2 → ℂ)`.
  Proof: `selfIntersectionNumber_eq_chernNumber`, the real form of
  `normalSpaceZeroSectionEquiv`, invariance of the Euler class under
  isomorphism, `complexEulerClass_twistCore_neg_one`, and the value $1$ of
  $h$ on the fundamental class of $\mathbb CP^1$ (as in the merged
  `evalFundamentalClass_hyperplaneClass_pow`, `Projectivization/Hypersurface/Degree.lean`,
  or directly).
- `Blowup.selfIntersectionNumber_exceptionalDivisor`: the same for the
  blowup of a complex surface, through `c.lift`, which is a biholomorphism
  near $Z$.
- With `Tautological.lean`, this completes the milestone *Tautological line
  bundle and the exceptional divisor*; the docstring of
  `selfIntersectionNumber_zeroSection` ends with its milestone line.

### `Blowup/ConnectedSum.lean`

For a connected complex manifold `M`, re-modelled on the real inner product
space `EuclideanSpace ℂ (Fin (n + 1))` with `Remodel` (Tau Ceti's
`TauCeti.ConnectedSum` needs `[InnerProductSpace ℝ E]`, which `Fin (n + 1) → ℂ`
is not), with its complex orientation carried along.

- `projectiveBlowupModelDiffeomorph n`: the diffeomorphism from
  `ℙ ℂ (Fin (n + 2) → ℂ)` minus the point $[0:\dots:0:1]$ onto
  `BlowupModel n`, $[z:w]\mapsto([z],\bar w z/\lvert z\rvert^2)$. It is the
  identification of the complement with the total space of $L^*=\mathcal O(1)$,
  followed by the conjugate-linear isomorphism $L^*\cong L$ of the
  Hermitian metric; so it reverses the complex orientations
  (`isOrientationReversing_projectiveBlowupModelDiffeomorph`), and it sends
  $[u:1]$ to $([u],u/\lvert u\rvert^2)$, the inversion.
- `Blowup.connectedSumDiffeomorph c`: the diffeomorphism from Tau Ceti's
  `TauCeti.ConnectedSum e₁ e₂` onto `Blowup c`, for
  `e₁ v = c.symm (ρ v)`, with $\rho(v)=\varepsilon v/\sqrt{1+\lvert v\rvert^2}$
  and $\varepsilon$ such that the closed ball of radius $\varepsilon$ is in
  `c.target`, and `e₂ u = [u : 1]`. It is the identity on $M\setminus p_0$,
  and $\tilde\phi^{-1}\circ S\circ$`projectiveBlowupModelDiffeomorph` on the
  other side, with $S(\ell,z)=(\ell,\varepsilon z/\sqrt{1+\lvert z\rvert^2})$;
  the two agree on the glued annuli because `e₁ v` is glued to
  `e₂ (inversion 0 1 v)`. Both sides are re-modelled on
  `EuclideanSpace ℂ (Fin (n + 1))`. `e₁` preserves the orientation of `M`,
  and `e₂`, being holomorphic, reverses that of $\overline{\mathbb CP}{}^n$,
  as Tau Ceti's `nonempty_diffeomorph_of_isOrientationReversingAt` asks.
- **Milestone, second statement** `Blowup.nonempty_orientationPreserving_diffeomorph_connectedSum`:
  `Blowup c`, re-modelled likewise, is diffeomorphic to
  `TauCeti.OrientedConnectedSum` of `M` and
  $\overline{\mathbb CP}{}^n$ by an orientation-preserving diffeomorphism,
  composing `connectedSumDiffeomorph` with *Connected sums*' orientation
  preserving independence (`ConnectedSum/OrientationPreserving.lean`).
  Hypotheses: `M` connected, Hausdorff, second countable, as Tau Ceti's
  connected sum needs.

### `Blowup/ExceptionalClass.lean`

For `M` smooth, charted on `E`, and `c` in the real atlas, so that the
statements serve `ChernClass.lean` and *Symplectic blowup*; a complex `M`
is a case of it by `maximalAtlas_subset_restrictScalars_of_ne_zero`.

- `Blowup.exceptionalClass c`, the class $e$: *Poincaré duals of
  submanifolds*' $d_Z$ of the real `divisorEmbedding c`, with the normal
  bundle oriented by the complex structure that `c.lift` carries from the
  model, which `normalSpaceZeroSectionEquiv` makes that of $L$;
  `exceptionalClass_def`.
- `exceptionalClass_restrict_compl`: its restriction to the complement of
  $Z$ vanishes (that file's vanishing off $Z$), and
  `exceptionalClass_pairing_compl`: in the page's form, its pairing with every
  class of $H_2(\widetilde M\setminus Z;\mathbb Z)$ is zero.
- `exceptionalClass_restrict_divisor`: for `1 ≤ n`, $\tilde\iota^*e=-h$, from
  the restriction of $d_Z$ to the Euler class of the normal bundle,
  `normalSpaceZeroSectionEquiv` through `c.lift`, and
  `complexEulerClass_twistCore_neg_one`.
- **Milestone, third statement**: the docstring of
  `exceptionalClass_restrict_divisor` ends with the line Milestone: *Blowup
  as a connected sum with the reversed projective space*, and names
  `nonempty_orientationPreserving_diffeomorph_connectedSum` and
  *Connected sums*' theorem for the other two statements.

### `Blowup/ChernClass.lean`

For `M`, `J`, `c`, `hJ` as in `AlmostComplex.lean`, with `M` Hausdorff and
second countable.

- **Milestone** `Blowup.firstChernClass_tangent`:
  $c_1(T\widetilde M,\tilde J)=\pi_M^*c_1(TM,J)-n\,e$ (the page's $n-1$ is
  Lean's `n`), with `c₁` as in *Setting and conventions*. Its docstring ends
  with the line Milestone: *First Chern class of a blowup at a point*, and
  names `canonicalBundleEquiv` for the holomorphic identity. Proof, the
  page's three steps:
  1. off $Z$, $d\pi_M$ is a complex isomorphism of $T\widetilde M$ with
     $\pi_M^*TM$ (`mfderiv_blowdown_comp_almostComplexStructure`), so the
     difference restricts to zero there, by `firstChernClass_pullback`;
  2. the long exact sequence of the pair lifts it to
     $H^2(\widetilde M,\widetilde M\setminus Z)$, which the Thom isomorphism
     of *Poincaré duals of submanifolds* identifies with $H^0(Z)\cong\mathbb Z$
     ($Z$ connected), generated by the class whose image is $e$; so it is
     $k\,e$;
  3. on a line of $Z$ (`1 ≤ n`): $T\widetilde M|_Z\cong TZ\oplus\nu_Z$, with
     $c_1(T\mathbb CP^n)=(n+1)h$ and $c_1(\nu_Z)=-h$, by the Whitney formula
     of the *Chern classes* extension; $\pi_M^*c_1$ restricts to zero on
     $Z$; and $\langle e,\ell\rangle=-1$ by `exceptionalClass_restrict_divisor`.
     So $n=-k$.
  For `n = 0`, $Z$ is a point and $\pi_M$ is a diffeomorphism carrying
  $\tilde J$ to $J$, so the formula is naturality.

### `Hypersurface/LineBundle.lean`

`Geometry/Manifold/Complex/Hypersurface/LineBundle.lean`, namespace
`SymplecticGeometry`, for a complex manifold `X` with model `I : ModelWithCorners ℂ F H`.

- `HypersurfaceData I X ι`, a structure: open sets `U i` covering `X`,
  holomorphic `f i : X → ℂ` on them, and holomorphic, nowhere zero `g i j`
  on $U_i\cap U_j$ with $f_i=g_{ij}f_j$ there and $g_{ij}g_{jk}=g_{ik}$; its divisor
  `D.support`, with `mem_support_iff`. A predicate on a set alone is not
  defined: the data is what the line bundle needs, and the blowup gives it.
- `D.lineBundleCore k : VectorBundleCore ℂ X ℂ ι`, for `k : ℤ`, with
  coordinate changes $g_{ji}^k$ on overlaps (in the pattern of Tau
  Ceti's `signedPointTwistCore`); `lineBundleCore_coordChange`, the
  instance `ContMDiffVectorBundle ω`, and `D.canonicalSection`, the
  holomorphic section of $\mathcal O(D)$ given by $f_i$ in chart $i$, which
  vanishes exactly on the support; whether it vanishes to first order does
  not depend on the chart (`mfderiv_f_eq_zero_iff`).
- `D.lineBundleCoreTensorEquiv k l`: $\mathcal O((k+l)D)\cong
  \mathcal O(kD)\otimes\mathcal O(lD)$, as for the library's
  `twistCoreTensorEquiv`.

### `Blowup/CanonicalBundle.lean`

For a complex manifold `M` and `c` in the complex atlas.

- `Blowup.hypersurfaceData c : HypersurfaceData 𝓘(ℂ, E) (Blowup c) (Option (Fin (n + 1)))`:
  the coordinate `w i` on the domain of `blowupModelChart i ∘ c.lift`, and
  `1` off $Z$; its support is the exceptional divisor.
- `coordForm_blowdown`: in the chart `i`, the pull-back by $\pi$ of the
  coordinate form $dz_1\wedge\dots\wedge dz_{n+1}$ is $w_i^{\,n}$ times the
  coordinate form of the chart, by the Jacobian of
  $(w)\mapsto(w_iw_j, w_i)$, with Tau Ceti's
  `TauCeti.CanonicalBundle.coordForm` and its change of charts.
- `Blowup.canonicalBundleEquiv c`: a fibrewise complex-linear isomorphism
  from `TauCeti.CanonicalBundle 𝓘(ℂ, E) (Blowup c)` to the tensor product of
  the pull-back along $\pi_M$ of `TauCeti.CanonicalBundle 𝓘(ℂ, E) M` with
  `(hypersurfaceData c).lineBundleCore n`, holomorphic on total spaces in
  both directions. In chart $i$, where $w_i^{-n}$ is the frame of
  $\mathcal O(nE)$, its inverse sends $\sigma\otimes w_i^{-n}$ to
  $w_i^{-n}\pi^*\sigma$; by `coordForm_blowdown` this takes the frame
  $dz_1\wedge\dots\wedge dz_{n+1}\otimes w_i^{-n}$ to the coordinate form
  of the chart, so it is holomorphic and invertible. For `n = 0` it is
  $K_{\widetilde M}\cong\pi^*K_M$. Its docstring says that this is the
  page's canonical-bundle identity, part of the milestone
  *First Chern class of a blowup at a point*.

## What the part uses

- Tau Ceti: projective space as a complex manifold
  (`Geometry/Manifold/Instances/Projectivization.lean`, `affineOpen`,
  `affineChart`), `Projectivization.twistCore`, analytic submanifolds
  (`IsMAnalyticSubmanifold`), the gluing of manifolds
  (`Geometry/Manifold/Gluing/`: `GlueData.lean`, `Map.lean`, `Basic.lean`;
  `Topology/Category/TopCat/GlueData.lean`), smooth embeddings and their normal bundles
  (`SmoothEmbedding`, `NormalSpace`, `DefiningFunctions`), the complex
  regularity lemmas (`Geometry/Manifold/Complex/Analytic.lean`), almost
  complex structures (`localPullback`, `ofComplexManifold`), orientations
  of complex manifolds, `TauCeti.ConnectedSum` and
  `TauCeti.OrientedConnectedSum`, the canonical bundle with `coordForm`,
  tensor products of bundles, and `signedPointTwistCore` as a pattern.
- Mathlib: `TopCat.GlueData`, `Projectivization.map`, `analyticOrderAt`,
  the identity theorem, `Bundle.Pullback`.
- The library: `Projectivization.Tautological` and
  `tautologicalTwistCoreEquiv`, `complexEulerClass_twistCore_neg_one`,
  `Projectivization.hyperplaneClass`, `firstChernClass` with
  `firstChernClass_pullback`, *Adjunction*'s `selfIntersectionNumber`,
  `Remodel`, `IsIntegrable`, and the complex orientation of
  `Geometry/Manifold/Complex/Orientation.lean`.
- Other parts, not yet merged: *Connected sums* (#3274, the orientation
  preserving independence), *Poincaré duals of submanifolds* (#3279, $d_Z$,
  its restrictions and the Thom isomorphism), the *Chern classes* extension
  (#3277, the Whitney formula over a manifold and $c_1(T\mathbb CP^n)$).

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #3281, *Build the part Complex blowup*. Where an issue waits
for another part, it waits for the building issue of that part's design
that adds the file named, once that design is merged; until then, for the
part's building issue given here. Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | The model blowup of $\mathbb C^n$ | `Blowup/Model.lean` | — | 450 |
| 2 | The model as the tautological line; the normal bundle of $Z$ | `Blowup/Tautological.lean` | 1 | 350 |
| 3 | Lifts of biholomorphisms and curves in the model | `Blowup/Lift.lean` | 1 | 400 |
| 4 | The blowup of a manifold at a point | `Blowup/Basic.lean` | 1, 3 | 700 |
| 5 | Lifts of holomorphic curves; *Complex blowup at a point* | `Blowup/Curve.lean` | 4 | 300 |
| 6 | The almost complex blowup | `Blowup/AlmostComplex.lean` | 4 | 300 |
| 7 | The self-intersection of the exceptional divisor | `Blowup/SelfIntersection.lean` | 2, 4 | 250 |
| 8 | The blowup as a connected sum | `Blowup/ConnectedSum.lean` | 4; #3274 | 500 |
| 9 | The exceptional class | `Blowup/ExceptionalClass.lean` | 2, 4, 8; #3279 | 250 |
| 10 | The first Chern class of the blowup | `Blowup/ChernClass.lean` | 6, 9; #3277, #3279 | 400 |
| 11 | The line bundle of a smooth hypersurface | `Hypersurface/LineBundle.lean` | — | 350 |
| 12 | The canonical bundle of the blowup | `Blowup/CanonicalBundle.lean` | 4, 11 | 400 |

Issues 1 and 11 can start once this design is merged. Issue 9 waits for 8
only for its milestone docstring, which names the second statement.
*Symplectic blowup* needs issues 1 (`Model.lean`), 4 and 6 (the chart
$\psi_0$ and the almost complex blowup), 9 and 10.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §§1 and 4.
* [C. Schnell, lecture notes on complex manifolds][Schnell2024], Lemma 23.5.
