# Integration over the fibre

This is the detailed design of part 51 of `DESIGN.md`, *Integration over the
fibre*. The part has no milestone. It builds the operator
$\int_F\colon\Omega^{r+m}(M)\to\Omega^r(B)$ of an oriented fibration
$\pi\colon M\to B$ with closed fibre $F$ of dimension $m$, which
`atlas/symplectic-fibrations.md` uses, in the normalization of the coupling
form, without defining it, and for which it cites Bott–Tu [BottTu1982],
§6. *Coupling forms* is its only user on the page.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. Manifolds
follow *Manifolds, families and signs* of `DESIGN.md`, and fibrations
*Fibrations, connections and diffeomorphism groups*: the base is `B` over
`I : ModelWithCorners ℝ E H`, the fibre `F` over `J : ModelWithCorners ℝ E' H'`,
the total space `M` over `IM : ModelWithCorners ℝ EM HM`, all models
finite-dimensional and boundaryless, all manifolds `IsManifold _ ∞ _`,
Hausdorff and σ-compact. The fibre is closed: `[CompactSpace F]
[BoundarylessManifold J F]`, oriented by `o : Manifold.Orientation J F (Fin m)`.
Forms are Tau Ceti's `SmoothForm _ _ ℝ k`; a form of degree $j\ge m$ is
written with degree `r + m`, so that no subtraction of degrees occurs.

## What exists, and what the part adds

Tau Ceti has everything the integral of one top form needs, and nothing on
fibre integrals (the page's Lean status says the same, and a search of Tau
Ceti, Mathlib and the library for `fiberIntegral`, `fibreIntegral` and
integrals of forms over the factor of a product finds only
`TestFunction.fiberIntegralCLM`, which pushes test functions forward
along a submersion between open subsets of normed spaces and does not apply
to forms on manifolds):

- `TauCeti.integralTopForm o φ` (`Geometry/Manifold/DifferentialForm/Integration/TopForm.lean`),
  linear on integrable forms (`integralTopForm_add_of_integrable`,
  `integralTopForm_smul`), with continuous compactly supported forms
  integrable (`Integration/Regularity.lean`);
- change of variables along an orientation-preserving open embedding,
  `Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`
  (`Integration/ChangeOfVariables.lean`), and the subgroup
  `Diffeomorph.orientationPreservingSubgroup` (`Geometry/Manifold/Orientation/Preserving.lean`);
- Stokes's theorem on a boundaryless manifold,
  `TauCeti.integralTopForm_mextDeriv_eq_zero` (`Integration/BoundarylessStokes.lean`);
- the Riemannian volume form of an orientation, `TauCeti.riemannianVolumeForm`,
  with `TauCeti.integralTopForm_smul_riemannianVolumeForm`
  ($\int f\,\mathrm{vol}=\int f\,d\mathrm{vol}_g$,
  `Geometry/Manifold/Riemannian/VolumeForm/Measure.lean`) and
  `TauCeti.nonempty_contMDiffRiemannianMetric`;
- smooth parametric integrals over a compact manifold,
  `ContMDiff.parametric_integral`, and differentiation and exterior
  differentiation under the integral sign, `TauCeti.hasFDerivAt_integral_of_contMDiffOn`,
  `TauCeti.extDeriv_integral_of_contMDiffOn`
  (`Geometry/Manifold/ContMDiff/ParametricIntegral.lean`);
- slices of a form on a product and their joint smoothness,
  `TauCeti.contMDiff_mpullback_prodMk_form` (`DifferentialForm/Pullback/Family.lean`),
  coordinate expressions on product frames,
  `TauCeti.RoughForm.inChartAt_prod_apply_append` (`DifferentialForm/Chart.lean`);
- forms on open subsets, restriction and locality of smoothness and of $d$
  (`DifferentialForm/Opens.lean`), pull-back, wedge and $d$ on smooth forms
  (`SmoothForm.mpullback`, `SmoothForm.wedge`, `TauCeti.mextDerivₗ`), and
  degree casts by `LinearEquiv.cast`, as in
  `TauCeti.integralTopForm_cast_mextDerivₗ_wedge`.

From Mathlib the part uses `AlternatingMap.map_linearDependent` and
`Fin.append`. From part 48, *Symplectic fibrations*, it uses only
`Geometry/Manifold/FiberBundle/MapFiber.lean` and
`Geometry/Manifold/FiberBundle/StructureGroup.lean`: Tau Ceti's atlas
`A : TauCeti.MapFiber.Atlas F π`, whose chart `A.trivAt b` at each `b` has
`b` in its base set, smooth atlases `A.IsContMDiff ∞ I J IM` (charts smooth
with smooth inverses), and oriented atlases,
`A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup o)`. The
statements below write these as `e ∈ A` (`e` is some `A.trivAt b'`),
`b ∈ e.baseSet` and `A.IsOriented o`, the last standing for both
`A.IsContMDiff ∞ I J IM` and
`A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup o)`, since
the structure group constrains only the coordinate changes and not the
charts themselves; the building issues use the names that
`design/symplectic-fibrations.md` and those two files give them.

## Decisions

- **Closed fibre.** The fibre is compact and boundaryless; compactly
  supported or vertically compactly supported forms are not treated. The
  page uses the operator only for compact total spaces, every smooth form on
  a compact fibre is integrable, and Stokes's theorem then holds with no
  support condition. A later page that needs vertical compact supports
  (Thom forms) generalizes the product file.
- **Sign: base vectors first.** The value of $\int_F\alpha$ at $b$ on
  $v_1,\dots,v_r$ is the integral over $F_b$ of
  $\alpha(\tilde v_1,\dots,\tilde v_r,\cdot)$ restricted to the fibre, for lifts
  $\tilde v_i$ of the $v_i$. This is Bott–Tu's convention, which integrates the
  fibre coordinates written to the right ([BottTu1982], §6): with it the
  projection formula is $\int_F(\pi^*\beta\wedge\alpha)=\beta\wedge\int_F\alpha$
  and $d\int_F=\int_F d$, both with no sign. The page writes only
  $\int_F\tau^{k+1}=0$ and its fibrewise form, which hold in every
  convention, so no `ERRATA.md` entry is needed.
- **The value does not depend on the lifts.** Two lifts differ by vertical
  vectors, and an alternating form of degree $r+m$ vanishes on $m+1$ vectors
  of the $m$-dimensional vertical space, so every term of the difference is
  zero. This is linear algebra (`AlternatingMap.map_append_add_of_mem`
  below). It makes the operator independent of the chart, and gives the
  fibrewise formula with horizontal lifts that *Coupling forms* needs for the
  equivalence of its normalization with mean value zero of
  $\tau_\Gamma(v_1^\sharp,v_2^\sharp)$.
- **Product first, then gluing.** The operator is first built on a product
  $B\times F$ (`prodFiberIntegral`), where the lifts are $(v,0)$, and all its
  calculus is proved there. On a fibration it is defined pointwise through
  the chart of the atlas at $b$, and every property is reduced to the product
  by pulling back along $\Psi_e(b,y)=e^{-1}(b,y)$ on $e.\mathrm{baseSet}\times F$.
  No partition of unity is needed: the integrand at $b$ only involves the
  fibre over $b$.
- **Smoothness through a volume form.** Fix a smooth Riemannian metric on
  $F$ and its volume form $\nu$ for `o`. The integrand at $(b,v)$ is
  $c(b,v,\cdot)\,\nu$ with $c$ jointly smooth, and its integral is
  $\int_F c(b,v,y)\,d\mathrm{vol}(y)$, which `ContMDiff.parametric_integral`
  makes smooth in $b$, read in a local frame of $TB$. The coefficient lemma
  (a continuous top form is its ratio to a nowhere vanishing top form times
  that form, smooth when both are) is about Tau Ceti types and goes in the
  `TauCeti` namespace, in the product file unless it is used elsewhere.
- **No new predicate.** The part adds definitions of operators only; the
  oriented-atlas hypothesis is part 48's.

## Files

### `Geometry/Manifold/DifferentialForm/FiberIntegral/Product/Basic.lean`

The fibre integral on `B × F`.

- `AlternatingMap.map_append_add_of_mem`, in
  `LinearAlgebra/Alternating/Basic.lean`: for a ring `K` with
  `[IsDomain K] [StrongRankCondition K]`, `[Module.IsTorsionFree K N]`,
  `f : W [⋀^Fin (r + m)]→ₗ[K] N`, a finite submodule `V` of `W`
  (`[Module.Finite K V]`) with `finrank K V ≤ m`, and `u : Fin r → W`, `w : Fin m → W` with all `u i` and
  `w j` in `V`, `f (Fin.append (v + u) w) = f (Fin.append v w)`. (Each term of
  the multilinear expansion with some `u i` has $m+1$ vectors in `V`, so
  `AlternatingMap.map_linearDependent` applies.) A
  `ContinuousAlternatingMap` corollary of the same name in its namespace, in
  `Topology/Algebra/Module/Alternating/Basic.lean`.
- `prodFiberIntegrand α b v : RoughForm J F ℝ m`, for
  `α : RoughForm (I.prod J) (B × F) ℝ (r + m)`, `b : B`,
  `v : Fin r → TangentSpace I b`: at `y` the alternating map
  `w ↦ α (b, y) (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)))`, the tangent
  vectors of the product read through `Manifold.tangentSpaceProdEquiv` as in
  `TauCeti.RoughForm.inChartAt_prod_apply_append`; `prodFiberIntegrand_apply`
  (`@[simp]`), linearity in `α`, multilinearity and alternation in `v`, and
  `isSmoothForm_prodFiberIntegrand` for smooth `α`. For `r = 0` it is the
  slice `mpullback J (I.prod J) (Prod.mk b) α` (`prodFiberIntegrand_degree_zero`,
  through the degree cast `0 + m = m`).
- `prodFiberIntegral o : SmoothForm (I.prod J) (B × F) ℝ (r + m) →ₗ[ℝ] SmoothForm I B ℝ r`,
  with `prodFiberIntegral_apply`:
  `(prodFiberIntegral o α).val b v = integralTopForm o (prodFiberIntegrand α.val b v)`.
  The value at `b` is a continuous alternating map because integration is
  linear on smooth forms of the compact `F` and `TangentSpace I b` is
  finite-dimensional; smoothness in `b` by the volume-form decision.
- `prodFiberIntegral_degree_zero_apply` (the integral over each fibre, `r = 0`):
  `(prodFiberIntegral o α).val b ![] = integralTopForm o (mpullback J (I.prod J) (Prod.mk b) (cast α).val)`.

Uses: Tau Ceti's `integralTopForm` and its linearity, `riemannianVolumeForm`,
`nonempty_contMDiffRiemannianMetric`, `ContMDiff.parametric_integral`,
`contMDiff_mpullback_prodMk_form`. About 400 lines.

### `Geometry/Manifold/DifferentialForm/FiberIntegral/Product/Naturality.lean`

How `prodFiberIntegral` meets pull-backs, products with base forms and
fibrewise diffeomorphisms.

- `prodFiberIntegral_mpullback_prodMap`: for smooth `f : B' → B`,
  `prodFiberIntegral o (mpullback (Prod.map f id) α) = mpullback f (prodFiberIntegral o α)`.
  With `f` the inclusion of an open subset this is restriction to an open
  subset of the base.
- `prodFiberIntegral_wedge_mpullback_fst` (projection formula): for `β : SmoothForm I B ℝ p`
  and `α` of degree `q + m`,
  `prodFiberIntegral o (cast (wedge (mpullback Prod.fst β) α)) = wedge β (prodFiberIntegral o α)`,
  the cast along `p + (q + m) = (p + q) + m`. Pointwise: in the shuffle sum of
  the wedge on `(v, 0)`, `(0, w)`, the pulled-back $\beta$ vanishes on every
  `(0, w j)`.
- `prodFiberIntegrand_mpullback_of_fst_eq` and
  `prodFiberIntegral_mpullback_of_fst_eq` (invariance under fibrewise
  diffeomorphisms): for a smooth `Φ : B × F → B × F` with `Prod.fst ∘ Φ = Prod.fst`
  whose slices `y ↦ (Φ (b, y)).2` are diffeomorphisms of `F` preserving `o`,
  `prodFiberIntegral o (mpullback Φ α) = prodFiberIntegral o α`, and the
  integrand version at one `b`. The gluing applies them with the open set
  `e.baseSet ∩ e'.baseSet` as base, to the coordinate change. Proof: `dΦ(v,0)` lifts `v`, so by
  `AlternatingMap.map_append_add_of_mem` the integrand of $\Phi^*\alpha$ at
  `b` is the pull-back of that of $\alpha$ along the slice, and
  `integralTopForm_mpullback_of_isOrientationPreservingAt` applies.

About 300 lines.

### `Geometry/Manifold/DifferentialForm/FiberIntegral/Product/ExtDeriv.lean`

- `prodFiberIntegral_mextDeriv`:
  `prodFiberIntegral o (cast (mextDerivₗ (I.prod J) (r + m) α)) = mextDerivₗ I r (prodFiberIntegral o α)`,
  the cast along `(r + m) + 1 = (r + 1) + m`.

Route ([BottTu1982], §6, the proof that integration along the fibre commutes
with $d$): both sides are local in `b` and natural under base
diffeomorphisms (`prodFiberIntegral_mpullback_prodMap`), so `B` may be an open
subset of `E`. There the flat derivative passes under the integral,
`TauCeti.extDeriv_integral_of_contMDiffOn`, applied to the coefficient
against the volume form. In the coordinate formula for $d\alpha$ on
$(v_0,0),\dots,(v_r,0),(0,w_1),\dots,(0,w_m)$ the terms that differentiate in
the base directions give $d\int_F\alpha$, and the remaining terms are, for
each `b`, the exterior derivative on `F` of an $(m-1)$-form, whose integral
vanishes by `TauCeti.integralTopForm_mextDeriv_eq_zero`. For `m = 0` there are
no such terms and Stokes is not used; the statement holds for every `m`.
About 400 lines.

### `Geometry/Manifold/DifferentialForm/FiberIntegral/Basic.lean`

The operator of an oriented fibration.

- `TauCeti.MapFiber.Atlas.fiberIntegrand A α b v : RoughForm J F ℝ m` for a chart
  `e ∈ A` at `b`, the integrand read through `Ψ_e`: the pull-back along
  `y ↦ e.symm (b, y)` of `α (ṽ_1, …, ṽ_r, ·)`, with `ṽ_i` the derivative of
  `e.symm` at `(b, y)` on `(v i, 0)`. The chart is `A.trivAt b`.
- `TauCeti.MapFiber.Atlas.fiberIntegral (A : TauCeti.MapFiber.Atlas F π) (hA : A.IsOriented o) :
  SmoothForm IM M ℝ (r + m) →ₗ[ℝ] SmoothForm I B ℝ r`, with
  `fiberIntegral_apply`: the value at `b` on `v` is
  `integralTopForm o (A.fiberIntegrand α b v)`.
- `fiberIntegral_apply_of_mem` (independence of the chart): for every
  `e ∈ A` with `b ∈ e.baseSet`, the value is the integral of the integrand
  read through `e`. From `prodFiberIntegrand_mpullback_of_fst_eq` for the
  coordinate change, which preserves `o` by `hA`.
- `fiberIntegral_apply_of_lift` (any lifts): for `e ∈ A` at `b` and
  `X : Fin r → (y : F) → TangentSpace IM (e.symm (b, y))` with
  `mfderiv IM I π _ (X i y) = v i` for all `i`, `y`, the value is the integral
  of the pull-back along `y ↦ e.symm (b, y)` of `α (X 1 y, …, X r y, ·)`. No
  regularity of `X` is needed: the integrands are equal as rough forms, by
  `AlternatingMap.map_append_add_of_mem`. With horizontal lifts this is the
  fibrewise formula of *Coupling forms*.
- `fiberIntegral_apply_zero` (the integral over each fibre): in degree `m`,
  the value at `b` is `integralTopForm o` of the pull-back of `α` along
  `y ↦ e.symm (b, y)`, for every chart `e` at `b`.
- `mpullback_subtype_val_fiberIntegral` (value in a trivialization): on `e.baseSet`, the
  restriction of `A.fiberIntegral hA α` is
  `prodFiberIntegral o (mpullback Ψ_e α)`, with
  `Ψ_e : e.baseSet × F → M`. Smoothness of `fiberIntegral` comes from it and
  `TauCeti.contMDiffAt_mpullback_subtype_val_iff`.

About 400 lines.

### `Geometry/Manifold/DifferentialForm/FiberIntegral/Calculus.lean`

Reduced to the product files through `mpullback_subtype_val_fiberIntegral` and the
locality of forms on open subsets.

- `fiberIntegral_mextDeriv`: `A.fiberIntegral hA (cast (mextDerivₗ IM (r + m) α)) = mextDerivₗ I r (A.fiberIntegral hA α)`;
  in particular the fibre integral of a closed form is closed.
- `fiberIntegral_wedge_mpullback` (projection formula):
  `A.fiberIntegral hA (cast (wedge (mpullback π hπ β) α)) = wedge β (A.fiberIntegral hA α)`,
  since `π ∘ Ψ_e = Prod.fst`.
- `fiberIntegral_mpullback` (naturality along maps of the base): for oriented
  fibrations `π' : M' → B'` with atlas `A'` and `π : M → B` with atlas `A`, the
  same `F` and `o`, a smooth `f : B' → B` and a smooth `g : M' → M` with
  `π ∘ g = f ∘ π'` whose fibre maps, read in charts `e' ∈ A'` at `b'` and
  `e ∈ A` at `f b'`, are diffeomorphisms of `F` preserving `o`:
  `A'.fiberIntegral hA' (mpullback g α) = mpullback f (A.fiberIntegral hA α)`.
  The hypothesis is stated inline; if part 48 builds pull-back fibrations,
  their canonical map satisfies it, and the corollary for them goes there.

About 250 lines.

## What the part uses

- From Mathlib: `AlternatingMap.map_linearDependent`, `Fin.append`,
  `LinearEquiv.cast`.
- From Tau Ceti: the declarations listed under *What exists*.
- From other parts: *Symplectic fibrations*, only
  `Geometry/Manifold/FiberBundle/MapFiber.lean` and `StructureGroup.lean`
  (atlases `TauCeti.MapFiber.Atlas` with `IsContMDiff`, their charts
  `A.trivAt b`, and oriented atlases as `HasStructureGroup`). The three
  product files use no part of the library.

## Issues

#2389, *Build the part Integration over the fibre*, is split into these, in
order; each waits only for those it names.

1. **`FiberIntegral/Product/Basic.lean`**: `AlternatingMap.map_append_add_of_mem`,
   `prodFiberIntegrand`, `prodFiberIntegral` with its smoothness and
   `prodFiberIntegral_degree_zero_apply`. Waits for nothing.
2. **`FiberIntegral/Product/Naturality.lean`**: base pull-back, projection
   formula, invariance under fibrewise orientation-preserving
   diffeomorphisms. Waits for issue 1.
3. **`FiberIntegral/Product/ExtDeriv.lean`**: `prodFiberIntegral_mextDeriv`.
   Waits for issues 1 and 2.
4. **`FiberIntegral/Basic.lean`**: `TauCeti.MapFiber.Atlas.fiberIntegral`,
   independence of the chart and of the lifts, the integral over each fibre,
   the value in a trivialization. Waits for issue 2 and for building issues 1
   and 2 of *Symplectic fibrations* (`MapFiber.lean`, `StructureGroup.lean`).
5. **`FiberIntegral/Calculus.lean`**: $d$, the projection formula and
   naturality for fibrations. Waits for issues 3 and 4.

Issues 1, 2 and 3 can start at once, in sequence, before *Symplectic
fibrations* has merged anything.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982],
  §6 (integration along the fibre, its commutation with $d$ and the
  projection formula, for oriented bundles and forms with compact vertical
  support; here the fibre is closed and Stokes's theorem on it replaces the
  support condition).
