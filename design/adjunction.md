# Adjunction

This is the detailed design of part 32 of `DESIGN.md`, *Adjunction*. It
covers the milestone *Adjunction formula* of
`atlas/almost-complex-structures.md`, McDuff–Salamon [McDuffSalamon2017],
Example 4.4.5, with the self-intersection number taken, as the page takes
it, to be the Euler number of the normal bundle. The example of plane curves
belongs to *Projective hypersurfaces*. The Chern-class facts come from
Milnor–Stasheff, *Characteristic Classes*, §14 (the top Chern class of a
complex bundle is the Euler class of its realification, oriented by the
complex structure), through *First Chern number*.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, as for `DESIGN.md`. Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, and paths of new files are under
`SymplecticGeometry/`.

## Setting and conventions

- **The ambient manifold.** `X : Type` with
  `I : ModelWithCorners ℝ E H`, `[FiniteDimensional ℝ E]`,
  `[IsManifold I ∞ X]` and an almost complex structure
  `J : TauCeti.SmoothAlmostComplexStructure I X`. Real dimension four is
  `hE : finrank ℝ E = 4`. No Hausdorffness, second countability or
  compactness of `X` is assumed: every choice below (a metric, a form) is
  made on bundles over the surface, which is compact.
- **The surface.** As in `design/first-chern-number.md`: `M : Type` with
  `[ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]` (Lean cannot call it
  `Σ`), embedded by `f : TauCeti.SmoothEmbedding (𝓡 2) I ∞ M X`. The two
  general files below allow any source model `I' : ModelWithCorners ℝ E' H'`
  in place of `𝓡 2`.
- **$J$-invariance.** "$J(T\Sigma)=T\Sigma$" is the hypothesis
  `hJ : ∀ x, ∀ v ∈ f.tangentRange x hn, J (f x) v ∈ f.tangentRange x hn`,
  with Tau Ceti's `TauCeti.SmoothEmbedding.tangentRange` and `hn` the proof
  that `∞ ≠ 0` in `ℕ∞ω`. It is the hypothesis `hp` of Tau Ceti's
  `TauCeti.AlmostComplexStructure.quotient` at each point, and no new
  predicate is defined. Inclusion is enough, since $J$ is invertible and the
  dimensions agree.
- **Orientation of the surface by $J$.** The orientation is an argument
  `o : TauCeti.Manifold.Orientation (𝓡 2) M (Fin 2)` with the hypothesis
  `ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace (𝓡 2) c)),
  mfderiv (𝓡 2) I f c (b 1) = J (f c) (mfderiv (𝓡 2) I f c (b 0)) →
  b.orientation = o.orientationAt c`: every frame $(u, ju)$, with $j$ the
  restriction of $J$, is positive. This is the form in which Tau Ceti's
  `Geometry/Symplectic/Manifold/AlmostComplex/Orientation.lean` writes "oriented
  by $j$" (its `ho`), with $j$ read through $df$, so that the milestone and
  its lemmas need no almost complex structure on `M`. Only the pointwise
  `shortExact_orientationAt_normalSpace` takes its hypothesis through the
  restriction `J.restrict f hJ` of *Complex submanifolds*, so
  `SelfIntersection.lean` imports its merged
  `Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`. That lemma
  holds for an embedding `f : SmoothEmbedding I' I ∞ N X` of any dimension
  `k` (`hk : finrank ℝ E' = k`); the surface is the case `k = 2`, where its
  callers convert `ho` with `orientation_eq_of_apply_one_eq`.
- **Orientation of the ambient manifold and of the normal bundle.** The
  formula does not mention the orientation of $X$; the page uses it only to
  orient the normal bundle, so that $T\Sigma\oplus\nu$ and $TX|_\Sigma$
  agree. The normal bundle is oriented directly by its complex structure,
  Tau Ceti's `TauCeti.VectorBundleOrientation.complex`, as `DESIGN.md`
  decided. `shortExact_orientationAt_normalSpace` (in `SelfIntersection.lean`)
  shows that this is the orientation the page means: with $X$ and $\Sigma$
  oriented by $J$, the orientations of $\Sigma$ and $\nu$ induce that of
  $X$ through the short exact sequence of the normal bundle.
- **Characteristic numbers.** $c_1(TX,J)$ is *First Chern number*'s
  `SymplecticGeometry.Bundle.firstChernClass G` of the complex tangent bundle
  `(J.toContMDiff ⊤).toContinuousComplexStructure.Fiber` (Tau Ceti's
  `Geometry/Symplectic/Manifold/AlmostComplex/ComplexTangentBundle.lean`),
  for a complex model `G : Type` with `[Fact (finrank ℝ E = 2 * finrank ℂ G)]`.
  Its value $\langle c_1(TX,J),[\Sigma]\rangle$ is the integer under
  `oₕ.evalFundamentalClass hM _ (f : C(M, X)) (firstChernClass G _)`,
  with `oₕ = o.toHomologicalOrientation` and
  `hM : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2`: Tau Ceti's evaluation on
  $f_*[\Sigma]$, so no homology class of $X$ is formed. The genus is Tau
  Ceti's `TauCeti.surfaceGenus M`.

## Decisions

`DESIGN.md` leaves three questions to this file.

### How $J$ descends to the normal bundle

The normal space at `x` is Tau Ceti's quotient
`f.NormalSpace x hn = TangentSpace I (f x) ⧸ f.tangentRange x hn`. Tau Ceti
already has the complex structure on a quotient by an invariant subspace,
`TauCeti.AlmostComplexStructure.quotient` (`Geometry/Symplectic/AlmostComplex/Quotient.lean`),
built with `Submodule.mapQ`, with `quotient_mk` and
`isComplexLinearMap_mkQ`. The pointwise structure is that construction
applied to `J.almostComplexStructureAt (f x)`; nothing new is needed in
linear algebra and no metric enters.

Smoothness is the new part. With the bundle structure that Tau Ceti installs
locally (`normalSpaceFiberBundle`, `normalSpaceVectorBundle`,
`normalSpaceContMDiffVectorBundle`, with model `P` and
`hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E'`), the map of total spaces
of the descended structure composed with `f.normalQuotientMap` is
`normalQuotientMap` composed with $J$ on the pull-back `f *ᵖ TangentSpace I`.
The latter is smooth, so Tau Ceti's `contMDiff_normalBundle_iff`
(`NormalSpace/VectorBundle/Quotient.lean`) makes the descended map smooth,
and Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff` (`Geometry/Manifold/VectorBundle/Hom.lean`)
turns this into a smooth section of the endomorphism bundle. The result is a
`SymplecticGeometry.Bundle.ContMDiffComplexStructure` on the normal bundle,
so all of *Symplectic vector bundles*' API, and through
`toContinuousComplexStructure` Tau Ceti's complex vector bundle
`.Fiber`, apply to it. `normalBundleMap` (for maps of pairs) does not
apply. As the approving review of #838 asked, the structure is in the
namespace `TauCeti.SmoothEmbedding`, in a file beside Tau Ceti's
`NormalSpace/` files. The structure serves this part; *Projective
hypersurfaces* does not use it, since Tau Ceti's normal bundle of a
holomorphic embedding over `ℂ` is already complex.

### The orientation of the normal bundle

The self-intersection number is the Euler number of the normal bundle with
its complex orientation:

$$\Sigma\cdot\Sigma = \langle e(\nu, \mathfrak o_{\mathbb C}),[\Sigma]\rangle,$$

in Lean the integer under `oₕ.evalFundamentalClass` applied to
`TauCeti.complexEulerClass ℂ ν_J h`, where `ν_J` is the complex line bundle
`.Fiber` of the descended structure, with model `ℂ` (real model `P := ℂ`
of the normal bundle). `complexEulerClass` is by definition the Euler class
`VectorBundleOrientation.eulerClass` of `VectorBundleOrientation.complex`,
reindexed, so this is the page's Euler number with no further translation.
That the complex orientation is the one induced by the orientations of $X$
and $\Sigma$ is the pointwise lemma `shortExact_orientationAt_normalSpace`, from Tau
Ceti's `Orientation.shortExact`, `TauCeti.prod_complexOrientation` and
`LinearEquiv.map_complexOrientation`. No
Poincaré duality is used, and the equality with $Q_X([\Sigma],[\Sigma])$ for
closed $X$ is not part of the milestone, as `DESIGN.md` says.

### The splitting of $TX|_\Sigma$

The overview first planned the splitting through Tau Ceti's orthogonal
representatives for a $J$-invariant metric on $TX$. Those need a
`RiemannianBundle` instance on the tangent bundle of all of $X$, and such a
metric exists only for a Hausdorff σ-compact $X$, which the page does not
assume. The splitting is needed only over $\Sigma$, so it is built on the
pull-back bundle `f *ᵖ TangentSpace I` over the compact surface, and with a
symplectic form instead of a metric, so that *First Chern number*'s
additivity, which is stated for symplectic bundles, applies to it directly:

1. Let `Jf` be `J.pullbackComplexStructure f f.contMDiff`, the pull-back of $J$ to
   `f *ᵖ TangentSpace I`, and `ω` a two-form compatible with `Jf`, given by
   the library's `ContMDiffComplexStructure.exists_compatible`
   (`Symplectic/ComplexStructure/Basic.lean`).
2. The tangent image $W$ (frames
   `Bundle.Pullback.hasLocalContMDiffSubbundleFrames_range_mfderiv`) is
   `Jf`-invariant, so `ω`, which tames `Jf`, is nondegenerate on it, and
   its `ω`-orthogonal
   $W^\omega$ is a complement and is `Jf`-invariant. The library's
   `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal_of_isCompl` and
   `contMDiff_totalSpace_projectionOnto_orthogonal`,
   `contMDiff_totalSpace_orthogonal_projectionOnto`
   (`Geometry/Manifold/VectorBundle/Orthogonal.lean`, applied to the flat of
   `ω`) make both projections smooth, as *Symplectic neighbourhoods* does in
   `Neighborhood/Frames.lean`.
3. On `TangentSpace I'` of `M`, the form `ω` read through $df$ is a smooth
   nondegenerate two-form $\sigma$; it is positive on the frames $(u, ju)$,
   so it induces `o` under `ho`.
4. On the normal bundle, $\omega_\nu$ is the form transported from $W^\omega$
   by Tau Ceti's metric-free `complementRepresentative`
   (`NormalSpace/Representative.lean`), whose smoothness is Tau Ceti's
   `contMDiff_normalBundle_of_contMDiff_normalClass`
   (`NormalSpace/VectorBundle/Representative.lean`). The representative
   intertwines the descended structure with `Jf`, so $\omega_\nu$ is
   compatible with it.
5. The fibrewise map $v\mapsto((df)^{-1}P_Wv,[v])$ from `f *ᵖ TangentSpace I`
   to `TangentSpace I' ×ᵇ NormalSpace` is a smooth isomorphism carrying `ω`
   to `σ.prod ω_ν` (the library's `ContMDiffTwoForm.prod`), since $W$ and
   $W^\omega$ are `ω`-orthogonal.

The two summands are then not complex subbundles with chosen complex
structures, but symplectic bundles with compatible structures, which is all
that `symplecticChernNumber_eq_chernNumber` and the additivity of *First
Chern number* need. *Almost complex manifolds*' `Metric.lean` is not used.

## Files

The files under `Geometry/Manifold/SmoothEmbedding/NormalSpace/` are general
(any dimensions, no compactness) and sit beside Tau Ceti's normal bundle
files, as the review of #838 advised; the others,
except the linear algebra of `shortExact_orientationAt_normalSpace`
(`LinearAlgebra/ComplexStructure/Orientation.lean`),
are in `Geometry/Symplectic/Manifold/AlmostComplex/`, beside Tau Ceti's folder of
that name (none of Tau Ceti's files there has their names). The overview first
named the single file `Geometry/Manifold/Complex/Adjunction.lean`; this
file splits it, names the last part `AdjunctionFormula.lean`, and uses the
almost complex folder, since nothing in the part is holomorphic; `DESIGN.md`
is updated to match. The list is in the order of the paths.

| File | Contents | Issue |
|---|---|---|
| `Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean` | the complex structure that $J$ induces on the normal spaces and on the normal bundle | 1 |
| `Geometry/Manifold/SmoothEmbedding/NormalSpace/Exact.lean` | the exact sequence of the differential and the normal class map | 3 |
| `Geometry/Manifold/SmoothEmbedding/NormalSpace/Representative.lean` | the representative of a normal class in a complement, as a projection | 2 |
| `Geometry/Symplectic/Manifold/AlmostComplex/AdjunctionFormula.lean` | the milestone | 4 |
| `Geometry/Symplectic/Manifold/AlmostComplex/NormalSplitting.lean` | the forms on the tangent and normal bundles and the symplectic splitting of the pulled-back tangent bundle | 2 |
| `Geometry/Symplectic/Manifold/AlmostComplex/SelfIntersection.lean` | the self-intersection number, its Chern number, the orientation lemma | 3 |
| `LinearAlgebra/ComplexStructure/Orientation.lean` | the orientation induced by an almost complex structure, and short exact sequences of complex-linear maps | 3 |

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean`

Namespace `TauCeti.SmoothEmbedding`, for `f : SmoothEmbedding I' I ∞ M X`,
`J : SmoothAlmostComplexStructure I X` and `hJ` as above; the first two items
take an embedding of any regularity `n` with `hn : n ≠ 0`.

- `normalAlmostComplexStructureAt f J hJ x : TauCeti.AlmostComplexStructure
  (f.NormalSpace x hn)`, defined as
  `(J.almostComplexStructureAt (f x)).quotient (f.tangentRange x hn) _`, whose
  invariance proof is `hJ x` after a rewrite by `almostComplexStructureAt_apply`,
  with `normalAlmostComplexStructureAt_def` by `(rfl)`.
- `@[simp] normalAlmostComplexStructureAt_normalClass`: on
  `f.normalClass x hn v` it gives `f.normalClass x hn (J (f x) v)`, from
  `quotient_mk`; and `@[simp] isComplexLinearMap_normalClass`, from
  `isComplexLinearMap_mkQ`.
- `contMDiffNormalComplexStructure f hdim J hJ`, of type
  `ContMDiffComplexStructure I' ⊤ P (fun x ↦ f.NormalSpace x hn)` under the
  `letI`s of Tau Ceti's `normalSpaceFiberBundle` and `normalSpaceVectorBundle`,
  the two that the type needs; its value at `x` is
  `normalAlmostComplexStructureAt` (`contMDiffNormalComplexStructure_apply`,
  `@[simp] almostComplexStructureAt_contMDiffNormalComplexStructure`). Smoothness as in
  *Decisions*.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/Exact.lean`

Namespace `TauCeti.SmoothEmbedding`, for a smooth embedding of any
regularity `n` over any field, with `hn : n ≠ 0`.

- `exact_mfderiv_normalClass`: the differential at `x` and
  `normalClass x hn` are exact (`Function.Exact`), from Tau Ceti's
  `normalClass_ker`.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/Representative.lean`

Namespace `TauCeti.SmoothEmbedding`, for an embedding of any regularity.

- `complementRepresentative_normalClass`: for a topological complement `W`
  of the tangent image, Tau Ceti's `complementRepresentative` of the class of
  `v` is the projection of `v` onto `W` along the tangent image.

### `Geometry/Symplectic/Manifold/AlmostComplex/NormalSplitting.lean`

Namespace `TauCeti.SmoothEmbedding`, for `f`, `J`, `hJ` as above, with
`Jf = J.pullbackComplexStructure f f.contMDiff`, the pull-back of $J$ to
`f *ᵖ TangentSpace I`, defined for any smooth map as
`TauCeti.SmoothAlmostComplexStructure.pullbackComplexStructure` in
`Geometry/Manifold/VectorBundle/ComplexStructure.lean`, the specialization
of `ContMDiffComplexStructure.pullback` to the tangent bundle, with
`pullbackComplexStructure_toEndomorphism`, `coe_pullbackComplexStructure`,
`pullbackComplexStructure_neg`, `apply_eq_pullbackComplexStructure_apply`
(on `(f *ᵖ TangentSpace I) y`, passed to `simp` with `hf`) and the `simp` lemmas
`pullbackComplexStructure_apply` (on `TangentSpace I (f y)`) and
`pullbackComplexStructure_neg_apply` (on `(f *ᵖ TangentSpace I) y`). No hypothesis on
`M` is needed: a form compatible with `Jf` comes from the library's
`ContMDiffComplexStructure.exists_compatible` where it is used. The
statements take a form `ω : ContMDiffTwoForm I' ⊤ E (f *ᵖ TangentSpace I)`
with `hω : ω.Tames Jf`, and `hω : ω.Compatible Jf` where invariance is used.

- `orthogonalTangentRange f ω x hn`, the `ω`-orthogonal of the tangent image
  as a subspace of `TangentSpace I (f x)`, with
  `mem_orthogonalTangentRange_iff`.
- `isCompl_tangentRange_orthogonal` and `isTopCompl_tangentRange_orthogonal`:
  at each point the tangent image and its `ω`-orthogonal are complements, by Tau Ceti's
  `SymplecticForm.Tames.isSymplectic_of_mem_invtSubmodule`; and
  `pullbackComplexStructure_mem_orthogonal`: for `ω` invariant under `Jf`,
  the orthogonal is `Jf`-invariant.
- The form $\sigma(u,v)=\omega(df\,u,df\,v)$ on `TangentSpace I'` is
  `ω.compMFDeriv f f.contMDiff`, defined for any smooth map as
  `ContMDiffTwoForm.compMFDeriv` in
  `Geometry/Manifold/VectorBundle/Symplectic/Pullback.lean`, which this file
  imports. Here: `isNondegenerate_compMFDeriv`, and `compMFDeriv_pos`:
  $\sigma(u,v)>0$ when $u\neq0$ and $df\,v=J\,df\,u$.
- `normalForm f hdim hJ ω hω : ContMDiffTwoForm I' ⊤ P (NormalSpace)`, the
  form $\omega_\nu(a,b)=\omega(r\,a, r\,b)$ with $r$ the complement
  representative for $W^\omega$, with `normalForm_normalClass` (its value on
  classes of vectors of $W^\omega$) and `compatible_normalForm`: it is
  compatible with `contMDiffNormalComplexStructure`.
- `normalSplitting f hJ ω hω x : (f *ᵖ TangentSpace I) x ≃L[ℝ]
  (TangentSpace I' ×ᵇ NormalSpace) x`, the inverse of `tangentNormalEquiv` for the
  representatives in $W^\omega$, with `normalSplitting_symm_apply`,
  `snd_normalSplitting_apply` and `mfderiv_fst_normalSplitting_apply`, the
  smoothness of its map of total spaces (`contMDiff_normalSplitting`), and
  `pushforward_normalSplitting`: it carries `ω` to
  `(ω.compMFDeriv f f.contMDiff).prod (normalForm f hdim hJ ω hω)`.

The orthogonal and `normalForm` stay in this file, with the splitting: they
share the complement and the smoothness of its representatives, and the file
stays under the limit for a new file.

### `Geometry/Symplectic/Manifold/AlmostComplex/SelfIntersection.lean`

Namespace `TauCeti.SmoothEmbedding`, for a surface `M` in `X` with
`hE : finrank ℝ E = 4` (so `hdim` for `P := ℂ` follows from `hE`),
`[CompactSpace M]`, `J`, `hJ` and `o`.

- `selfIntersectionNumber f hE J hJ o : ℤ`, the integer under
  `o.toHomologicalOrientation.evalFundamentalClass _ _ (ContinuousMap.id M)`
  of `TauCeti.complexEulerClass ℂ ν_J _`, with `ν_J` the complex line bundle
  `(f.contMDiffNormalComplexStructure _ J hJ).toContinuousComplexStructure.Fiber` of
  model `ℂ`; with `selfIntersectionNumber_def` by `(rfl)`. Its docstring
  says that this is $\langle e(\nu_J), [M, o]\rangle$, the Euler number of the
  normal bundle oriented by its complex structure, and that it is the
  self-intersection number when `o` is the orientation given by $J$ (`ho`).
- `selfIntersectionNumber_eq_chernNumber`: it equals *First Chern number*'s
  `Bundle.chernNumber oₕ ℂ ν_J`, by `firstChernClass_eq_complexEulerClass`.
- `selfIntersectionNumber_neg_orientation`: reversing `o` negates the number, from
  `chernNumber_neg_orientation`.
- `shortExact_orientationAt_normalSpace`: for an embedding `f` of a manifold
  `N` of any real dimension `k` whose tangent spaces `J` preserves, if
  `o.orientationAt c` is the
  orientation of `(J.restrict f hJ).almostComplexStructureAt c`, reindexed, Tau
  Ceti's `Orientation.shortExact` of the sequence
  $0\to T_c\Sigma\to T_{f c}X\to\nu_c\to 0$ (the differential and
  `normalClass`, exact by `exact_mfderiv_normalClass` of
  `NormalSpace/Exact.lean`) sends
  `o.orientationAt c` and the complex orientation of $(\nu_c, J_\nu)$ to the
  complex orientation of $(T_{f c}X, J)$. No splitting is chosen. The complex
  orientations are `AlmostComplexStructure.orientation` of
  `LinearAlgebra/ComplexStructure/Orientation.lean` (below), and the lemma
  is its `shortExact_orientation`, the differential being complex linear by
  `isComplexLinearMap_mfderiv` and the normal class map by
  `isComplexLinearMap_normalClass`.

### `LinearAlgebra/ComplexStructure/Orientation.lean`

Namespace `TauCeti.AlmostComplexStructure`, for an almost complex structure
`J` on a finite-dimensional real vector space `V`.

- `orientation_eq_complexOrientation`: Tau Ceti's `J.orientation rfl` is
  its `complexOrientation` of `V` with the complex structure
  `J.complexModule`.
- `orientation_prod` (the orientation of `J₁.prod J₂` is the
  product orientation) and `orientation_eq_of_apply_one_eq` (in real
  dimension two, a basis $(e, Je)$ gives the orientation of `J`).
- `shortExact_orientation`: for a short exact sequence
  $0\to U\to V\to W\to 0$ whose maps are complex linear for `J₁`, `J`
  and `J₂`, `Orientation.shortExact` sends the orientations of `J₁` and
  `J₂` to that of `J`. The proof splits the sequence along a complex-linear
  section, `IsComplexLinearMap.exists_rightInverse_of_surjective` of
  *Linear complex structures*, so no invariant complement appears in the
  statement.

### `Geometry/Symplectic/Manifold/AlmostComplex/AdjunctionFormula.lean`

- `Bundle.chernNumber_pullback_complexStructure`, in the namespace
  `SymplecticGeometry.Bundle`, sits with *First Chern number* in
  `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean`: for a smooth
  complex structure `K` on a bundle `V` over `B : Type` and a smooth map `φ`
  from a compact oriented surface,
  `chernNumber oₕ hM G (K.pullback φ hφ).toContinuousComplexStructure.Fiber`
  is the integer under `oₕ.evalFundamentalClass hM _ (φ : C(M, B))
  (firstChernClass G K.toContinuousComplexStructure.Fiber)`, by
  `ContMDiffComplexStructure.firstChernClass_pullback` and
  `TauCeti.HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap`.
  It is stated for any bundle, its natural generality.
- **Milestone** `adjunction_formula`, in the namespace
  `TauCeti.SmoothEmbedding`, for `X`, `J`, `hE`, `G`, the closed connected
  surface `M`, `f`, `hJ`, `o` and `ho` as in *Setting and conventions*:

  ```
  2 * (TauCeti.surfaceGenus M : ℤ) - 2 =
    f.selfIntersectionNumber hE J hJ o -
      (o.toHomologicalOrientation.evalFundamentalClass hM _ (f : C(M, X))
        (SymplecticGeometry.Bundle.firstChernClass G
          (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)).down
  ```

  Its docstring ends with the line Milestone: *Adjunction formula*. The page's
  second form, $K\cdot\Sigma+\Sigma\cdot\Sigma=2g-2$ with $K=-c_1(TX,J)$, is
  the same equation, and is not stated again. Proof: choose `ω` by
  `ContMDiffComplexStructure.exists_compatible` for
  `J.pullbackComplexStructure f f.contMDiff`. Then

  - $\langle c_1(TX,J),[\Sigma]\rangle$ is `chernNumber` of `Jf` by
    `chernNumber_pullback_complexStructure`, which is
    `symplecticChernNumber` of `(f *ᵖ TX, ω)` by
    `symplecticChernNumber_eq_chernNumber`;
  - by `symplecticChernNumber_congr` along `normalSplitting` and
    `symplecticChernNumber_whitneySum`, that is the sum of the numbers of
    `(TΣ, ω.compMFDeriv f f.contMDiff)` and `(ν, normalForm)`;
  - the first is $2-2g$ by `symplecticChernNumber_tangent`, since
    `ω.compMFDeriv f f.contMDiff` induces `o` (`compMFDeriv_pos` with `ho`);
  - the second is `chernNumber` of `ν_J` by
    `symplecticChernNumber_eq_chernNumber` with `compatible_normalForm`, and
    so `selfIntersectionNumber` by `selfIntersectionNumber_eq_chernNumber`.

  The hypotheses are the page's: real dimension four, $J$-invariant tangent
  planes, $\Sigma$ compact, connected, embedded and oriented by $J$; the
  page's implicit compactness of $\Sigma$ is the one the book leaves
  unstated.

## What the part uses

- Tau Ceti, normal bundles: `SmoothEmbedding.NormalSpace`, `tangentRange`,
  `normalClass`, `normalQuotientMap`, `normalSpaceFiberBundle`,
  `normalSpaceVectorBundle`, `normalSpaceContMDiffVectorBundle`,
  `contMDiff_normalBundle_iff`, `complementRepresentative` with its
  lemmas, `contMDiff_normalBundle_of_contMDiff_normalClass`.
- Tau Ceti, complex structures and orientations:
  `AlmostComplexStructure.quotient` with `quotient_mk` and
  `isComplexLinearMap_mkQ`; `AlmostComplexStructure.restrict`;
  `contMDiff_hom_bundle_iff`; `ContMDiffAlmostComplexStructure.toContinuousComplexStructure`;
  `Bundle.ContinuousComplexStructure.Fiber`; `VectorBundleOrientation.complex`,
  `complexEulerClass`; `prod_complexOrientation`, `LinearEquiv.map_complexOrientation`;
  `Manifold.Orientation.orientationAt`; `HomologicalOrientation.evalFundamentalClass`;
  `surfaceGenus`; `nonempty_contMDiffRiemannianMetric`.
- *Symplectic vector bundles*, merged: `ContMDiffComplexStructure` with
  `tangentEquiv`, `pullback` and `toContinuousComplexStructure`;
  `ContMDiffTwoForm` with `prod`, `pushforward`, `compMFDeriv`,
  `compatibleForm` and `compatible_compatibleForm`.
- *Linear complex structures*, merged: `LinearAlgebra/ComplexStructure/Hom.lean`,
  which `Orientation.lean` imports for
  `IsComplexLinearMap.exists_rightInverse_of_surjective`.
- The library's merged `Geometry/Manifold/VectorBundle/Pullback.lean`
  (`Bundle.Pullback.hasLocalContMDiffSubbundleFrames_range_mfderiv`,
  `contMDiff_totalSpace_mfderiv`) and `Geometry/Manifold/VectorBundle/Orthogonal.lean`.
- *Projective hypersurfaces*: `Geometry/Manifold/SmoothEmbedding/NormalSpace/Splitting.lean`
  (`tangentNormalEquiv`, whose inverse is `normalSplitting`).
- *First Chern number*: `Topology/VectorBundle/Complex/FirstChernClass.lean`
  and `ChernNumber/Basic.lean` (#784: `firstChernClass`,
  `firstChernClass_pullback`, `firstChernClass_congr`,
  `firstChernClass_eq_complexEulerClass`, `chernNumber`,
  `chernNumber_neg_orientation`, `symplecticChernNumber`,
  `symplecticChernNumber_eq_chernNumber`, `symplecticChernNumber_congr`; #1922:
  `symplecticChernNumber_whitneySum`) and `ChernNumber/Axioms.lean` (#788:
  `symplecticChernNumber_tangent`). `ChernNumber/EulerNumber.lean` (#785) is
  not needed: the self-intersection number is the Euler class itself, not a
  count of zeros, and $c_1(T\Sigma)$ is `symplecticChernNumber_tangent`.

Mathlib, Tau Ceti and this library were searched, at the pinned versions,
for an adjunction formula, a complex structure on a normal bundle, and a
self-intersection number defined through an Euler class. Tau Ceti has the
complex structure on a quotient space (above) but not on the normal
bundle; it uses the adjunction formula only as an input (the genus bound of
`Geometry/Symplectic/JHolomorphic/GenusWindow.lean`, and the canonical
characteristic covector of plumbing lattices), and its genus of plane curves
is the algebraic one of schemes.

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #879, *Build the part Adjunction*. Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | The complex structure on the normal bundle | `Geometry/Manifold/SmoothEmbedding/NormalSpace/ComplexStructure.lean` | — | 200 |
| 2 | The symplectic splitting of the tangent bundle along a $J$-invariant submanifold | `AlmostComplex/NormalSplitting.lean`, `NormalSpace/Representative.lean` | 1 | 400 |
| 3 | The self-intersection number | `AlmostComplex/SelfIntersection.lean`, `LinearAlgebra/ComplexStructure/Orientation.lean`, `NormalSpace/Exact.lean` | 1; #784 | 250 |
| 4 | The adjunction formula | `AlmostComplex/AdjunctionFormula.lean` | 2, 3; #784, #788 | 200 |

Issue 1 can start once this design is merged, and issue 2 after it; both
use only Tau Ceti and merged files of the library. The milestone is proved in
issue 4. *Projective hypersurfaces* does not use issue 1: it takes Tau Ceti's
normal bundle over `ℂ` for the normal bundle of a hypersurface.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §4.4, Example 4.4.5.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of
  Mathematics Studies 76, Princeton (1974), §14.
