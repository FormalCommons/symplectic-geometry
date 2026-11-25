# Poincaré duals of submanifolds

This is the detailed design of part 58 of `DESIGN.md`, *Poincaré duals of
submanifolds*, for the page `auxiliary/first-chern-class.md`. The part proves
the milestone *Thom class and Poincaré dual of a submanifold*: for a closed
embedded submanifold $Z\subset X$ of codimension $r$ with oriented normal
bundle $\nu$, the Thom isomorphism of $\nu$ with integral coefficients, the
class $d_Z\in H^r(X;\mathbb Z)$ obtained from the Thom class through a
tubular neighbourhood and excision, its vanishing on $X\setminus Z$, its
restriction $e(\nu)$ to $Z$, and, for closed oriented $X$ and $Z$,
$d_Z\frown[X]=i_*[Z]$. It also proves that the zero set of a section
transverse to the zero section of an oriented bundle has $d_Z$ equal to the
Euler class of the bundle, which *Asymptotically holomorphic sections*
(`ZeroSet.lean`) and *Complex blowup* (`ExceptionalClass.lean`,
`ChernClass.lean`) use. It waits for no part.

All names below are in the namespace given with them. Paths of new files
are under `SymplecticGeometry/`; Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`. Sources: Bott–Tu [BottTu1982], §6
(Propositions 6.18, 6.24 and 6.41) for the construction, and Hatcher
[Hatcher2017], §3.2, for Thom classes and Euler classes over the integers;
the Mayer–Vietoris proof of the Thom isomorphism follows Milnor–Stasheff,
*Characteristic Classes*, Theorem 10.4, as Tau Ceti's does.

## The setting

- $Z$ and $X$ are manifolds `Z X : Type` (universe `0`, the universe of Tau
  Ceti's fundamental classes) over boundaryless models
  `I : ModelWithCorners ℝ E H`, `J : ModelWithCorners ℝ V G`, with `E`, `V`
  finite-dimensional, `IsManifold _ ∞ _`, and `[T2Space X]
  [SecondCountableTopology X]` (the hypotheses of Tau Ceti's tubular
  neighbourhood theorem); $Z$ inherits both.
- The submanifold is an embedding `f : TauCeti.SmoothEmbedding I J ∞ Z X`
  with `hf : IsClosed (Set.range f)`. Tau Ceti has no subset-based notion of
  submanifold, and its normal bundles and tubes are stated for embeddings.
- The normal bundle is Tau Ceti's intrinsic quotient
  `f.NormalSpace x hn` (`Geometry/Manifold/SmoothEmbedding/NormalSpace/Basic.lean`),
  with model fibre a space `P` of dimension
  `hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E`, and its bundle structure
  installed by `letI` from `instTopologicalSpaceNormalBundle`,
  `normalSpaceFiberBundle` and `normalSpaceVectorBundle`
  (`NormalSpace/VectorBundle/Basic.lean`), as Tau Ceti's
  `diagonalNormalOrientation` does. The codimension is `r = finrank ℝ P`;
  `r = 0` is allowed throughout (then $Z$ is open and closed, $\nu$ is the
  zero bundle and $d_Z$ is the indicator class of $Z$ in degree $0$).
- A normal orientation is
  `o : TauCeti.VectorBundleOrientation P (f.NormalSpace · hn) (Fin r)`.

Declarations about `TauCeti.SmoothEmbedding` are in the namespace
`TauCeti.SmoothEmbedding`, as `AGENTS.md` asks for declarations that dot
notation on a Tau Ceti type finds; declarations about Tau Ceti's bundles,
pairs and cohomology are in `TauCeti` or `TopCat`, under the names of
the neighbouring Tau Ceti lemmas.

## What exists

- **Thom classes over any base** (`Topology/VectorBundle/Orientation/ThomClass.lean`):
  `VectorBundleOrientation.thomClassOfModel o hι ω g` for any rank and any
  coefficients (`R' K M'`, a class `g` of the model pair), with
  `isThomClass_thomClassOfModel` when `g` generates and the uniqueness
  `eq_thomClassOfModel_of_forall` by fibre restrictions;
  `VectorBundleOrientation.thomClass o hF` for rank `n + 1` with
  coefficients `ULift ℤ`, `eq_thomClass_iff`, `thomClass_neg`, and the
  pull-back `singularCohomologyMap_pullbackThomPairMap_thomClass`; the
  fibrewise-isomorphism lemmas of `Orientation/FiberwiseEquiv.lean`.
- **Euler classes**: `TauCeti.eulerClass R k M F E n u`, the zero section
  pulled back to absolute cohomology (`Topology/VectorBundle/EulerClass.lean`),
  `VectorBundleOrientation.eulerClass` for `ULift ℤ`, and
  `TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero`: for a
  section nonzero off `S`, the Euler class is the image of the pull-back of
  `u` in $H^n(B,B\setminus S)$.
- **Thom isomorphism** (`Topology/VectorBundle/Thom/Isomorphism.lean`):
  `TauCeti.thomMap` ($a\mapsto\pi^*a\smile u$) for chain coefficients
  `ModuleCat.of K K`, `K` a commutative ring, bijective over a finite
  trivializing open cover (`thomEquivOfBiUnionEqUniv`,
  `thomEquivOfIUnionEqUniv`), over a compact base
  (`thomEquivOfCompactSpace`) and, over a field, over any base
  (`thomEquivOfField`, `Thom/Homology.lean`). Its proof is a Mayer–Vietoris
  induction: `TopCat.bijective_pullbackCupRestrict_union`
  (`AlgebraicTopology/Cohomology/MayerVietoris/PullbackCup.lean`) and
  `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`. Nothing gives
  it with integer coefficients over a non-compact manifold.
- **Tubes**: `TauCeti.SmoothEmbedding.exists_isTubularNeighborhood_subset`
  and `exists_diffeomorph_normalBundle_subset`
  (`Geometry/Manifold/TubularNeighborhood/Existence.lean`), a diffeomorphism
  of the whole normal bundle onto an open set, equal to `f` on the zero
  section. Neither states the derivative of the tube along the zero
  section, and there is no uniqueness of tubes.
- **Excision** (`AlgebraicTopology/Cohomology/Excision.lean`) and
  additivity of cohomology over disjoint unions
  (`TauCeti.isLimitFanSingularCohomology`, `Cohomology/Additivity/`).
- **Fundamental classes and caps**: homological orientations,
  `TauCeti.Manifold.Orientation.toHomologicalOrientation` (dimension
  `n + 1`), `HomologicalOrientation.fundamentalClass` and
  `mapFundamentalClass` (`AlgebraicTopology/Singular/LocalHomology/`),
  `TopCat.singularCap` with Hatcher's convention (the cochain is evaluated on
  the front face, `Cap/Basic.lean`), its naturality, relative caps
  (`Cap/Relative.lean`, `Cap/AbsoluteRelative.lean`) and the cross product
  with caps (`Cap/CrossRel.lean`). The library has Poincaré duality for
  closed manifolds, `HomologicalOrientation.bijective_singularCap_fundamentalClass`
  (`AlgebraicTopology/Cohomology/CompactSupport/Duality/Manifold.lean`).
- **Orientations of exact sequences**: `Orientation.cokerOfExact`
  (`LinearAlgebra/Orientation/Exact/Basic.lean`) and `Orientation.shortExact`,
  both with the subspace first.
- **Zero sets**: the manifold structure on the regular zeros of a section,
  `sectionZeroChartedSpace`, `isManifold_sectionZero` and
  `isImmersionOfComplement_coe_sectionZero`
  (`Geometry/Manifold/VectorBundle/Section/Manifold.lean`); the local index
  as the sign of the determinant, `sectionIndex_eq_sign_det_of_hasFDerivAt`
  (`Topology/VectorBundle/Orientation/SectionIndex/Degree.lean`), whose
  linearization argument the local-degree lemma below follows.

A search of Tau Ceti, Mathlib and the library for Poincaré duals,
dual classes of submanifolds and Thom classes of embeddings finds nothing;
the only `dualClass` is a private helper of local orientations.

## Decisions

- **Coefficients.** Integral cohomology appears in Tau Ceti in two forms
  that neither library converts: the Thom isomorphism takes chain
  coefficients `ModuleCat.of K K`, while `VectorBundleOrientation.thomClass`,
  its Euler class, `complexEulerClass` and the fundamental classes take
  `ULift ℤ`. So the constructions are generic in the coefficients
  `(R : ModuleCat k) k (M : ModuleCat k)`, as `TauCeti.eulerClass` is, and
  start from any relative class `u` of the Thom pair. The Thom isomorphism
  of the milestone is stated for the Thom class `thomClassOfModel` with
  `K = ℤ` and any generator of the model pair, and the class $d_Z$ itself,
  `dualClass`, with chain coefficients and values `ULift ℤ` and the
  generator selected by the orientation, so that its restriction to $Z$ is
  Tau Ceti's Euler class of the Thom class, the page's $e(\nu)$, and in
  positive codimension `VectorBundleOrientation.eulerClass` with no
  conversion, its cap product
  with Tau Ceti's fundamental class is defined, and *Complex blowup*
  compares it with `complexEulerClass` directly (and with `hyperplaneClass`
  through *Chern classes*' `uliftIntegralCohomologyIso`).
- **The order of the orientations.** The normal orientation induced by
  orientations of $X$ and $Z$ puts the normal directions first: a positive
  basis of $\nu_z$, lifted to $T_zX$, followed by a positive basis of
  $T_zZ$, is a positive basis of $T_zX$. This is the page's convention, and
  with Hatcher's cap product (front face) it is the one for which
  $d_Z\frown[X]=i_*[Z]$ holds with no sign. It differs from
  `Orientation.cokerOfExact`, which puts the subspace first, by the sign
  $(-1)^{r\dim Z}$.
- **Thom isomorphism over σ-compact bases, by two disjoint unions.** No
  finite trivializing cover is needed. A locally compact, σ-compact
  Hausdorff space is the union of two open sets $U_0$, $U_1$, each a
  disjoint union of open sets with compact closure (the even and the odd
  annuli $\operatorname{int}K_{i+1}\setminus K_{i-1}$ of a compact
  exhaustion). Each such piece, and each piece of $U_0\cap U_1$, which is a
  disjoint union of intersections of pieces, lies in a finite union of
  trivializing open sets, where Tau Ceti's finite-cover result applies;
  additivity of cohomology passes bijectivity (and vanishing below the rank)
  to the disjoint unions, and one Mayer–Vietoris step,
  `TopCat.bijective_pullbackCupRestrict_union`, to the whole base. This
  works over any commutative ring and any coefficient module, and every
  manifold here is σ-compact. The cover lemma and the additivity step are
  stated in general, so that *Chern classes*' Leray–Hirsch induction, which
  has its own Mayer–Vietoris step `TopCat.lerayHirschRestrict_union_bijective`,
  can use them for the same question (#3276); this design does not decide
  that update.
- **Normalized tubes.** The class carried by a tube depends on whether the
  tube preserves the fibre orientations, which Tau Ceti's tubes do not
  record. A tube is *normalized* if, at each $x\in Z$, the derivative at $0$
  of its restriction to the fibre $\nu_x$, followed by the quotient
  $T_{f(x)}X\to\nu_x$, is the identity. Composing a tube of
  `exists_diffeomorph_normalBundle_subset` with the inverse of this
  fibrewise linear automorphism, a smooth bundle automorphism, normalizes
  it. $d_Z$ is defined through a chosen normalized tube, and the
  independence theorem says that every normalized tube gives the same
  class.
- **The local-degree lemma carries the proofs.** A class of
  $H^r(X,X\setminus Z)$ is determined by its restrictions to the normal
  slices $(\nu_x,\nu_x\setminus0)\to(X,X\setminus Z)$ of a normalized tube
  (excision and Tau Ceti's uniqueness by fibre restrictions over any base),
  and a map of pairs from a small ball of $\nu_x$ whose normal component has
  derivative the identity at $0$ restricts like the slice (straight-line
  homotopy to the linearization on a small ball, as in
  `sectionIndex_eq_sign_det_of_hasFDerivAt`). Independence of the tube,
  naturality under diffeomorphisms and the zero-set theorem are each this
  lemma applied to a different map.
- **No transverse pull-back in general.** `DESIGN.md` listed naturality
  under maps transverse to $Z$. Nothing in the plan uses it beyond zero sets
  of sections, and building $g^{-1}(Z)$ as an embedded submanifold with
  normal bundle $g^*\nu$ for a general transverse $g$ is a part of its own;
  the zero-set file treats the case that the users need, and naturality is
  stated under diffeomorphisms and open embeddings.
- **Zero-dimensional $Z$.** Tau Ceti's conversion of smooth to homological
  orientations needs dimension `n + 1`. For $\dim Z=0$ the closed manifold
  $Z$ is finite, an orientation is a sign $\varepsilon_z$ at each point,
  and $i_*[Z]=\sum_z\varepsilon_z[z]$; the cap theorem has a companion for
  this case, stated with that sum, so the milestone holds in every
  dimension. $\dim X=0$ forces $r=0$ and is the same companion.

## Files

### `Topology/Compactness/SigmaCompactCover.lean`

- `exists_isOpen_isCompact_closure_pairwise_disjoint_cover`: in a locally
  compact, σ-compact `T2Space`, there are `U : Fin 2 → ℕ → Set X`, open,
  with compact closures, `Pairwise (Disjoint on U j)` for each `j`, and
  `⋃ j i, U j i = univ`. (Each `U j i`, having compact closure, lies in a
  finite union of members of any open cover; the Thom isomorphism uses this
  for the cover by trivializing sets.)

### `AlgebraicTopology/Cohomology/Additivity/PullbackCup.lean`

In the setting of Tau Ceti's `TopCat.pullbackCupRestrict` (a map
`π : Y → B`, a subset of `Y`, a relative class `u`):

- `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`: for
  pairwise disjoint open `V i ⊆ B`, the map over `⋃ i, V i` is bijective if
  it is over each `V i`, by `TauCeti.isLimitFanSingularCohomology` and its
  relative form, and the compatibility of the restriction maps with the
  product decompositions;
- `TopCat.isZero_singularCohomology_ofInclusion_iUnion_of_pairwiseDisjoint`:
  the same for the vanishing of the relative cohomology of the pair over
  `⋃ i, V i`, which the Mayer–Vietoris step needs below the rank.

### `Topology/VectorBundle/Thom/SigmaCompact.lean`

- `TauCeti.bijective_thomMap_of_sigmaCompactSpace`: for `[T2Space B]
  [LocallyCompactSpace B] [SigmaCompactSpace B] [VectorBundle ℝ F E]`,
  `[FiniteDimensional ℝ F]`, a commutative ring `K`, a module `M` and a Thom
  class `u` (`IsThomClass F E u`), `thomMap F E M (finrank ℝ F) p m h u` is
  bijective; `TauCeti.thomEquivOfSigmaCompactSpace`, the equivalence, with
  `thomEquivOfSigmaCompactSpace_apply`, named after Tau Ceti's
  `thomEquivOfCompactSpace`. Proof as in *Decisions*.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/ThomClass.lean`

- `Orientation.modelThomGenerator ω`, for `ω : Orientation ℝ P (Fin r)`:
  the class of $H^r(P,P\setminus0;\mathrm{ULift}\,\mathbb Z)$ selected by
  `ω`, Tau Ceti's `Orientation.localCohomologyClass` for `r = n + 1` and the
  unit class for `r = 0` ($P$ is then a point and $P\setminus0$ empty);
  `modelThomGenerator_neg` and `span_modelThomGenerator` (it generates).
- `TauCeti.SmoothEmbedding.normalThomClass f hdim o g`: the Thom class of
  `o`, `o.thomClassOfModel` with a fixed orientation `ω₀` of `P` (from
  `Module.finBasisOfFinrankEq`, as in Tau Ceti's `exists_isThomClass`) and a
  class `g` of the model pair, generic in the coefficients;
  `isThomClass_normalThomClass` when `g` generates; `normalThomClass_neg`.
  The class of the orientation is `normalThomClass f hdim o
  (modelThomGenerator ω₀)`; `thomClassOfModel_modelThomGenerator_eq` says
  that it does not depend on `ω₀` (both `ω` and `g` change sign), and
  `normalThomClass_eq_thomClass` that for `r = n + 1` it is
  `o.thomClass`, by `eq_thomClass_iff`.
- `TauCeti.SmoothEmbedding.bijective_thomMap_normalThomClass`: for
  `K = ℤ` and any generator `g`, the Thom map of the normal bundle is
  bijective, $H^k(Z;\mathbb Z)\cong H^{k+r}(\nu,\nu\setminus Z;\mathbb Z)$,
  from `bijective_thomMap_of_sigmaCompactSpace`.

### `Geometry/Manifold/TubularNeighborhood/Normalized.lean`

- `TauCeti.SmoothEmbedding.IsNormalizedTube f Φ`: `Φ` is a diffeomorphism
  of the total space of the normal bundle onto an open set of `X`, equal to
  `f` on the zero section, which is normalized: for each `x`, read in the
  trivialization at `x`, the derivative of `Φ` at the zero of the fibre on
  vertical vectors `(0, w)`, `w : P`, followed by `f.normalClassL x`, is the
  trivialization's identification of `P` with `f.NormalSpace x hn` (the
  fibres carry no norm, so the condition is read through the
  trivialization; it does not depend on which linear trivialization).
- `TauCeti.SmoothEmbedding.exists_isNormalizedTube_subset`: inside every
  open set containing the range, from `exists_diffeomorph_normalBundle_subset`
  and the inverse of the fibrewise derivative, a smooth bundle
  automorphism (`isNormalizedTube_comp_bundleEquiv` is the step).

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/DualClass.lean`

With `hf : IsClosed (range f)` and a normalized tube `Φ` with open image
`W ⊇ range f`:

- `TauCeti.SmoothEmbedding.tubePairIso Φ`: the isomorphism of pairs
  $(\nu,\nu\setminus Z)\cong(W,W\setminus Z)$, and
  `relDualClassOf f hf u`, for `u` in $H^n(\nu,\nu\setminus Z;R,k,M)$:
  the class of $H^n(X,X\setminus Z)$ corresponding to `u` under this
  isomorphism and the excision isomorphism
  $H^n(X,X\setminus Z)\cong H^n(W,W\setminus Z)$ of Tau Ceti's
  `TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset`, through the tube chosen by
  `exists_isNormalizedTube_subset` with `O = univ`; `dualClassOf f hf u`,
  its image in $H^n(X)$.
- `relDualClass f hf o` and `dualClass f hf o`, the classes of
  `normalThomClass f hdim o (modelThomGenerator ω₀)`, with coefficients
  `ULift ℤ`.
- `dualClassOf_restrict_compl`: the restriction of `dualClassOf f hf u` to
  $X\setminus\operatorname{range}f$ is zero (exactness of the pair).
- `dualClassOf_restrict`: its pull-back along `f` is
  `TauCeti.eulerClass R k M P _ n u`, since `Φ` composed with the zero
  section is `f`; `dualClass_restrict`, its case for `dualClass`, and
  `dualClass_restrict_eq_eulerClass`, for `r = n + 1`, with
  `VectorBundleOrientation.eulerClass o` (by `normalThomClass_eq_thomClass`).
- `dualClassOf_neg`, `dualClass_neg` (reversing the orientation), and
  linearity of `relDualClassOf` in `u`.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/DualClass/Slice.lean`

- `relDualClassOf_eq_iff_forall_slice`: a class of $H^n(X,X\setminus Z)$ is
  `relDualClassOf f hf u` exactly when its restriction along each normal
  slice of a normalized tube is the fibre restriction of `u`; for
  `u = normalThomClass f hdim o g` this is Tau Ceti's uniqueness by fibre
  restrictions.
- `singularCohomologyMap_slice_eq_of_hasFDerivAt`: the local-degree lemma
  of *Decisions*.
- `relDualClassOf_eq_of_isNormalizedTube`: every normalized tube defines
  the same class (independence of the tube).
- `dualClass_comp_diffeomorph`: for a diffeomorphism `φ : X' ≃ X`, the
  class of `φ⁻¹ ∘ f` with the normal orientation carried by `dφ` (Tau
  Ceti's `normalSpaceEquiv` of `NormalSpace/Map.lean` and
  `VectorBundleOrientation.comap`) is `φ^* dualClass f hf o`; the same for
  an open embedding of an open set containing the range.

### `Geometry/Manifold/Orientation/NormalOrientation.lean`

- `TauCeti.SmoothEmbedding.normalOrientation f hdim oX oZ`: the normal
  orientation induced by `oX : Manifold.Orientation J X (Fin (m + r))` and
  `oZ : Manifold.Orientation I Z (Fin m)`, normal directions first, a
  `VectorBundleOrientation`; built pointwise from `Orientation.cokerOfExact`
  of $0\to T_zZ\to T_{f(z)}X\to\nu_z\to0$ and the sign $(-1)^{rm}$, with
  local constancy in Tau Ceti's trivializations of the normal bundle, as in
  `VectorBundleOrientation.transverse`.
- `normalOrientation_apply` (the characterization by positive bases),
  `normalOrientation_neg_left`, `normalOrientation_neg_right`.

### `Geometry/Manifold/Orientation/DualClass.lean`

For closed `X` and `Z` (`[CompactSpace X]`), `hf`, and
`o = normalOrientation f hdim oX oZ`:

- `TauCeti.SmoothEmbedding.dualClass_cap_fundamentalClass`: for
  `m + 1 = finrank ℝ E`, the cap product of `dualClass f hf o` with the
  fundamental class of `oX.toHomologicalOrientation` is
  `mapFundamentalClass f` of `oZ.toHomologicalOrientation`. Proof: by
  naturality of the cap product, the cap with $[X]$ is the image of the
  relative cap of `relDualClass` with the image of $[X]$ in
  $H_{m+r}(X,X\setminus Z)$; excision and the tube carry this to the normal
  bundle, where a class of $H_m$ of a neighbourhood that deformation
  retracts onto $Z$ is determined by its local classes at the points of
  $Z$, and over a trivializing chart
  $\mathbb R^r\times\mathbb R^m$ the local computation is Tau Ceti's
  compatibility of caps with cross products,
  `TopCat.singularCap_singularHomologyCrossRel` (`Cap/CrossRel.lean`), with
  the normal factor first.
- `dualClass_cap_fundamentalClass_of_finrank_eq_zero`: the companion for
  $\dim Z=0$ of *Decisions*.
- the milestone theorem
  `TauCeti.SmoothEmbedding.bijective_thomMap_and_dualClass_cap_fundamentalClass`,
  the conjunction of `bijective_thomMap_normalThomClass`,
  `dualClass_restrict_compl`, `dualClass_restrict` and, for closed oriented
  `X` and `Z` with the induced normal orientation,
  `dualClass_cap_fundamentalClass`, with the milestone line *Thom class and
  Poincaré dual of a submanifold*. The plan's identity
  $d_Z=\mathrm{PD}(i_*[Z])$ is this cap identity, as `DESIGN.md`'s
  convention *Poincaré duals* says; by
  `bijective_singularCap_fundamentalClass` it determines $d_Z$.

### `Geometry/Manifold/VectorBundle/ZeroSet/Embedding.lean`

For a smooth vector bundle `E' → X` with model fibre `F'` and a smooth
section `s` transverse to the zero section (at each zero, the vertical
derivative $D s(x):T_xX\to E'_x$, read in any trivialization, is onto):

- `TauCeti.SmoothEmbedding.ofTransverseSection s hs`: the inclusion of the
  zero set, with Tau Ceti's manifold structure `sectionZeroChartedSpace`, as
  a `SmoothEmbedding`, with `isClosed_range_ofTransverseSection`;
- `normalSpaceEquivOfTransverseSection`: the isomorphism of the normal
  bundle of the zero set with the restriction of `E'`, induced by $Ds$
  (whose kernel is the tangent space of the zero set), as a fibrewise
  continuous linear equivalence over the inclusion, in the form that Tau
  Ceti's `thomPairMapOfFiberwise` takes; and
  `normalOrientationOfSection o'`, the normal orientation it carries from an
  orientation `o'` of `E'`.

### `Geometry/Manifold/VectorBundle/ZeroSet/DualClass.lean`

- `TauCeti.SmoothEmbedding.relDualClass_ofTransverseSection`: the pull-back
  of the Thom class of `E'` along `s`, in $H^r(X,X\setminus s^{-1}(0))$, is
  `relDualClass` of the zero set with `normalOrientationOfSection o'`, by
  `relDualClassOf_eq_iff_forall_slice` and the local-degree lemma (the
  normal component of $s$ along a normal slice has derivative $Ds$, the
  isomorphism that orients the normal bundle);
- `TauCeti.SmoothEmbedding.dualClass_ofTransverseSection`: $d_Z=e(E')$, from
  the previous line and
  `TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero` with
  `S` the zero set, for every rank, and for complex line bundles with
  `complexEulerClass`.

## Uses from other parts

None. The part uses Tau Ceti as listed above, and from the library only
`bijective_singularCap_fundamentalClass` (merged), for the remark that the
cap identity determines $d_Z$.

## Issues

Each is a few hundred lines; they are listed in an order in which they can
be done, each with what it waits for.

1. **Cover by two disjoint unions and additivity of the Thom map.**
   `Topology/Compactness/SigmaCompactCover.lean` and
   `AlgebraicTopology/Cohomology/Additivity/PullbackCup.lean`. Waits for
   nothing.
2. **Thom isomorphism over σ-compact bases.**
   `Topology/VectorBundle/Thom/SigmaCompact.lean`. Waits for 1.
3. **Normalized tubes.**
   `Geometry/Manifold/TubularNeighborhood/Normalized.lean`. Waits for
   nothing.
4. **Normal Thom class and the Thom isomorphism of the normal bundle.**
   `NormalSpace/ThomClass.lean`. Waits for 2.
5. **The dual class.** `NormalSpace/DualClass.lean`: the definitions, the
   vanishing off $Z$ and the restriction to $Z$. Waits for 3 and 4.
6. **Slices, independence and naturality.** `NormalSpace/DualClass/Slice.lean`.
   Waits for 5.
7. **Induced normal orientation.** `Orientation/NormalOrientation.lean`.
   Waits for nothing.
8. **Cap with the fundamental class and the milestone.**
   `Orientation/DualClass.lean`. Waits for 6 and 7.
9. **Zero sets as embedded submanifolds.** `ZeroSet/Embedding.lean`. Waits
   for nothing.
10. **The dual class of a zero set is the Euler class.**
    `ZeroSet/DualClass.lean`. Waits for 6 and 9. This is the zero-set
    statement: *Asymptotically holomorphic sections* (`ZeroSet.lean`) and
    *Complex blowup* (`ExceptionalClass.lean`, `ChernClass.lean`) wait for
    this issue only.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982]
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017]
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of
  Mathematics Studies 76, Princeton (1974), §10.
