# Poincaré duals of submanifolds

This is the detailed design of part 58 of `DESIGN.md`, *Poincaré duals of
submanifolds*, for the page `auxiliary/first-chern-class.md`. The part proves
the milestone *Thom class and Poincaré dual of a submanifold*: for a closed
embedded submanifold $Z\subset X$ of codimension $r$ with oriented normal
bundle $\nu$, the Thom isomorphism of $\nu$ with integral coefficients, the
fibre restrictions of its Thom class (on each fibre, the generator of its
orientation), the class $d_Z\in H^r(X;\mathbb Z)$ obtained from the Thom class through a
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
  neighbourhood theorem, and the plan's convention that manifolds are
  Hausdorff and second countable); $Z$ inherits both.
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
  it in cohomology with integer coefficients over a non-compact manifold;
  in homology, `bijective_homologyThomMap` and `homologyThomIso`
  (`Thom/Homology.lean`) hold over any base and any ring, but passing them to
  integral cohomology would need the universal coefficient sequence.
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
  with caps (`Cap/CrossRel.lean`). Tau Ceti has Poincaré duality for
  closed manifolds, `HomologicalOrientation.bijective_singularCap_fundamentalClass`
  (`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/Manifold.lean`).
- **Orientations of exact sequences**: `Orientation.cokerOfExact`
  (`LinearAlgebra/Orientation/Exact/Basic.lean`) and `Orientation.ofExact`,
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

- **Coefficients.** Integral cohomology appears in Tau Ceti in two forms:
  the Thom isomorphism takes chain coefficients `ModuleCat.of K K`, while
  `VectorBundleOrientation.thomClass`, its Euler class, `complexEulerClass`
  and the fundamental classes take `ULift ℤ`. The library converts Thom
  classes between them (`IsThomClass.singularCohomologyChainCoefficientMap`,
  `IsThomClass.singularCohomologyValueMap` and
  `eulerClass_uliftIntegralCohomologyEquiv`, in
  `Topology/VectorBundle/Thom/ChangeOfCoefficients.lean`). So the
  constructions are generic in the coefficients
  `(R : ModuleCat k) k (M : ModuleCat k)`, as `TauCeti.eulerClass` is, and
  start from any relative class `u` of the Thom pair. The class $d_Z$
  itself, `dualClass`, has chain coefficients and values `ULift ℤ` and the
  generator selected by the orientation, so that its restriction to $Z$ is
  Tau Ceti's Euler class of the Thom class, the page's $e(\nu)$, and in
  positive codimension `VectorBundleOrientation.eulerClass` with no
  conversion; its cap product with Tau Ceti's fundamental class is defined,
  and *Complex blowup* compares it with `complexEulerClass` directly (and
  with `hyperplaneClass` through *Chern classes*' `uliftIntegralCohomologyIso`).
  The Thom isomorphism of the milestone is stated for the same Thom class,
  carried to chain coefficients and values `ℤ` by the isomorphism
  `ULift ℤ ≅ ℤ` through these conversion lemmas, so that the milestone
  speaks of one class $u_\nu$.
- **The order of the orientations.** The normal directions come first, as
  on the page, in local homology: at each $z$, the local orientation class
  of $X$ at $f(z)$ is, in a trivialization, the homology cross product of
  the local orientation of $\nu_z$ followed by that of $Z$ at $z$. This is
  what Hatcher's cap product (front face), Tau Ceti's
  `TopCat.singularCap_singularHomologyCrossRel`, needs for
  $d_Z\frown[X]=i_*[Z]$ with no sign. Under Tau Ceti's identification of
  linear orientations with local homology generators the cross product is
  not the product orientation: by the library's
  `TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`
  (and `crossSign_eq`), the cross product of the local orientations of `ω`
  and `ω'` is $(-1)^{\dim\cdot\dim'}$ times the local orientation of
  `ω.prod ω'`. Exchanging the two blocks of a basis costs the same sign, so
  the cross product normal first is the local orientation of the linear
  orientation *tangent first*: a positive basis of $T_zZ$ followed by lifts
  of a positive basis of $\nu_z$ is a positive basis of $T_zX$. The normal
  orientation is therefore plain `Orientation.cokerOfExact` of
  $0\to T_zZ\to T_{f(z)}X\to\nu_z\to0$, with no sign correction.
  `design/chern-classes.md` meets the same sign for the Whitney sum.
- **Thom isomorphism over second-countable bases, by Mayer–Vietoris
  induction.** No finite trivializing cover is needed. Tau Ceti's
  `TauCeti.mayerVietoris_induction` (`Topology/MayerVietoris.lean`) proves a
  property of all open sets of a Hausdorff, locally compact, second-countable
  space from a basis closed under nonempty intersections, binary unions
  (given the two sets and their intersection) and countable disjoint
  unions. Here the property of `U` is that the Thom map over `U` is
  bijective in every degree, and an earlier induction over the same basis
  shows that the Thom pair over `U` has no homology below the rank; the
  basis is the open sets inside the base set of a linear trivialization,
  where Tau Ceti's local result
  `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`
  applies; the binary step is `TopCat.bijective_pullbackCupRestrict_union`;
  the disjoint step is additivity of cohomology and homology. This
  works over any commutative ring and any coefficient module, and every
  manifold here is second countable. It is the one route to the Thom
  isomorphism over a non-compact base in this library, and
  `design/chern-classes.md` agrees. Two other routes were set aside:
  - *Chern classes*' finite trivializing covers
    (`HasFiniteTrivializingCover.of_chartedSpace`, its issue 23, with Tau
    Ceti's `thomEquivOfBiUnionEqUniv`) would also give it over every
    manifold, but this part, and through it the milestone, would then wait
    for that extension's covering-dimension issues (17–23 there). The
    finite covers stay where *Chern classes* needs them, for the
    classifying maps of its Whitney formula.
  - Tau Ceti's chain-level homology Thom isomorphism
    `TauCeti.quasiIso_pushforwardCapChainMap_thomPair` (`Thom/Homology.lean`),
    a quasi-isomorphism between complexes of free modules, gives a
    cochain homotopy equivalence after `Hom(-, M)` by
    `ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`,
    over any base. Reading it as `thomMap` needs the cohomology of the
    shifted complex and a comparison, cochain by cochain, of the dual of
    the cap map with `pullbackCup`, which neither library has. That route
    removes second countability, which no space here lacks.

  *Chern classes*' Leray–Hirsch induction is not changed: it is stated
  over a finite trivializing cover, and the plan asks for no $c_k$ over a
  non-compact base (`design/chern-classes.md`, *The bases*).
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
- **Zero-dimensional $Z$ and $X$.** Tau Ceti converts smooth orientations
  to homological ones in dimension `n + 1`
  (`toHomologicalOrientation`) and in dimension `0`
  (`toHomologicalOrientationOfZeroDim`, `Orientation/ZeroDim/Basic.lean`,
  with its fundamental classes in `Orientation/ZeroDim/FundamentalClass.lean`,
  both under `AlgebraicTopology/Singular/LocalHomology/`). The cap theorem
  has a case for $\dim Z=0$ through the second, so the milestone holds in
  every dimension; $\dim X=0$ forces $r=0$ and is that case.

## Files

### `AlgebraicTopology/Cohomology/Additivity/PullbackCup.lean`

In the setting of Tau Ceti's `TopCat.pullbackCupRestrict` (a map
`π : Y → B`, a subset of `Y`, a relative class `u`):

- `TopCat.bijective_pullbackCupRestrict_iUnion_of_pairwiseDisjoint`: for
  pairwise disjoint open `V i ⊆ B`, the map over `⋃ i, V i` is bijective if
  it is over each `V i`, by `TauCeti.isLimitFanSingularCohomology` and its
  relative form, and the compatibility of the restriction maps with the
  product decompositions;
- `TopCat.isZero_singularHomology_ofInclusion_iUnion_of_pairwiseDisjoint`:
  the same for the vanishing of the relative homology of the pair over
  `⋃ i, V i`, which the Mayer–Vietoris step needs below the rank.

### `Topology/VectorBundle/Thom/SecondCountable.lean`

- `TauCeti.bijective_thomMap_of_secondCountableTopology`: for `[T2Space B]
  [LocallyCompactSpace B] [SecondCountableTopology B] [VectorBundle ℝ F E]`,
  a commutative ring `K`, a module `M` and a Thom
  class `u` (`IsThomClass F E u`), `thomMap F E M (finrank ℝ F) p m h u` is
  bijective; `TauCeti.thomEquivOfSecondCountableTopology`, the equivalence,
  with `thomEquivOfSecondCountableTopology_apply`, named after Tau Ceti's
  `thomEquivOfCompactSpace`. Proof as in *Decisions*.

### `Topology/VectorBundle/Orientation/ThomClass.lean`

- `Orientation.modelThomGenerator ω hP`, for `ω : Orientation ℝ P (Fin r)`
  and `hP : finrank ℝ P = r`:
  the class of $H^r(P,P\setminus0;\mathrm{ULift}\,\mathbb Z)$ selected by
  `ω`, Tau Ceti's `Orientation.localCohomologyClass` for `r = n + 1` and the
  unit class for `r = 0` ($P$ is then a point and $P\setminus0$ empty), up
  to the sign of `ω`;
  `modelThomGenerator_neg` and `span_modelThomGenerator` (it generates).
- `TauCeti.VectorBundleOrientation.canonicalThomClass o hr`, for
  `o : VectorBundleOrientation F E (Fin r)` over any base and
  `hr : finrank ℝ F = r`: the class of $H^r(E,E_0;\mathrm{ULift}\,\mathbb Z)$
  restricting on each fibre to the generator selected by the fibre
  orientation. It takes no choice of an orientation of `F`. Its fibre
  restrictions, `singularCohomologyMap_fiberThomPairMap_canonicalThomClass`:
  for every linear trivialization `e` at `x`, the pull-back, by
  `(e.continuousLinearEquivAt ℝ x hx).complZeroPairIso`, of
  `modelThomGenerator (e.mapOrientation _ hx (o x))`; the uniqueness
  `eq_canonicalThomClass_iff`; `isThomClass_canonicalThomClass`,
  `canonicalThomClass_neg`, and `canonicalThomClass_eq_thomClass` (for
  `r = n + 1` it is `o.thomClass`). It is glued from the fibre generators
  as Tau Ceti's `thomClass` is, not taken from `thomClassOfModel`: that
  class is stated with the `ℤ`-linear structure `ModuleCat.instLinear`,
  while `localCohomologyClass`, `thomClass` and the integral classes here
  use `Linear.preadditiveIntLinear`.
- `TauCeti.VectorBundleOrientation.intCanonicalThomClass o hr`, over a base
  in `Type`: the class `o.canonicalThomClass hr`, in degree
  `finrank ℝ F`, carried to chain coefficients and values `ℤ` by
  `ULift ℤ ≅ ℤ` (`singularCohomologyChainCoefficientMap` and the value map
  of `Topology/VectorBundle/Thom/ChangeOfCoefficients.lean`), a Thom class
  by `isThomClass_intCanonicalThomClass`.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/ThomClass.lean`

The Thom class of a normal orientation `o` is `o.canonicalThomClass rfl`
of the normal bundle, with no name of its own; its fibre restrictions, read
in a trivialization since the fibres carry no norm, are
`singularCohomologyMap_fiberThomPairMap_canonicalThomClass`.

- `TauCeti.SmoothEmbedding.bijective_thomMap_intCanonicalThomClass`: the Thom
  map of `o.intCanonicalThomClass hr` is bijective,
  $H^k(Z;\mathbb Z)\cong H^{k+r}(\nu,\nu\setminus Z;\mathbb Z)$, from
  `bijective_thomMap_of_secondCountableTopology`.

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

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/DualClass/Basic.lean`

With `hf : IsClosed (range f)` and a normalized tube `Φ` with open image
`W ⊇ range f`:

- `TauCeti.SmoothEmbedding.tubePairIso f hn hdim Φ hΦ` (`hΦ`: `Φ` is `f` on the zero
  section): the isomorphism of pairs
  $(\nu,\nu\setminus Z)\cong(W,W\setminus Z)$, and
  `relDualClassOf f hn hdim hf u`, for `u` in $H^n(\nu,\nu\setminus Z;R,k,M)$:
  the class of $H^n(X,X\setminus Z)$ corresponding to `u` under this
  isomorphism and the excision isomorphism
  $H^n(X,X\setminus Z)\cong H^n(W,W\setminus Z)$ of Tau Ceti's
  `TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset`, through the tube chosen by
  `exists_isNormalizedTube_subset` with `O = univ`; `dualClassOf f hn hdim hf u`,
  its image in $H^n(X)$.
- `relDualClass f hn hdim hf o hr` and `dualClass f hn hdim hf o hr`, the classes of
  `o.canonicalThomClass hr`, with coefficients
  `ULift ℤ`.
- `dualClassOf_restrict_compl`: the restriction of `dualClassOf f hn hdim hf u` to
  $X\setminus\operatorname{range}f$ is zero (exactness of the pair);
  `dualClass_restrict_compl`, its case for `dualClass`.
- `dualClassOf_restrict`: its pull-back along `f` is
  `TauCeti.eulerClass R k M P _ n u`, since `Φ` composed with the zero
  section is `f`; `dualClass_restrict`, its case for `dualClass`, and
  `dualClass_restrict_eq_eulerClass`, for `r = n + 1`, with
  `VectorBundleOrientation.eulerClass o` (by `canonicalThomClass_eq_thomClass`).
- `dualClassOf_neg`, `dualClass_neg` (reversing the orientation), and
  linearity of `relDualClassOf` in `u`.

### `Geometry/Manifold/SmoothEmbedding/NormalSpace/DualClass/Slice.lean`

- `eq_relDualClassOf_iff_forall_slice`: for a class `u` of the
  normal bundle in degree `r = finrank ℝ P` (for instance
  `o.canonicalThomClass rfl`), a class of
  $H^r(X,X\setminus Z)$ is `relDualClassOf f hn hdim hf u` exactly when its
  restriction along each normal slice of the normalized tube that defines it is the fibre
  restriction of `u`; by excision and Tau Ceti's uniqueness by fibre
  restrictions, `TauCeti.singularCohomology_thomPair_ext`. (A class of another degree
  is not determined by its fibre restrictions.)
- `singularCohomologyMap_slice_eq_of_hasFDerivAt`: the local-degree lemma
  of *Decisions*.
- `relDualClassOf_eq_of_isNormalizedTube`: every normalized tube defines
  the same class (independence of the tube).
- `dualClass_comp_diffeomorph`: for a diffeomorphism `φ : X' ≃ X`, the
  class of `φ⁻¹ ∘ f` with the normal orientation carried by `dφ` (Tau
  Ceti's `normalSpaceEquiv` of `NormalSpace/Map.lean` and
  `VectorBundleOrientation.comap`) is `φ^* dualClass f hn hdim hf o hr`; the same for
  an open embedding of an open set containing the range.

### `Geometry/Manifold/Orientation/NormalOrientation.lean`

- `TauCeti.SmoothEmbedding.normalOrientation f hn hdim oX oZ`: the normal
  orientation induced by `oX : Manifold.Orientation J X (Fin (m + r))` and
  `oZ : Manifold.Orientation I Z (Fin m)`, normal directions first in local
  homology (see *Decisions*), a `VectorBundleOrientation`; built pointwise
  as `Orientation.cokerOfExact` of $0\to T_zZ\to T_{f(z)}X\to\nu_z\to0$,
  with no sign, and with local constancy in Tau Ceti's trivializations of
  the normal bundle, as in `VectorBundleOrientation.transverse`.
- `normalOrientation_apply` (each fibre is that cokernel orientation),
  `ofExact_normalOrientation` and `normalOrientation_eq_iff` (the
  characterization by positive bases: a positive basis of $T_zZ$ followed
  by lifts of a positive basis of $\nu_z$),
  `normalOrientation_neg_left`, `normalOrientation_neg_right`.

### `AlgebraicTopology/Cohomology/Cap/ProdLocal.lean`

The local computation, on Tau Ceti types: for the model pair
$(P,P\setminus0)$ of dimension `r` and a vector space `Q` of dimension
`m`, at the origin, the cap product of the pull-back of the generator
`modelThomGenerator ω` along the first projection with the cross product
`TauCeti.LocalOrientation.cross` of the local orientations of `ω` and of an
orientation `ω'` of `Q`, normal factor first, pushed forward along the
second projection, is the local orientation of `ω'`; from
`TopCat.singularCap_singularHomologyCrossRel` (`Cap/CrossRel.lean`). The
form used below reads the cross product, by
`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`,
as the local orientation of the linear orientation of $P\times Q$ that
puts `ω'` first, the order `normalOrientation` produces. This is where the
order of *Decisions* enters. For `r = 0` or `m = 0` the statement
degenerates to the unit and needs no product orientation.

### `Geometry/Manifold/Orientation/DualClass.lean`

For closed `X` and `Z` (`[CompactSpace X]`), `hf`, and
`o = normalOrientation f hn hdim oX oZ`:

- `TauCeti.SmoothEmbedding.dualClass_cap_fundamentalClass`: for
  `m + 1 = finrank ℝ E`, the cap product of `dualClass f hn hdim hf o hr` with the
  fundamental class of `oX.toHomologicalOrientation` is
  `mapFundamentalClass f` of `oZ.toHomologicalOrientation`. Proof: by
  naturality of the cap product, the cap with $[X]$ is the image of the
  relative cap of `relDualClass` with the image of $[X]$ in
  $H_{m+r}(X,X\setminus Z)$; excision and the tube carry this to the normal
  bundle, where a class of $H_m$ of a neighbourhood that deformation
  retracts onto $Z$ is determined by its local classes at the points of
  $Z$, and in a trivialization the local class is `Cap/ProdLocal.lean`'s,
  once the local orientation of $X$ at $f(z)$ is identified with the cross
  product of the local orientations of $\nu_z$ and of $Z$ at $z$, normal
  first (`ofExact_normalOrientation` and
  `coe_cross_localOrientation_eq_neg_one_pow_smul`).
- `dualClass_cap_fundamentalClass_of_finrank_eq_zero`: the case
  $\dim Z=0$, with `toHomologicalOrientationOfZeroDim` and its fundamental
  class.
- the milestone theorem
  `TauCeti.SmoothEmbedding.bijective_thomMap_and_dualClass_cap_fundamentalClass`,
  the conjunction of `bijective_thomMap_intCanonicalThomClass`,
  `singularCohomologyMap_fiberThomPairMap_canonicalThomClass` (on each fibre
  the Thom class is the generator of the fibre's orientation),
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

- `TauCeti.SmoothEmbedding.ofTransverseSection hm hsm hs hE`: the inclusion of
  the zero set, with the atlas `SymplecticGeometry.transverseZeroSetChartedSpace` built from Tau
  Ceti's `sectionZeroChartedSpace`
  (modelled on a space of dimension `dim X - r`, through identifications of
  the kernels of the derivative), and the immersion
  `SymplecticGeometry.isImmersionOfComplement_coe_transverseZeroSet`, as a `SmoothEmbedding`, with
  `isClosed_range_ofTransverseSection`. Tau Ceti's atlas is stated for a
  base modelled directly on a normed space, with chosen trivializations,
  surjectivity and complemented kernels as data; a base over a general
  boundaryless model `J` is first carried to Tau Ceti's
  `BoundarylessModel J X`, as `Geometry/Manifold/RegularValue/Level.lean`
  does for level sets, and `ofTransverseSection` takes the order `hm : m ≠ 0`,
  the smoothness `hsm` of the section, its transversality `hs` and the
  dimension `hE` of the model; the choices are made once from `hs`.

### `Geometry/Manifold/VectorBundle/ZeroSet/NormalSpace.lean`

- `SymplecticGeometry.normalSpaceEquivOfTransverseSection`: the isomorphism of the normal
  bundle of the zero set with the restriction of `E'`, induced by $Ds$
  (whose kernel is the tangent space of the zero set), as a fibrewise
  continuous linear equivalence over the inclusion, in the form that Tau
  Ceti's `thomPairMapOfFiberwise` takes; and
  `SymplecticGeometry.normalOrientationOfSection o'`, the normal orientation it carries from an
  orientation `o'` of `E'`.

### `Geometry/Manifold/VectorBundle/ZeroSet/DualClass.lean`

- `TauCeti.SmoothEmbedding.relDualClass_ofTransverseSection`: the pull-back
  of the Thom class of `E'` along `s`, in $H^r(X,X\setminus s^{-1}(0))$, is
  `relDualClass` of the zero set with `SymplecticGeometry.normalOrientationOfSection o'`, by
  `eq_relDualClassOf_iff_forall_slice` and the local-degree lemma (the
  normal component of $s$ along a normal slice has derivative $Ds$, the
  isomorphism that orients the normal bundle);
- `TauCeti.SmoothEmbedding.dualClass_ofTransverseSection`: $d_Z=e(E')$, from
  the previous line and
  `TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero` with
  `S` the zero set, for every rank, and for complex line bundles with
  `complexEulerClass`.

## Uses from other parts

None. The part uses Tau Ceti as listed above, and from the library the
merged change-of-coefficient lemmas of
`Topology/VectorBundle/Thom/ChangeOfCoefficients.lean` and
`bijective_singularCap_fundamentalClass`, for the remark that the cap
identity determines $d_Z$.

## Issues

Each is a few hundred lines; they are listed in an order in which they can
be done, each with what it waits for.

1. **Additivity of the Thom map over disjoint unions.**
   `AlgebraicTopology/Cohomology/Additivity/PullbackCup.lean`. Waits for
   nothing.
2. **Thom isomorphism over second-countable bases.**
   `Topology/VectorBundle/Thom/SecondCountable.lean`, by
   `TauCeti.mayerVietoris_induction`. Waits for 1.
3. **Normalized tubes.**
   `Geometry/Manifold/TubularNeighborhood/Normalized.lean`. Waits for
   nothing.
4. **Normal Thom class and the Thom isomorphism of the normal bundle.**
   `NormalSpace/ThomClass.lean`. Waits for 2.
5. **The dual class.** `NormalSpace/DualClass/Basic.lean`: the definitions, the
   vanishing off $Z$ and the restriction to $Z$. Waits for 3 and 4.
6. **Slices, independence and naturality.** `NormalSpace/DualClass/Slice.lean`.
   Waits for 5.
7. **Induced normal orientation.** `Orientation/NormalOrientation.lean`.
   Waits for nothing.
8. **The local cap computation.** `Cap/ProdLocal.lean`. Waits for 4 (for
   `modelThomGenerator`).
9. **Cap with the fundamental class and the milestone.**
   `Orientation/DualClass.lean`. Waits for 5, 7 and 8.
10. **Zero sets as embedded submanifolds.** `ZeroSet/Embedding.lean`. Waits
    for nothing.
11. **The normal bundle of a zero set.** `ZeroSet/NormalSpace.lean`. Waits
    for 10.
12. **The dual class of a zero set is the Euler class.**
    `ZeroSet/DualClass.lean`. Waits for 6 and 11. This is the zero-set
    statement: *Asymptotically holomorphic sections* (`ZeroSet.lean`) and
    *Complex blowup* (`ExceptionalClass.lean`, `ChernClass.lean`) wait for
    this issue only.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982]
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017]
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of
  Mathematics Studies 76, Princeton (1974), §10.
