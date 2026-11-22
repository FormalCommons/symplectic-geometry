# Chern classes

This is the detailed design of part 33 of `DESIGN.md`, *Chern classes*. It
settles what `DESIGN.md` leaves to this file: how the Chern classes are
constructed, how the Euler characteristic formula is proved, and how the part
is split into issues. The part proves no milestone itself. It gives *Projective
hypersurfaces* (part 34) what the page's milestone *Chern classes of projective
hypersurfaces* needs: Chern classes $c_k$ of complex vector bundles in integral
cohomology, with the Whitney sum formula, $c_1$ equal to *First Chern number*'s
`SymplecticGeometry.Bundle.firstChernClass`, the top class equal to Tau Ceti's
`TauCeti.complexEulerClass`, the cohomology ring of $\mathbb CP^n$, and the
value of the Euler class of the tangent bundle of a closed oriented manifold
on its fundamental class.

Sources: Bott–Tu [BottTu1982], §20 (the projective bundle, the
Leray–Hirsch theorem, the definition of Chern classes by the relation of the
tautological class, the splitting principle); A. Hatcher, *Vector Bundles and
K-Theory*, §3.1 (Theorem 3.2 and its proof, in particular the proof of the
Whitney sum formula without a splitting); J. W. Milnor, J. D. Stasheff,
*Characteristic Classes*, §§12 and 14 (the Gysin sequence, the cohomology of
$\mathbb CP^n$, the top Chern class as the Euler class); J. Milnor, *Topology
from the Differentiable Viewpoint*, §6 (Poincaré–Hopf). Only Bott–Tu has a
key in the plan's `references.bib`; the module docstrings cite the others in
full, as Tau Ceti does.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions, as for `DESIGN.md`. Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`.

## The decisions

### Chern classes by the projective bundle

The classes are defined as Grothendieck does, in the normalization of Bott–Tu,
§20. For a complex vector bundle $E\to B$ of rank $n$ let
$\pi:P(E)\to B$ be its projective bundle, whose fibre over $b$ is the space of
complex lines in $E_b$, and $S\subset\pi^*E$ its tautological line. Put

$$x:=-e(S_{\mathbb R})\in H^2(P(E);\mathbb Z),$$

the first Chern class of the dual of $S$ (Tau Ceti's `complexEulerClass` of
$S$, negated). The restrictions of $1,x,\dots,x^{n-1}$ to each fibre form a
basis of the cohomology of $\mathbb CP^{n-1}$, so by Leray–Hirsch every class
of $P(E)$ is uniquely $\sum_{i<n}\pi^*a_i\,x^i$. The Chern classes
$c_k(E)\in H^{2k}(B;\mathbb Z)$ are the unique classes with $c_0(E)=1$ and

$$\sum_{i=0}^{n}\pi^*c_i(E)\,x^{n-i}=0,$$

and $c_k(E)=0$ for $k>n$. For a line bundle $L$, $P(L)=B$ and $S=L$, so the
relation reads $c_1(L)=-x=e(L_{\mathbb R})$: the normalization agrees with
Tau Ceti's Euler class and with *First Chern number*'s class on lines.

The reasons for this choice, against a recursive definition through the
Gysin sequence (Milnor–Stasheff, §14) or a classifying space:

- **Tau Ceti has the tools.** The Leray–Hirsch theorem for products,
  with global classes restricting to a basis of every fibre
  (`TopCat.lerayHirschProdOfClasses_bijective`,
  `AlgebraicTopology/Cohomology/LerayHirsch/FiberwiseBasis.lean`), is the
  local case, and the Mayer–Vietoris step for the Leray–Hirsch map
  (`TopCat.lerayHirschRestrict_union_bijective`,
  `AlgebraicTopology/Cohomology/LerayHirsch/MayerVietoris.lean`) is the
  induction over a finite trivializing cover. The integral cohomology of
  $\mathbb CP^{n-1}$ is free and finitely generated
  (`TauCeti.ComplexProjectiveSpace.projective_singularHomology`), as
  Leray–Hirsch over $\mathbb Z$ needs.
- **The Whitney formula needs no splitting.** Hatcher's proof (VBKT,
  Theorem 3.2) multiplies the two relations of $E_1$ and $E_2$ on
  $P(E_1\oplus E_2)$. Each vanishes on an open set, the complement of
  $P(E_2)$ or of $P(E_1)$, which deformation retracts onto $P(E_1)$ or
  $P(E_2)$; the two open sets cover $P(E_1\oplus E_2)$, so the product of
  the relative classes is zero, and it is a monic relation of degree
  $n_1+n_2$ whose coefficients are $\sum_{i+j=k}c_i(E_1)c_j(E_2)$. Tau
  Ceti's relative cup product of two open sets
  (`TopCat.singularRelativeCup`, `AlgebraicTopology/Cohomology/Cup/Relative.lean`)
  is the tool.
- **The splitting principle is one step.** $\pi^*$ is injective, and over a
  compact Hausdorff base $\pi^*E\cong S\oplus S^\perp$ for the orthogonal
  complement in a Hermitian metric pulled back from a trivial bundle (Tau
  Ceti's `Topology/VectorBundle/TrivialEmbedding.lean` and
  `Topology/VectorBundle/Complement.lean`). Statements that both sides
  satisfy for sums and for lines are then proved by induction on the rank:
  the top class is the Euler class, and $c_1$ is `firstChernClass`.

### The Euler characteristic by Poincaré–Hopf for a gradient

For a compact boundaryless smooth manifold $M$ of dimension $m+1$ with an
orientation, the Euler class of $TM$ evaluated on $[M]$ is the alternating
sum of the Betti numbers. Tau Ceti has every step but one:

- `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`
  (`Topology/VectorBundle/Orientation/SectionIndex.lean`): if a section has
  finitely many zeros, the Euler number adds up its indices at them;
- `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`
  (`Topology/VectorBundle/Orientation/SectionIndex/Degree.lean`): where the
  section, written in coordinates whose chart and trivialization agree in
  orientation, has an invertible derivative, its index is the sign of that
  derivative's determinant;
- `TauCeti.exists_isMorse` and
  `TauCeti.IsMorse.finsum_sign_det_vectorFieldChartDerivative_mgradient`
  (`Geometry/Manifold/Morse/PoincareHopf.lean`): a Morse function exists,
  and the signs of the determinants of the chart derivatives of its gradient
  at its zeros sum to the Euler characteristic.

What is missing is that, for the tangent bundle oriented by a manifold
orientation, the local index of a vector field at a nondegenerate zero is
the sign of the determinant of `TauCeti.vectorFieldChartDerivative`: the
chart and its derivative trivialization are oriented together, and the sign
does not depend on the chart, since a change of chart conjugates the
derivative. One issue proves it and the formula. No Poincaré duality is
used, so this part does not wait for *First Chern number*'s Poincaré duality
prerequisites (#806–#810), which `DESIGN.md` listed.

### The cohomology ring of $\mathbb CP^n$ by the Thom isomorphism

Tau Ceti has the additive cohomology of $\mathbb CP^n$ only
(`AlgebraicTopology/Cellular/ComplexProjective/Cohomology.lean`). For a
complex vector space $V$ of dimension $n+1$ let $T\to\mathbb P(V)$ be the
tautological line. The complement of its zero section is $V\setminus\{0\}$,
which is a sphere of dimension $2n+1$ up to homotopy. In the long exact
sequence of the pair $(T,T_0)$, Tau Ceti's Thom isomorphism
(`TauCeti.thomEquivOfCompactSpace`, `Topology/VectorBundle/Thom/Isomorphism.lean`)
identifies the relative groups with those of $\mathbb P(V)$ shifted by two,
and the composite $H^k(\mathbb P(V))\to H^{k+2}(\mathbb P(V))$ is the cup
product with the Euler class. The cohomology of the sphere vanishes in the
degrees between, so this product is bijective for $k\le 2n-2$. Hence
$h^k$ generates $H^{2k}$ for $k\le n$, with $h=-e(T)$. This is the Gysin
argument of Milnor–Stasheff, §12, without a general Gysin sequence.

### Coefficients and the graded ring

The Chern classes lie in Tau Ceti's `TopCat.integralCohomology`
(`AlgebraicTopology/Cohomology/IntegralCup.lean`), singular cohomology with
chain coefficients `ULift ℤ` and cochain values `ℤ`, with the cup product
`TopCat.integralCup`. This is not the convention of `complexEulerClass` and
`firstChernClass`, whose cochain values are `ULift ℤ`
(`Topology/VectorBundle/Orientation/Complex/EulerClass.lean`,
`design/first-chern-number.md`); `evalFundamentalClass` is generic in the
values and takes either. The classes take values in `ℤ` because Tau Ceti
gives the integral cup product there the laws a ring needs (associativity,
the unit, graded commutativity), and nothing comparable for values in
`ULift ℤ`. Neither library maps cohomology between the two conventions
(`TauCeti.uliftIntIso` acts only on homology), so the part adds the bridge
`TopCat.uliftIntegralCohomologyIso`, compatible with pull-backs and cup
products (see *Files*), and states every comparison with `complexEulerClass`
or `firstChernClass` through it. Bases are `B : Type`, as for these. The
total Chern class and the Whitney formula need a ring. Neither library has
a graded cohomology ring, and the full ring is only graded commutative, so
the part adds the commutative ring of even-degree classes,
`TopCat.EvenIntegralCohomology X`, the direct sum of the $H^{2k}(X;\mathbb Z)$
with Mathlib's `DirectSum.GCommRing`. Statements of single degrees, such as
$c_k(E_1\oplus E_2)=\sum_{i+j=k}c_i(E_1)\smile c_j(E_2)$, are also given with
`integralCup`, for uses that stay in one degree.

### The bases

The theorems assume `[CompactSpace B]` and, where a Hermitian metric is
needed, `[T2Space B]`. Compactness gives the finite trivializing cover that
Leray–Hirsch uses, as for Tau Ceti's `thomEquivOfCompactSpace`. The
Leray–Hirsch theorem itself is stated for a finite trivializing cover, so a
later extension to other bases changes only hypotheses. Every base in *Projective
hypersurfaces* is compact. The definition of `chernClass` needs no
hypothesis: where Leray–Hirsch fails it has the value `0`, and no theorem
is stated there.

### `FirstChernClass.lean` stays where it is

*First Chern number*'s `Topology/VectorBundle/Complex/FirstChernClass.lean`
(#784) does not move into `ChernClass/`. Parts 13, 31 and 32 import it, and
it needs no projective bundle. The file `ChernClass/FirstChernClass.lean`
proves that $c_1$ equals it, and so the two stay one notion.

## Conventions

- **Bundles.** A complex vector bundle is Mathlib's
  `[VectorBundle ℂ G E]` with `[FiniteDimensional ℂ G]` over `B : Type`, as
  for `firstChernClass`. Its rank is `finrank ℂ G`. A direct sum is Mathlib's
  `E₁ ×ᵇ E₂` with model `G₁ × G₂`, the form of Tau Ceti's Whitney formula; a
  pull-back is `f *ᵖ E`.
- **The tautological class.** $x=-e(S)$ and $h=-e(T)$, as above, so that
  $c_1(L)=e(L)$ for lines and $h$ is the class of the hyperplane bundle
  $\mathcal O(1)$ (the dual of $T$).
- **Degrees.** $c_k(E)$ lies in `(TopCat.of B).integralCohomology (2 * k)`.
  The relation is written with
  `TopCat.EvenIntegralCohomology` and the ring map of $\pi$, in which
  $x$ has index $1$.

## Files

All files are under `SymplecticGeometry/`. The Chern classes themselves are
in `Topology/VectorBundle/Complex/ChernClass/`, as in `DESIGN.md`. General
infrastructure that does not mention Chern classes goes into files of its
own, at the place of its subject. No folder here has the name of a Tau Ceti
file at the same place: Tau Ceti has the folders
`AlgebraicTopology/Cohomology/LerayHirsch/`,
`Topology/VectorBundle/Orientation/Complex/` and
`Geometry/Manifold/Orientation/`, and no file named like the folders added
here.

### `AlgebraicTopology/Cohomology/EvenIntegralCohomology.lean`

In the namespace `TopCat`, for `X : TopCat.{0}`:

- `EvenIntegralCohomology X := ⨁ k : ℕ, X.integralCohomology (2 * k)`, with
  the instance `DirectSum.GCommRing (fun k ↦ ↥(X.integralCohomology (2 * k)))`
  whose multiplication is `integralCup (2 * i) (2 * j) (2 * (i + j))` and
  whose unit is `integralCohomologyOne`; associativity, the unit laws and
  commutativity come from `integralCup_assoc`, `integralCup_integralCohomologyOne`,
  `integralCup_integralCohomologyOne_right` and `integralCup_gradedComm`
  (the sign is $+1$ in even degrees). So `EvenIntegralCohomology X` is a
  `CommRing`.
- `evenIntegralCohomologyOf X k`, the inclusion of degree `2 * k`, an
  additive map, with `evenIntegralCohomologyOf_mul` (the product of two
  classes is their cup product) and `evenIntegralCohomologyOf_one`.
- `evenIntegralCohomologyMap (f : X ⟶ Y) : EvenIntegralCohomology Y →+*
  EvenIntegralCohomology X`, the pull-back in each degree, a ring map by
  `integralCup_naturality`, with `evenIntegralCohomologyMap_of`,
  `evenIntegralCohomologyMap_id` and `evenIntegralCohomologyMap_comp`.

### `AlgebraicTopology/Cohomology/IntegralCohomologyULift.lean`

In the namespace `TopCat`, for `X : TopCat.{0}`, with
`H^n(X; ULift ℤ)` for `X.singularCohomology (ModuleCat.of ℤ (ULift ℤ)) ℤ
(ModuleCat.of ℤ (ULift ℤ)) n`, the convention of `complexEulerClass`:

- `uliftIntegralCohomologyIso X n : H^n(X; ULift ℤ) ≅ X.integralCohomology n`,
  the map on cohomology of the cochain map that composes values with
  `TauCeti.uliftIntIso.hom` (`ChainComplex.linearYonedaObjMap`, as in Tau
  Ceti's `FactorPullback.lean`), an isomorphism since `uliftIntIso` is one;
  with its value on a cochain representative.
- `uliftIntegralCohomologyIso_naturality`: it commutes with
  `singularCohomologyMap f` for `f : X ⟶ Y`.
- `uliftIntegralCohomologyIso_singularCup`: the isomorphism carries
  `X.singularCup ℤ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom
  p q n h a b` to `X.integralCup p q n h` of the images of `a` and `b`, since
  `uliftIntIso` carries Tau Ceti's `ModuleCat.uliftTensorSelfIso ℤ`, the
  multiplication `a ⊗ b ↦ ⟨a.down * b.down⟩` of the values, to
  `integralCoeffMul`.
- `integralCohomologyLinearEquiv X n`, the linear equivalence from
  cohomology with chain coefficients and values `ℤ`, in the form
  `TopCat.lerayHirsch` takes for `k = ℤ`, to `X.integralCohomology n`,
  with `_naturality` and `_singularCup`.

### `AlgebraicTopology/Cohomology/ChangeOfValues.lean`

The change of cochain values in singular cohomology, in the namespace
`TopCat`, for any abelian `C`, the counterpart of Tau Ceti's
`singularCohomologyChainCoefficientIso`:

- `singularCohomologyValueMap X R k g n` for `g : M ⟶ M'`, the map on
  cohomology of `ChainComplex.linearYonedaObjMap k g`, with its value on a
  cocycle class, `_id`, `_comp` and `_naturality` (it commutes with
  `singularCohomologyMap f`).
- `singularCohomologyValueIso X R k e n` for `e : M ≅ M'`.
- `singularCup_singularCohomologyValueMap`: if `(g₁ ⊗ g₂) ≫ μ' = μ ≫ g`, the
  change of values carries the cup product along `μ` to the cup product
  along `μ'`.

### `AlgebraicTopology/Cohomology/LinearCongr.lean`

The change of linear structure in singular cohomology, in the namespace
`TopCat`, for any abelian `C` and two equal structures `L₁ L₂ : Linear k C`:
`singularCohomologyLinearCongr e X R M n` for `e : L₁ = L₂`, the linear
equivalence `LinearEquiv.cast` along `e`, with `_refl`, `_symm`, `_trans`,
`_naturality` (it commutes with `singularCohomologyMap f`) and `_singularCup`
(it carries cup products to cup products). `IntegralCohomologyULift.lean` uses it to pass
from `ModuleCat.instLinear` to `CategoryTheory.Linear.preadditiveIntLinear`.

### `Algebra/Homology/Monoidal/CupChangeOfValues.lean`

In the namespace `TauCeti.ChainComplex`, for a diagonal `D : E ⟶ A ⊗ B`:
`cupCochain_comp_comp`, the cup product of cochains under morphisms of
values that intertwine two pairings, and
`cup_homologyMap_linearYonedaObjMap`, the same on cohomology. The latter
adapts Tau Ceti's `cup_naturality`.

### `AlgebraicTopology/Cohomology/LerayHirsch/MayerVietoris.lean`

The Mayer–Vietoris step for the Leray–Hirsch map of a family of classes,
copied from Tau Ceti's main branch (commit `ee1e8aa`), which has it and
the pinned release does not; the files keep Tau Ceti's paths, names and
statements, so moving Tau Ceti past them deletes them. For `p : E ⟶ B`,
classes `e d : ι d → Hᵈ(E; k)` and `S ⊆ B`, `TopCat.lerayHirschRestrict p e S n`
is the map `⨁_{d + q = n} ⨁_{i : ι d} H^q(S; k) ⟶ Hⁿ(p⁻¹ S; k)`,
`(a_{d,i}) ↦ ∑ p^*a_{d,i} ⌣ e_{d,i}|`. The theorem
`TopCat.lerayHirschRestrict_union_bijective`: for `U`, `V` open in `U ∪ V`,
if the maps over `U`, `V` and `U ∩ V` are bijective in all degrees `m ≤ n`,
so is the map over `U ∪ V`; `TopCat.lerayHirsch_bijective_of_union_eq_univ`
is the case `U ∪ V = B`. The proof compares the two Mayer–Vietoris
sequences, with a direct sum of copies of the sequence of the base, one for
each class. It uses these copies of Tau Ceti's files of the same commit:

- `Algebra/DirectSum/Prod.lean`: `DirectSum.prodLinearEquiv`.
- `AlgebraicTopology/Cohomology/LerayHirsch/Defs.lean`:
  `TopCat.lerayHirsch p n e`, the map over all of `B`, with
  `TopCat.lerayHirsch_lof` and naturality.
- `AlgebraicTopology/Cohomology/LerayHirsch/Restriction.lean`:
  `TopCat.lerayHirschRestrict`, `TopCat.lerayHirschRestrict_empty_bijective`
  and `TopCat.lerayHirschRestrict_univ_bijective_iff`.
- `AlgebraicTopology/Cohomology/MayerVietoris/Basic.lean`,
  `AlgebraicTopology/Cohomology/MayerVietoris/Cup.lean`,
  `AlgebraicTopology/Cohomology/MayerVietoris/Pair.lean` and
  `AlgebraicTopology/Cohomology/Relative.lean`: only the declarations that
  the pin lacks and that the proof of
  `TopCat.singularCohomologyMayerVietorisδ_singularCup` needs.
- `AlgebraicTopology/Cohomology/MayerVietoris/Module.lean`: the
  Mayer–Vietoris sequence with product middle term and `Function.Exact`.

### `AlgebraicTopology/Cohomology/LerayHirsch/Bundle.lean`

The Leray–Hirsch theorem for a fibre bundle `[FiberBundle F Z]` over `Y`
with a finite trivializing cover, `s : Finset Y` with
`⋃ y ∈ s, (trivializationAt F Z y).baseSet = Set.univ`, whose fibre `F` has
homology projective in every degree and finitely generated in degrees
`p ≤ n`:

- `TopCat.lerayHirsch_bijective`, for the map `TopCat.lerayHirsch π n c`
  over all of `Y` (from `LerayHirsch/Defs.lean`, see the previous
  section): if the restrictions of the classes
  `c p i` to the fibre over every point, read through the trivialization at
  that point, form a basis of `Hᵖ(F; k)`, then it is bijective in degree
  `n`. Over one trivializing set it is `TopCat.lerayHirschProdOfClasses_bijective`
  through the trivialization; the finite cover is handled by induction with
  the previous file. The fibre inclusion `Bundle.Trivialization.fiberInclusion`
  comes from `Topology/FiberBundle/Basic.lean` of *Symplectic vector bundles*.
- `TopCat.lerayHirschEquiv`, the linear equivalence, with its value on
  summands; and `TopCat.singularCohomologyMap_injective_of_lerayHirsch_injective`,
  the injectivity of
  `π^*` (the summand of the unit class, when `c 0` is the unit), the form
  the splitting principle uses.
- The integral form, for `TopCat.integralCohomology` and `integralCup`,
  through `TopCat.integralCohomologyLinearEquiv`; the
  Chern classes use only this form. Its map `TopCat.integralLerayHirsch` is
  additive, with `TopCat.integralLerayHirsch_bijective`, the additive
  equivalence `TopCat.integralLerayHirschEquiv` and
  `TopCat.singularCohomologyMap_injective_of_integralLerayHirsch_injective`.

### `Topology/VectorBundle/ProjectiveBundle/Basic.lean`

In the namespace `SymplecticGeometry.Bundle`, for a vector bundle `E` over
`B` with finite-dimensional model `G` over a nontrivially normed field `𝕜`
(the Chern classes use `𝕜 = ℂ`; `𝕜 = ℝ` serves later Stiefel–Whitney
classes at no cost):

- `ProjectiveBundle 𝕜 G E := Bundle.TotalSpace (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b))`,
  the projective bundle, with its topology and `FiberBundle (ℙ 𝕜 G)`
  structure from Mathlib's `FiberPrebundle`: the pretrivialization of a
  trivialization `e` of `E` sends a line `ℓ ⊆ E b` to `(b, e_b ℓ)`
  (`Projectivization.map`), and its transitions are continuous since the
  coordinate changes of `E` are, and the action of linear maps on `ℙ 𝕜 G` is
  jointly continuous (Tau Ceti's
  `Projectivization.continuousAt_linearProjection`).
- `ProjectiveBundle.projection`, the projection as a continuous map (a
  declaration named `ProjectiveBundle.proj` would take over the field
  notation `p.proj`); over a compact base, for `RCLike 𝕜` and
  finite-dimensional `G`, `CompactSpace` is the instance
  `FiberBundle.compactSpace_totalSpace`; `T2Space` over a Hausdorff base
  is Tau Ceti's instance `TauCeti.FiberBundle.t2Space_totalSpace` (the
  fibre is compact Hausdorff, Tau Ceti's
  `Topology/Algebra/Projectivization.lean`).
- `ProjectiveBundle.map`, the map induced by a fibrewise linear isomorphism
  continuous on total spaces, a homeomorphism over `B`; and
  `ProjectiveBundle.pullbackHomeomorph (f : C(B', B))`, identifying
  `ProjectiveBundle 𝕜 G (f *ᵖ E)` with the pull-back of `ProjectiveBundle 𝕜 G E`
  along `f`, with the map `ProjectiveBundle.pullbackMap f` to
  `ProjectiveBundle 𝕜 G E` over `f`.
- For a direct sum, `ProjectiveBundle.inl` and `ProjectiveBundle.inr`, the
  closed embeddings of `P(E₁)` and `P(E₂)` into `P(E₁ ×ᵇ E₂)`, with disjoint
  ranges; and `ProjectiveBundle.inlRetraction`, the retraction of the
  complement of the range of `inr` onto `P(E₁)`, which for
  `[NormedAlgebra ℝ 𝕜]` is a deformation retraction through the lines
  spanned by $v_1+tv_2$, $t\in[0,1]$
  (`homotopic_inlCompl_comp_inlRetraction`, `inlHomotopyEquiv`).

The file imports *Symplectic vector bundles*'
`Topology/VectorBundle/ZeroSet.lean`, for the closedness of zero sets.

The instance `FiberBundle.compactSpace_totalSpace`, compactness of the total
space of a fibre bundle with compact fibre over a compact base, is in a file
of its own, `Topology/FiberBundle/Compact.lean`, which this file imports.

### `LinearAlgebra/Projectivization/Basic.lean`

`Projectivization.normalizedRep φ x`, the representative of a point `x` of
`ℙ K V` on which a linear form `φ` is `1`, with its algebraic lemmas, and
`Projectivization.mk_eq_of_mem_submodule`. The path is that of Tau Ceti's
file with `linearProjectionDomain`, which it imports.

### `Topology/Algebra/Projectivization.lean`

`Projectivization.continuousOn_normalizedRep`: for a continuous `φ`, the
normalized representative is continuous on `linearProjectionDomain φ`. The
path is that of Tau Ceti's file with `isOpen_linearProjectionDomain`.

### `Topology/Algebra/Module/Equiv/Submodule.lean`

`ContinuousLinearMap.equivMapOfLeftInverse`: a continuous linear map with a
continuous left inverse restricts to a continuous linear equivalence of a
submodule onto its image, the continuous form of Mathlib's
`Submodule.equivMapOfInjective`. The path is that of Mathlib's file with
`ContinuousLinearEquiv.ofSubmodules`.

### `Analysis/LocallyConvex/SeparatingDual.lean`

`SeparatingDual.of_injective`: a topological module with an injective
continuous linear map into one with separating dual has separating dual.

### `Topology/VectorBundle/SeparatingDual.lean`

`VectorBundle.separatingDual`: for `b : B`, the fibre `E b` of a vector
bundle with model `F` has separating dual when `F` has, through the
trivialization at `b`. With Tau Ceti's `VectorBundle.isTopologicalAddGroup`
and `VectorBundle.continuousSMul`, it gives the fibres `E b` the instances
that `Projectivization.Tautological 𝕜 (E b)` needs.

### `Topology/VectorBundle/ProjectiveBundle/Tautological.lean`

- `Projectivization.Tautological 𝕜 V : ℙ 𝕜 V → Type`, `ℓ ↦ ℓ.submodule`, the
  tautological line over the projective space of a topological vector space
  `V` (not only a normed one, since the fibres `E b` are not normed), a vector
  bundle with model `𝕜` under `[SeparatingDual 𝕜 V]`, trivialized over the affine
  open set of a nonzero continuous functional `φ` by `v ↦ φ v`. And
  `Projectivization.tautologicalComplZeroHomeomorph`: the complement of its
  zero section is homeomorphic to `{v : V // v ≠ 0}` by `v ↦ ([v], v)`.
  Tau Ceti's `finiteGrassmannian.Tautological 𝕜 1 N` lives on a
  Grassmannian of coordinate spaces, not on `ℙ 𝕜 V` for every `V`, which the
  fibres `ℙ 𝕜 (E b)` of a projective bundle need.
- `SymplecticGeometry.Bundle.ProjectiveBundle.Tautological 𝕜 G E`, the
  tautological line over `ProjectiveBundle 𝕜 G E`, with fibre `p.2.submodule`
  over `p`, a vector bundle with model `𝕜`, with the continuous inclusion
  into the pull-back of `E` along `projection`. Its restriction to the fibre over
  `b` is `Projectivization.Tautological 𝕜 (E b)`; its pull-backs along
  `ProjectiveBundle.map`, `pullbackMap`, `inl` and `inr` are the tautological
  lines of the source, by fibrewise isomorphisms continuous on total spaces.

The topology of the second line is Tau Ceti's `TauCeti.subbundleTopology`
(`Topology/VectorBundle/Subbundle.lean`), for the lines as subspaces of the
fibres of that pull-back. The file imports the three files above.

### `Topology/VectorBundle/Smul.lean`

Copied from Tau Ceti's main branch (commit `aa1b4e9e2a`), under Tau Ceti's
header: `TauCeti.VectorBundle.totalSpaceHomotopyEquiv`, the projection of a
real vector bundle as a homotopy equivalence.

### `Topology/VectorBundle/EulerClass.lean`

Copied from Tau Ceti's main branch (commit `aa1b4e9e2a`), under Tau Ceti's
header: `TauCeti.zeroSectionComplProjHom` and the exact sequence of the
Thom pair with `Hᵐ(B)` in place of `Hᵐ(E)`. Imports `Smul.lean` above, and
the pinned Tau Ceti's `Thom/Connectivity.lean` for `TauCeti.zeroSectionComplProj`.

### `Topology/VectorBundle/Thom/Isomorphism.lean`

Copied from Tau Ceti's main branch (commit `aa1b4e9e2a`), under Tau Ceti's
header: `TauCeti.eulerClass_thomMap`. Imports `EulerClass.lean` above.

### `Topology/VectorBundle/Thom/Gysin.lean`

Copied from Tau Ceti's main branch (commit `aa1b4e9e2a`), under Tau Ceti's
header: `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`, the
exactness of the Gysin sequence at `Hᵐ(B)`. Imports `Thom/Isomorphism.lean` above.

### `AlgebraicTopology/Cohomology/PairChangeOfCoefficients.lean`

The changes of coefficients of `ChangeOfValues.lean`, `LinearCongr.lean` and
Tau Ceti's `singularCohomologyChainCoefficientMap`, for the cohomology of a
pair, in the namespace `TopPair`: `singularCohomologyChainCoefficientMap`,
`singularCohomologyValueMap` and `singularCohomologyLinearCongr`, with
`_naturality` (they commute with `TopPair.singularCohomologyMap f`) and
their compatibility with `TopPair.singularCohomologyπ`.

### `Topology/VectorBundle/Thom/ChangeOfCoefficients.lean`

The three changes of `PairChangeOfCoefficients.lean` carry Thom classes to
Thom classes (`TauCeti.IsThomClass.singularCohomologyChainCoefficientMap`,
`…ValueMap`, `…LinearCongr`) and commute with `TauCeti.eulerClass`. Imports
`PairChangeOfCoefficients.lean`.

### `Topology/VectorBundle/Thom/CupEulerClass.lean`

The Gysin step of the Thom argument above, for any real vector bundle and
coefficients: `TauCeti.injective_singularCup_eulerClass`,
`TauCeti.surjective_singularCup_eulerClass` and
`TauCeti.bijective_singularCup_eulerClass`, cup product with `e(u)` when
the Thom map of `u` is injective, surjective or bijective and the cohomology
of `E₀` vanishes in the degree below the target, in the target, or both; and
`TauCeti.bijective_integralCup_complexEulerClass`, the bijective case for
`complexEulerClass` over a compact base, in `TopCat.integralCohomology`.
Imports `Thom/Gysin.lean`, `Thom/ChangeOfCoefficients.lean`,
`IntegralCohomologyULift.lean` and Tau Ceti's `Orientation/Complex/EulerClass.lean`.

### `AlgebraicTopology/Cohomology/ComplSingleton.lean`

- `TauCeti.isZero_singularCohomology_complSingleton_subtype_of_ne`: for a
  real normed space `F` of finite dimension `d` and `x : F`,
  `Hᵐ(F ∖ {x}; R, N) = 0` for `m ≠ 0` and `m + 1 ≠ d`, for projective `R`.
  It serves `ChernClass/ProjectiveSpace.lean`, where the deleted tautological
  line is `{v : V // v ≠ 0}`.

### `Topology/VectorBundle/Complex/ChernClass/ProjectiveSpace.lean`

For a complex vector space `V` with `finrank ℂ V = n + 1`:

- `Projectivization.hyperplaneClass V := -(uliftIntegralCohomologyIso _ 2).hom
  (complexEulerClass ℂ (Projectivization.Tautological ℂ V) _)`, in degree
  two.
- `Projectivization.bijective_zsmul_hyperplaneClass_pow`: for `k ≤ n`,
  `m ↦ m • h ^ k` is a bijection from `ℤ` onto `H^{2k}(ℙ ℂ V; ℤ)` (powers
  in `EvenIntegralCohomology`, read in degree `k`); the proof is the Thom
  argument above.
- `Projectivization.hyperplaneClass_pow_eq_zero`: `h ^ (n + 1) = 0`, since
  `H^{2n+2}` vanishes (Tau Ceti's `isZero_singularCohomology_of_lt`,
  transported along a linear equivalence `V ≃ (Fin (n + 1) → ℂ)` and
  `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`).
- `Projectivization.evenIntegralCohomologyEquiv`, the ring isomorphism
  `ℤ[X] ⧸ (X ^ (n + 1)) ≃+* EvenIntegralCohomology (ℙ ℂ V)` sending `X` to
  `h`; odd degrees vanish by Tau Ceti's `isZero_singularCohomology_of_odd`.
- `Projectivization.hyperplaneClass_map`: the map of projective spaces
  induced by a linear injection `V →ₗ[ℂ] W` pulls `h` back to `h`; for a
  linear equivalence this carries the results above from one fibre of a
  projective bundle to another.

### `Topology/VectorBundle/Complex/ChernClass/Basic.lean`

In the namespace `SymplecticGeometry.Bundle`, for a complex vector bundle
`E` with model `G` over `B : Type`, with `n := finrank ℂ G`:

- `projectiveBundleClass G E`, the class $x=-e(S)$ of
  `ProjectiveBundle.Tautological ℂ G E`, in degree two, the image of its
  `complexEulerClass` under `uliftIntegralCohomologyIso`, negated; its
  restriction to each fibre is `hyperplaneClass (E b)`.
- `chernClass G E k : (TopCat.of B).integralCohomology (2 * k)`, defined
  from `TopCat.integralLerayHirschEquiv` for the classes $x^i$, $i<n$, applied to
  $-x^n$ when the Leray–Hirsch map is bijective, `1` for `k = 0`, and `0`
  for `k > n` and where the map is not bijective; with `chernClass_def`.
- `totalChernClass G E : TopCat.EvenIntegralCohomology (TopCat.of B)`, the
  sum of the `evenIntegralCohomologyOf _ k (chernClass G E k)` for
  `k ≤ n`; with `totalChernClass_def`.
- Under `[CompactSpace B]`: `sum_chernClass_mul_projectiveBundleClass_pow`,
  the relation $\sum_{i\le n}\pi^*c_i\,x^{n-i}=0$ in
  `EvenIntegralCohomology (TopCat.of (ProjectiveBundle ℂ G E))`;
  `chernClass_eq_of_sum_mul_pow_eq_zero`, the uniqueness: classes $a_i$
  with $a_0=1$ satisfying the relation are the Chern classes;
  `injective_projectiveBundle_proj`, the injectivity of $\pi^*$ in every
  degree.
- `chernClass_zero` (`= 1`), `chernClass_eq_zero_of_finrank_lt`, and
  `chernClass_one_eq_complexEulerClass` for a line bundle (`n = 1`):
  `chernClass G E 1 = (uliftIntegralCohomologyIso _ 2).hom
  (complexEulerClass G E _)`, from the relation on `P(L) ≅ B`.

### `Topology/VectorBundle/Complex/ChernClass/Naturality.lean`

- `chernClass_pullback (f : C(B', B))`, with `B` and `B'` compact: the
  classes of `f *ᵖ E` are the pull-backs, since `pullbackMap` carries the
  tautological class and the relation, and uniqueness applies;
  `totalChernClass_pullback`, through `evenIntegralCohomologyMap`.
- `chernClass_congr`: a complex-linear fibrewise isomorphism continuous on
  total spaces preserves the classes, through `ProjectiveBundle.map`.
- `chernClass_trivial`: the classes of `Bundle.Trivial B G` vanish in
  positive degree, pulled back from a point; `totalChernClass_trivial`.

### `Topology/VectorBundle/Complex/ChernClass/Whitney.lean`

- `totalChernClass_prod`, with `B` compact:
  `totalChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = totalChernClass G₁ E₁ *
  totalChernClass G₂ E₂`, by Hatcher's argument above: the relations of
  $E_1$ and $E_2$, pulled back to $P(E_1\oplus E_2)$, vanish on the
  complements of the ranges of `inr` and `inl` (by `inlRetraction`, its
  mirror and naturality), so they lift to relative classes, and their
  relative cup product lies in the cohomology of
  $(P,P)$, which is zero.
- `chernClass_prod`, the same in degree `k`, as a sum of `integralCup`s.

### `Topology/VectorBundle/Complex/ChernClass/Splitting.lean`

For `E` of rank `n + 1` over a compact Hausdorff `B`:

- `ProjectiveBundle.tautologicalComplement G E`, the orthogonal complement
  of the tautological line in the pull-back of `E` to `P(E)`, for the
  Hermitian metric pulled back from a fibrewise injection of `E` into a
  trivial bundle (`TauCeti.weightedTrivializationMap`, Tau Ceti's
  `bundleComplementVectorBundle`), a complex vector bundle of rank `n`;
- `ProjectiveBundle.pullbackEquivTautologicalProdComplement`, the
  complex-linear fibrewise isomorphism, continuous on total spaces, of the
  pull-back of `E` with `Tautological ×ᵇ tautologicalComplement`.

With `injective_projectiveBundle_proj` this is the splitting principle in the
one-step form that the inductions below use; `P(E)` is again compact
Hausdorff.

### `AlgebraicTopology/Singular/Kunneth/Connecting.lean`

The connecting morphism on the cross product of the pairs of the file below,
in the second factor, for the value of
`TauCeti.LocalOrientation.crossSign m 0`:
`TopCat.singularHomologyCrossRelPair_comp_singularHomologyδ_comp_singularHomologyπ`,
that the connecting morphism of `(X × Y, A × Y ∪ X × B)`, followed by the map
to `Hₙ'(A × Y ∪ X × B, A × Y)`, sends `a × b` to `(-1) ^ p` times the image of
`TopCat.singularHomologyCrossRel` of `a` and `δ b` under
`TopPair.prodExcisionFst`. It is a file of its own, beside
`RelativePair.lean`, which it imports.

### `AlgebraicTopology/Singular/Kunneth/RelativePair.lean`

The homology cross product of two pairs, for the Whitney file below:
`TopCat.singularHomologyCrossRelPair`,
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₙ(X × Y, fst⁻¹(A) ∪ snd⁻¹(B); R ⊗ S)`, built
from Tau Ceti's shuffle map `TopCat.shufflePair`, with `_def`,
`singularHomologyCrossRelPair_naturality`, and its compatibility with
`TopCat.singularHomologyCrossRel`
(`whiskerLeft_singularHomologyπ_comp_singularHomologyCrossRelPair`) and with
`TopCat.singularHomologyCross`
(`singularHomologyCross_comp_singularHomologyπ_eq_singularHomologyCrossRelPair`).
It uses these copies of Tau Ceti's files of the commit `c9d170eed5`:

- `AlgebraicTopology/Singular/Kunneth/Pair.lean`: `TopCat.shufflePair`
  with its characterization and naturality, without the quasi-isomorphism
  results.
- `AlgebraicTopology/Singular/Excision.lean`: `TopPair.prodUnionTripleFst`
  and `TopPair.prodExcisionFst`.
- `AlgebraicTopology/Singular/Relative.lean`, the existing copy, to which
  `TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id`
  is added.

### `AlgebraicTopology/Cohomology/Cup/RelativeKronecker.lean`

The Kronecker pairing of the relative cross products, for the Whitney file
below: `TopCat.singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross`,
`⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)` for Tau Ceti's
`TauCeti.singularRelativeCross` and `TopCat.singularHomologyCrossRelPair`,
with no sign. For coefficient morphisms `u : T ⟶ R ⊗ S` it adds
`TopCat.singularRelativeCup_eq_homologyMap_singularRelativeCup` and
`TopCat.singularKronecker_singularRelativeCupPullback_fst_snd`, and the form
for local classes, `TauCeti.singularKronecker_complZeroPairCross`, with
coefficients in modules, which applies to the cup data of
`eulerClass_thomClassOfModel_prod`. The file is in `Cup/`, next to Tau Ceti's
`Cup/Relative.lean`, and not in a folder `Cohomology/CrossProduct/`, which
would be named like Tau Ceti's file `Cohomology/CrossProduct.lean`. Its chain-level
steps, the shuffle map of the pairs into the small chains
(`TopCat.shuffleSmallPair`) and the relative Eilenberg–Zilber homotopy
(`TopCat.shuffleAlexanderWhitneyPairHomotopy`), are public and sit in
`Singular/Kunneth/RelativePair.lean`, which the file imports.

### `AlgebraicTopology/SimplicialSet/TripleAcyclicModels.lean`

Acyclic models for three factors of simplicial chains, which the
associativity of the cross product of pairs needs:
`SSet.tripleTensorChainComplexHomotopy`, a chain homotopy between two
natural families of chain maps
`(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C((K ⊗ L) ⊗ M; U)` that agree in degree
zero, and `SSet.tripleTensorChainComplexHomotopy_hom_naturality`. It adds
the cone `SSet.stdSimplex.tripleProdConeChain` on the chains of
`(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]` and `SSet.tripleTensorChainComplexXDesc`, the maps
out of a triple tensor product of chain groups.

### `AlgebraicTopology/Singular/LocalHomology/Orientation/Cross/Basic.lean`

The cross product of local orientations, for the Whitney file below, in Tau
Ceti's namespace: `TauCeti.localHomologyCross`, the cross product of the pairs
`(X, X ∖ {x})` and `(Y, Y ∖ {y})` read in the local homology of `X × Y` at
`(x, y)` with the coefficients multiplied by `ModuleCat.uliftTensorSelfIso ℤ`;
`TauCeti.isLocalOrientation_localHomologyCross`, that it carries local
orientations of vector spaces to a local orientation; and
`TauCeti.LocalOrientation.cross`, with `cross_neg_left`, `cross_neg_right`,
the naturality `cross_map_complZeroPairIso`, and the sign
`TauCeti.LocalOrientation.crossSign m n` comparing it with
`TauCeti.LocalOrientation.prod` (`coe_cross_eq_crossSign_smul`), whose value
is not computed there.

### `AlgebraicTopology/Singular/MayerVietoris/Connecting.lean`

Tau Ceti's Mayer–Vietoris connecting morphism read through the pair of
one piece, for computing `crossSign m 0` through the sphere generator:
`TopCat.mayerVietorisδ_eq_singularHomologyδ_left`, the composite of
`Hₙ(X) ⟶ Hₙ(X, V)`, the inverse of the excision map of
`TopPair.excisionMap U V` and the connecting morphism of
`TopPair.interPair U V`, with sign `1`, ending with the map induced by
`TopPair.interPairSndIso U V`, the homeomorphism
`TopPair.interPairSndHomeomorph U V` from the subspace of
`TopPair.interPair U V` onto `U ∩ V`, which this file defines;
`TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right`, the same through
`(V, U ∩ V)` with sign `-1`; and
`TopCat.reducedMayerVietorisδ_succ_eq_singularHomologyδ_left` for the
reduced morphism in positive degrees. They come from the simplicial-set
statements `SSet.mayerVietorisδ_comp_homologyMap_of_fst` and `_of_snd`.

### `Topology/VectorBundle/Orientation/Complex/Whitney.lean`

The integral Whitney formula for Euler classes of complex bundles, in Tau
Ceti's terms and namespace, which Tau Ceti's `Orientation/Whitney.lean`
proves only when the Thom classes are fixed by any chosen classes of the
model fibres:

- that `TauCeti.complZeroPairCross` sends the local generators selected by
  orientations `ω₁` and `ω₂` of the model fibres to the generator selected
  by `ω₁.prod ω₂`, which turns
  `TauCeti.VectorBundleOrientation.eulerClass_thomClassOfModel_prod` into
  `TauCeti.VectorBundleOrientation.eulerClass_prod` for
  `TauCeti.VectorBundleOrientation.eulerClass`;
- that the complex orientation of `E₁ ×ᵇ E₂` is the product of the complex
  orientations, reindexed;
- `TauCeti.complexEulerClass_prod`: `complexEulerClass (G₁ × G₂) (E₁ ×ᵇ E₂) =
  complexEulerClass G₁ E₁ ⌣ complexEulerClass G₂ E₂`, the cup product being
  `singularCup ℤ integralCoeffComul (ModuleCat.uliftTensorSelfIso ℤ).hom` on
  classes with values in `ULift ℤ`, as in `eulerClass_thomClassOfModel_prod`.

### `Topology/VectorBundle/Orientation/Complex/Tensor.lean`

- `TauCeti.complexEulerClass_tensorProduct`: for complex line bundles `L`,
  `L'` over a compact Hausdorff base, the Euler class of `L ⊗ L'` (Tau
  Ceti's `Topology/VectorBundle/TensorProduct/Basic.lean`) is the sum of
  their Euler classes. Proof: a fibrewise injection into a trivial bundle
  (`TauCeti.weightedTrivializationMap`) gives classifying maps to
  projective spaces, under which `L ⊗ L'` is pulled back from the external
  tensor product of the tautological lines on $\mathbb P^N\times\mathbb P^M$.
  There $H^2$ is free on the two pulled-back hyperplane classes (Tau Ceti's
  `TopCat.lerayHirschProd_bijective`, with the ring of
  `ChernClass/ProjectiveSpace.lean`), and restricting to the two axes
  gives the coefficients.
- `Projectivization.complexEulerClass_twistCore_one`: on
  `ℙ ℂ (Fin (n + 1) → ℂ)`, the Euler class of Tau Ceti's
  `Projectivization.twistCore 1`, read through `uliftIntegralCohomologyIso`,
  is `hyperplaneClass`, since
  `twistCore (-1)` is the tautological line (`twistTransition_neg_one_mul`)
  and `twistCore 1 ⊗ twistCore (-1)` is trivial (`twistTransition_add`).
  *Projective hypersurfaces* uses this to read the page's $h$.

### `Topology/VectorBundle/FiniteRank/Tensor.lean`

Beside Tau Ceti's `FiniteRank/Tensor.lean`, in Tau Ceti's terms only;
`Determinant.lean` imports it.

- `TauCeti.FiniteRankBundleCore.tensorFiberEquiv` and
  `continuous_tensorFiberEquiv`: the fibres of `FiniteRankBundleCore.tensor A D`
  are the tensor products of the fibres of `A` and `D`, through
  `TauCeti.piTensorEquiv`, continuously into Tau Ceti's tensor product
  bundle.
- `TauCeti.FiniteRankBundleCore.detWhitneySumIso`: the determinant line of
  `whitneySum A D` is `tensor A.det D.det`, by a constant change of
  coordinates (`det_coordChange_whitneySum`).

### `Topology/VectorBundle/Determinant.lean` (addition)

- `SymplecticGeometry.Bundle.detCoreProdIso`: the determinant line of
  `E₁ ×ᵇ E₂` is the tensor product of the determinant lines, from the
  exterior powers of Tau Ceti's biproduct of finite-rank cores
  (`Topology/VectorBundle/FiniteRank/Biproduct.lean`, `Tensor.lean`); and,
  read on bundles, the complex-linear fibrewise isomorphism continuous on
  total spaces that `firstChernClass` takes.

### `Topology/VectorBundle/Complex/ChernClass/EulerClass.lean`

- `chernClass_finrank_eq_complexEulerClass`: for `finrank ℂ G = r + 1` and
  `B` compact Hausdorff, `chernClass G E (r + 1)` is the image of
  `complexEulerClass G E _` under `uliftIntegralCohomologyIso` (degrees
  `2 * (r + 1) = 2 * r + 2`). By induction on `r` with the splitting
  principle: for lines `chernClass_one_eq_complexEulerClass`, and
  for `L ×ᵇ Q` both sides are products, by `chernClass_prod` (the top term)
  and `TauCeti.complexEulerClass_prod`, compared by
  `uliftIntegralCohomologyIso_singularCup`.

### `Topology/VectorBundle/Complex/ChernClass/FirstChernClass.lean`

- `chernClass_one_eq_firstChernClass`: for `B` compact Hausdorff,
  `chernClass G E 1 = (uliftIntegralCohomologyIso _ 2).hom
  (firstChernClass G E)`. By induction on the rank with
  the splitting principle: both sides are additive on `L ×ᵇ Q`, the first
  by `chernClass_prod`, the second by `detCoreProdIso`,
  `TauCeti.complexEulerClass_tensorProduct` and `firstChernClass_congr`; on
  lines both are `complexEulerClass` (`firstChernClass_eq_complexEulerClass`).
  Rank zero: both vanish (`chernClass_eq_zero_of_finrank_lt`, and
  `firstChernClass_congr` with a fibrewise isomorphism to the trivial
  bundle, then `firstChernClass_trivial`).

### `Geometry/Manifold/Orientation/EulerCharacteristic.lean`

For a compact Hausdorff boundaryless smooth manifold `M` modelled on `E`
with `finrank ℝ E = m + 1` and `o : TauCeti.Manifold.Orientation I M (Fin (m + 1))`:

- `TauCeti.Manifold.Orientation.sectionIndex_eq_sign_det_vectorFieldChartDerivative`:
  for a continuous vector field `X`, differentiable at a zero `z` at which
  `vectorFieldChartDerivative I X z` is invertible, the local index of `X`
  for `o.toVectorBundleOrientation` and `o.toHomologicalOrientation` is the
  sign of its determinant;
- `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_sum_finrank_singularHomology`:
  the Euler class of `o.toVectorBundleOrientation` evaluated on the
  fundamental class of `o.toHomologicalOrientation` is
  $\sum_{i\le m+1}(-1)^i\dim_k H_i(M;k)$ for any division ring `k`; and
  `TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`,
  the same with `TauCeti.eulerChar M` under a finite CW type instance
  argument, which `TauCeti.FiniteCWType.of_isManifold` supplies. Both come
  from a Morse function, a Riemannian metric and the three Tau Ceti results
  above.

Dimension zero is excluded, as in Tau Ceti's homological orientations; odd
dimensions are included (both sides vanish).

## What the part uses

- From *First Chern number*: `firstChernClass` with `firstChernClass_congr`,
  `firstChernClass_trivial` and `firstChernClass_eq_complexEulerClass`
  (#784), only in `ChernClass/FirstChernClass.lean`; `detCore` from the merged
  `Topology/VectorBundle/Determinant.lean`.
- From *First Chern number*: its file
  `AlgebraicTopology/Singular/LocalHomology/OrientedChart.lean`, only in
  `Geometry/Manifold/Orientation/EulerCharacteristic.lean`, for
  `TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation`.
- From *Symplectic vector bundles*: `Bundle.Trivialization.fiberInclusion`
  (`Topology/FiberBundle/Basic.lean`), only in `LerayHirsch/Bundle.lean`.
- From Tau Ceti: integral cohomology and cup products
  (`AlgebraicTopology/Cohomology/IntegralCup.lean`, `Cup/Relative.lean`),
  the isomorphism `uliftIntIso` of `ULift ℤ` with `ℤ`, the multiplication
  `ModuleCat.uliftTensorSelfIso` of `ULift ℤ`
  (`Algebra/Category/ModuleCat/Monoidal/Unit.lean`),
  Leray–Hirsch for products (`LerayHirsch/`), the Mayer–Vietoris step of
  the Thom isomorphism, the Thom isomorphism, Euler classes of oriented and
  complex bundles and their Whitney formula for model classes, section
  indices, the additive cohomology of $\mathbb CP^n$ and its comparison with
  `ℙ ℂ (Fin (n + 1) → ℂ)`, trivial embeddings and complements of bundles,
  tensor products of bundles, `Projectivization.twistCore`, Morse functions
  and Poincaré–Hopf for their gradients.
- From Mathlib: `FiberPrebundle`, `VectorBundle`, `Projectivization`,
  `DirectSum.GCommRing`, `Polynomial`.

## What later parts do with it

*Projective hypersurfaces* reads the page's $h$ through
`complexEulerClass_twistCore_one`, computes total Chern classes with
`totalChernClass_prod`, `totalChernClass_pullback` and `chernClass_congr`,
and gets $\chi(M)=\langle c_n(TM),[M]\rangle$ from
`chernClass_finrank_eq_complexEulerClass` and
`evalFundamentalClass_eulerClass_eq_eulerChar`. Comparing the complex orientation
of $TM$ (`TauCeti.VectorBundleOrientation.complex`) with the manifold
orientation `TauCeti.complexManifoldOrientation` belongs to that part's
design.

## Issues

Each issue is a few hundred lines, in an order where each issue's blockers
come before it. Issues 1, 2, 3, 5, 13 and 16 can start at once.

1. **Even integral cohomology ring.**
   `AlgebraicTopology/Cohomology/EvenIntegralCohomology.lean`.
2. **Integral cohomology with values in `ULift ℤ`.**
   `AlgebraicTopology/Cohomology/IntegralCohomologyULift.lean`, with
   `AlgebraicTopology/Cohomology/ChangeOfValues.lean` and
   `Algebra/Homology/Monoidal/CupChangeOfValues.lean`.
3. **Leray–Hirsch: the Mayer–Vietoris step.**
   `AlgebraicTopology/Cohomology/LerayHirsch/MayerVietoris.lean`.
4. **Leray–Hirsch for bundles with a finite trivializing cover.**
   `AlgebraicTopology/Cohomology/LerayHirsch/Bundle.lean`. Waits for 3.
5. **The projective bundle.** `Topology/VectorBundle/ProjectiveBundle/Basic.lean`.
6. **Tautological lines.** `Topology/VectorBundle/ProjectiveBundle/Tautological.lean`.
   Waits for 5.
7. **The cohomology ring of $\mathbb CP^n$.**
   `ChernClass/ProjectiveSpace.lean`. Waits for 1, 2 and 6.
8. **Definition of the Chern classes.** `ChernClass/Basic.lean`. Waits for
   2, 4 and 7.
9. **Naturality.** `ChernClass/Naturality.lean`. Waits for 8.
10. **Whitney sum formula.** `ChernClass/Whitney.lean`. Waits for 9.
11. **Integral Whitney formula for Euler classes.**
    `Topology/VectorBundle/Orientation/Complex/Whitney.lean`. Waits for 2.
12. **Euler class of a tensor product of lines, and $\mathcal O(1)$.**
    `Topology/VectorBundle/Orientation/Complex/Tensor.lean`. Waits for 2
    and 7.
13. **Determinant of a direct sum.** Addition to
    `Topology/VectorBundle/Determinant.lean`, with
    `Topology/VectorBundle/FiniteRank/Tensor.lean`.
14. **Splitting principle.** `ChernClass/Splitting.lean`. Waits for 8.
15. **Top class and first class.** `ChernClass/EulerClass.lean` and
    `ChernClass/FirstChernClass.lean`. Waits for 2, 10, 11, 12, 13, 14 and
    *First Chern number*'s #784 (the second file only; it may be split
    off if #784 is not merged).
16. **Euler characteristic formula.**
    `Geometry/Manifold/Orientation/EulerCharacteristic.lean`.
