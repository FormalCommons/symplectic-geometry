# Lagrangian Grassmannian

The detailed design of part 6 of `DESIGN.md`, *Lagrangian Grassmannian*. It
serves the milestone *Lagrangian frames and the Lagrangian Grassmannian* of
`atlas/linear-symplectic-geometry.md` (McDuff–Salamon [McDuffSalamon2017],
§2.3, Lemmas 2.3.1 and 2.3.2 and p. 50), and it provides what the Lagrangian
issues of *Maslov index* need from this part (`design/maslov-index.md`,
items G1–G9).

Files are under `SymplecticGeometry/`. Paths of Tau Ceti files are relative to
`.lake/packages/TauCeti/TauCeti/`. Declarations about this part's new type are
in the namespace `SymplecticGeometry.LagrangianGrassmannian`, written `ℒ.`
below. Declarations about Mathlib or Tau Ceti notions go in their namespaces.
In this document `ℒ ι` abbreviates `LagrangianGrassmannian (stdForm ι)`. A file
may introduce the same abbreviation as a `local notation`; it is never a
global name.

## Decisions

1. **The type.** For a real vector space `V` with
   `ω : TauCeti.SymplecticForm V`, `LagrangianGrassmannian ω` is a structure
   extending `Submodule ℝ V` with one more field, `isLagrangian'`. This is the
   pattern of Mathlib's `Module.Grassmannian`. The type is algebra: it lives in
   `LinearAlgebra/Symplectic/Lagrangian/Basic.lean`, and only its topology is
   under `Topology/`, so that no `LinearAlgebra/` file of this part imports a
   `Topology/` file. It gets a `SetLike` instance, so `Λ : ℒ ι` coerces to a
   submodule and to a set. The book's $\mathcal{L}(V,\omega)$ is
   `LagrangianGrassmannian ω`, and $\mathcal{L}(n)$ is `ℒ (Fin n)`. A subtype
   `{L // ω.IsLagrangian L}` was rejected: it would pick up whatever instances
   `Submodule` gets later, and dot notation on it would not find this part's
   API.
2. **The topology** (the question that `DESIGN.md` leaves to this file).
   When `V` is an inner product space over ℝ of finite dimension, `LagrangianGrassmannian ω`
   carries the topology induced by `Λ ↦ (Λ : Submodule ℝ V).starProjection`,
   with values in `V →L[ℝ] V`, so a subspace is identified with its orthogonal
   projection. The reasons:
   - it is defined for any index type `ι`, and for any `V`, while Tau Ceti's
     `TauCeti.finiteGrassmannian ℝ n (2 n)` lives on `Fin N → ℝ`. Reaching it needs a
     reindexing `Fin n ⊕ Fin n ≃ Fin (n + n)` that every later statement
     would carry;
   - it is Hausdorff at once, because a subspace is the range of its
     projection;
   - the quotient $\mathrm{U}(n)/\mathrm{O}(n)$ needs a base point and a choice of
     unitary model, which a general $(V,\omega)$ lacks.

   The other two candidates are then theorems on `StdSpace ι`. The unitary
   group acts on `ℒ ι` through the homomorphism `TauCeti.GLSymplectic.ofUnitary`, and the unitary
   frame map $\mathrm{U}(n)\to\mathcal{L}(n)$ is the orbit map of the
   horizontal subspace. It is continuous, since its projection is
   $R\,P_0\,R^T$ with $R$ the realification. Its source is compact, so it is a
   quotient map, and Tau Ceti's `TauCeti.quotientStabilizerHomeomorph` gives
   the homeomorphism $\mathrm{U}(n)/\mathrm{O}(n)\cong\mathcal{L}(n)$ once the
   stabilizer is identified with $\mathrm{O}(n)$. For `ι = Fin n`, the map into
   `TauCeti.finiteGrassmannian ℝ n (n + n)` is an embedding, and this needs neither
   the unitary frames nor `Quotient.lean`. The coordinate isometry
   `StdSpace.finSumIsometry n` conjugates the projection onto `Λ` into the
   projection onto its image. On the compact Hausdorff space
   `TauCeti.finiteGrassmannian`, the map `V ↦ V.toEuclidean.starProjection` into a
   Hausdorff space of operators is continuous by Tau Ceti and injective by
   `TauCeti.finiteGrassmannian.toEuclidean_injective` and `Submodule.starProjection_inj`, hence a closed
   embedding (`Topology/Grassmannian/Tautological.lean`); and the map out of
   `ℒ (Fin n)`,
   composed with it, is the embedding `Λ ↦ Λ.starProjection` followed by a
   homeomorphism (`Topology.IsEmbedding.of_comp_iff`). A map out of
   `ℒ ι` is continuous as soon as its composite with the unitary frame map
   is, by `isQuotientMap_unitaryFrame.continuous_iff`; the Maslov part uses
   exactly this.
3. **Where the theory is stated.** The type and its topology are general.
   Everything else is stated on `StdSpace ι` with `stdForm ι`: the action, the
   unitary frames, the charts, the direct sum, the manifold structure. That is
   where the milestone and the Maslov part need it, and `DESIGN.md`'s
   principles put the matrix theory there. Generalizing to an arbitrary
   $(V,\omega)$ through a Darboux isomorphism is left to a later page that
   needs it.
4. **Lagrangian frames and complex frames.** A real $2n\times n$ matrix is
   written `Matrix.fromRows X Y`, with `X Y : Matrix ι ι ℝ`, the book's
   $\binom{X}{Y}$. Its complex frame is
   `X.map ofReal + Complex.I • Y.map ofReal`, the book's $X+iY$.
   `TauCeti.complexToRealEuclidean` turns Tau Ceti's `Matrix.realImage (X + i Y)` into
   the range of `Matrix.toEuclideanLin (fromRows X Y)`. This dictionary is
   how Tau Ceti's frame results apply: `Matrix.realImage_mul_map_ofReal`,
   `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal`, and
   `Matrix.GeneralLinearGroup.realOrthonormalize` with
   `realOrthonormalize_mem_unitaryGroup` and `continuous_realOrthonormalize`.
   The dictionary and the reality of the Gram matrix mention only Mathlib and
   Tau Ceti objects, so they are stated in the namespace `Matrix`.
5. **Charts.** The basic chart takes the Lagrangians transverse to the
   horizontal subspace $\{y=0\}$. It sends `Λ` to the symmetric `S` with
   `Λ = StdSpace.graphY S`, the subspace $\{(Sy,y)\}$. This is Tau Ceti's
   convention: `Matrix.lagrangianChart S` is the real image of `S + i·1`,
   which `TauCeti.complexToRealEuclidean` turns into the same subspace. It is also the
   chart that the crossing forms of *Maslov index* use, relative to the
   horizontal subspace. The chart at any other point is this one translated by
   a unitary matrix. As `DESIGN.md` §6 asks, there is a second graph chart,
   on the Lagrangians transverse to the vertical subspace $\{x=0\}$: it sends
   `Λ` to the symmetric `S` with `Λ = StdSpace.graph S`, and it is the basic
   chart after the action of `TauCeti.GLSymplectic.symJ` and before
   `S ↦ -S` (decision 6). The model space is `selfAdjoint (Matrix ι ι ℝ)`, the
   symmetric matrices (the star of a real matrix is its transpose). Its norm
   comes from `open scoped Matrix.Norms.L2Operator`, as in Tau Ceti's
   `Geometry/Manifold/Instances/PositiveDefiniteMatrix.lean`. The smooth
   structure does not depend on that choice, but the instance has to name one.
6. **Two kinds of graph.** The milestone's graph of `A` is $\{(x,Ax)\}$, the
   submodule `StdSpace.graph A`. The chart points $\{(Sy,y)\}$ of decision 5
   are the submodule `StdSpace.graphY S`. Both are defined for every real
   matrix and are Lagrangian exactly when the matrix is symmetric. The first
   serves the statement, the second the charts, and the two transverse-chart
   facts are stated in the same form, one with each kind. Each kind is the
   image of the other under `TauCeti.GLSymplectic.symJ`, which sends
   `graph A` to `graphY (-A)`.
7. **Transitivity without Witt.** `DESIGN.md` names Tau Ceti's Witt theorem
   `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend` as the source of
   $\mathrm{Sp}$-transitivity. Transitivity of $\mathrm{U}(n)$ is proved here
   anyway, since the milestone asks for it, and $\mathrm{U}(n)\subset\mathrm{Sp}(2n)$
   through `TauCeti.GLSymplectic.ofUnitary`. That gives
   $\mathrm{Sp}$-transitivity directly, so Witt's theorem is not used.
8. **Comparison with `DESIGN.md`.** Every file in §6's list on `main`
   (after #67, #75 and #101) is kept, with the content §6 gives it: the type
   in `LinearAlgebra/Symplectic/Lagrangian/Basic.lean` and its topology in
   `Topology/Grassmannian/Lagrangian/Basic.lean`, `Frame.lean` with both
   graph statements, `Action.lean`, `Transverse.lean` and `Sum.lean` (the
   sum, the reindexing equivalence, their unitary frames and the
   equivariance) under `LinearAlgebra/Symplectic/Lagrangian/`,
   `Quotient.lean`, `Graph.lean` with both graph charts, the manifold file,
   `LinearAlgebra/TotallyReal/Euclidean.lean` with the range of
   `Matrix.lagrangianChart` and the example showing isotropy is needed,
   `Fibration.lean`, and `Topology/Grassmannian/Lagrangian/Sum.lean` with
   only the continuity of the sum and the reindexing homeomorphism. The
   direct sum of standard spaces is §1's `StdSpace.sumEquiv`, used as §1
   states it (after #63). One statement moves within the part:
   complementary iff disjoint, which §6 puts in `Transverse.lean`, is
   `isCompl_iff_disjoint` in `LinearAlgebra/Symplectic/Lagrangian/Basic.lean`,
   since it holds for a general `ω` and `Transverse.lean` is about
   `StdSpace ι`. Declarations about `StdSpace ι` alone
   (`StdSpace.complexEuclideanEquiv`, `StdSpace.swap`,
   `StdSpace.finSumIsometry`, the coordinate lemmas
   `StdSpace.x_piLpCongrLeft_sumCongr` and `StdSpace.y_piLpCongrLeft_sumCongr`,
   with their API) are added to part 1's `Standard/Basic.lean`; the section
   *Additions to Standard model's `Standard/Basic.lean`* lists them. The
   other departures are #79's,
   the issue that changes §6 to match: `Topology/Grassmannian/Lagrangian/Finite.lean`;
   the general files under `LinearAlgebra/Matrix/` (the real points of the
   unitary group, the complex frame facts and the dimension of the space of
   symmetric matrices); the route to transitivity of decision 7; and
   dropping `Matrix.lagrangianChartCLE`, which this design does not use.
   Two items of #79's list have lapsed: `Standard/Sum.lean`, which §1's
   `StdSpace.sumEquiv` replaces, and `Chart.lean`, since the chart file
   keeps §6's name `Graph.lean`. #79 says to follow the design as merged.

   This file does not edit `DESIGN.md`.
9. **Dimension zero.** For `ι` empty, `StdSpace ι` is zero, `ℒ ι` has one
   point, and $\mathrm{U}(0)$ and the model space are trivial. Every statement
   below holds with no case split, and the dimension formula gives $0$. No
   statement needs `Nonempty ι`.

## Files and their contents

### `LinearAlgebra/Matrix/UnitaryGroup/Real.lean`

The real points of the unitary group, that is, $\mathrm{O}(n)$ inside
$\mathrm{U}(n)$, as a subgroup of `unitaryGroup ι ℂ`. Tau Ceti has the same
group as a subgroup of `GL ι ℂ`:
`TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`
(`LinearAlgebra/Matrix/GeneralLinearGroup/Orthogonal/Unitary.lean`) says
that `GLOrthogonal ι ℂ ⊓ unitarySubgroup (GL ι ℂ)` is the image of the real
orthogonal group. This file carries that subgroup to `unitaryGroup ι ℂ`,
which the stabilizer and the fibration need.

- `Matrix.UnitaryGroup.realSubgroup (ι) : Subgroup (unitaryGroup ι ℂ)`, the
  image of `(GLOrthogonal ι ℂ).subgroupOf (unitarySubgroup (GL ι ℂ))` under
  Mathlib's `unitarySubgroupUnitsEquiv`.
- API: `mem_realSubgroup_iff_exists` (`U` is in it iff `U = O.map ofReal` for
  some `O ∈ Matrix.orthogonalGroup ι ℝ`), derived from
  `TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real` (Tau Ceti's
  `Matrix.exists_mem_orthogonalGroup_map_eq_of_mul_transpose_eq_one` may
  shorten it); `mem_realSubgroup_iff` (iff
  `(U : Matrix ι ι ℂ).map Complex.im = 0`); `map_ofReal_mem_realSubgroup`;
  `isClosed_realSubgroup`.

### `LinearAlgebra/Matrix/OfReal.lean`

Facts about real matrices read over `ℂ` through `map ofReal`, in the namespace
`Matrix`, next in spirit to Tau Ceti's
`Matrix.map_im_conjTranspose_mul_self_mul_map_ofReal`
(`LinearAlgebra/Matrix/OfReal.lean`), whose `Matrix.map_ofReal_mul` they use.
General lemmas, which the Siegel upper half space uses too:

- `Matrix.transpose_map_ofReal_mul_map_ofReal`:
  `(P.map ofReal)ᵀ * Q.map ofReal = (Pᵀ * Q).map ofReal`.
- `Matrix.conjTranspose_map_ofReal`: `(P.map ofReal)ᴴ = (P.map ofReal)ᵀ`.

Three facts about complex frames:

- `Matrix.map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq
  {X Y : Matrix m n ℝ} (h : Xᵀ * Y = Yᵀ * X)`: for
  `M = X.map ofReal + I • Y.map ofReal`, `(Mᴴ * M).map im = 0`.
- `Matrix.range_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ)`: the range of
  `toEuclideanLin (fromRows X Y)` is the image of
  `Matrix.realImage (X.map ofReal + I • Y.map ofReal)` under
  `TauCeti.complexToRealEuclidean ι`, read through `WithLp.equiv`.
- `Matrix.exists_det_sub_smul_ne_zero {X Y : Matrix ι ι ℝ}
  (h : (X.map ofReal + I • Y.map ofReal).det ≠ 0) : ∃ t : ℝ, (X - t • Y).det ≠ 0`:
  `t ↦ det (X - t Y)` is a real polynomial, nonzero at `t = -i`, so it is not
  identically zero (Mathlib's `Polynomial.funext`). `Transverse.lean` uses it
  for a common transverse Lagrangian.

### `LinearAlgebra/Matrix/SelfAdjoint.lean`

- `Matrix.finrank_selfAdjoint`, for a nontrivial commutative ring `R` with
  trivial star (`[CommRing R] [Nontrivial R] [StarRing R] [TrivialStar R]`),
  a finite `ι` and decidable equality:
  `Module.finrank R (selfAdjoint (Matrix ι ι R)) =
  Fintype.card ι * (Fintype.card ι + 1) / 2`. Tau Ceti already counts the
  symmetric bilinear forms on a finite free module,
  `LinearMap.BilinForm.finrank_symmSubmodule`
  (`LinearAlgebra/BilinearForm/Symmetric.lean`, which imports no measure
  theory), so the proof carries that count over. Mathlib's
  `LinearMap.BilinForm.toMatrix'` restricts to a linear equivalence from
  `LinearMap.BilinForm.symmSubmodule R (ι → R)` onto
  `selfAdjoint (Matrix ι ι R)`, by
  `LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm` and
  `Matrix.isHermitian_iff_isSymm`. The file makes it public, as
  `Matrix.symmSubmoduleEquivSelfAdjoint` (for decidable equality on `ι`),
  with `coe_symmSubmoduleEquivSelfAdjoint_apply` and
  `coe_symmSubmoduleEquivSelfAdjoint_symm_apply` (both `@[simp]`,
  by `rfl`).
  `LinearEquiv.finrank_eq` and `Module.finrank_fintype_fun_eq_card` finish
  it; `Nontrivial R` gives the `StrongRankCondition R` that the last lemma
  needs, and cannot be dropped: over the zero ring every `finrank` is `1`,
  while the formula gives `3` for `ι = Fin 2`. Its one definition is that
  equivalence.
  The milestone uses the case `R = ℝ`.

### `Analysis/InnerProductSpace/PiL2.lean`

A general fact about matrices acting on Euclidean space, beside Mathlib's
file of that name, in the namespace `Matrix`, over `RCLike 𝕜`:

- `Matrix.piLpCongrLeft_toEuclideanLin_apply (e : m ≃ n) (M : Matrix m m 𝕜) z`:
  `piLpCongrLeft 2 𝕜 𝕜 e (toEuclideanLin M z) =
  toEuclideanLin (reindex e e M) (piLpCongrLeft 2 𝕜 𝕜 e z)`.
  `LinearAlgebra/Symplectic/Lagrangian/Sum.lean` uses it for
  `reindex_unitaryFrame`.

### `Analysis/Matrix/EuclideanLin.lean`

A general fact about Tau Ceti's `Matrix.toEuclideanCLE`, beside Tau Ceti's
file of that name, in the namespace `Matrix`, over `RCLike 𝕜`:

- `Matrix.coe_toLinearEquiv_toEuclideanCLE (A : Matrix ι ι 𝕜) (hA : A.det ≠ 0)`
  (`@[simp]`): `((A.toEuclideanCLE hA).toLinearEquiv : _ →ₗ[𝕜] _) =
  A.toEuclideanLin`, the linear-map form of Tau Ceti's
  `Matrix.coe_toEuclideanCLE`. `Action.lean` uses it for
  `isLagrangian_map_toEuclideanLin` and `ℒ.coe_smul_eq_map_toEuclideanCLE`.

### `Analysis/Complex/Circle.lean`

A general fact about Tau Ceti's `TauCeti.circleEquivUnitary`, beside Tau
Ceti's file of that name, in the namespace `TauCeti`; it imports only Tau
Ceti:

- `TauCeti.circleEquivUnitary_smul` (`@[simp]`): for `[MulAction ℂ M]`,
  `circleEquivUnitary z • x = (z : ℂ) • x`. `Action.lean` uses it to compute
  the scalar unitary of `rotate`.

### `Analysis/Normed/Lp/PiLp.lean`

A general fact about Mathlib's `LinearIsometryEquiv.piLpCongrLeft`, in the
namespace `LinearIsometryEquiv`, beside Tau Ceti's file of that name
(`TauCeti/Analysis/Normed/Lp/PiLp.lean`, which has `piLpCongrLeft_refl`), its
natural upstream home:

- `LinearIsometryEquiv.piLpCongrLeft_trans (e : ι ≃ ι') (f : ι' ≃ ι'')`
  (`@[simp]`): `(piLpCongrLeft p 𝕜 E e).trans (piLpCongrLeft p 𝕜 E f) =
  piLpCongrLeft p 𝕜 E (e.trans f)`, the composition counterpart of Tau
  Ceti's `piLpCongrLeft_refl`. `LinearAlgebra/Symplectic/Lagrangian/Sum.lean`
  uses it for `reindex_trans`.

### `Topology/Algebra/Matrix/Realify.lean`

A general fact about Tau Ceti's `TauCeti.GLSymplectic`, in the namespace
`TauCeti.GLSymplectic`, beside Tau Ceti's file of that name, which defines
`TauCeti.GLSymplectic.ofUnitary` and `TauCeti.GLSymplectic.coe_ofUnitary`; it imports only Tau Ceti. Tau Ceti's
`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean` is no home
for it: Tau Ceti's `Topology/Algebra/Matrix/Realify.lean` imports that file,
so the lemma there could not see `TauCeti.GLSymplectic.ofUnitary`.

- `TauCeti.GLSymplectic.sum_ofUnitary (U : unitaryGroup ι ℂ)
  (U' : unitaryGroup κ ℂ)`: `sum (ofUnitary U, ofUnitary U') =
  ofUnitary (Matrix.UnitaryGroup.sum (U, U'))`, from
  `Matrix.realify_fromBlocks_zero`.
  `LinearAlgebra/Symplectic/Lagrangian/Sum.lean` uses it for
  `sum_unitaryFrame`.

### `Topology/Grassmannian/Tautological.lean`

A general fact about Tau Ceti's finite Grassmannian, beside Tau Ceti's file
of that name, in the namespace `TauCeti.finiteGrassmannian`, for any
`RCLike 𝕜`:

- `TauCeti.finiteGrassmannian.isClosedEmbedding_starProjection_toEuclidean`:
  `V ↦ V.toEuclidean.starProjection` is a closed embedding of
  `TauCeti.finiteGrassmannian 𝕜 r N` into the operators on `EuclideanSpace 𝕜 (Fin N)`.
  Tau Ceti's `TauCeti.finiteGrassmannian.continuous_starProjection_toEuclidean` gives continuity,
  `TauCeti.finiteGrassmannian.toEuclidean_injective` and `Submodule.starProjection_inj` injectivity,
  and `Continuous.isClosedEmbedding` concludes, since the source is compact
  and the target Hausdorff. `Finite.lean` uses it.

### Additions to *Standard model*'s `LinearAlgebra/Symplectic/Standard/Basic.lean`

Three declarations about the standard model alone, which this part needs and
part 1 lacks, in the namespace `SymplecticGeometry.StdSpace`, so that other parts
find them there.

- `StdSpace.complexEuclideanEquiv ι : EuclideanSpace ℂ ι ≃L[ℝ] StdSpace ι`,
  defined as `(PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)).trans
  (TauCeti.complexToRealEuclidean ι)`. It is how this part compares its
  subspaces of `StdSpace ι` with Tau Ceti's subspaces of
  `EuclideanSpace ℂ ι`. API:
  `complexEuclideanEquiv_def`, and the `@[simp]` lemmas
  `x_complexEuclideanEquiv : (complexEuclideanEquiv ι v).x = fun i ↦ (v i).re`
  and `y_complexEuclideanEquiv : (complexEuclideanEquiv ι v).y = fun i ↦ (v i).im`,
  from `x_complexToRealEuclidean` and `y_complexToRealEuclidean`. The `@[simp]` lemma
  `stdComplexStructure_complexEuclideanEquiv` says that it carries
  multiplication by `I` to `J₀`. Building issue 3 adds it.
- `StdSpace.swap ι : StdSpace ι ≃ₗ[ℝ] StdSpace ι`, the coordinate swap
  `(x, y) ↦ (y, x)`, the composite of `equivProd`, `LinearEquiv.prodComm` and
  `equivProd.symm`. It goes beside `equivProd`, before the file's
  `variable [Fintype ι]`, since it needs no finiteness. API: `swap_def`, and the
  `@[simp]` lemmas `x_swap`, `y_swap`, and their coordinate forms
  `swap_apply_inl : swap ι z (Sum.inl i) = z (Sum.inr i)` and `swap_apply_inr`
  (all four by `(rfl)`, so that `simp` pushes `swap` through `x_apply` and
  `y_apply`), `swap_swap`,
  `symm_swap`, and `map_swap_ker_x` and `map_swap_ker_y`, which say that it
  exchanges `LinearMap.ker StdSpace.x` and `LinearMap.ker StdSpace.y`. After
  `stdForm_apply`, the lemma `stdForm_swap` says that it reverses the
  sign of `ω₀`: `stdForm ι (swap ι z) (swap ι w) = -stdForm ι z w`.
- `StdSpace.finSumIsometry n : StdSpace (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + n))`,
  the relabelling of coordinates
  `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv`. It comes right
  after `sq_x_add_sq_y_le_norm_sq`, between the file's two
  `variable [Fintype ι]` lines. `Finite.lean` uses it to reach Tau
  Ceti's Grassmannian. API: `finSumIsometry_def`, and the `@[simp]` lemmas
  `finSumIsometry_apply : finSumIsometry n z k = z (finSumFinEquiv.symm k)`
  and `finSumIsometry_symm_apply :
  (finSumIsometry n).symm v i = v (finSumFinEquiv i)`.

This part also uses
`SymplecticGeometry.isSymplectomorphism_piLpCongrLeft_sumCongr` (`σ : ι ≃ κ`),
which is already in `Standard/Basic.lean`: the coordinate
permutation `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ)` carries
`stdForm ι` to `stdForm κ`. Beside it, building issue 11 added the
coordinates of that permutation, as two `@[simp]` lemmas in the namespace
`SymplecticGeometry.StdSpace`:
`x_piLpCongrLeft_sumCongr : x (piLpCongrLeft 2 ℝ ℝ (σ.sumCongr σ) z) = z.x ∘ σ.symm`
and `y_piLpCongrLeft_sumCongr`, the same for `y`.
`LinearAlgebra/Symplectic/Lagrangian/Sum.lean` uses them for
`reindex_horizontal` and `reindex_vertical`.

The direct sum of two models is §1's `StdSpace.sumEquiv ι κ : StdSpace (ι ⊕ κ)
≃L[ℝ] StdSpace ι × StdSpace κ`, in this same file, with its lemma that it
carries `stdForm (ι ⊕ κ)` to `(stdForm ι).prod (stdForm κ)`, and its lemma
in `Standard/Matrix.lean` that it conjugates
`Matrix.toEuclideanLin (Matrix.symplecticSum A B)` to the product of the
maps of `A` and `B`. Building issue 11 added all three to
`Standard/Basic.lean` and `Standard/Matrix.lean` (merged, #232), and
*Symplectic vector bundles* uses them as they are.

### `LinearAlgebra/Symplectic/Lagrangian/Basic.lean`

The type, for a general symplectic vector space, with no topology.

- `structure LagrangianGrassmannian (ω : TauCeti.SymplecticForm V) extends
  Submodule ℝ V` with `isLagrangian' : ω.IsLagrangian toSubmodule`.
- API: the `SetLike` instance, `@[ext] ext`, `toSubmodule_injective`,
  `isLagrangian (Λ) : ω.IsLagrangian Λ`, `mem_toSubmodule`, `coe_mk`
  (`@[simp]`), `mk_toSubmodule`.
- `ℒ.isCompl_iff_disjoint`: for two Lagrangians, being complementary is the
  same as meeting only in zero, by Mathlib's `Submodule.isCompl_iff_disjoint`
  and `TauCeti.SymplecticForm.IsLagrangian.two_mul_finrank`. It is stated for a general `ω` on a
  finite-dimensional `V`.

### `LinearAlgebra/Symplectic/Lagrangian/Frame.lean`

Lagrangian frames on `StdSpace ι`, pure linear algebra. Namespace
`SymplecticGeometry` (and `SymplecticGeometry.StdSpace` for the graphs).

- `StdSpace.graph (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι)`, defined as
  the image of `A.mulVecLin.graph` under `(StdSpace.equivProd ι).symm`
  (`Matrix.mulVecLin` rather than `Matrix.toLin'`, which is the same map but
  needs `DecidableEq ι`).
  API: `StdSpace.mem_graph_iff : z ∈ graph A ↔ z.y = A *ᵥ z.x` (`@[simp]`),
  and `StdSpace.graph_injective`.
- `StdSpace.graphY (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι)`, the graph
  over the `y` coordinate, defined as the image `(graph A).map (StdSpace.swap ι)`
  of `graph A` under the coordinate swap of `Standard/Basic.lean`
  (`graphY_def`, by `(rfl)`). API: `StdSpace.mem_graphY_iff : z ∈ graphY A ↔ z.x = A *ᵥ z.y` (`@[simp]`),
  `StdSpace.graphY_injective`, and `StdSpace.map_symJ_graph`, saying that
  `TauCeti.GLSymplectic.symJ` sends `graph A` to `graphY (-A)`.
- Both graphs are complementary to the coordinate subspace they are graphs
  over, for every `A`, symmetric or not:
  `StdSpace.isCompl_graph_ker_x : IsCompl (graph A) (LinearMap.ker StdSpace.x)`
  and
  `StdSpace.isCompl_graphY_ker_y : IsCompl (graphY A) (LinearMap.ker StdSpace.y)`.
  Every `z` is `(z.x, A z.x) + (0, z.y - A z.x)`, and a vector of the graph
  with `x = 0` is zero.
- The coordinate swap `StdSpace.swap ι` of `Standard/Basic.lean` carries
  `graph A` to `graphY A` by the definition (`graphY_def`), and exchanges the
  kernels of `x` and `y` (`map_swap_ker_x`, `map_swap_ker_y`). So
  `graphY_injective`, `isCompl_graphY_ker_y` and
  `exists_eq_graphY_of_isCompl_ker_y` are not proved again: they are
  `graph_injective`, `isCompl_graph_ker_x` and
  `exists_eq_graph_of_isCompl_ker_x` transported along `swap`
  (`Submodule.map_injective_of_injective`, `OrderIso.isCompl` with
  `Submodule.orderIsoMapComap`; for the last, `swap` is an involution, by
  `symm_swap`).
- The comparison with Tau Ceti's complex picture, through
  `StdSpace.complexEuclideanEquiv ι` (written `ε` here). Then
  `StdSpace.map_realSubspace :
  (TauCeti.realSubspace ι).map ε = LinearMap.ker StdSpace.y` and
  `StdSpace.map_lagrangianChart (S : Matrix ι ι ℝ) :
  (Matrix.lagrangianChart S).map ε = StdSpace.graphY S`, both from
  `x_complexEuclideanEquiv`, `y_complexEuclideanEquiv` and Tau Ceti's
  `Matrix.mem_lagrangianChart`. Also
  `stdForm_apply_eq_im_inner (v w : EuclideanSpace ℂ ι) :
  stdForm ι (ε v) (ε w) = (inner ℂ v w).im`, from `stdForm_apply` and
  `PiLp.inner_apply`.
- `isLagrangian_range_fromRows_iff (X Y : Matrix ι ι ℝ) :
  (stdForm ι).IsLagrangian (LinearMap.range (Matrix.toEuclideanLin (Matrix.fromRows X Y)))
  ↔ (Matrix.fromRows X Y).rank = Fintype.card ι ∧ Xᵀ * Y = Yᵀ * X`.
  The `@[simp]` lemmas `StdSpace.x_toEuclideanLin_fromRows` and
  `StdSpace.y_toEuclideanLin_fromRows` give the coordinates `X u` and `Y u`
  of the column combination `Z u`; from them and `stdForm_apply`,
  `stdForm_toEuclideanLin_fromRows` computes $\omega_0(Zu,Zv)=u^T(X^TY-Y^TX)v$,
  and `isIsotropic_range_fromRows_iff` reads isotropy of the range as
  `Xᵀ * Y = Yᵀ * X`. The rank is the dimension of the range by Tau Ceti's
  `Matrix.rank_eq_finrank_range_toEuclideanLin`, and a Lagrangian is an
  isotropic subspace of half dimension by
  `isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq` of
  `LinearAlgebra/Symplectic/Subspace.lean` (#64).
- `StdSpace.range_toEuclideanLin_fromRows_one_eq_graph :
  LinearMap.range (toEuclideanLin (fromRows 1 A)) = StdSpace.graph A` and
  `StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY`, the same for
  `fromRows A 1` and `graphY A`, derived from the first through `swap`: the
  `@[simp]` lemmas `StdSpace.swap_toEuclideanLin_fromRows` (pointwise) and
  `StdSpace.map_swap_range_toEuclideanLin_fromRows` say that `swap` carries
  the columns of `fromRows X Y` to those of `fromRows Y X`. With `coe_ofFrame`,
  they read the graph of a symmetric matrix as an `ofFrame`, for the charts.
  `StdSpace.range_toEuclideanLin_fromRows_eq_graph`, the mirror of
  `StdSpace.range_toEuclideanLin_fromRows_eq_graphY`: for invertible `X`,
  `fromRows X Y` spans `graph (Y * X⁻¹)`, through `swap`.
- `ℒ.ofFrame (X Y : Matrix ι ι ℝ)
  (h : (stdForm ι).IsLagrangian (range (toEuclideanLin (fromRows X Y)))) : ℒ ι`,
  the Lagrangian that the frame spans, with `coe_ofFrame` (`@[simp]`): its
  submodule is the range of `toEuclideanLin (fromRows X Y)`, and
  `mem_ofFrame_iff` (`@[simp]`), membership in that range. This is the
  constructor of G6; `isLagrangian_range_fromRows_iff` turns the rank and
  symmetry conditions into `h`. Every Lagrangian spanned by a frame, in this
  part, is written `ofFrame X Y h`, never as an anonymous pair.
- `ℒ.finrank_eq_card (Λ : ℒ ι) : finrank ℝ Λ = Fintype.card ι`, from
  `TauCeti.SymplecticForm.IsLagrangian.two_mul_finrank` and `finrank_stdSpace`, for every use of the
  dimension of a Lagrangian of `StdSpace ι`. With it,
  `ℒ.injective_toEuclideanLin_of_range_eq`: a matrix `Z` whose columns span a
  Lagrangian is injective, as `Maslov/Path/RegularPieces.lean` uses.
- `isLagrangian_map_swap_iff` (`@[simp]`): `L.map (swap ι)` is Lagrangian for
  `ω₀` iff `L` is. Since `stdForm_swap` says that `swap` multiplies `ω₀` by
  `-1`, this is the case `e = swap`, `c = -1` of
  `TauCeti.SymplecticForm.isLagrangian_map_iff_of_apply_eq_mul` in `Subspace.lean`:
  a linear equivalence that scales the forms by a constant `c ≠ 0` maps
  Lagrangians onto Lagrangians. That lemma is
  `TauCeti.SymplecticForm.isLagrangian_map_transport_iff` after `TauCeti.SymplecticForm.isLagrangian_rescale_iff`.
- `isLagrangian_graph_iff (A : Matrix ι ι ℝ) :
  (stdForm ι).IsLagrangian (StdSpace.graph A) ↔ A.IsSymm`. Under
  `(equivProd ι).symm`, `ω₀` is the standard pairing of `(ι → ℝ) × (ι → ℝ)`;
  the proof transports along it (`TauCeti.SymplecticForm.isLagrangian_map_transport_iff`), applies
  Tau Ceti's `TauCeti.SymplecticForm.isLagrangian_graph_iff_of_pairing`, and recognizes the
  resulting condition as Mathlib's `Matrix.isSymm_toBilin'_iff_isSymm`.
  `isLagrangian_graphY_iff`, the same for `graphY A`, follows from it
  through `graphY_def` and `isLagrangian_map_swap_iff`. Neither is derived
  from the frame criterion.
- `det_ne_zero_of_isLagrangian_range_fromRows`: the complex frame of a
  Lagrangian frame is invertible. The Lagrangian range is maximal totally
  real for `J₀` (`TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_compatible` with
  `stdForm_compatible`). By `StdSpace.range_toEuclideanLin_fromRows_eq_map_realImage`
  it is the image under `complexEuclideanEquiv`, which intertwines multiplication by
  `I` with `J₀` (`stdComplexStructure_complexEuclideanEquiv`), of `(X + i Y).realImage`;
  so that real image is maximal totally real (`LinearEquiv.isMaximalTotallyReal_map_iff`), and Tau Ceti's
  `isMaximalTotallyReal_realImage_iff` gives `det (X + i Y) ≠ 0`. With
  `Matrix.map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq`
  (a corollary of `Matrix.map_im_conjTranspose_mul_self`,
  `Im ((X + i Y)ᴴ (X + i Y)) = Xᵀ Y - Yᵀ X`), this is the hypothesis of Tau
  Ceti's `realOrthonormalize_mem_unitaryGroup`.
- `isLagrangian_range_fromRows_one (hA : A.IsSymm)`: `fromRows A 1` is a
  Lagrangian frame, since it spans `graphY A`
  (`StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY`, `isLagrangian_graphY_iff`).
- `StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian`:
  a Lagrangian frame `fromRows X Y` spans a subspace meeting
  `LinearMap.ker StdSpace.x` only in `0` iff `X` is invertible. It is
  `disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian`
  transported along `swap` (`map_swap_range_toEuclideanLin_fromRows`,
  `map_swap_ker_x`), and is used by the crossing-form formula of
  *Maslov index*.
- Transverse subspaces are graphs, stated for submodules. The horizontal and
  vertical subspaces are `LinearMap.ker StdSpace.y` and
  `LinearMap.ker StdSpace.x`, so they need no new names here.
  - `StdSpace.exists_eq_graph_of_isCompl_ker_x` and
    `StdSpace.exists_eq_graphY_of_isCompl_ker_y`: any subspace `L`
    complementary to `LinearMap.ker StdSpace.x` (resp. `StdSpace.y`) is
    `graph A` (resp. `graphY A`) for some `A`. These are the converses of
    `isCompl_graph_ker_x` and `isCompl_graphY_ker_y`. The second is the first
    transported along `swap`, as above. For the first, the projection to `x`
    is bijective on `L`: its kernel on `L` is zero, and `L` plus
    the kernel is everything. So Mathlib's `Submodule.exists_eq_graph`
    applies to the image of `L` in `(ι → ℝ) × (ι → ℝ)`, and
    `Submodule.map_symm_eq_iff` brings the graph back to `StdSpace ι`.
  - `exists_eq_graph_of_isCompl`: a Lagrangian `L` complementary to
    `LinearMap.ker StdSpace.x` satisfies `∃ S, S.IsSymm ∧ L = StdSpace.graph S`.
  - `exists_eq_graphY_of_isCompl`: a Lagrangian `L` complementary to
    `LinearMap.ker StdSpace.y` satisfies `∃ S, S.IsSymm ∧ L = StdSpace.graphY S`.

  In each case the previous item gives the matrix, and
  `isLagrangian_graph_iff` (resp. `isLagrangian_graphY_iff`) makes it
  symmetric.

### `LinearAlgebra/Symplectic/Lagrangian/Action.lean`

The actions of $\mathrm{Sp}(2n)$ and $\mathrm{U}(n)$ and the unitary frames,
as algebra. It uses the matrix dictionary of *Standard model*
(`LinearAlgebra/Symplectic/Standard/Matrix.lean`, #62):
`mem_symplecticGroup_iff_forall_stdForm`, which reads membership of a
matrix in `Matrix.symplecticGroup` as invariance of `stdForm` under
`toEuclideanLin`, and `TauCeti.conj_complexToRealEuclidean_toLin'`, which
turns a complex matrix acting on `ι → ℂ` into its realification acting on
`StdSpace ι`. With Tau Ceti's `TauCeti.GLSymplectic.coe_ofUnitary` (the matrix of
`TauCeti.GLSymplectic.ofUnitary U` is `(U : Matrix ι ι ℂ).realify`), the second relates the
unitary action to Tau Ceti's `Matrix.realImage`.

- `instance : MulAction (GLSymplectic ι ℝ) (ℒ ι)`, with
  `coe_smul : ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) = Λ.map (Matrix.toEuclideanLin g)`
  (`@[simp]`), and `coe_smul_eq_map_toEuclideanCLE`, the same subspace as the
  image of `Λ` under the linear equivalence
  `(Matrix.toEuclideanCLE g _).toLinearEquiv`, from
  `Matrix.coe_toLinearEquiv_toEuclideanCLE`. The result is Lagrangian by
  `TauCeti.SymplecticForm.isLagrangian_map_iff_of_apply_eq_mul`
  (`Subspace.lean`) with `c = 1`, the map `toEuclideanLin g` preserving `ω₀` by
  `mem_symplecticGroup_iff_forall_stdForm`. On a frame,
  `coe_smul_of_coe_eq`: if `Λ` is spanned by the columns of `Z`, then
  `g • Λ` is spanned by those of `g * Z`; `coe_smul_graphY`
  (`Transverse.lean`, with `coe_ofFrame`) and the frame of
  `g • unitaryFrame U` (`Quotient.lean`, with `coe_unitaryFrame`) follow
  from it.
- `instance : MulAction (unitaryGroup ι ℂ) (ℒ ι)`, the action through the
  monoid homomorphism `TauCeti.GLSymplectic.ofUnitary` (`MulAction.compHom`),
  with `unitary_smul_def : U • Λ = ofUnitary U • Λ` and its reverse
  `ofUnitary_smul : ofUnitary U • Λ = U • Λ` (`@[simp]`), so that `U • Λ` is the
  simp normal form.
- `ℒ.horizontal ι`, `ℒ.vertical ι : ℒ ι`: $\{y=0\}$ and $\{x=0\}$ (G1). Their
  submodules are `LinearMap.ker StdSpace.y` and `LinearMap.ker StdSpace.x`
  (`coe_horizontal`, `coe_vertical`). They are Lagrangian as `graph 0` and
  `graphY 0` (`StdSpace.graph_zero`, `StdSpace.graphY_zero` of `Frame.lean`),
  by `isLagrangian_graph_iff` and `isLagrangian_graphY_iff`. API:
  `mem_horizontal_iff`, `mem_vertical_iff` (`@[simp]`),
  `isCompl_horizontal_vertical`, and
  `symJ_smul_horizontal : TauCeti.GLSymplectic.symJ ι ℝ • horizontal ι = vertical ι`.
  The charts are centred at `vertical ι`. A unitary `U` with
  `U • vertical ι = Λ` is `MulAction.exists_smul_eq (unitaryGroup ι ℂ)
  (vertical ι) Λ`, from the `IsPretransitive` instance below; no lemma
  restates it.
- `ℒ.unitaryFrame (U : unitaryGroup ι ℂ) : ℒ ι := U • horizontal ι` (G2),
  with:
  - `unitaryFrame_def`;
  - `coe_unitaryFrame`: the range of
    `toEuclideanLin (fromRows (U.map re) (U.map im))`, which is the image
    of `Matrix.realImage U` under `StdSpace.complexEuclideanEquiv ι`. Both come from
    `TauCeti.GLSymplectic.coe_ofUnitary` and `TauCeti.conj_complexToRealEuclidean_toLin'`: the columns
    of `realify U` indexed by `inl` are `fromRows (U.map re) (U.map im)`;
  - `unitaryFrame_one` and `unitaryFrame_mul` (both `@[simp]`):
    `unitaryFrame (U * U') = U • unitaryFrame U'`.
- `ℒ.unitaryOfFrame h : unitaryGroup ι ℂ`, for
  `h : (stdForm ι).IsLagrangian (range (toEuclideanLin (fromRows X Y)))`:
  the `realOrthonormalize` of `X + i Y`, made a unit by
  `GeneralLinearGroup.mkOfDetNeZero` and
  `det_ne_zero_of_isLagrangian_range_fromRows` (`Frame.lean`), unitary by
  `realOrthonormalize_mem_unitaryGroup` (`coe_unitaryOfFrame`). Then
  `unitaryFrame_unitaryOfFrame : unitaryFrame (unitaryOfFrame h) = ofFrame X Y h`
  (`@[simp]`), by `realImage_realOrthonormalize`. Every passage from a
  Lagrangian frame to a unitary frame goes through this construction; its
  continuity in the frame is `continuous_unitaryOfFrame` (`Quotient.lean`).
- `ℒ.unitaryFrame_surjective`: transitivity of $\mathrm{U}(n)$. Take any basis
  of `Λ` as a frame (`Frame.lean`) and apply `unitaryFrame_unitaryOfFrame`. It gives the
  instances `MulAction.IsPretransitive (unitaryGroup ι ℂ) (ℒ ι)` and
  `MulAction.IsPretransitive (GLSymplectic ι ℝ) (ℒ ι)`. Transitivity is then
  Mathlib's `MulAction.exists_smul_eq`, with no restatement here.
- `ℒ.unitaryFrame_eq_unitaryFrame_iff :
  unitaryFrame U = unitaryFrame U' ↔ U⁻¹ * U' ∈ Matrix.UnitaryGroup.realSubgroup ι`,
  from `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal`,
  `Matrix.realImage_map_ofReal` and `mem_realSubgroup_iff_exists`. Its
  corollary is
  `ℒ.stabilizer_horizontal :
  MulAction.stabilizer (unitaryGroup ι ℂ) (horizontal ι) = Matrix.UnitaryGroup.realSubgroup ι`.
- Supporting statements of the file: `isLagrangian_map_toEuclideanLin` (in
  `SymplecticGeometry`), the image of a Lagrangian under a matrix
  `A ∈ Matrix.symplecticGroup ι ℝ`, which the `smul` instance applies through
  `TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup`; and, in `ℒ.`, `coe_unitary_smul`,
  `coe_unitaryFrame_eq_map` (the second description of `coe_unitaryFrame`),
  `finrank_unitaryFrame_inf_horizontal` (`finrank (unitaryFrame U ⊓ V₀)` is the
  dimension of `U.realImage ⊓ realSubspace ι`) and
  `unitaryFrame_eq_horizontal_iff`, from which both
  `unitaryFrame_eq_unitaryFrame_iff` and `stabilizer_horizontal` follow.
- Supporting statements placed elsewhere. In `Standard/Matrix.lean`:
  `StdSpace.complexEuclideanEquiv_toEuclideanCLM` (through
  `complexEuclideanEquiv ι`, a complex matrix acts as its realification). In
  `Frame.lean`: `StdSpace.map_realImage`
  (`A.realImage.map ε = (LinearMap.ker y).map (toEuclideanLin A.realify)`),
  `StdSpace.range_toEuclideanLin_fromRows_eq_map_realImage` (the span of
  `fromRows X Y` is `(X + i Y).realImage` carried by `ε`), `StdSpace.graph_zero`
  and `StdSpace.graphY_zero`. In `Matrix/UnitaryGroup/Real.lean`:
  `Matrix.UnitaryGroup.map_re_conjTranspose_mul_self` (`Re (Uᴴ U) = 1`).

### `LinearAlgebra/Symplectic/Lagrangian/Transverse.lean`

Chart points and transverse pairs, as algebra: G7–G9.

- `ℒ.graphY (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι`, whose submodule is
  `StdSpace.graphY S` (`coe_graphY`): the points of the basic chart. API:
  `mem_graphY_iff` (`@[simp]`); `coe_graphY_eq_map`, the image of Tau
  Ceti's `Matrix.lagrangianChart S` under `complexEuclideanEquiv ι`, which
  is `StdSpace.map_lagrangianChart`; `graphY_injective`; `graphY_zero`,
  which is the vertical subspace; `graphY_eq_ofFrame`, saying
  `graphY S = ofFrame S 1 (isLagrangian_range_fromRows_one hS)`, `hS` the
  symmetry of `S`, for the Lagrangian frame `fromRows S 1`, whose span is
  `StdSpace.graphY S` (`StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY`);
  and `graphY_eq_unitaryFrame`, saying
  `graphY S = unitaryFrame (unitaryOfFrame (isLagrangian_range_fromRows_one hS))`,
  the unitary frame of the complex frame `S + i·1`. It follows from
  `graphY_eq_ofFrame` by `unitaryFrame_unitaryOfFrame` (`Action.lean`).
  `continuous_graphY` (`Graph.lean`) also goes through `graphY_eq_ofFrame`.
- `ℒ.graph (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι`, whose submodule is
  `StdSpace.graph S` (`coe_graph`): the points of the second chart.
  API: `mem_graph_iff` (`@[simp]`), `graph_injective`,
  `graph_zero` (the horizontal subspace), and
  `symJ_smul_graph : symJ ι ℝ • graph S = graphY (-S)`
  (from `map_symJ_graph`).
- The two transverse-chart facts, in the same form:
  - `ℒ.isCompl_horizontal_iff : IsCompl (Λ : Submodule ℝ _) (horizontal ι) ↔
    ∃ S, S.IsSymm ∧ (Λ : Submodule ℝ _) = StdSpace.graphY S`;
  - `ℒ.isCompl_vertical_iff : IsCompl (Λ : Submodule ℝ _) (vertical ι) ↔
    ∃ S, S.IsSymm ∧ (Λ : Submodule ℝ _) = StdSpace.graph S`.

  The forward directions are `exists_eq_graphY_of_isCompl` and
  `exists_eq_graph_of_isCompl`. Their corollaries
  `ℒ.range_graphY : Set.range graphY =
  {Λ | IsCompl (Λ : Submodule ℝ _) (horizontal ι)}` and
  `ℒ.range_graph : Set.range graph =
  {Λ | IsCompl (Λ : Submodule ℝ _) (vertical ι)}` are the sources of the
  two graph charts.
- `ℒ.exists_isCompl_isCompl (Λ Λ' : ℒ ι) :
  ∃ Λ'' : ℒ ι, IsCompl (Λ'' : Submodule ℝ _) Λ ∧ IsCompl (Λ'' : Submodule ℝ _) Λ'`.
  Move `Λ` to the horizontal subspace by a unitary matrix, and write
  `Λ' = unitaryFrame (X + iY)`. The point `graphY ⟨t • 1, _⟩` is
  transverse to `Λ'` iff `det (X - t • Y) ≠ 0`. That determinant is a real
  polynomial in `t` whose value at `t = i` is $\det\overline{(X+iY)}\neq0$, so
  some real `t` is not a root.
- `ℒ.exists_smul_eq_horizontal_vertical {Λ Λ' : ℒ ι}
  (h : IsCompl (Λ : Submodule ℝ _) Λ') :
  ∃ g : GLSymplectic ι ℝ, g • horizontal ι = Λ ∧ g • vertical ι = Λ'`.
  Move `Λ` to the horizontal subspace by a unitary matrix. Then `Λ'` is
  `graphY S`, and the shear `fromBlocks 1 S 0 1`, symplectic by
  Tau Ceti's `SymplecticGroup.fromBlocks_upper_mem` since `S` is symmetric
  and lifted to `TauCeti.GLSymplectic ι ℝ` by
  `(TauCeti.GLSymplectic.mulEquivSymplecticGroup ι ℝ).symm`, fixes the
  horizontal subspace and carries the vertical one to `Λ'`.
- Supporting statements: `ℒ.isCompl_smul_iff` (an element of
  `TauCeti.GLSymplectic ι ℝ` preserves complementarity of Lagrangians, through
  `Submodule.orderIsoMapComap` after `coe_smul_eq_map_toEuclideanCLE`), which
  both transverse-pair results use; and
  `ℒ.finrank_smul_inf_smul` (it keeps `finrank (Λ ⊓ Λ')`), which
  `Maslov/Path/Naturality.lean` uses; its unitary form
  `ℒ.finrank_unitary_smul_inf_smul`, and `ℒ.finrank_inf_unitaryFrame`
  (`finrank (Λ ⊓ unitaryFrame U) = finrank ((U⁻¹ • Λ) ⊓ V₀)`), which
  `Maslov/Path/Naturality.lean` uses, and so does the zero axiom of *Maslov
  index* (`Maslov/Path/Basic.lean`), with `finrank_unitaryFrame_inf_horizontal`
  of `Lagrangian/Action.lean`.

### `LinearAlgebra/TotallyReal/Euclidean.lean`

Beside Tau Ceti's file of that name, in the namespace `Matrix`: the
surjectivity that Tau Ceti lacks next to `Matrix.lagrangianChart_injective`
and `Matrix.lagrangianChart_inf_realSubspace`, in Tau Ceti's terms. Write
`J := (LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ`.

- `Matrix.exists_isSymm_eq_lagrangianChart {V : Submodule ℝ (EuclideanSpace ℂ n)}
  (hV : TauCeti.IsMaximalTotallyReal J V)
  (hiso : ∀ v ∈ V, ∀ w ∈ V, (inner ℂ v w).im = 0)
  (hreal : V ⊓ TauCeti.realSubspace n = ⊥) :
  ∃ S : Matrix n n ℝ, S.IsSymm ∧ V = S.lagrangianChart`.
  Its image `V.map (StdSpace.complexEuclideanEquiv n)` is isotropic for `stdForm` by
  `stdForm_apply_eq_im_inner`, and has dimension `n` by Tau Ceti's
  `TauCeti.IsMaximalTotallyReal.two_mul_finrank_eq` (`J` is injective), so it is
  Lagrangian. It meets `LinearMap.ker StdSpace.y = (realSubspace n).map (complexEuclideanEquiv n)`
  (`StdSpace.map_realSubspace`) only in zero, so the two are complementary
  by dimension. Then `exists_eq_graphY_of_isCompl` gives `S`, and
  `StdSpace.map_lagrangianChart` with the injectivity of this map
  gives `V = S.lagrangianChart`.
- The isotropy hypothesis is needed, and the file shows it by an `example`:
  for `n = Fin 2` and `S = !![0, 1; 0, 0]`, `det (S + i·1) = -1 ≠ 0`, so
  `S.lagrangianChart` is maximal totally real (`lagrangianChart_def` and
  Tau Ceti's `isMaximalTotallyReal_realImage`) and meets `TauCeti.realSubspace (Fin 2)` only in
  zero (`lagrangianChart_inf_realSubspace`), but it is not
  `T.lagrangianChart` for any symmetric `T`, by `lagrangianChart_inj`,
  since `S` is not symmetric.

### `Topology/Grassmannian/Lagrangian/Basic.lean`

The topology of the type, for a general symplectic inner product space of
finite dimension.

- Under `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]`:
  - `instance : TopologicalSpace (LagrangianGrassmannian ω)`, induced by
    `starProjection`;
  - `isEmbedding_starProjection`, `continuous_starProjection`, and
    `continuous_iff_continuous_starProjection` (a map into it is continuous
    iff its projections are);
  - `instance : T2Space`.

### `Topology/Grassmannian/Lagrangian/Quotient.lean`

The topology of `ℒ ι` in terms of unitary frames.

- `ℒ.continuous_unitaryFrame`: the projection is $R P_0 R^T$ with
  `R = Matrix.realify U`, by `TauCeti.GLSymplectic.coe_ofUnitary` and
  `TauCeti.conj_complexToRealEuclidean_toLin'` (`Action.lean`), with Tau
  Ceti's `LinearIsometryEquiv.conjStarAlgEquiv_starProjection` for the
  projection onto the image of a subspace under a unitary operator.
- `instance : CompactSpace (ℒ ι)`, as the image of a compact space.
- `ℒ.isQuotientMap_unitaryFrame` and `ℒ.isOpenQuotientMap_unitaryFrame`. The
  map is open because it is the orbit map of a group action up to the
  homeomorphism below. A map out of `ℒ ι` is continuous when its composite
  with `unitaryFrame` is, by `isQuotientMap_unitaryFrame.continuous_iff`.
- `ℒ.quotientHomeomorph : unitaryGroup ι ℂ ⧸ realSubgroup ι ≃ₜ ℒ ι`, Tau
  Ceti's `TauCeti.quotientStabilizerHomeomorph (unitaryGroup ι ℂ)
  (horizontal ι) continuous_unitaryFrame`, composed with the homeomorphism of
  quotients that `stabilizer_horizontal` gives, Mathlib's
  `Homeomorph.Quotient.congrRight`. Tau Ceti builds
  `TauCeti.quaternionUnitarySphereQuotientHomeomorph` the same way
  (`Topology/Algebra/Quaternion/Symplectic/FirstColumn.lean`).
  `quotientHomeomorph_mk` (`@[simp]`, the value at `U` is `unitaryFrame U`)
  follows from Tau Ceti's `Homeomorph.Quotient.congrRight_mk` and
  `TauCeti.quotientStabilizerHomeomorph_mk`.
  This is the book's $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$.
- `instance : ContinuousSMul (GLSymplectic ι ℝ) (ℒ ι)` and
  `instance : ContinuousSMul (unitaryGroup ι ℂ) (ℒ ι)` (G4). Use
  `IsOpenQuotientMap.prodMap` with the identity on `TauCeti.GLSymplectic ι ℝ`. The
  composite `(g, U) ↦ g • unitaryFrame U` is the Lagrangian spanned by the
  horizontal columns of `g * realify U` (the matrix of `TauCeti.GLSymplectic.ofUnitary U` is
  `realify U` by `TauCeti.GLSymplectic.coe_ofUnitary`), and it is continuous by
  `continuous_ofFrame`: the Lagrangian `ofFrame (X t) (Y t) (h t)` spanned by a
  continuous family of Lagrangian frames is `unitaryFrame (unitaryOfFrame (h t))`
  (`unitaryFrame_unitaryOfFrame`), continuous by `continuous_unitaryOfFrame`
  (`coe_unitaryOfFrame` and `continuous_realOrthonormalize`) and
  `continuous_unitaryFrame`. The unitary instance follows by
  `TauCeti.GLSymplectic.continuous_ofUnitary`.
- `ℒ.rotationPath Λ ε : Path Λ (rotate ε Λ)`, `s ↦ rotate (ε * s) Λ`, with
  `rotationPath_apply` (`@[simp]`), next to `continuous_rotate`, so that
  `Maslov/Basic.lean` builds `halfTurnLoop` from it.

### `Topology/Grassmannian/Lagrangian/Finite.lean`

The comparison with Tau Ceti's Grassmannian, for `ι = Fin n`.

- `ℒ.toFiniteGrassmannian : ℒ (Fin n) → TauCeti.finiteGrassmannian ℝ n (n + n)`,
  the image under `StdSpace.finSumIsometry n : StdSpace (Fin n) ≃ₗᵢ[ℝ]
  EuclideanSpace ℝ (Fin (n + n))` (of `Standard/Basic.lean`), followed by
  `WithLp.linearEquiv 2 ℝ (Fin (n + n) → ℝ)`. API:
  `coe_toFiniteGrassmannian` (`@[simp]`, by `(rfl)`);
  `toEuclidean_toFiniteGrassmannian` (`@[simp]`: read in
  `EuclideanSpace ℝ (Fin (n + n))`, the image is the map of `Λ` along
  `finSumIsometry n`);
  `starProjection_toEuclidean_toFiniteGrassmannian` (the projection onto the
  image is the projection onto `Λ` conjugated by `finSumIsometry n`, through
  `ContinuousLinearEquiv.arrowCongr`, from
  `Submodule.starProjection_map_apply`); `toFiniteGrassmannian_injective`
  and `toFiniteGrassmannian_inj` (`@[simp]`).
- `ℒ.isEmbedding_toFiniteGrassmannian`, with
  `ℒ.continuous_toFiniteGrassmannian` (`@[fun_prop]`), and
  `ℒ.range_toFiniteGrassmannian` (the subspaces whose pull-back along
  `finSumIsometry n` is Lagrangian). So `ℒ (Fin n)` has the subspace
  topology of `TauCeti.finiteGrassmannian`. The proof is as in decision 2, through
  `TauCeti.finiteGrassmannian.isClosedEmbedding_starProjection_toEuclidean`.
- `ℒ.isClosedEmbedding_toFiniteGrassmannian`: the embedding is closed, since
  it is continuous and injective, `ℒ (Fin n)` is compact and
  `TauCeti.finiteGrassmannian` is Hausdorff. `Quotient.lean` is imported only for the
  instance `CompactSpace (ℒ (Fin n))`, which the closedness of the image needs
  and the embedding itself does not.

### `Topology/Grassmannian/Lagrangian/Graph.lean`

The two graph charts of `DESIGN.md` §6, as partial homeomorphisms. The model
is Tau Ceti's `Topology/Grassmannian/Graph.lean`, which does the same for
`TauCeti.finiteGrassmannian`; the building issue credits it.

- `ℒ.continuous_graphY`, from `continuous_ofFrame` (`Quotient.lean`)
  for the frame `fromRows S 1`, which spans `graphY S`.
- `ℒ.unitaryFrame_eq_graphY_iff`: `unitaryFrame U = graphY S` iff
  `U.map im` is invertible and `U.map re * (U.map im)⁻¹ = S`, the form of
  `TauCeti.finiteGrassmannian.frameSpan_eq_graph_iff` for unitary frames. It is
  `eq_graphY_iff_of_coe_eq` (`Transverse.lean`, for any Lagrangian spanned
  by a frame `fromRows X Y`) applied to `coe_unitaryFrame U`.
- `ℒ.isOpenEmbedding_graphY`: `graphY` is an open embedding. The preimage
  under the open quotient map `unitaryFrame` of the image of an open set is
  open, by the previous item.
- `ℒ.isOpen_setOf_isCompl (Λ₀ : ℒ ι) : IsOpen {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ _) Λ₀}`.
  For `Λ₀` horizontal, it is the range of `graphY`. Translate for general
  `Λ₀` by the symplectic action (`isCompl_smul_iff`).
- `ℒ.graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))`,
  the basic chart, the inverse of the open embedding `graphY`, with source
  `{Λ | IsCompl Λ (horizontal ι)}` (`range_graphY`) and target `univ`.
  API: `graphYChart_def`, and `graphYChart_source`, `graphYChart_target`,
  `graphYChart_symm_apply` and `graphYChart_graphY` (all `@[simp]`). Also
  `unitaryFrame_mem_graphYChart_source_iff`: `unitaryFrame U` is in the
  source iff `Y = U.map im` is invertible; and
  `coe_graphYChart_unitaryFrame`: for such `U`, the value at
  `unitaryFrame U` is $XY^{-1}$ for `X = U.map re`. This gives continuity
  on the source through the open quotient map. Both are the frame lemmas
  `mem_graphYChart_source_iff_isUnit` and `coe_graphYChart_eq_mul_inv` below,
  applied to `coe_unitaryFrame U`.
- `ℒ.graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))`,
  the chart on the Lagrangians transverse to the vertical subspace, with
  source `{Λ | IsCompl Λ (vertical ι)}` (`range_graph`), target
  `univ`, and inverse `graph`. It is the homeomorphism `symJ ι ℝ • ·`
  of `ℒ ι`, then `graphYChart`, then the homeomorphism `S ↦ -S`; this is
  `symJ_smul_graph`. API: `graphChart_def`, `graphChart_apply`
  (`graphChart Λ = -graphYChart (symJ ι ℝ • Λ)`), and `graphChart_source`,
  `graphChart_target`, `graphChart_symm_apply` and `graphChart_graph` (all
  `@[simp]`). The mirrors of the frame lemmas of `graphYChart`:
  `mem_graphChart_source_iff_isUnit` (a Lagrangian spanned by `fromRows X Y`
  is in the source iff `X` is invertible) and `coe_graphChart_eq_mul_inv`
  (its value is `Y X⁻¹`); the first is the `graphY` version transported
  along `swap`.

### `Topology/Grassmannian/Lagrangian/Fibration.lean`

Path lifting along the unitary frame map (G3). The model is Tau Ceti's unitary
Stiefel fibration, `Topology/Grassmannian/StiefelFibration/Unitary.lean`,
built the same way; the building issue credits it.

- `ℒ.exists_trivialization_unitaryFrame (Λ : ℒ ι) :
  ∃ e : Bundle.Trivialization (realSubgroup ι) unitaryFrame, Λ ∈ e.baseSet`.
  Write `Λ = U • vertical ι` (`MulAction.exists_smul_eq`). Over the open
  set `U • graphYChart.source` (by `graphYChart_source`, the translate by
  `U` of `{Λ' | IsCompl Λ' (horizontal ι)}`), which contains `Λ` because
  `vertical ι = graphY 0` (`graphY_zero`, `Transverse.lean`) is in the
  chart source, the section is
  `Λ' ↦ U * unitaryOfFrame (isLagrangian_range_fromRows_one hS)`, where
  `S` is the chart value of `U⁻¹ • Λ'` in `graphYChart` and `hS` its
  symmetry (`isHermitian_iff_isSymm.1 S.property`). It is a section by
  `unitaryFrame_mul`, `graphY_eq_unitaryFrame` (`Transverse.lean`) and
  `graphYChart_symm_apply`; it is continuous on the open set by
  `continuous_unitaryOfFrame` (`Quotient.lean`) for the frames
  `fromRows S 1`, composed with the continuity of `graphYChart` on its
  source and of the action. No frame is orthonormalized by hand here. Tau Ceti's
  `Subgroup.localSectionTrivializationOfCosetFibers` makes the
  trivialization, with fibres given by `unitaryFrame_eq_unitaryFrame_iff`.
- `ℒ.hasHomotopyLiftingProperty_unitaryFrame (A)`, from Tau Ceti's
  `TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization`. `ℒ ι` is
  compact Hausdorff, hence normal and paracompact.
- `ℒ.exists_path_lift_unitaryFrame (γ : Path Λ Λ') (hU : unitaryFrame U = Λ) :
  ∃ (V : unitaryGroup ι ℂ) (δ : Path U V), ∀ t, unitaryFrame (δ t) = γ t`,
  Tau Ceti's `TauCeti.HasHomotopyLiftingProperty.exists_path_lift` applied
  to the previous item, in the form of a path of unitary frames that the
  Maslov index files use.
- The same fact in the categorical form that Tau Ceti's fibration results
  use, `ℒ.unitaryFrame_mem_serreFibrations`, by Tau Ceti's
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`; with it
  Tau Ceti's `TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations` lifts
  paths too.

### `LinearAlgebra/Symplectic/Lagrangian/Sum.lean`

Direct sum and reindexing as algebra (G5). Following §6, this file imports
no `Topology/` file of this part.

- `ℒ.sum : ℒ ι × ℒ κ → ℒ (ι ⊕ κ)`, the image of `Λ.prod Λ'` under
  `(StdSpace.sumEquiv ι κ).symm`. It is Lagrangian by Tau Ceti's
  `TauCeti.SymplecticForm.IsLagrangian.prod` and `TauCeti.SymplecticForm.isLagrangian_map_transport_iff`, with §1's lemma
  that `sumEquiv` carries `stdForm (ι ⊕ κ)` to the product form. API:
  `coe_sum`, `mem_sum_iff` (`@[simp]`); `sum_horizontal` and `sum_vertical`
  (`@[simp]`); `sum_graphY` (a block-diagonal chart value);
  `sum_unitaryFrame` (`@[simp]`), whose value at
  `(unitaryFrame U, unitaryFrame U')` is
  the frame of Tau Ceti's `Matrix.UnitaryGroup.sum (U, U')`
  (`LinearAlgebra/Matrix/UnitaryGroup/Block.lean`), through
  `Matrix.realify_fromBlocks_zero`; and `sum_smul`, with
  `sum (g • Λ, h • Λ') = TauCeti.GLSymplectic.sum (g, h) • sum (Λ, Λ')`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Sum.lean`), from
  §1's matrix lemma for `sumEquiv` in `Standard/Matrix.lean`.
- `ℒ.reindex (e : ι ≃ κ) : ℒ ι ≃ ℒ κ`, the image under
  `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)`, which is
  Lagrangian by the lemma `isLagrangian_map_piLpCongrLeft_sumCongr` of this
  file, from `isSymplectomorphism_piLpCongrLeft_sumCongr`. API:
  `coe_reindex`, `reindex_symm`, `reindex_trans`, `reindex_refl`;
  `reindex_unitaryFrame : reindex e (unitaryFrame U) =
  unitaryFrame (Matrix.unitaryReindexContinuousMulEquiv ℂ e U)`, with Tau
  Ceti's map (`Topology/Algebra/Matrix/UnitaryGroup.lean`), whose coercion is
  `Matrix.reindex e e U` (§6's `U.submatrix e.symm e.symm`). The proof
  rewrites the horizontal Lagrangian as its image under `reindex e`
  (`reindex_horizontal`), then goes through
  `coe_unitaryReindexContinuousMulEquiv_apply`, then `Matrix.realify_reindex`
  (`(reindex e e A).realify = reindex (e.sumCongr e) (e.sumCongr e) A.realify`,
  in the general file `LinearAlgebra/Matrix/Realify.lean`, beside
  `Matrix.realify_submatrix`), and then
  `Matrix.piLpCongrLeft_toEuclideanLin_apply` along `e.sumCongr e`;
  `reindex_horizontal` and `reindex_vertical`, by
  `x_piLpCongrLeft_sumCongr` and `y_piLpCongrLeft_sumCongr`.
  `sum_unitaryFrame` goes through `TauCeti.GLSymplectic.sum_ofUnitary`, and
  `reindex_trans` through `LinearIsometryEquiv.piLpCongrLeft_trans`.

### `Topology/Grassmannian/Lagrangian/Sum.lean`

The topology of the direct sum and of reindexing.

- `ℒ.continuous_sum`, through the open quotient map on both factors
  (`isOpenQuotientMap_unitaryFrame`, Mathlib's `IsOpenQuotientMap.prodMap`),
  `sum_unitaryFrame` and the continuity of `Matrix.UnitaryGroup.sum`.
- `ℒ.reindexHomeomorph (e : ι ≃ κ) : ℒ ι ≃ₜ ℒ κ`, with underlying
  equivalence `reindex e`, continuous both ways in the same way, by
  `reindex_unitaryFrame` and the continuity of
  `Matrix.unitaryReindexContinuousMulEquiv ℂ e` and of its inverse
  (`symm_unitaryReindexContinuousMulEquiv`). API:
  `coe_reindexHomeomorph`, `reindexHomeomorph_symm` and
  `toEquiv_reindexHomeomorph` (`@[simp]`), and `reindexHomeomorph_apply`.

### `Geometry/Manifold/Instances/LagrangianGrassmannian.lean`

The manifold structure and the milestone.

- `instance : ChartedSpace (selfAdjoint (Matrix ι ι ℝ)) (ℒ ι)`. The chart at
  `Λ` is `U⁻¹ •` followed by `graphYChart`, for the unitary `U` chosen by
  `MulAction.exists_smul_eq (unitaryGroup ι ℂ) (vertical ι) Λ`, so that
  `U • vertical ι = Λ`. The basic
  chart is centred at the vertical subspace, so its translate by `U` contains
  `Λ`. The atlas is the set of all such translates. The translate is
  `ℒ.unitaryChart U` (with `unitaryChart_apply`, `unitaryChart_symm_apply`,
  `mem_unitaryChart_source_iff` and `unitaryChart_target`), and the chosen
  unitary is `ℒ.chartUnitary Λ` (with `chartUnitary_smul_vertical`). API:
  `atlas_eq`, `chartAt_eq`, `chartAt_symm_apply`, with
  `(chartAt _ Λ).symm S = chartUnitary Λ • graphY S`, `chartAt_self`, and
  `mem_chart_source`.
- `instance : IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι)`. A
  transition map is `S ↦ (A S + B)(C S + D)⁻¹` for the blocks of a real
  symplectic matrix. It is smooth where it is defined, by Tau Ceti's
  `ContDiffAt.inverse`. For `g : GLSymplectic ι ℝ`,
  `contDiffOn_graphYChart_smul_graphY` is that smoothness; and
  `unitaryChart_symm_trans_apply`, `unitaryChart_symm_trans_source` for the
  transition maps of the atlas. The proof uses three lemmas placed with
  their topics. In `Transverse.lean`, `ℒ.coe_smul_graphY`: `g • graphY S`
  is spanned by `fromRows (A S + B) (C S + D)`, from `coe_smul_of_coe_eq` and
  `graphY_eq_ofFrame`. In `Graph.lean`, for a
  Lagrangian spanned by a frame `fromRows X Y`,
  `mem_graphYChart_source_iff_isUnit` (it is in the basic chart's source
  iff `Y` is invertible) and `coe_graphYChart_eq_mul_inv` (its chart value
  is `X Y⁻¹`), and in `Transverse.lean`, `eq_graphY_iff_of_coe_eq`. These
  rest on facts about frames added to `Frame.lean`:
  `StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff` and its form
  `disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian` for a
  Lagrangian frame, and
  `StdSpace.range_toEuclideanLin_fromRows_eq_graphY`.
- The milestone, as one theorem, `lagrangianGrassmannian_properties`, stated
  for a finite type `ι` with decidable equality. In it, `ℒ ι` is the file's
  local notation and `ℒ.foo` stands for `LagrangianGrassmannian.foo`:

  ```lean
  theorem lagrangianGrassmannian_properties :
      (∀ X Y : Matrix ι ι ℝ,
        (stdForm ι).IsLagrangian
            (LinearMap.range (Matrix.toEuclideanLin (Matrix.fromRows X Y))) ↔
          (Matrix.fromRows X Y).rank = Fintype.card ι ∧ Xᵀ * Y = Yᵀ * X) ∧
      (∀ A : Matrix ι ι ℝ, (stdForm ι).IsLagrangian (StdSpace.graph A) ↔ A.IsSymm) ∧
      (∀ A ∈ Matrix.symplecticGroup ι ℝ, ∀ L : Submodule ℝ (StdSpace ι),
        (stdForm ι).IsLagrangian L →
          (stdForm ι).IsLagrangian (L.map (Matrix.toEuclideanLin A))) ∧
      (∀ Λ : ℒ ι, ∃ U : unitaryGroup ι ℂ,
        TauCeti.GLSymplectic.ofUnitary U • ℒ.horizontal ι = Λ) ∧
      (∃ e : unitaryGroup ι ℂ ⧸ Matrix.UnitaryGroup.realSubgroup ι ≃ₜ ℒ ι,
        ∀ U, e (QuotientGroup.mk U) = TauCeti.GLSymplectic.ofUnitary U • ℒ.horizontal ι) ∧
      IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι) ∧
      Module.finrank ℝ (selfAdjoint (Matrix ι ι ℝ)) =
        Fintype.card ι * (Fintype.card ι + 1) / 2 ∧
      ∀ Λ : ℒ ι, ∃ U : unitaryGroup ι ℂ, ∀ S,
        (chartAt (selfAdjoint (Matrix ι ι ℝ)) Λ).symm S =
          TauCeti.GLSymplectic.ofUnitary U • ℒ.graphY S
  ```

  Its docstring ends with "Milestone: *Lagrangian frames and the Lagrangian
  Grassmannian*." The statement keeps the book's hypotheses: real
  $n\times n$ blocks, the standard form, the full symplectic group. It is
  slightly more general, since `ι` is any finite type and not only `Fin n`.
  It needs no entry in `ERRATA.md`. The third item starts from a matrix
  `A ∈ Matrix.symplecticGroup ι ℝ`: it is
  `isLagrangian_map_toEuclideanLin` itself. The dimension item is
  `Matrix.finrank_selfAdjoint`.

## What the part uses

- *Standard model*: `StdSpace`, `StdSpace.x`, `StdSpace.y`, `equivProd`,
  `stdForm`, `stdForm_apply`, `stdForm_compatible`,
  `isSymplectomorphism_sumEquivProd`, `x_complexToRealEuclidean`,
  `y_complexToRealEuclidean` (merged, #41); the matrix dictionary
  `mem_symplecticGroup_iff_forall_stdForm` and
  `TauCeti.conj_complexToRealEuclidean_toLin'` (merged, #62);
  `isSymplectomorphism_piLpCongrLeft_sumCongr`; `StdSpace.sumEquiv` with its two
  lemmas (merged, #232).
- *Symplectic subspaces* (merged, #64):
  `isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq`; this part adds
  `TauCeti.SymplecticForm.isLagrangian_map_iff_of_apply_eq_mul` there.
- The library's general `LinearAlgebra/Matrix/Realify.lean` (merged, #173 and
  #232; it imports only Tau Ceti): `Matrix.realify_reindex`, for
  `reindex_unitaryFrame`. Tau Ceti's `Matrix.realify_smul_one`
  (`LinearAlgebra/Matrix/Realify.lean`), the realification of a scalar
  matrix, serves `Maslov/Path/RegularPieces.lean`.
- Tau Ceti:
  - Lagrangian subspaces and graphs: `TauCeti.SymplecticForm.IsLagrangian`,
    `TauCeti.SymplecticForm.IsLagrangian.two_mul_finrank`,
    `TauCeti.SymplecticForm.isLagrangian_graph_iff_of_pairing`, `TauCeti.SymplecticForm.isLagrangian_map_transport_iff`,
    `TauCeti.SymplecticForm.rescale`, `TauCeti.SymplecticForm.isLagrangian_rescale_iff`,
    `TauCeti.SymplecticForm.isSymplectomorphism_iff_transport_eq`,
    `TauCeti.SymplecticForm.IsSymplectomorphism.map_orthogonal`, `TauCeti.SymplecticForm.isLagrangian_prod_iff`,
    `TauCeti.SymplecticForm.IsLagrangian.prod`, `TauCeti.SymplecticForm.isLagrangian_prod_top_bot`,
    `TauCeti.SymplecticForm.isLagrangian_prod_bot_top`, `TauCeti.SymplecticForm.IsIsotropic.disjoint_map_of_tames`.
  - Frames and charts (`LinearAlgebra/TotallyReal/Euclidean.lean`,
    `Lagrangian.lean`, `LinearAlgebra/Matrix/OfReal.lean`):
    `Matrix.realImage`, `realImage_mul_map_ofReal`,
    `exists_mem_orthogonalGroup_eq_mul_map_ofReal`,
    `map_im_conjTranspose_mul_self_mul_map_ofReal`, `lagrangianChart`,
    `lagrangianChartFrame`, `mem_lagrangianChart`, `lagrangianChart_injective`,
    `lagrangianChart_inj`, `lagrangianChart_inf_realSubspace`,
    `TauCeti.realSubspace`, `TauCeti.IsMaximalTotallyReal`,
    `TauCeti.IsMaximalTotallyReal.two_mul_finrank_eq`,
    `isMaximalTotallyReal_realImage`, `isMaximalTotallyReal_realImage_iff`,
    `TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_compatible`,
    `LinearEquiv.isMaximalTotallyReal_map_iff`,
    `Matrix.rank_eq_finrank_range_toEuclideanLin`,
    `realOrthonormalize`,
    `realImage_realOrthonormalize`, `realOrthonormalize_mem_unitaryGroup`,
    `continuous_realOrthonormalize`.
  - Groups: `TauCeti.GLSymplectic`, `TauCeti.GLSymplectic.ofUnitary`,
    `TauCeti.GLSymplectic.coe_ofUnitary`, `TauCeti.GLSymplectic.continuous_ofUnitary`,
    `TauCeti.GLSymplectic.mulEquivSymplecticGroup`,
    `SymplecticGroup.fromBlocks_upper_mem`,
    `TauCeti.GLSymplectic.symJ`, `TauCeti.GLSymplectic.sum`, `TauCeti.GLSymplectic.continuous_sum`,
    `Matrix.symplecticSum`, `Matrix.UnitaryGroup.sum`,
    `Matrix.UnitaryGroup.continuous_sum`, `TauCeti.GLOrthogonal`,
    `TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`,
    `Matrix.realify_fromBlocks_zero`, the `CompactSpace` instance of
    `unitaryGroup`, `Matrix.unitaryReindexContinuousMulEquiv`,
    `Matrix.coe_unitaryReindexContinuousMulEquiv_apply`,
    `Matrix.symm_unitaryReindexContinuousMulEquiv`.
  - Topology: `TauCeti.finiteGrassmannian`,
    `TauCeti.finiteGrassmannian.continuous_starProjection_toEuclidean`,
    `TauCeti.quotientStabilizerHomeomorph`, `TauCeti.quotientStabilizerHomeomorph_mk`,
    `Homeomorph.Quotient.congrRight_mk`,
    `Subgroup.localSectionTrivializationOfCosetFibers`,
    `TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization`,
    `TauCeti.HasHomotopyLiftingProperty.exists_path_lift`,
    `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`,
    `TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations`.
  - Models that the building issues credit: Tau Ceti's
    `Topology/Grassmannian/Graph.lean` and
    `Topology/Grassmannian/StiefelFibration/Unitary.lean`.
- Mathlib: `Submodule.starProjection`, `Submodule.starProjection_map_apply`,
  `Submodule.isCompl_iff_disjoint`, `Matrix.fromRows`, `Matrix.rank`,
  `Matrix.toEuclideanLin`, `LinearMap.graph`,
  `LinearEquiv.prodComm`, `Submodule.exists_eq_graph`,
  `Submodule.map_symm_eq_iff`, `Matrix.isSymm_toBilin'_iff_isSymm`,
  `LinearMap.BilinForm.toMatrix'`,
  `LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm`,
  `Matrix.isHermitian_iff_isSymm`, `LinearEquiv.finrank_eq`,
  `Module.finrank_fintype_fun_eq_card`, `Homeomorph.Quotient.congrRight`,
  `MulAction.compHom`, `MulAction.exists_smul_eq`, `MulAction.stabilizer`,
  `unitarySubgroupUnitsEquiv`, `IsQuotientMap.continuous_iff`,
  `IsOpenQuotientMap.prodMap`, `Topology.IsInducing.of_comp`,
  `LinearIsometryEquiv.piLpCongrLeft`,
  `PiLp.continuousLinearEquiv`, `contDiffAt_ringInverse`.

Nothing here redefines a Mathlib or Tau Ceti notion. The new definitions are
`LagrangianGrassmannian` with its topology, `realSubgroup` (Tau Ceti's
$\mathrm{O}(n)\subset\mathrm{U}(n)$ carried from `GL ι ℂ` to
`unitaryGroup ι ℂ`), `StdSpace.graph`, `StdSpace.graphY`,
`StdSpace.complexEuclideanEquiv` (in part 1's file), the unitary action, and
the maps `ofFrame`, `unitaryFrame`, `graphY`, `graph`, `graphYChart`,
`graphChart`, `sum`, `reindex`, `reindexHomeomorph` and
`toFiniteGrassmannian`
on the new type. Tau Ceti has a
`Matrix.lagrangianChart` on `EuclideanSpace ℂ ι`, but no space of Lagrangian
subspaces, no topology on one, and no real graph on `StdSpace ι`. Each new
map comes with its comparison to Tau Ceti's object.

## Interface with *Maslov index*

| Item of `design/maslov-index.md` | Here |
|---|---|
| G1, `V₀ ι`, `V₁ ι` | `ℒ.horizontal ι`, `ℒ.vertical ι` |
| G2, unitary frames, $\mathrm{U}(n)/\mathrm{O}(n)$ | `ℒ.unitaryFrame`, `unitaryFrame_surjective`, `unitaryFrame_eq_unitaryFrame_iff`, `quotientHomeomorph`; continuity of maps out of `ℒ ι` by `isQuotientMap_unitaryFrame.continuous_iff` |
| G3, path lifting | `exists_path_lift_unitaryFrame`, from `hasHomotopyLiftingProperty_unitaryFrame` and Tau Ceti's `TauCeti.HasHomotopyLiftingProperty.exists_path_lift` |
| G4, the action | the `MulAction` and `ContinuousSMul` instances, `unitaryFrame_mul` |
| G5, sum and reindexing | `ℒ.sum`, `ℒ.reindex` and their compatibilities; `continuous_sum`, `ℒ.reindexHomeomorph` |
| G6, frame criterion and spanned Lagrangian | `isLagrangian_range_fromRows_iff` (stated with `fromRows X Y` for the book's frame `Z`) and `ℒ.ofFrame` with `coe_ofFrame` |
| G7, transverse charts | `ℒ.isCompl_horizontal_iff`, `ℒ.isCompl_vertical_iff`; as charts, `ℒ.graphYChart` and `ℒ.graphChart` |
| G8, a Lagrangian transverse to two given ones | `ℒ.exists_isCompl_isCompl` |
| G9, transverse pairs are one orbit | `ℒ.exists_smul_eq_horizontal_vertical` |

## Building issues

Sub-issues of #30, *Build the part Lagrangian Grassmannian*, to be created in
this order. The sizes are estimates. An issue may start once its blockers are
merged.

1. **Real points of the unitary group.** `LinearAlgebra/Matrix/UnitaryGroup/Real.lean`.
   About 100 lines. No blockers.
2. **The space of Lagrangian subspaces.** `LinearAlgebra/Symplectic/Lagrangian/Basic.lean`.
   About 150 lines. No blockers.
3. **Lagrangian frames.** `LinearAlgebra/Matrix/OfReal.lean` and
   `LinearAlgebra/Symplectic/Lagrangian/Frame.lean`, with
   `StdSpace.complexEuclideanEquiv` in `Standard/Basic.lean`: the complex frame facts,
   `StdSpace.graph` and `StdSpace.graphY` with `isCompl_graph_ker_x` and
   `isCompl_graphY_ker_y`, the comparison `map_realSubspace`,
   `map_lagrangianChart` and `stdForm_apply_eq_im_inner`, the frame and
   graph criteria, `ofFrame`, and both `exists_eq_graph_of_isCompl` and
   `exists_eq_graphY_of_isCompl`. About 400 lines. Blocked by 2.
4. **The topology.** `Topology/Grassmannian/Lagrangian/Basic.lean`. About 100
   lines. Blocked by 2.
5. **The actions and unitary frames.** `LinearAlgebra/Symplectic/Lagrangian/Action.lean`.
   About 300 lines. Blocked by 1 and 3.
6. **Chart points and transverse pairs.** `LinearAlgebra/Symplectic/Lagrangian/Transverse.lean`:
   `graphY`, `graph`, the transverse-chart facts, and both
   transverse-pair results. About 350 lines. Blocked by 5.
7. **The quotient topology.** `Topology/Grassmannian/Lagrangian/Quotient.lean`.
   About 300 lines. Blocked by 4 and 5.
8. **Comparison with `finiteGrassmannian`.** `Topology/Grassmannian/Lagrangian/Finite.lean`.
   About 200 lines. Blocked by 4.
9. **The graph charts.** `Topology/Grassmannian/Lagrangian/Graph.lean`:
   `graphYChart` and `graphChart`. About 300 lines. Blocked by 6 and 7.
10. **Path lifting.** `Topology/Grassmannian/Lagrangian/Fibration.lean`.
    About 200 lines. Blocked by 9.
11. **Direct sums and reindexing, as algebra.**
    `LinearAlgebra/Symplectic/Lagrangian/Sum.lean`: `ℒ.sum`, `ℒ.reindex` and
    their compatibilities, using the existing
    `isSymplectomorphism_piLpCongrLeft_sumCongr` from `Standard/Basic.lean`;
    and §1's `StdSpace.sumEquiv` with its two lemmas. About 300
    lines. Blocked by 6.
12. **Direct sums and reindexing, topology.**
    `Topology/Grassmannian/Lagrangian/Sum.lean`: `continuous_sum` and
    `reindexHomeomorph`. About 100 lines. Blocked by 7 and 11.
13. **The manifold structure and the milestone.**
    `LinearAlgebra/Matrix/SelfAdjoint.lean` and
    `Geometry/Manifold/Instances/LagrangianGrassmannian.lean`. About 450
    lines. Blocked by 9.
14. **The range of Tau Ceti's chart.** `LinearAlgebra/TotallyReal/Euclidean.lean`:
    `Matrix.exists_isSymm_eq_lagrangianChart` and its example. About 120
    lines. Blocked by 3.

The Lagrangian issues of *Maslov index* wait for 6, 7, 9, 10, 11 and 12.
Issues 8, 13 and 14 are not needed there.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.3.
* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993],
  §2, for the graph chart relative to the horizontal subspace.
