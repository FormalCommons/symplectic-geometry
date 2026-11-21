# Lagrangian Grassmannian

The detailed design of part 6 of `DESIGN.md`, *Lagrangian Grassmannian*. It
serves the milestone *Lagrangian frames and the Lagrangian Grassmannian* of
`atlas/linear-symplectic-geometry.md` (McDuff–Salamon [McDuffSalamon2017],
§2.3, Lemmas 2.3.1 and 2.3.2 and p. 50), and it provides what the Lagrangian
issues of *Maslov index* need from this part (`design/maslov-index.md`, PR
#52, items G1–G9).

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
     `finiteGrassmannian ℝ n (2 n)` lives on `Fin N → ℝ`. Reaching it needs a
     reindexing `Fin n ⊕ Fin n ≃ Fin (n + n)` that every later statement
     would carry;
   - it is Hausdorff at once, because a subspace is the range of its
     projection;
   - the quotient $\mathrm{U}(n)/\mathrm{O}(n)$ needs a base point and a choice of
     unitary model, which a general $(V,\omega)$ lacks.

   The other two candidates are then theorems on `StdSpace ι`. The unitary
   group acts on `ℒ ι` through the homomorphism `ofUnitary`, and the unitary
   frame map $\mathrm{U}(n)\to\mathcal{L}(n)$ is the orbit map of the
   horizontal subspace. It is continuous, since its projection is
   $R\,P_0\,R^T$ with $R$ the realification. Its source is compact, so it is a
   quotient map, and Tau Ceti's `TauCeti.quotientStabilizerHomeomorph` gives
   the homeomorphism $\mathrm{U}(n)/\mathrm{O}(n)\cong\mathcal{L}(n)$ once the
   stabilizer is identified with $\mathrm{O}(n)$. For `ι = Fin n`, the map into
   `finiteGrassmannian ℝ n (n + n)` is an embedding: it is continuous, by the
   quotient property, and Tau Ceti's
   `finiteGrassmannian.continuous_starProjection_toEuclidean` recovers the
   projection from its image (`Topology.IsInducing.of_comp`). A map out of
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
   `complexToRealEuclidean` turns Tau Ceti's `Matrix.realImage (X + i Y)` into
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
   which `complexToRealEuclidean` turns into the same subspace. It is also the
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
   `exists_isSymplectomorphism_extend` as the source of
   $\mathrm{Sp}$-transitivity. Transitivity of $\mathrm{U}(n)$ is proved here
   anyway, since the milestone asks for it, and $\mathrm{U}(n)\subset\mathrm{Sp}(2n)$
   through `TauCeti.GLSymplectic.ofUnitary`. That gives
   $\mathrm{Sp}$-transitivity directly, so Witt's theorem is not used.
8. **Comparison with `DESIGN.md` §6.** Every file in §6's list on `main`
   (after #67) is kept, with the content §6 gives it: `Frame.lean` with both
   graph statements, `Graph.lean` with both graph charts, the manifold file,
   `LinearAlgebra/TotallyReal/Euclidean.lean` with the range of
   `Matrix.lagrangianChart` and the example showing isotropy is needed,
   `Fibration.lean` and `Sum.lean`. The departures fall in two groups, each
   with the issue that changes §6 to match:
   - #74 (PR #75): the type goes to `LinearAlgebra/Symplectic/Lagrangian/`;
     the action file becomes `Action.lean` there (algebra) and
     `Topology/Grassmannian/Lagrangian/Quotient.lean` (topology); and
     `Transverse.lean` goes to `LinearAlgebra/Symplectic/Lagrangian/`.
   - #79: `Topology/Grassmannian/Lagrangian/Finite.lean`; the general files
     outside the part's folders (the real points of the unitary group, the
     complex frame facts and the dimension of the space of symmetric matrices
     under `LinearAlgebra/Matrix/`, and the direct sum of standard spaces in
     part 1's folder); the route to transitivity of decision 7; and dropping
     `Matrix.lagrangianChartCLE`, which this design does not use. The chart
     file keeps §6's name `Graph.lean`, so the `Chart.lean` item that #79
     lists lapses; #79 says to follow the design as merged.

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
  `inf_unitarySubgroup_eq_map_real` (Tau Ceti's
  `Matrix.exists_mem_orthogonalGroup_map_eq_of_mul_transpose_eq_one` may
  shorten it); `mem_realSubgroup_iff` (iff
  `(U : Matrix ι ι ℂ).map Complex.im = 0`); `map_ofReal_mem_realSubgroup`;
  `isClosed_realSubgroup`.

### `LinearAlgebra/Matrix/OfReal.lean`

Two facts about complex frames, in the namespace `Matrix`, next in spirit to
Tau Ceti's `Matrix.map_im_conjTranspose_mul_self_mul_map_ofReal`
(`LinearAlgebra/Matrix/OfReal.lean`).

- `Matrix.map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq
  {X Y : Matrix m n ℝ} (h : Xᵀ * Y = Yᵀ * X)`: for
  `M = X.map ofReal + I • Y.map ofReal`, `(Mᴴ * M).map im = 0`.
- `Matrix.range_toEuclideanLin_fromRows (X Y : Matrix ι ι ℝ)`: the range of
  `toEuclideanLin (fromRows X Y)` is the image of
  `Matrix.realImage (X.map ofReal + I • Y.map ofReal)` under
  `complexToRealEuclidean ι`, read through `WithLp.equiv`.

### `LinearAlgebra/Matrix/SelfAdjoint.lean`

- `Matrix.finrank_selfAdjoint : Module.finrank ℝ (selfAdjoint (Matrix ι ι ℝ)) =
  Fintype.card ι * (Fintype.card ι + 1) / 2`. Tau Ceti has the same count as
  `finrank_symmetricMatrix`, but in
  `MeasureTheory/Measure/SymmetricMatrix/Basic.lean`, which imports Haar
  measure; this file does not import it, and stays within linear algebra.
  The proof is a linear equivalence
  `Matrix.selfAdjointEquivSym2 : selfAdjoint (Matrix ι ι ℝ) ≃ₗ[ℝ] (Sym2 ι → ℝ)`,
  sending `S` to `Sym2.lift ⟨fun i j ↦ S i j, _⟩` (well defined since `S` is
  symmetric), with inverse `f ↦ of fun i j ↦ f s(i, j)`. Then
  `Module.finrank_fintype_fun_eq_card`, Mathlib's `Sym2.card`
  (`Mathlib/Data/Sym/Card.lean`) and `Nat.choose_two_right` give the count.
  API: `selfAdjointEquivSym2_apply` and `selfAdjointEquivSym2_symm_apply`
  (`@[simp]`).

### `LinearAlgebra/Symplectic/Lagrangian/Basic.lean`

The type, for a general symplectic vector space, with no topology.

- `structure LagrangianGrassmannian (ω : TauCeti.SymplecticForm V) extends
  Submodule ℝ V` with `isLagrangian' : ω.IsLagrangian toSubmodule`.
- API: the `SetLike` instance, `@[ext] ext`, `toSubmodule_injective`,
  `isLagrangian (Λ) : ω.IsLagrangian Λ`, `mem_toSubmodule`, `coe_mk`
  (`@[simp]`), `mk_toSubmodule`.
- `ℒ.isCompl_iff_disjoint`: for two Lagrangians, being complementary is the
  same as meeting only in zero, by Mathlib's `Submodule.isCompl_iff_disjoint`
  and `IsLagrangian.two_mul_finrank`. It is stated for a general `ω` on a
  finite-dimensional `V`.

### `LinearAlgebra/Symplectic/Lagrangian/Frame.lean`

Lagrangian frames on `StdSpace ι`, pure linear algebra. Namespace
`SymplecticGeometry` (and `SymplecticGeometry.StdSpace` for the graphs).

- `StdSpace.graph (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι)`, defined as
  the image of `(Matrix.toLin' A).graph` under `(StdSpace.equivProd ι).symm`.
  API: `StdSpace.mem_graph_iff : z ∈ graph A ↔ z.y = A *ᵥ z.x` (`@[simp]`),
  and `StdSpace.graph_injective`.
- `StdSpace.graphY (A : Matrix ι ι ℝ) : Submodule ℝ (StdSpace ι)`, the graph
  over the `y` coordinate, the image of `(Matrix.toLin' A).graph` under the
  linear equivalence
  `(LinearEquiv.prodComm ℝ (ι → ℝ) (ι → ℝ)).trans (StdSpace.equivProd ι).symm`.
  API: `StdSpace.mem_graphY_iff : z ∈ graphY A ↔ z.x = A *ᵥ z.y` (`@[simp]`),
  `StdSpace.graphY_injective`, and `StdSpace.map_symJ_graph`, saying that
  `symJ` sends `graph A` to `graphY (-A)`.
- Both graphs are complementary to the coordinate subspace they are graphs
  over, for every `A`, symmetric or not:
  `StdSpace.isCompl_graph_ker_x : IsCompl (graph A) (LinearMap.ker StdSpace.x)`
  and
  `StdSpace.isCompl_graphY_ker_y : IsCompl (graphY A) (LinearMap.ker StdSpace.y)`.
  Every `z` is `(z.x, A z.x) + (0, z.y - A z.x)`, and a vector of the graph
  with `x = 0` is zero.
- The comparison with Tau Ceti's complex picture. Write
  `e := ((EuclideanSpace.equiv ι ℂ).toLinearEquiv.restrictScalars ℝ).trans
  (complexToRealEuclidean ι).toLinearEquiv`, from `EuclideanSpace ℂ ι` to
  `StdSpace ι`. Then `StdSpace.map_realSubspace :
  (TauCeti.realSubspace ι).map e = LinearMap.ker StdSpace.y` and
  `StdSpace.map_lagrangianChart (S : Matrix ι ι ℝ) :
  (Matrix.lagrangianChart S).map e = StdSpace.graphY S`, both from
  `x_complexToRealEuclidean`, `y_complexToRealEuclidean` and Tau Ceti's
  `Matrix.mem_lagrangianChart`. Also
  `stdForm_apply_eq_im_inner (v w : EuclideanSpace ℂ ι) :
  stdForm ι (e v) (e w) = (inner ℂ v w).im`, from `stdForm_apply` and
  `PiLp.inner_apply`.
- `isLagrangian_range_fromRows_iff (X Y : Matrix ι ι ℝ) :
  (stdForm ι).IsLagrangian (LinearMap.range (Matrix.toEuclideanLin (Matrix.fromRows X Y)))
  ↔ (Matrix.fromRows X Y).rank = Fintype.card ι ∧ Xᵀ * Y = Yᵀ * X`. The
  form on the frame is $u^T(X^TY-Y^TX)v$ by `stdForm_apply`. The rank is
  the dimension of the range. Lagrangian is isotropic of half dimension, by
  `isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq` of
  `LinearAlgebra/Symplectic/Subspace.lean` (#64).
- `ℒ.ofFrame (X Y : Matrix ι ι ℝ) (hrank : (fromRows X Y).rank = Fintype.card ι)
  (hXY : Xᵀ * Y = Yᵀ * X) : ℒ ι`, the Lagrangian that the frame spans, with
  `coe_ofFrame` (`@[simp]`): its submodule is the range of
  `toEuclideanLin (fromRows X Y)`. This is the constructor of G6.
- `isLagrangian_graph_iff (A : Matrix ι ι ℝ) :
  (stdForm ι).IsLagrangian (StdSpace.graph A) ↔ A.IsSymm`, from Tau Ceti's
  `isLagrangian_graph_iff_of_pairing` through `equivProd` and
  `isLagrangian_map_transport_iff`. It is not derived from the frame
  criterion. `isLagrangian_graphY_iff` follows by `map_symJ_graph`.
- `det_ne_zero_of_isLagrangian_range_fromRows`: the complex frame of a
  Lagrangian frame is invertible. A complex kernel vector $a+ib$ gives
  $Za=-J_0Zb$, which lies in $\Lambda\cap J_0\Lambda=0$ by
  `IsIsotropic.disjoint_map_of_tames` and `stdForm_compatible`. With
  `Matrix.map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq`, this is
  the hypothesis of Tau Ceti's `realOrthonormalize_mem_unitaryGroup`.
- Transverse Lagrangians are graphs, stated for submodules and in the same
  form. The horizontal and vertical subspaces are `LinearMap.ker StdSpace.y`
  and `LinearMap.ker StdSpace.x`, so they need no new names here.
  - `exists_eq_graph_of_isCompl`: a Lagrangian `L` complementary to
    `LinearMap.ker StdSpace.x` satisfies `∃ S, S.IsSymm ∧ L = StdSpace.graph S`.
  - `exists_eq_graphY_of_isCompl`: a Lagrangian `L` complementary to
    `LinearMap.ker StdSpace.y` satisfies `∃ S, S.IsSymm ∧ L = StdSpace.graphY S`.

  In each case `L` is the graph of the inverse of the projection to `x`
  (resp. `y`). That projection is bijective on `L`, because its kernel is
  zero and the dimensions agree. Mathlib's `Submodule.toLinearPMap` builds the
  linear map from the image of `L` in the product
  (`Submodule.toLinearPMap_graph_eq`, with `Submodule.existsUnique_from_graph`
  for the uniqueness of values), and `isLagrangian_graph_iff` (resp.
  `isLagrangian_graphY_iff`) makes it symmetric. The converses are
  `isCompl_graph_ker_x` and `isCompl_graphY_ker_y` above.

### `LinearAlgebra/Symplectic/Lagrangian/Action.lean`

The actions of $\mathrm{Sp}(2n)$ and $\mathrm{U}(n)$ and the unitary frames,
as algebra. It uses the matrix dictionary of *Standard model*
(`LinearAlgebra/Symplectic/Standard/Matrix.lean`, #62):
`mem_symplecticGroup_iff_forall_stdForm`, which reads membership of a
matrix in `Matrix.symplecticGroup` as invariance of `stdForm` under
`toEuclideanLin`, and `TauCeti.conj_complexToRealEuclidean_toLin'`, which
turns a complex matrix acting on `ι → ℂ` into its realification acting on
`StdSpace ι`. With Tau Ceti's `GLSymplectic.coe_ofUnitary` (the matrix of
`ofUnitary U` is `(U : Matrix ι ι ℂ).realify`), the second relates the
unitary action to Tau Ceti's `Matrix.realImage`.

- `instance : MulAction (GLSymplectic ι ℝ) (ℒ ι)`, with
  `coe_smul : ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) = Λ.map (Matrix.toEuclideanLin g)`
  (`@[simp]`). The result is Lagrangian by
  `IsSymplectomorphism.map_orthogonal`, the map `toEuclideanLin g` being a
  symplectomorphism by `mem_symplecticGroup_iff_forall_stdForm`.
- `instance : MulAction (unitaryGroup ι ℂ) (ℒ ι)`, the action through the
  monoid homomorphism `TauCeti.GLSymplectic.ofUnitary` (`MulAction.compHom`),
  with `unitary_smul_def : U • Λ = ofUnitary U • Λ`.
- `ℒ.horizontal ι`, `ℒ.vertical ι : ℒ ι`: $\{y=0\}$ and $\{x=0\}$ (G1). Their
  submodules are `LinearMap.ker StdSpace.y` and `LinearMap.ker StdSpace.x`
  (`coe_horizontal`, `coe_vertical`). They are Lagrangian by Tau Ceti's
  `isLagrangian_prod_top_bot` and `isLagrangian_prod_bot_top`, carried along
  `isSymplectomorphism_sumEquivProd` of *Standard model*. API:
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
    of `Matrix.realImage U` under `e` (`Frame.lean`). Both come from
    `coe_ofUnitary` and `conj_complexToRealEuclidean_toLin'`: the columns
    of `realify U` indexed by `inl` are `fromRows (U.map re) (U.map im)`;
  - `unitaryFrame_one` and `unitaryFrame_mul` (both `@[simp]`):
    `unitaryFrame (U * U') = U • unitaryFrame U'`.
- `ℒ.unitaryFrame_surjective`: transitivity of $\mathrm{U}(n)$. Take any basis
  of `Λ` as a frame (`Frame.lean`), orthonormalize its complex frame by
  `realOrthonormalize`, and use `realImage_realOrthonormalize`. It gives the
  instances `MulAction.IsPretransitive (unitaryGroup ι ℂ) (ℒ ι)` and
  `MulAction.IsPretransitive (GLSymplectic ι ℝ) (ℒ ι)`. Transitivity is then
  Mathlib's `MulAction.exists_smul_eq`, with no restatement here.
- `ℒ.unitaryFrame_eq_unitaryFrame_iff :
  unitaryFrame U = unitaryFrame U' ↔ U⁻¹ * U' ∈ Matrix.UnitaryGroup.realSubgroup ι`,
  from `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal`,
  `Matrix.realImage_mul_map_ofReal` and `mem_realSubgroup_iff_exists`. Its
  corollary is
  `ℒ.stabilizer_horizontal :
  MulAction.stabilizer (unitaryGroup ι ℂ) (horizontal ι) = Matrix.UnitaryGroup.realSubgroup ι`.

### `LinearAlgebra/Symplectic/Lagrangian/Transverse.lean`

Chart points and transverse pairs, as algebra: G7–G9.

- `ℒ.lagrangianChart (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι`, whose
  submodule is `StdSpace.graphY S` (`coe_lagrangianChart`). API:
  `mem_lagrangianChart_iff` (`@[simp]`); `coe_lagrangianChart_eq_map`, the
  image of Tau Ceti's `Matrix.lagrangianChart S` under `e`, which is
  `StdSpace.map_lagrangianChart`; `lagrangianChart_injective`;
  `lagrangianChart_zero`, which is the vertical subspace; and
  `lagrangianChart_eq_unitaryFrame`, saying
  `lagrangianChart S = unitaryFrame ⟨realOrthonormalize (S + i·1), _⟩`. The
  unitary proof is `realOrthonormalize_mem_unitaryGroup`, whose hypothesis
  holds since $(S+i)^*(S+i)=S^2+1$ is real; the equality is Tau Ceti's
  `det_lagrangianChartFrame_ne_zero` and `realImage_realOrthonormalize`.
- The two transverse-chart facts, in the same form:
  - `ℒ.isCompl_horizontal_iff : IsCompl (Λ : Submodule ℝ _) (horizontal ι) ↔
    ∃ S, S.IsSymm ∧ (Λ : Submodule ℝ _) = StdSpace.graphY S`;
  - `ℒ.isCompl_vertical_iff : IsCompl (Λ : Submodule ℝ _) (vertical ι) ↔
    ∃ S, S.IsSymm ∧ (Λ : Submodule ℝ _) = StdSpace.graph S`.

  The forward directions are `exists_eq_graphY_of_isCompl` and
  `exists_eq_graph_of_isCompl`. The corollary
  `ℒ.range_lagrangianChart : Set.range lagrangianChart =
  {Λ | IsCompl (Λ : Submodule ℝ _) (horizontal ι)}` is the source of the
  basic graph chart.
- `ℒ.graphPoint (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι`, whose submodule is
  `StdSpace.graph S` (`coe_graphPoint`): the points of the second chart.
  API: `mem_graphPoint_iff` (`@[simp]`), `graphPoint_injective`,
  `graphPoint_zero` (the horizontal subspace),
  `symJ_smul_graphPoint : symJ ι ℝ • graphPoint S = lagrangianChart (-S)`
  (from `map_symJ_graph`), and `ℒ.range_graphPoint : Set.range graphPoint =
  {Λ | IsCompl (Λ : Submodule ℝ _) (vertical ι)}`.
- `ℒ.exists_isCompl_isCompl (Λ Λ' : ℒ ι) :
  ∃ Λ'' : ℒ ι, IsCompl (Λ'' : Submodule ℝ _) Λ ∧ IsCompl (Λ'' : Submodule ℝ _) Λ'`.
  Move `Λ` to the horizontal subspace by a unitary matrix, and write
  `Λ' = unitaryFrame (X + iY)`. The point `lagrangianChart (t • 1)` is
  transverse to `Λ'` iff `det (X - t • Y) ≠ 0`. That determinant is a real
  polynomial in `t` whose value at `t = i` is $\det\overline{(X+iY)}\neq0$, so
  some real `t` is not a root.
- `ℒ.exists_smul_eq_horizontal_vertical {Λ Λ' : ℒ ι}
  (h : IsCompl (Λ : Submodule ℝ _) Λ') :
  ∃ g : GLSymplectic ι ℝ, g • horizontal ι = Λ ∧ g • vertical ι = Λ'`.
  Move `Λ` to the horizontal subspace by a unitary matrix. Then `Λ'` is
  `lagrangianChart S`, and the shear `fromBlocks 1 S 0 1`, symplectic by
  Tau Ceti's `SymplecticGroup.fromBlocks_upper_mem` since `S` is symmetric
  and lifted to `GLSymplectic ι ℝ` by
  `(TauCeti.GLSymplectic.mulEquivSymplecticGroup ι ℝ).symm`, fixes the
  horizontal subspace and carries the vertical one to `Λ'`.

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
  Its image `V.map e` (`Frame.lean`) is isotropic for `stdForm` by
  `stdForm_apply_eq_im_inner`, and has dimension `n` by Tau Ceti's
  `IsMaximalTotallyReal.two_mul_finrank_eq` (`J` is injective), so it is
  Lagrangian. It meets `LinearMap.ker StdSpace.y = (realSubspace n).map e`
  (`StdSpace.map_realSubspace`) only in zero, so the two are complementary
  by dimension. Then `exists_eq_graphY_of_isCompl` gives `S`, and
  `StdSpace.map_lagrangianChart` with the injectivity of `Submodule.map e`
  gives `V = S.lagrangianChart`.
- The isotropy hypothesis is needed, and the file shows it by an `example`:
  for `n = Fin 2` and `S = !![0, 1; 0, 0]`, `det (S + i·1) = -1 ≠ 0`, so
  `S.lagrangianChart` is maximal totally real (`lagrangianChart_def` and
  Tau Ceti's `isMaximalTotallyReal_realImage`) and meets `realSubspace (Fin 2)` only in
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
  `R = Matrix.realify U`, by `coe_ofUnitary` and
  `conj_complexToRealEuclidean_toLin'` (`Action.lean`).
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
  `quaternionUnitarySphereQuotientHomeomorph` the same way
  (`Topology/Algebra/Quaternion/Symplectic/FirstColumn.lean`).
  `quotientHomeomorph_mk` (`@[simp]`, the value at `U` is `unitaryFrame U`)
  follows from Tau Ceti's `Homeomorph.Quotient.congrRight_mk` and
  `quotientStabilizerHomeomorph_mk`.
  This is the book's $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$.
- `instance : ContinuousSMul (GLSymplectic ι ℝ) (ℒ ι)` and
  `instance : ContinuousSMul (unitaryGroup ι ℂ) (ℒ ι)` (G4). Use
  `IsOpenQuotientMap.prodMap` with the identity on `GLSymplectic ι ℝ`. The
  composite `(g, U) ↦ g • unitaryFrame U` is `unitaryFrame` of the
  orthonormalized complex frame of `g * realify U` restricted to the
  horizontal columns (`Frame.lean`; the matrix of `ofUnitary U` is
  `realify U` by `coe_ofUnitary`, and `conj_complexToRealEuclidean_toLin'`
  turns the columns into a complex frame), and it is continuous by
  `continuous_realOrthonormalize`. The unitary instance follows by
  `continuous_ofUnitary`.

### `Topology/Grassmannian/Lagrangian/Finite.lean`

The comparison with Tau Ceti's Grassmannian, for `ι = Fin n`.

- `ℒ.toFiniteGrassmannian : ℒ (Fin n) → TauCeti.finiteGrassmannian ℝ n (n + n)`,
  the image under the coordinate isometry built from
  `LinearIsometryEquiv.piLpCongrLeft` along `finSumFinEquiv` and
  `WithLp.equiv`. API: `coe_toFiniteGrassmannian`.
- `ℒ.isEmbedding_toFiniteGrassmannian`, and `ℒ.range_toFiniteGrassmannian`
  (the subspaces whose pull-back is Lagrangian). So `ℒ (Fin n)` has the
  subspace topology of `finiteGrassmannian`. The proof is as in decision 2,
  using `Submodule.starProjection_map_apply`.

### `Topology/Grassmannian/Lagrangian/Graph.lean`

The two graph charts of `DESIGN.md` §6, as partial homeomorphisms. The model
is Tau Ceti's `Topology/Grassmannian/Graph.lean`, which does the same for
`TauCeti.finiteGrassmannian`; the building issue credits it.

- `ℒ.continuous_lagrangianChart`, from `lagrangianChart_eq_unitaryFrame`,
  `continuous_realOrthonormalize` and `continuous_unitaryFrame`.
- `ℒ.isOpen_setOf_isCompl (Λ₀ : ℒ ι) : IsOpen {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ _) Λ₀}`.
  For `Λ₀` horizontal, the preimage under `unitaryFrame` is
  `{U | det (U.map im) ≠ 0}`. Translate for general `Λ₀`.
- `ℒ.graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))`,
  the basic chart, with source `{Λ | IsCompl Λ (horizontal ι)}`
  (`range_lagrangianChart`), target `univ`, and inverse `lagrangianChart`.
  API: `graphYChart_source`, `graphYChart_target`, `graphYChart_symm_apply`
  and `graphYChart_lagrangianChart` (both `@[simp]`). Also
  `coe_graphYChart_unitaryFrame`: on the source, the value at
  `unitaryFrame U` is $XY^{-1}$ for `X = U.map re` and `Y = U.map im`. This
  gives continuity on the source through the open quotient map.
- `ℒ.graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))`,
  the chart on the Lagrangians transverse to the vertical subspace, with
  source `{Λ | IsCompl Λ (vertical ι)}` (`range_graphPoint`), target
  `univ`, and inverse `graphPoint`. It is the homeomorphism `symJ ι ℝ • ·`
  of `ℒ ι`, then `graphYChart`, then the homeomorphism `S ↦ -S`; this is
  `symJ_smul_graphPoint`. API: `graphChart_source`, `graphChart_target`,
  `graphChart_symm_apply` and `graphChart_graphPoint` (both `@[simp]`).

### `Topology/Grassmannian/Lagrangian/Fibration.lean`

Path lifting along the unitary frame map (G3). The model is Tau Ceti's unitary
Stiefel fibration, `Topology/Grassmannian/StiefelFibration/Unitary.lean`,
built the same way; the building issue credits it.

- `ℒ.exists_trivialization_unitaryFrame (Λ : ℒ ι) :
  ∃ e : Bundle.Trivialization (realSubgroup ι) unitaryFrame, Λ ∈ e.baseSet`.
  Write `Λ = U • vertical ι` (`MulAction.exists_smul_eq`). Over the open
  set `U • {Λ' | IsCompl Λ' (horizontal ι)}`, which contains `Λ` because the
  vertical subspace is the chart point of `0`, the section is
  `Λ' ↦ U * realOrthonormalize (S + i·1)`, where `S` is the chart value of
  `U⁻¹ • Λ'` in `graphYChart`. Tau Ceti's
  `Subgroup.localSectionTrivializationOfCosetFibers` makes the
  trivialization, with fibres given by `unitaryFrame_eq_unitaryFrame_iff`.
- `ℒ.hasHomotopyLiftingProperty_unitaryFrame (A)`, from Tau Ceti's
  `hasHomotopyLiftingProperty_of_exists_trivialization`. `ℒ ι` is compact
  Hausdorff, hence normal and paracompact. Path lifting is then Tau Ceti's
  `HasHomotopyLiftingProperty.exists_path_lift` applied to it, with no
  restatement here.
- The same fact in the categorical form that Tau Ceti's fibration results
  use, `ℒ.unitaryFrame_mem_serreFibrations`, by Tau Ceti's
  `TopCat.mem_serreFibrations_of_exists_trivialization`; with it Tau Ceti's
  `TopCat.exists_path_lift_of_mem_serreFibrations` lifts paths too.

### `LinearAlgebra/Symplectic/Standard/Sum.lean`

The direct sum of standard spaces. It belongs with *Standard model*, but only
this part uses it so far.

- `StdSpace.sumEquiv ι κ : StdSpace ι × StdSpace κ ≃ₗ[ℝ] StdSpace (ι ⊕ κ)`,
  which regroups the coordinates by `Equiv.sumSumSumComm`, as Tau Ceti's
  `Matrix.symplecticSum` does. API: `x` and `y` of `sumEquiv ι κ (z, w)`
  (`@[simp]`); `isSymplectomorphism_sumEquiv` from
  `(stdForm ι).prod (stdForm κ)` to `stdForm (ι ⊕ κ)`; and
  `toEuclideanLin_symplecticSum`, which says that `sumEquiv` intertwines
  `toEuclideanLin A × toEuclideanLin B` with
  `toEuclideanLin (Matrix.symplecticSum A B)`.
- `isSymplectomorphism_piLpCongrLeft_sumCongr (e : ι ≃ κ)`: the coordinate
  permutation `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)`
  carries `stdForm ι` to `stdForm κ`.

### `Topology/Grassmannian/Lagrangian/Sum.lean`

Direct sum and reindexing (G5).

- `ℒ.sum : ℒ ι × ℒ κ → ℒ (ι ⊕ κ)`, the image of `Λ.prod Λ'` under
  `sumEquiv`. It is Lagrangian by Tau Ceti's `IsLagrangian.prod` and
  `isLagrangian_map_transport_iff`. API: `coe_sum`; `continuous_sum`, through
  the open quotient map on both factors; `sum_unitaryFrame`, whose value at
  `(unitaryFrame U, unitaryFrame U')` is the frame of
  `Matrix.UnitaryGroup.sum (U, U')` (`@[simp]`); `sum_smul`, with
  `sum (g • Λ, h • Λ') = TauCeti.GLSymplectic.sum (g, h) • sum (Λ, Λ')`;
  `sum_horizontal` and `sum_vertical` (`@[simp]`); `sum_lagrangianChart`
  (a block-diagonal chart value).
- `ℒ.reindex (e : ι ≃ κ) : ℒ ι ≃ₜ ℒ κ`, the image under
  `piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)`. API: `coe_reindex`, `reindex_symm`,
  `reindex_trans`, `reindex_refl`;
  `reindex_unitaryFrame : reindex e (unitaryFrame U) =
  unitaryFrame (Matrix.unitaryReindexContinuousMulEquiv ℂ e U)`, with Tau
  Ceti's reindexing of unitary groups
  (`Topology/Algebra/Matrix/UnitaryGroup.lean`); `reindex_horizontal` and
  `reindex_vertical`.

### `Geometry/Manifold/Instances/LagrangianGrassmannian.lean`

The manifold structure and the milestone.

- `instance : ChartedSpace (selfAdjoint (Matrix ι ι ℝ)) (ℒ ι)`. The chart at
  `Λ` is `U⁻¹ •` followed by `graphYChart`, for the unitary `U` chosen by
  `MulAction.exists_smul_eq (unitaryGroup ι ℂ) (vertical ι) Λ`, so that
  `U • vertical ι = Λ`. The basic
  chart is centred at the vertical subspace, so its translate by `U` contains
  `Λ`. The atlas is the set of all such translates. API:
  `chartAt_symm_apply`, with `(chartAt _ Λ).symm S = U • lagrangianChart S`,
  and `mem_chart_source`.
- `instance : IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι)`. A
  transition map is `S ↦ (A S + B)(C S + D)⁻¹` for the blocks of a real
  symplectic matrix. It is smooth where it is defined, by Mathlib's
  `contDiffAt_ringInverse`.
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
          TauCeti.GLSymplectic.ofUnitary U • ℒ.lagrangianChart S
  ```

  Its docstring ends with "Milestone: *Lagrangian frames and the Lagrangian
  Grassmannian*." The statement keeps the book's hypotheses: real
  $n\times n$ blocks, the standard form, the full symplectic group. It is
  slightly more general, since `ι` is any finite type and not only `Fin n`.
  It needs no entry in `ERRATA.md`. The third item starts from a matrix
  `A ∈ Matrix.symplecticGroup ι ℝ`: `mem_symplecticGroup_iff_forall_stdForm`
  makes `toEuclideanLin A` a symplectomorphism, and
  `IsSymplectomorphism.map_orthogonal` concludes. The dimension item is
  `Matrix.finrank_selfAdjoint`.

## What the part uses

- *Standard model*: `StdSpace`, `StdSpace.x`, `StdSpace.y`, `equivProd`,
  `stdForm`, `stdForm_apply`, `stdForm_compatible`,
  `isSymplectomorphism_sumEquivProd`, `x_complexToRealEuclidean`,
  `y_complexToRealEuclidean` (merged, #41); the matrix dictionary
  `mem_symplecticGroup_iff_forall_stdForm` and
  `TauCeti.conj_complexToRealEuclidean_toLin'` (merged, #62).
- *Symplectic subspaces* (merged, #64):
  `isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq`.
- Tau Ceti:
  - Lagrangian subspaces and graphs: `SymplecticForm.IsLagrangian`,
    `IsLagrangian.two_mul_finrank`,
    `isLagrangian_graph_iff_of_pairing`, `isLagrangian_map_transport_iff`,
    `IsSymplectomorphism.map_orthogonal`, `isLagrangian_prod_iff`,
    `IsLagrangian.prod`, `isLagrangian_prod_top_bot`,
    `isLagrangian_prod_bot_top`, `IsIsotropic.disjoint_map_of_tames`.
  - Frames and charts (`LinearAlgebra/TotallyReal/Euclidean.lean`,
    `Lagrangian.lean`, `LinearAlgebra/Matrix/OfReal.lean`):
    `Matrix.realImage`, `realImage_mul_map_ofReal`,
    `exists_mem_orthogonalGroup_eq_mul_map_ofReal`,
    `map_im_conjTranspose_mul_self_mul_map_ofReal`, `lagrangianChart`,
    `lagrangianChartFrame`, `mem_lagrangianChart`, `lagrangianChart_injective`,
    `lagrangianChart_inj`, `lagrangianChart_inf_realSubspace`,
    `realSubspace`, `IsMaximalTotallyReal`,
    `IsMaximalTotallyReal.two_mul_finrank_eq`,
    `isMaximalTotallyReal_realImage`,
    `det_lagrangianChartFrame_ne_zero`, `realOrthonormalize`,
    `realImage_realOrthonormalize`, `realOrthonormalize_mem_unitaryGroup`,
    `continuous_realOrthonormalize`.
  - Groups: `GLSymplectic`, `GLSymplectic.ofUnitary`,
    `GLSymplectic.coe_ofUnitary`, `continuous_ofUnitary`,
    `GLSymplectic.mulEquivSymplecticGroup`,
    `SymplecticGroup.fromBlocks_upper_mem`,
    `GLSymplectic.symJ`, `GLSymplectic.sum`, `continuous_sum`,
    `Matrix.symplecticSum`, `Matrix.UnitaryGroup.sum`,
    `Matrix.UnitaryGroup.continuous_sum`, `GLOrthogonal`,
    `GLOrthogonal.inf_unitarySubgroup_eq_map_real`,
    `Matrix.unitaryReindexContinuousMulEquiv`, the `CompactSpace` instance of
    `unitaryGroup`.
  - Topology: `finiteGrassmannian`,
    `finiteGrassmannian.continuous_starProjection_toEuclidean`,
    `quotientStabilizerHomeomorph`, `quotientStabilizerHomeomorph_mk`,
    `Homeomorph.Quotient.congrRight_mk`,
    `Subgroup.localSectionTrivializationOfCosetFibers`,
    `hasHomotopyLiftingProperty_of_exists_trivialization`,
    `HasHomotopyLiftingProperty.exists_path_lift`,
    `TopCat.mem_serreFibrations_of_exists_trivialization`,
    `TopCat.exists_path_lift_of_mem_serreFibrations`.
  - Models that the building issues credit: Tau Ceti's
    `Topology/Grassmannian/Graph.lean` and
    `Topology/Grassmannian/StiefelFibration/Unitary.lean`.
- Mathlib: `Submodule.starProjection`, `Submodule.starProjection_map_apply`,
  `Submodule.isCompl_iff_disjoint`, `Matrix.fromRows`, `Matrix.rank`,
  `Matrix.toEuclideanLin`, `EuclideanSpace.equiv`, `LinearMap.graph`,
  `LinearEquiv.prodComm`, `Submodule.toLinearPMap`,
  `Submodule.toLinearPMap_graph_eq`, `Submodule.existsUnique_from_graph`,
  `Sym2.lift`, `Sym2.card`, `Nat.choose_two_right`,
  `Module.finrank_fintype_fun_eq_card`, `Homeomorph.Quotient.congrRight`,
  `MulAction.compHom`, `MulAction.exists_smul_eq`, `MulAction.stabilizer`,
  `unitarySubgroupUnitsEquiv`, `IsQuotientMap.continuous_iff`,
  `IsOpenQuotientMap.prodMap`, `Topology.IsInducing.of_comp`,
  `LinearIsometryEquiv.piLpCongrLeft`, `contDiffAt_ringInverse`.

Nothing here redefines a Mathlib or Tau Ceti notion. The new definitions are
`LagrangianGrassmannian` with its topology, `realSubgroup` (Tau Ceti's
$\mathrm{O}(n)\subset\mathrm{U}(n)$ carried from `GL ι ℂ` to
`unitaryGroup ι ℂ`), `StdSpace.graph`, `StdSpace.graphY`,
`StdSpace.sumEquiv`, `Matrix.selfAdjointEquivSym2`, the unitary action, and
the maps `ofFrame`, `unitaryFrame`, `lagrangianChart`, `graphPoint`,
`graphYChart`, `graphChart`, `sum`, `reindex` and `toFiniteGrassmannian`
on the new type. Tau Ceti has a
`Matrix.lagrangianChart` on `EuclideanSpace ℂ ι`, but no space of Lagrangian
subspaces, no topology on one, and no real graph on `StdSpace ι`. Each new
map comes with its comparison to Tau Ceti's object.

## Interface with *Maslov index*

| Item of `design/maslov-index.md` | Here |
|---|---|
| G1, `V₀ ι`, `V₁ ι` | `ℒ.horizontal ι`, `ℒ.vertical ι` |
| G2, unitary frames, $\mathrm{U}(n)/\mathrm{O}(n)$ | `ℒ.unitaryFrame`, `unitaryFrame_surjective`, `unitaryFrame_eq_unitaryFrame_iff`, `quotientHomeomorph`; continuity of maps out of `ℒ ι` by `isQuotientMap_unitaryFrame.continuous_iff` |
| G3, path lifting | `hasHomotopyLiftingProperty_unitaryFrame` with Tau Ceti's `HasHomotopyLiftingProperty.exists_path_lift` |
| G4, the action | the `MulAction` and `ContinuousSMul` instances, `unitaryFrame_mul` |
| G5, sum and reindexing | `ℒ.sum`, `ℒ.reindex` and their compatibilities |
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
   `LinearAlgebra/Symplectic/Lagrangian/Frame.lean`: the complex frame facts,
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
   `lagrangianChart`, `graphPoint`, the transverse-chart facts, and both
   transverse-pair results. About 350 lines. Blocked by 5.
7. **The quotient topology.** `Topology/Grassmannian/Lagrangian/Quotient.lean`.
   About 300 lines. Blocked by 4 and 5.
8. **Comparison with `finiteGrassmannian`.** `Topology/Grassmannian/Lagrangian/Finite.lean`.
   About 200 lines. Blocked by 7.
9. **The graph charts.** `Topology/Grassmannian/Lagrangian/Graph.lean`:
   `graphYChart` and `graphChart`. About 300 lines. Blocked by 6 and 7.
10. **Path lifting.** `Topology/Grassmannian/Lagrangian/Fibration.lean`.
    About 200 lines. Blocked by 9.
11. **Direct sums and reindexing.** `LinearAlgebra/Symplectic/Standard/Sum.lean`
    and `Topology/Grassmannian/Lagrangian/Sum.lean`. About 350 lines. Blocked
    by 6 and 7.
12. **The manifold structure and the milestone.**
    `LinearAlgebra/Matrix/SelfAdjoint.lean` and
    `Geometry/Manifold/Instances/LagrangianGrassmannian.lean`. About 450
    lines. Blocked by 9.
13. **The range of Tau Ceti's chart.** `LinearAlgebra/TotallyReal/Euclidean.lean`:
    `Matrix.exists_isSymm_eq_lagrangianChart` and its example. About 120
    lines. Blocked by 3.

The Lagrangian issues of *Maslov index* wait for 6, 7, 9, 10 and 11. Issues 8,
12 and 13 are not needed there.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.3.
* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993],
  §2, for the graph chart relative to the horizontal subspace.
