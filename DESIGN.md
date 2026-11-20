# Design

This is the overview of the library's design, as `AGENTS.md` describes it: the
parts of the library, the folders and files each part owns, the definitions
that several parts share, which parts build on which, and the part (or the
existing Mathlib or Tau Ceti declaration) that proves each milestone of the
plan. A part may have a detailed design of its own in `design/<part>.md`,
where `<part>` is the part's name below; the parts that need one are marked.

The first page of the plan that this design covers is
`atlas/linear-symplectic-geometry.md` (McDuff–Salamon [McDuffSalamon2017],
Chapter 2; for the Maslov index of paths also Robbin–Salamon
[RobbinSalamon1993]). The parts are named after their mathematics, not after
that page, so that the next pages (`atlas/symplectic-manifolds.md`,
`atlas/almost-complex-structures.md`, …) extend them or add parts beside them.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions: Tau Ceti `v4.37.0-rc1` (commit `e0e414c`, see
`lakefile.toml`) and the Mathlib it pins. Paths of Tau Ceti files are given
relative to `.lake/packages/TauCeti/TauCeti/`.

## Principles

- **Tau Ceti is the base, not a competitor.** Tau Ceti already has most of the
  linear theory: symplectic forms, Lagrangian subspaces, Darboux bases, the
  symplectic matrix group with its polar decompositions and maximal compact
  subgroup, complex structures with compatibility and taming, the Cayley
  transform, the Maslov index of symplectic loops and of totally real loops,
  and the complex coordinate model `ι → ℂ` with its splitting
  `TauCeti.complexToRealEuclidean`. The library never redefines these
  notions. It adds the missing theorems about them, in the namespace of the
  notion they are about (`Matrix.…`, `SymplecticGroup.…`,
  `TauCeti.SymplecticForm.…`, `TauCeti.GLSymplectic.…`), so that they can move
  into Tau Ceti unchanged, and new notions in `SymplecticGeometry`.
- **One representation per notion.** Where Tau Ceti has two models of the same
  object (for example `Matrix.symplecticGroup` and `TauCeti.GLSymplectic`),
  the library states results in the model the surrounding Tau Ceti API uses,
  and does not add a third. A complex structure is always a
  `TauCeti.AlmostComplexStructure`; matrices with square $-1$ are reached only
  through a homeomorphism with it.
- **Transport rather than re-derive.** Tau Ceti states much of the theory on
  `ι → ℂ` or on `V × V`. The library's own model is reached from these by
  `complexToRealEuclidean` and `EuclideanSpace.sumEquivProd`, and the
  structures on it are defined as transports along them, so that the results
  move with them.
- **Shared definitions come first and are few.** The only part that many
  others wait for is *Standard model*, which is small (a few hundred lines)
  and has no theorems of substance. Everything else can be built in parallel
  once its direct prerequisites are merged; the graph below has depth at most
  four.
- **Files do not clash with Tau Ceti's.** A folder of this library never has
  the name of a Tau Ceti file at the same place (no `Foo/` here beside Tau
  Ceti's `Foo.lean`), so that both can move upstream as they are. A file of
  this library may have the name of a Tau Ceti file: upstream, the two merge.

## Conventions

The library uses McDuff–Salamon's conventions for the linear theory. Each
convention is fixed by a lemma, mostly of *Standard model*, and later parts
rewrite with that lemma rather than recompute a sign. The plan's sign
conventions for manifolds (`auxiliary/02-signs.md`) concern Hamiltonian
vector fields and moment maps, which the linear theory does not use; the parts
that later pages add follow them.

- **The model space.** `StdSpace ι` is `EuclideanSpace ℝ (ι ⊕ ι)` for a finite
  type `ι` (usually `Fin n`), with `StdSpace.x z i = z (Sum.inl i)` and
  `StdSpace.y z i = z (Sum.inr i)`. Three reasons fix this choice. Mathlib
  indexes `Matrix.J ι ℝ` and `Matrix.symplecticGroup ι ℝ` by `ι ⊕ ι`, so a
  matrix acts on the model through `Matrix.toEuclideanLin` with no
  reindexing. Tau Ceti's `complexToRealEuclidean ι : (ι → ℂ) ≃L[ℝ]
  StdSpace ι` lands in it, real parts at `inl`, imaginary parts at `inr`. And
  its norm is the Euclidean norm of all $2n$ coordinates. The norm of a Lean
  product `E × F` is the larger of the two norms, so metric statements
  (balls, cylinders, ellipsoids, widths) are never made on
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.
- **$\omega_0$ and $J_0$.** `stdForm ι` and `stdComplexStructure ι` are the
  transports of `TauCeti.stdComplexPiSymplecticForm ι` and of multiplication
  by `I` on `ι → ℂ` along `complexToRealEuclidean ι`. *Standard model* proves:
  `stdForm_apply`, $\omega_0(z,w)=\sum_i(x_i(z)y_i(w)-y_i(z)x_i(w))$;
  `stdComplexStructure_x` and `stdComplexStructure_y`, $x(J_0z)=-y(z)$ and
  $y(J_0z)=x(z)$, that is, $J_0$ is `Matrix.toEuclideanLin (Matrix.J ι ℝ)`;
  `stdForm_apply_eq_inner`, $\omega_0(z,w)=\langle J_0z,w\rangle$; and
  `stdForm_toBilinForm`, that $\omega_0$ is `-Matrix.toBilin' (Matrix.J ι ℝ)`
  read through `WithLp`. For `ι = Fin n` the last one says that Tau Ceti's
  `stdSymplecticBilinForm ℝ n` is $-\omega_0$.
- **The symplectic group.** Mathlib's membership condition is $AJA^T=J$. The
  condition that $A$ preserves $\omega_0$, $A^TJA=J$, is
  `SymplecticGroup.mem_iff'`, and *Standard model*'s
  `mem_symplecticGroup_iff_isSymplectomorphism` turns either into a statement
  about `Matrix.toEuclideanLin A`. Topological statements (paths, loops,
  homotopies, the Maslov index) use Tau Ceti's subgroup
  `TauCeti.GLSymplectic ι ℝ` of `GL (ι ⊕ ι) ℝ`, as Tau Ceti's Maslov index
  does.
- **Bases from a Gram matrix.** The `(inr i, inl j)` entry of `Matrix.J` is
  $\delta_{ij}$ and the `(inl i, inr j)` entry is $-\delta_{ij}$. So for a
  basis `b` with `Matrix.J` as Gram matrix, the pairs of the book with
  $\omega(u_j,v_k)=\delta_{jk}$ are $u_j=$ `b (inr j)` and $v_j=$ `b (inl j)`.
  Tau Ceti's `TauCeti.SymplecticForm.IsDarbouxBasis` is already in the book's
  normalization. A statement that produces a basis says in its docstring which
  of the two it uses.
- **Tau Ceti's objects with another sign or factor.** Tau Ceti's definitions
  are used as they are. A milestone that involves one of them is stated with
  the book's object, written as `-` or `2⁻¹ •` of Tau Ceti's, not as a new
  definition:

  | Tau Ceti | The book's object |
  |---|---|
  | `TauCeti.stdSymplecticBilinForm` | $-$ it is $\omega_0$ (see above) |
  | `TauCeti.SymplecticForm.twistedProd` | $-$ it is $(-\omega_1)\oplus\omega_2$; the Lagrangians agree, Maslov indices of loops change sign |
  | `TauCeti.SymplecticForm.symmetrizedBilinForm` | $2^{-1}$ times it is $g_{\omega,J}$ |
  | the Cayley transform of a tame $J$ (`Geometry/Symplectic/Cayley/`) | $-$ it is the book's $W$ |

- **Polar decompositions.** Tau Ceti has both. `Units.polarUnitary_mul_sqrt_star_mul`
  (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`) is the
  right decomposition $A=U\sqrt{A^*A}$ in any C*-algebra, with uniqueness
  `Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`; for matrices,
  `SymplecticGroup.polarUnitary_mem` and `SymplecticGroup.sqrt_mul_star_mem`
  (`Analysis/Matrix/Polar/Symplectic.lean`) say that the unitary factor and
  the factor $\sqrt{AA^*}$ of a symplectic $A$ are symplectic. The book's $U$
  is `Units.polarUnitary`.
- **Maslov indices.** The normalizations are the book's: the loop
  $t\mapsto e^{2\pi it}$ of $\mathrm{U}(1)$ has index $1$, and so has the loop
  $t\mapsto e^{\pi it}\mathbb{R}$ in $\mathcal{L}(1)$. If a later part defines
  the Robbin–Salamon index for paths of matrices in $\mathrm{Sp}(2n)$, which on loops is
  twice the book's index, its name and docstring say so.
- **Loops and homotopies.** A loop is a `Path x x` on the unit interval, as in
  Tau Ceti. Homotopy of loops means free homotopy through loops (a continuous
  `F : I × I → X` with `F (s, 0) = F (s, 1)`), the hypothesis of Tau Ceti's
  `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`. The *Maslov index* part
  fixes the predicate for it, reusing Tau Ceti's free loop spaces in
  `Topology/MappingSpace/FreeLoop.lean` if they fit.
- **Exterior powers.** $\omega^n$ is Tau Ceti's
  `ContinuousAlternatingMap.wedgePow`, which is $n!$ on a Darboux basis.

## Shared definitions

These notions are used by several parts. All are reused from Tau Ceti or
Mathlib, except the three definitions of *Standard model* and the bundle
complex structures of *Symplectic vector bundles*, which *First Chern number*
also uses.

| Notion | Representation | Where |
|---|---|---|
| Symplectic vector space $(V,\omega)$ over $\mathbb{R}$ | `[AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : TauCeti.SymplecticForm V)` | Tau Ceti |
| Symplectic form over a field `k` | `ω : LinearMap.BilinForm k V` with `ω.IsAlt` and `ω.Nondegenerate` | Mathlib |
| $\omega_0$ on $k^{2n}$ | `-TauCeti.stdSymplecticBilinForm k n` | Tau Ceti |
| $W^\omega$; isotropic, coisotropic, symplectic, Lagrangian subspaces | `TauCeti.SymplecticForm.orthogonal`, `IsIsotropic`, `IsCoisotropic`, `IsSymplectic`, `IsLagrangian` | Tau Ceti |
| Linear symplectomorphism | `TauCeti.SymplecticForm.IsSymplectomorphism` | Tau Ceti |
| $\mathrm{Sp}(2n)$ | `Matrix.symplecticGroup ι ℝ`; as a topological group `TauCeti.GLSymplectic ι ℝ` | Mathlib, Tau Ceti |
| $\mathrm{U}(n)$ inside $\mathrm{Sp}(2n)$ | `Matrix.unitaryGroup ι ℂ` with `Matrix.realify`, `TauCeti.GLSymplectic.ofUnitary` | Mathlib, Tau Ceti |
| Linear complex structure, with its topology | `TauCeti.AlmostComplexStructure V` (topology in `Geometry/Symplectic/AlmostComplex/Topology.lean`) | Tau Ceti |
| Compatible, tame | `TauCeti.SymplecticForm.Compatible`, `TauCeti.SymplecticForm.Tames` | Tau Ceti |
| $J_{g,\omega}$ (ambient $g$) | `TauCeti.SymplecticForm.polarComplexStructure` | Tau Ceti |
| $\mathbb{C}^n\cong\mathbb{R}^{2n}$ | `TauCeti.complexToRealEuclidean` (`Analysis/Complex/Euclidean/Space.lean`) | Tau Ceti |
| Degree of a circle loop | `Circle.degree` (`Topology/Circle/Degree.lean`) | Tau Ceti |
| Maslov index of a symplectic loop | `TauCeti.GLSymplectic.maslovIndex` (`Analysis/Matrix/SymplecticGroup/Maslov.lean`) | Tau Ceti |
| Continuous complex structure on a real vector bundle | `TauCeti.Bundle.ContinuousComplexStructure` (`Topology/VectorBundle/Complex/Structure.lean`) | Tau Ceti |
| $C^n$ complex structure on a smooth real vector bundle, with its topology | `SymplecticGeometry.Bundle.ContMDiffComplexStructure`, generalizing `TauCeti.ContMDiffAlmostComplexStructure I n M` with its field names and its `n`, mapping to the continuous one; on $TM$ identified with `ContMDiffAlmostComplexStructure` for every $n$, and with `TauCeti.SmoothAlmostComplexStructure` through `smoothEquiv` | *Symplectic vector bundles* |
| Bundle metrics $\mathrm{Met}(E)$, with their topology | `Bundle.ContMDiffRiemannianMetric` with Tau Ceti's `frameTopology` (`Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`) | Mathlib, Tau Ceti |
| $\mathbb{R}^{2n}$, $\omega_0$, $J_0$ | `SymplecticGeometry.StdSpace ι`, `SymplecticGeometry.stdForm ι`, `SymplecticGeometry.stdComplexStructure ι` | *Standard model* |

### Standard model: the definitions and their API

- `StdSpace ι := EuclideanSpace ℝ (ι ⊕ ι)`, an `abbrev`.
- Coordinates: `StdSpace.x, StdSpace.y : StdSpace ι →ₗ[ℝ] (ι → ℝ)`, with `ι`
  implicit so that `z.x` and `z.y` elaborate by dot notation; they come with
  `@[simp]` lemmas `StdSpace.x_apply`, `StdSpace.y_apply`; `StdSpace.ext`
  (`z.x = w.x → z.y = w.y → z = w`, tagged `@[ext]`); the constructor
  `StdSpace.equivProd ι : StdSpace ι ≃ₗ[ℝ] (ι → ℝ) × (ι → ℝ)` (built from
  `EuclideanSpace.equiv` and `ContinuousLinearEquiv.sumPiEquivProdPi`), with `@[simp]`
  lemmas for `x`, `y` of `(equivProd ι).symm (a, b)` and for
  `equivProd ι z = (z.x, z.y)`; and `x`, `y` of
  `complexToRealEuclidean ι u` as the real and imaginary parts of `u`.
- `stdForm ι : TauCeti.SymplecticForm (StdSpace ι)`, defined as
  `(stdComplexPiSymplecticForm ι).transport
  (complexToRealEuclidean ι).toLinearEquiv`, with
  `stdForm_def` (by `(rfl)`), `@[simp] stdForm_apply` in terms of `x` and `y`,
  `stdForm_toBilinForm` (the relation with `Matrix.toBilin' (Matrix.J ι ℝ)`),
  and `stdForm_apply_eq_inner`.
- `stdComplexStructure ι : TauCeti.AlmostComplexStructure (StdSpace ι)`,
  defined as the transport of `AlmostComplexStructure.ofComplexModule (ι → ℂ)`
  along the same map, with `stdComplexStructure_def`, `@[simp]` lemmas
  `stdComplexStructure_x` and `stdComplexStructure_y`,
  `stdComplexStructure_eq_toEuclideanLin_J`, and
  `stdForm_compatible : (stdForm ι).Compatible (stdComplexStructure ι)`, which
  is `stdComplexPiSymplecticForm_compatible.transport`.
- The comparison with Tau Ceti's product model: the symplectomorphism from
  `stdForm ι` to `stdSymplecticForm` on
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` along
  `EuclideanSpace.sumEquivProd`, carrying `stdComplexStructure ι` to
  `AlmostComplexStructure.product`.
- The matrix dictionary: `mem_symplecticGroup_iff_isSymplectomorphism`
  (`A ∈ Matrix.symplecticGroup ι ℝ` if and only if `Matrix.toEuclideanLin A`
  preserves `stdForm ι`); a real matrix commutes with `Matrix.J` if and only if
  its map commutes with `stdComplexStructure ι`; and the complex side, from Tau
  Ceti's `Matrix.realify_I_smul_one` and `complexToRealEuclidean_mulVec`
  (`Analysis/Complex/Euclidean/Matrix.lean`): `complexToRealEuclidean`
  intertwines a complex matrix with its `Matrix.realify`.

## Parts

Each part lists its folder and files, what it builds on, and the milestones it
proves. Files are under `SymplecticGeometry/`. A part's files may be split
further when they grow, following `AGENTS.md`.

### 1. Standard model

- **Files:** `LinearAlgebra/Symplectic/Standard/Basic.lean` (`StdSpace`, its
  coordinates, `stdForm`, `stdComplexStructure`, the product comparison),
  `LinearAlgebra/Symplectic/Standard/Matrix.lean` (the matrix dictionary).
- **Builds on:** Mathlib, Tau Ceti.
- **Milestones:** none. It is the interface the other parts share.

### 2. Symplectic vector spaces

- **Files:** `LinearAlgebra/Symplectic/Darboux.lean` (over any field `k`, the
  isometry of an alternating nondegenerate form on a space of dimension $2n$
  with `-stdSymplecticBilinForm k n` on `Fin n ⊕ Fin n → k`, from Tau Ceti's
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and
  `Module.Basis.isometryEquivOfToMatrixEq`, with the basis reordered as in
  *Conventions*; its properties come from `isAlt_stdSymplecticBilinForm`,
  `stdSymplecticBilinForm_nondegenerate` and
  `stdSymplecticBilinForm_single_single` through negation; over $\mathbb{R}$
  the same with `stdForm`),
  `LinearAlgebra/Symplectic/Subspace.lean` (isotropic if and only if the
  complement is coisotropic; every isotropic subspace lies in a Lagrangian
  one), `LinearAlgebra/Symplectic/Reduction.lean` (for coisotropic $W$, the
  form on $W/W^\omega$ and its uniqueness, from Tau Ceti's `reduction`, whose
  quotient is by $W\cap W^\omega=W^\omega$).
- **Builds on:** *Standard model*.
- **Milestones:** *Linear Darboux theorem*, *Symplectic complements*,
  *Lagrangian extension lemma*, *Linear symplectic reduction*.

### 3. Symplectic group

- **Files:** `LinearAlgebra/Matrix/SymplecticGroup/Spectrum.lean` (eigenvalue
  pairing $\lambda\leftrightarrow\lambda^{-1}$ with algebraic multiplicities,
  even multiplicity at $\pm1$, $\omega_0$-orthogonality of eigenvectors for
  $\lambda\lambda'\neq1$ with the bilinear extension; from Tau Ceti's
  `SymplecticGroup.charpoly_inv`, `SymplecticGroup.reflect_charpolyRev` and
  `LinearMap.IsAdjointPair.apply_eq_zero_of_mem_genEigenspace`),
  `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean` (algebraic facts beside
  Mathlib's `SymplecticGroup.transpose_mem`, over a commutative star ring:
  `SymplecticGroup.star_mem` and `SymplecticGroup.star_mem_iff`),
  `Analysis/Matrix/Polar/Basic.lean` (the general right polar decomposition
  of `GL n 𝕜` over `RCLike 𝕜`, beside Tau Ceti's left forms:
  `Matrix.GeneralLinearGroup.posDef_sqrt_star_mul` and
  `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`),
  `Analysis/Matrix/Polar/Symplectic.lean` (the right decomposition
  $\Psi=UP$ with uniqueness, `SymplecticGroup.existsUnique_unitary_mul_posDef`:
  Tau Ceti's `Units.polarUnitary_mul_sqrt_star_mul` gives the factorization,
  `Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef` its uniqueness,
  and `SymplecticGroup.polarUnitary_mem` makes $U$ symplectic; what this file
  adds for the symplectic group is `SymplecticGroup.sqrt_star_mul_mem`, that
  $\sqrt{\Psi^*\Psi}$ is symplectic, $\Psi^*$ the conjugate transpose, which
  is `SymplecticGroup.sqrt_mul_star_mem` applied to `star Ψ`, symplectic by
  `SymplecticGroup.star_mem`),
  `Analysis/Matrix/Polar/GLSymplectic.lean` (the deformation retraction:
  `TauCeti.GLSymplectic.polarHomotopy` fixes $\mathrm{U}(n)$ at all times,
  since it is the restriction of `Matrix.GeneralLinearGroup.polarHomotopy`
  (`Analysis/Matrix/Polar/Deformation.lean`), a homotopy relative to the
  unitary elements of $\mathrm{GL}(2n,\mathbb{R})$, that is, to $\mathrm{O}(2n)$, and
  $\mathrm{U}(n)=\mathrm{Sp}(2n)\cap\mathrm{O}(2n)$; at time $t$ it is `polarDeformation`, $P^{1-t}U$ for
  $\Psi=PU$, which a short computation identifies with the book's
  $f_t(\Psi)=\Psi(\Psi^T\Psi)^{-t/2}$; so it is a homotopy rel $\mathrm{U}(n)$ from the
  identity to the retraction, and the inclusion
  $\mathrm{U}(n)\to\mathrm{Sp}(2n)$ is a `ContinuousMap.HomotopyEquiv`, by
  Tau Ceti's `ContinuousMap.HomotopyEquiv.ofDeformationRetraction`).
- **Builds on:** Mathlib, Tau Ceti.
- **Milestones:** *Spectrum of a symplectic matrix*, *Symplectic polar
  decomposition and the maximal compact subgroup*.

### 4. Unitary group topology

- **Files:** first two general files, named like the Tau Ceti files they
  extend so that the two merge upstream.
  `Topology/Grassmannian/StiefelFibration/ForgetLast.lean`: over any
  `RCLike 𝕜`, the homotopy groups of the space of unit vectors
  `finiteOrthonormalFrame 𝕜 1 N` vanish below degree
  $\dim_{\mathbb{R}}\mathbb{k}^N-1$, in the namespace
  `TauCeti.finiteOrthonormalFrame`, beside the real
  `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`, under a name
  of its own that its issue checks is unused there (for example
  `subsingleton_homotopyGroup_unitVector`). Tau Ceti's
  `TauCeti.ComplexProjectiveSpace.subsingleton_homotopyGroup_sphere`
  (`Topology/ComplexProjectiveSpace/Hopf/Exact.lean`) is the sphere-level
  statement over $\mathbb{C}$. It identifies
  the space with the unit sphere of `EuclideanSpace 𝕜 (Fin N)` by
  `TauCeti.finiteOrthonormalFrame.forgetLastFiberSphere` at the $0$-frame
  (`Topology/Grassmannian/ForgetLast.lean`) and applies
  `TauCeti.subsingleton_homotopyGroup_sphere_of_lt`
  (`AlgebraicTopology/Sphere/HomotopyGroup.lean`), which holds in any real
  normed space of finite dimension, so $\mathbb{C}^N$ is never compared with
  $\mathbb{R}^{2N}$. `Topology/Grassmannian/StiefelFibration/Stability.lean`:
  the stable range `Matrix.UnitaryGroup.isNConnected_fromBlocksOne`, in the
  namespace of Tau Ceti's `fromBlocksOne`, `detCircle` and
  `instPathConnectedSpace` for Mathlib's `Matrix.unitaryGroup`. It is stated
  over any `RCLike 𝕜`, with the hypothesis
  `2 ≤ Module.finrank ℝ 𝕜 * (m + 1)`: the block inclusion `fromBlocksOne` of
  $\mathrm{U}(m,\mathbb{k})$ in $\mathrm{U}(1+m,\mathbb{k})$ is
  `Module.finrank ℝ 𝕜 * (m + 1) - 2`-connected. For $\mathbb{k}=\mathbb{C}$
  the hypothesis always holds and the bound is $2m$, the case the milestone
  uses; for $\mathbb{k}=\mathbb{R}$ it gives $\mathrm{O}(m)\to\mathrm{O}(1+m)$
  for $m\ge1$. The hypothesis is needed: for $\mathbb{k}=\mathbb{R}$ and
  $m=0$ the bound truncates to $0$ in `ℕ`, and $\mathrm{O}(0)\to\mathrm{O}(1)=\{\pm1\}$
  does not reach $-1$. It is the analogue of
  `TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne` and is
  proved in the same way. Then
  `Analysis/Matrix/UnitaryGroup/FundamentalGroup.lean`, which holds only the
  milestone: $\det:\mathrm{U}(n)\to S^1$, Tau Ceti's
  `Matrix.UnitaryGroup.detCircle`, induces an isomorphism of fundamental
  groups for $n\ge1$, by induction from $\mathrm{U}(1)\cong S^1$, which is
  Tau Ceti's `Matrix.UnitaryGroup.detCircleEquivOfUnique`
  (`Analysis/Matrix/UnitaryGroup/Torus.lean`, with forward map `detCircle`),
  along the
  stable range, which commutes with $\det$; and its corollary that
  $\mathrm{SU}(n)$ (Mathlib's `Matrix.specialUnitaryGroup`) is simply
  connected, for $n\ge1$ through the homeomorphism
  $\mathrm{U}(n)\cong\mathrm{SU}(n)\times S^1$,
  $A\mapsto(A\operatorname{diag}(\det A^{-1},1,\dots,1),\det A)$, with the
  diagonal factor built by `TauCeti.unitaryTorusHom`, under which
  $\det$ is the second projection, and for $n=0$ because the group is a point.
  Tau Ceti's `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`
  is the case $n=2$. Last, `Analysis/Matrix/SymplecticGroup/FundamentalGroup.lean`
  ($\pi_1(\mathrm{Sp}(2n))\cong\mathbb{Z}$ for $n\ge1$, through *Symplectic
  group*'s homotopy equivalence).
- **Builds on:** Mathlib, Tau Ceti; the last file also on *Symplectic group*.
  The stable range uses Tau Ceti's unitary Stiefel fibration over `RCLike 𝕜`
  with $r=1$: `TauCeti.unitaryFrameMap` ($\mathrm{U}(1+m,\mathbb{k})\to$ unit
  vectors of $\mathbb{k}^{1+m}$) is a Serre fibration
  (`TauCeti.unitaryFrameMap_mem_serreFibrations`,
  `exists_trivialization_unitaryFrameMap`,
  `Topology/Grassmannian/StiefelFibration/Unitary.lean`) whose fibre is the
  block-embedded $\mathrm{U}(m,\mathbb{k})$
  (`TauCeti.unitaryFrameFiberHomeomorph`); the base is a sphere of
  dimension `Module.finrank ℝ 𝕜 * (m + 1) - 1` (for $\mathbb{C}$,
  $S^{2m+1}$), so the fibre inclusion is connected one degree below that, by
  `TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`, which needs a
  path-connected base: the sphere has positive dimension exactly under the
  hypothesis `2 ≤ Module.finrank ℝ 𝕜 * (m + 1)`. Only $r=1$ is
  planned: a general $r$ would need the fibration of frames by `forgetLast`
  over $\mathbb{C}$, which Tau Ceti has only over $\mathbb{R}$, and nothing
  here needs it. Connectedness of $\mathrm{U}(n)$ is Tau Ceti's
  `Matrix.UnitaryGroup.instPathConnectedSpace`, and $\pi_1(S^1)$ is
  `Circle.fundamentalGroupMulEquiv`.
- **Milestones:** *Fundamental group of the unitary group*: the isomorphisms
  for $n\ge1$, and the simple connectivity of $\mathrm{SU}(n)$ for every $n$.
  For $n=0$ both $\mathrm{U}(0)$ and $\mathrm{Sp}(0)$ are trivial groups, while
  $\pi_1(S^1)\cong\mathbb{Z}$. `ERRATA.md` records this, and the part proves
  next to each isomorphism that the group is trivial for $n=0$.

### 5. Maslov index (needs `design/maslov-index.md`)

One part for all Maslov indices, because they share their framework (loops,
free homotopies, the axioms, the uniqueness argument). Its design file splits
it into issues; the overview fixes its folders and its dependencies.

- **Files:** `Analysis/Matrix/SymplecticGroup/Maslov.lean` (symplectic
  loops: the converse of the homotopy axiom from part 4, uniqueness of the
  axiomatic characterization; named like Tau Ceti's file of the same subject,
  so that the two merge upstream), `LinearAlgebra/Symplectic/Lagrangian/Maslov/`
  (loops and paths of Lagrangian subspaces of `StdSpace ι`).
- **Builds on:** *Standard model*, *Symplectic group*, *Unitary group
  topology*, *Lagrangian Grassmannian*. From Tau Ceti, transferred to
  `StdSpace ι` along `complexToRealEuclidean` rather than re-derived: the
  Lagrangian loop index through `realImageLoop`, `maslovIndex_realImageLoop`,
  `maslovPhase_realImage` and `Matrix.UnitaryGroup.maslovIndex_eq_degree`
  (the book's $\det(U^2)$ description); the direct-sum axiom from
  `TotallyRealLoop.maslovIndex_prod`
  (`LinearAlgebra/TotallyReal/Maslov/Prod.lean`); paths relative to a
  Lagrangian from `TotallyRealPath.transverseMaslovIndex`
  (`LinearAlgebra/TotallyReal/Maslov/Transverse.lean`); the crossing-form
  theorems of `Analysis/Matrix/UnitaryGroup/Maslov/` and
  `Analysis/Matrix/HermitianSignature/`.
- **Milestones:** *Maslov index for loops of symplectic matrices*, *Maslov
  index for loops of Lagrangian subspaces*, *Crossing-form formula for the
  Maslov index*, *Maslov index for paths of Lagrangian subspaces*.
- **The design file decides:** how "a function on loops for every $n$" is
  stated for uniqueness (a family indexed by `n : ℕ` on `Fin n`, with the
  direct-sum axiom through `Fin (n + m) ≃ Fin n ⊕ Fin m`); whether the path
  index is real- or $\tfrac12\mathbb{Z}$-valued (Tau Ceti's is real); how a
  general reference Lagrangian $V$ reduces to $\mathbb{R}^n\times\{0\}$ by
  $\mathrm{Sp}(2n)$-transitivity (from *Lagrangian Grassmannian*); the
  dictionary between Lagrangian subspaces of `StdSpace ι` and Tau Ceti's
  totally real subspaces of `ι → ℂ`; and the order of the issues, symplectic
  loops first, since they need only parts 3 and 4.

### 6. Lagrangian Grassmannian (needs `design/lagrangian-grassmannian.md`)

- **Files:** `Topology/Grassmannian/Lagrangian/Basic.lean` (the space
  $\mathcal{L}(V,\omega)$ of Lagrangian subspaces and its topology),
  `LinearAlgebra/Symplectic/Lagrangian/Frame.lean` (the frame criterion
  $\operatorname{rank}=n$, $X^TY=Y^TX$; graphs of symmetric matrices, from Tau
  Ceti's `isLagrangian_graph_iff_of_pairing`),
  `Topology/Grassmannian/Lagrangian/Action.lean` (the action of
  $\mathrm{Sp}(2n)$, transitivity already for $\mathrm{U}(n)$, the stabilizer
  $\mathrm{O}(n)$ and $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$),
  `Topology/Grassmannian/Lagrangian/Graph.lean` (the graph charts by
  symmetric matrices),
  `Geometry/Manifold/Instances/LagrangianGrassmannian.lean` (the manifold
  structure of dimension $n(n+1)/2$, from the charts of `Graph.lean`),
  `LinearAlgebra/TotallyReal/Euclidean.lean` (the range of Tau Ceti's
  `Matrix.lagrangianChart`, beside Tau Ceti's file of that name),
  `Topology/Grassmannian/Lagrangian/Fibration.lean` (path lifting),
  `Topology/Grassmannian/Lagrangian/Sum.lean` (direct sums and reindexing),
  `Topology/Grassmannian/Lagrangian/Transverse.lean` (common transverse
  Lagrangians and transverse pairs). Below, $V_0$ is $\mathbb{R}^n\times\{0\}$
  ($y=0$), $V_1$ is $\{0\}\times\mathbb{R}^n$ ($x=0$), and the unitary frame
  map $\mathrm{U}(n)\to\mathcal{L}(n)$ sends $U$ to the image of $V_0$ under
  `Matrix.toEuclideanLin (Matrix.realify U)`. `design/maslov-index.md` lists
  what the *Maslov index* part needs of the items below.
- **Builds on:** *Standard model*. From Tau Ceti, transferred along
  `complexToRealEuclidean`: the charts `Matrix.lagrangianChart` and
  `Matrix.lagrangianChartCLE` (`LinearAlgebra/TotallyReal/Euclidean.lean`);
  frames and the stabilizer through `Matrix.realImage`,
  `Matrix.exists_mem_orthogonalGroup_eq_mul_map_ofReal` and
  `realOrthonormalize_mem_unitaryGroup`; $\mathrm{Sp}$-transitivity from the
  Witt theorem `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`.
- **Graphs of transverse Lagrangians** (`Frame.lean`). A Lagrangian
  transverse to $V_1$ is $\{y=Sx\}$, and one transverse to $V_0$ is
  $\{x=Sy\}$, for a unique symmetric $S$. This is the converse of the graph
  criterion: Mathlib's `Submodule.exists_eq_graph` gives a linear map whose
  `LinearMap.graph` is the subspace, from the bijectivity of the projection
  onto the complement, and Tau Ceti's `isLagrangian_graph_iff_of_pairing`
  its symmetry; uniqueness is that of a graph.
- **The range of `Matrix.lagrangianChart`**
  (`LinearAlgebra/TotallyReal/Euclidean.lean`, namespace `Matrix`). The
  surjectivity Tau Ceti lacks beside `Matrix.lagrangianChart_injective` and
  `Matrix.lagrangianChart_inf_realSubspace`, in Tau Ceti's terms: a real
  subspace `V` of `EuclideanSpace ℂ n` that is `IsMaximalTotallyReal` for
  multiplication by $i$, is isotropic in the form of
  `Matrix.im_inner_eq_zero_of_mem_lagrangianChart`
  (`(inner ℂ v w).im = 0` for `v w ∈ V`), and has
  `V ⊓ TauCeti.realSubspace n = ⊥` is `lagrangianChart S` for a symmetric
  `S`. The isotropy cannot be dropped: for `n = Fin 2` and
  $S=\begin{pmatrix}0&1\\0&0\end{pmatrix}$, $\det(S+i)=-1$, so
  `lagrangianChart S` is maximal totally real and transverse to
  `realSubspace (Fin 2)`, but by `Matrix.lagrangianChart_injective` it is
  the chart of no symmetric matrix. The statement follows from the second
  graph statement, transferred along `TauCeti.complexToRealEuclidean n`
  composed with `EuclideanSpace.equiv` (`EuclideanSpace ℂ n ≃ (n → ℂ)`); the
  composite carries `TauCeti.realSubspace n` to $V_0$ and
  `lagrangianChart S` to $\{x=Sy\}$.
- **Graph charts** (`Graph.lean`). For the topology the design file picks,
  the Lagrangians transverse to $V_0$, and those transverse to $V_1$, form
  open subsets of $\mathcal{L}(n)$, each homeomorphic to the symmetric
  matrices by the graph statements above; the first chart sends $S$ to the
  transfer of `Matrix.lagrangianChart S`. Tau Ceti's
  `Topology/Grassmannian/Graph.lean` does the same for
  `TauCeti.finiteGrassmannian`. The manifold file and `Fibration.lean` both
  use these charts, so that no `Topology/` file depends on the manifold one.
- **Path lifting** (`Fibration.lean`). The unitary frame map is locally
  trivial with fibre $\mathrm{O}(n)$, hence a Serre fibration, so every path
  in $\mathcal{L}(n)$ lifts to a path in $\mathrm{U}(n)$ from any frame of its
  start point. Its fibres are the left cosets of the real orthogonal matrices
  (from `Action.lean`). Near $V_1$, a continuous section sends $\{x=Sy\}$ to
  `Matrix.GeneralLinearGroup.realOrthonormalize` of
  `Matrix.lagrangianChartFrame S`, transferred (unitary by
  `realOrthonormalize_mem_unitaryGroup`, continuous by
  `continuous_realOrthonormalize`, with the same real image by
  `realImage_realOrthonormalize`), $S$ being the coordinate of the graph
  chart of `Graph.lean` on the Lagrangians transverse to $V_0$; left
  translation by $\mathrm{U}(n)$ gives sections near every point. Tau Ceti's
  `Subgroup.localSectionTrivializationOfCosetFibers`
  (`Topology/Algebra/Group/Quotient/LocalSection.lean`) turns these sections
  into trivializations,
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`
  (`Topology/Homotopy/SerreFibration/FiberBundle.lean`) into a Serre
  fibration, and `TauCeti.TopCat.exists_path_lift_of_mem_serreFibrations`
  (`Topology/Homotopy/SerreFibration/Basic.lean`) into the lift. Tau Ceti's
  unitary Stiefel fibration (`Topology/Grassmannian/StiefelFibration/Unitary.lean`)
  is built the same way and is the model for the file.
- **Direct sums and reindexing** (`Sum.lean`). The direct sum
  $\mathcal{L}(\iota)\times\mathcal{L}(\kappa)\to\mathcal{L}(\iota\oplus\kappa)$,
  read in the coordinates of `Equiv.sumSumSumComm` as Tau Ceti's
  `Matrix.symplecticSum` is, continuous; and for `e : ι ≃ κ` the
  homeomorphism $\mathcal{L}(\iota)\simeq_t\mathcal{L}(\kappa)$, the image
  under the coordinate permutation along `Equiv.sumCongr e e`, with lemmas
  for its inverse and for composition. Both commute with unitary frames: the
  sum of the frames of $U$ and $U'$ is the frame of
  `Matrix.UnitaryGroup.sum (U, U')` (`LinearAlgebra/Matrix/UnitaryGroup/Block.lean`,
  through `Matrix.realify_fromBlocks_zero`), and reindexing the frame of $U$
  gives the frame of the reindexed matrix `U.submatrix e.symm e.symm`, unitary
  by Mathlib's `Matrix.submatrix_equiv_mem_unitary`. The sum is equivariant
  for `TauCeti.GLSymplectic.sum`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Sum.lean`). Continuity
  comes from $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$: the frame map is
  an open quotient map, and so is a product of two such maps (Mathlib's
  `IsOpenQuotientMap.prodMap`). How the
  reindexing meets `GLSymplectic.reindex` is proved with that definition, in
  the *Maslov index* part, so that this part does not depend on it.
- **Transverse Lagrangians** (`Transverse.lean`). Any two Lagrangians
  $\Lambda_1,\Lambda_2$ have a common transverse Lagrangian: move $\Lambda_1$
  to $V_0$ by a unitary matrix; if $X+iY$ is a unitary frame of the moved
  $\Lambda_2$, then $\det(X+tY)$ is a polynomial in $t$ that is nonzero at
  $t=i$, so it has finitely many real roots, and for any other real $t$ the
  Lagrangian $\{x=-ty\}$, the transfer of `Matrix.lagrangianChart` of the
  scalar matrix $-t$ (Tau Ceti's `Matrix.lagrangianChart_smul_one` describes
  it), is transverse to both. And $\mathrm{Sp}(2n)$ acts
  transitively on pairs $(V,W)$ of transverse Lagrangians, each pair being
  $g\cdot(V_0,V_1)$: a unitary matrix takes $V$ to $V_0$; the moved $W$ is
  $\{x=Sy\}$ with $S$ symmetric, by the graph statement above; and the shear
  $\begin{pmatrix}1&S\\0&1\end{pmatrix}$ fixes $V_0$ and takes $V_1$ to
  $\{x=Sy\}$. The shear is symplectic for symmetric $S$ by Tau Ceti's
  `SymplecticGroup.fromBlocks_upper_mem`, for any index type, lifted to
  `TauCeti.GLSymplectic ι ℝ` by
  `(TauCeti.GLSymplectic.mulEquivSymplecticGroup ι ℝ).symm`. For $n=0$ these
  statements hold trivially, $\mathcal{L}(0)$ being a point.
- **Milestones:** *Lagrangian frames and the Lagrangian Grassmannian*.
- **The design file decides:** the topology of $\mathcal{L}(n)$. The
  candidates are the subspace topology of Tau Ceti's
  `TauCeti.finiteGrassmannian ℝ n (2 n)` (`Topology/Grassmannian/`, a
  quotient of frames, but indexed by `Fin N` rather than `ι ⊕ ι`), the
  topology induced by orthogonal projections, or the quotient
  $\mathrm{U}(n)/\mathrm{O}(n)$. Whichever it picks, it proves the others
  homeomorphic, so that the Maslov part can use the quotient description.

### 7. Linear nonsqueezing (needs `design/linear-nonsqueezing.md`)

- **Files:** `Analysis/InnerProductSpace/Symplectic/AffineSymplectic.lean`
  (affine symplectic maps $z\mapsto\Psi z+z_0$, symplectic balls and
  cylinders in `StdSpace ι`), `.../Nonsqueezing.lean` (affine nonsqueezing),
  `.../Ellipsoid.lean` (ellipsoids, their normal form $E(r)$, uniqueness of
  the symplectic spectrum, the volume formula; from Tau Ceti's Williamson
  theorem `TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`,
  with the book's radii $r_k^2=2/\nu_k$), `.../LinearWidth.lean` (the linear
  symplectic width and its value on ellipsoids), `.../Rigidity.lean` (the
  linear nonsqueezing property and linear rigidity).
- **Builds on:** *Standard model*.
- **Milestones:** *Affine nonsqueezing theorem*, *Simultaneous normal form of
  a symplectic form and an inner product*, *Linear symplectic width of an
  ellipsoid*, *Linear symplectic rigidity*.
- **The design file decides:** the value type of the width (`ℝ≥0∞`, so that
  unbounded sets have width $\infty$), how an ellipsoid centred at $0$ is
  given (a positive definite form, or the image of the unit ball under a
  linear isomorphism), and the statement of "symplectic or anti-symplectic".

### 8. Linear complex structures (needs `design/linear-complex-structures.md`)

- **Files:** `LinearAlgebra/ComplexStructure/Standard.lean` (every complex
  structure $J$ on a $2n$-dimensional space is conjugate to
  `stdComplexStructure (Fin n)` by a linear isomorphism $\Phi$: Tau Ceti's
  `ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`
  (`Geometry/Symplectic/Complex/Module/Conjugacy.lean`) gives $\Phi$ from
  `EuclideanSpace ℂ (Fin n)` with multiplication by `I`, composed with
  `complexToRealEuclidean`), `Topology/ComplexStructure/Orbit.lean` (the space
  `AlmostComplexStructure (StdSpace ι)` with Tau Ceti's topology, as the orbit
  of $J_0$ under $\mathrm{GL}(2n,\mathbb{R})$, with stabilizer the realified
  $\mathrm{GL}(n,\mathbb{C})$ by Tau Ceti's
  `Matrix.GeneralLinearGroup.mem_range_realify_iff`; the homeomorphism with
  the quotient; the two components), `Topology/ComplexStructure/Oriented.lean`
  (the component of $J_0$, its homotopy type $\mathrm{SO}(2n)/\mathrm{U}(n)$,
  and the case $\mathbb{R}^4$, homotopy equivalent to $S^2$).
- **Builds on:** *Standard model*.
- **Milestones:** *Linear complex structures are standard*.
- **The design file decides:** how the quotient homeomorphism is obtained (an
  open orbit map, from a local section or from the inverse function theorem on
  `GL`); the models of $\mathrm{GL}(2n,\mathbb{R})/\mathrm{GL}(n,\mathbb{C})$
  and $\mathrm{SO}(2n)/\mathrm{U}(n)$ (Mathlib quotients by subgroups, or a
  space of complex structures compatible with the Euclidean metric); the
  model of $S^2$ and the explicit map for $n=2$; and the issues, a few hundred
  lines each, in that order.

### 9. Compatible complex structures (needs `design/compatible-complex-structures.md`)

- **Files:** `LinearAlgebra/Symplectic/Compatible.lean` (the four equivalent
  characterizations and the two of the exercise, including the converse of
  Tau Ceti's `Compatible.hermitianCore`),
  `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure.lean`
  ($J_{g,\omega}$ for an arbitrary inner product $g$ given as a bilinear form,
  its equivariance under $\mathrm{GL}(V)$, and the lemma identifying it, for
  the ambient inner product, with Tau Ceti's `polarComplexStructure`; Tau
  Ceti's `TauCeti.SymplecticForm.polarComplexStructure_transport` gives the
  equivariance in that case),
  `Topology/Algebra/Module/InnerProducts.lean` (the space $\mathrm{Met}(V)$
  of all inner products on $V$, a convex open subset of the symmetric bilinear forms,
  from Tau Ceti's `TauCeti.convex_setOfPred_posDef` in coordinates),
  `Topology/ComplexStructure/Compatible.lean` (the identification
  $J\mapsto-J_0J$ with the symmetric positive definite symplectic matrices,
  using Tau Ceti's `Compatible.cayleyEquiv`; the homotopy equivalences with
  $\mathrm{Met}(V)$ and between forms and complex structures for fixed $g$;
  the inclusion of compatible into tame structures as a homotopy equivalence;
  the contractions are explicit maps, not only Tau Ceti's contractibility
  instances, see below),
  `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`
  (a compact subgroup of the symplectic group lies in some conjugate of
  $\mathrm{U}(n)$, from Tau Ceti's
  `exists_compatible_forall_isComplexLinearMap` and the transport of a
  compatible pair to $(\omega_0,J_0)$).
- **Builds on:** *Standard model*, *Linear complex structures*.
- **Milestones:** *Characterizations of compatible complex structures*,
  *Contractibility of the space of compatible complex structures*, *Complex
  structures versus symplectic forms*, *Compact subgroups of the symplectic
  group*, *Contractibility of the space of tame complex structures*.
- **The design file decides:** the topology on spaces of forms and complex
  structures (the finite-dimensional topology of `V →ₗ[ℝ] V` and of bilinear
  forms, as Tau Ceti's contractibility instances use the operator norm; it
  checks they agree with Tau Ceti's topology on `AlmostComplexStructure`);
  how the milestones' smoothness and diffeomorphism conjuncts are stated (as
  manifold structures, or as `ContDiff` of the maps in coordinates; the
  nondegenerate forms and the inner products are open in their
  finite-dimensional spaces, but the complex structures lie in the closed set
  $\{J^2=-1\}$ of $\mathrm{End}(V)$, of positive codimension, so for them the
  file chooses between a submanifold structure and maps defined on an open
  neighbourhood in $\mathrm{End}(V)$); and how the GL-equivariant
  constructions are stated so that *Symplectic vector bundles* can apply them
  fibrewise. For that the file delivers the contraction of the compatible
  structures through the Cayley transform, the map $(g,\omega)\mapsto
  J_{g,\omega}$ and the contraction of the tame structures as explicit
  formulas. The two Cayley-transform contractions, taken relative to a
  reference structure $J_0$, are given on the set $U_{J_0}$ of
  $A\in\mathrm{End}(V)$ such that $1-J_0A$ is invertible and
  $1-b\cdot$`cayleyFormula J₀ A` is invertible for every $b\in[0,1]$: the two
  units that `contDiffAt_cayleyPathFormula`
  (`Geometry/Symplectic/Cayley/Smooth.lean`) asks for. This set is open,
  since $[0,1]$ is compact. It does not contain every complex structure
  ($A=-J_0$ gives $1-J_0A=0$), but for an $\omega$-compatible $J_0$ it
  contains the $\omega$-tame structures, hence the compatible ones. The
  first unit is `Tames.isUnit_one_sub_mul_of_toLinearMap`, which needs
  $J_0$ only tame; the second is
  `Compatible.isUnit_one_sub_smul_cayleyFormula`, which needs $J_0$
  compatible (both in `Geometry/Symplectic/Cayley/Smooth.lean`). The
  contractions also take a compatible $J_0$, as Tau Ceti's do. The map $(g,\omega)\mapsto J_{g,\omega}$ is given on the open set
  of pairs of an inner product and a nondegenerate form. All three are
  $C^\infty$ there in the structure (and $J_{g,\omega}$ also in $g$), with all
  derivatives continuous in the time; Tau Ceti's `ContractibleSpace`
  instances give only continuous contractions, which do not suffice.

### 10. Linear Moser

- **Files:** `Geometry/Symplectic/LinearMoser.lean`. Given nondegenerate
  forms $\omega_t$ on $V$ that depend smoothly on $t\in\mathbb{R}$, it builds
  invertible $\Psi_t$, smooth in $t$, starting at the identity and pulling
  each $\omega_t$ back to $\omega_0$: $\Psi_t$ solves $\dot\Psi_t=A_t\Psi_t$,
  with $A_t=-\tfrac12\,\omega_t^{-1}\circ\dot\omega_t$, the inverse being that
  of the contraction $V\to V^*$, so that no inner product is needed. The
  same file treats a smooth path of complex structures in the same way. If
  the bundle case needs smoothness in a parameter as well, the parametric
  version goes in `Analysis/ODE/DysonSeries.lean`, in the namespace
  `SymplecticGeometry` (the lemma is about the function `dysonSeriesLeft`,
  which dot notation does not reach, and a name in `TauCeti` could clash with
  a later Tau Ceti lemma), extending `TauCeti.continuous_parametric_dysonSeriesLeft`
  from continuity to smoothness. Before a series proof, that issue checks
  whether Tau Ceti's `ODE.exists_contDiffOn_picard_solution`
  (`Analysis/ODE/SmoothParameter.lean`) or `TauCeti.contDiff_timeDependentFlow`
  (`Dynamics/Flow/Variational.lean`) already gives it.
- **Builds on:** Tau Ceti's linear equations (`Analysis/ODE/DysonSeries.lean`):
  `TauCeti.dysonSeriesLeft` solves $\dot\Gamma=p\,\Gamma$,
  `TauCeti.contDiff_dysonSeriesLeft` gives a $C^{n+1}$ solution for a $C^n$
  coefficient, and `TauCeti.eq_dysonSeriesLeft_apply` gives uniqueness. So
  this part needs no general ODE theory of its own beyond the parametric
  lemma, which is general material and sits in its own file. It uses no other
  part.
- **Milestones:** *Linear Moser lemma*.
- The construction is canonical, a formula in the family and its derivative,
  so that *Symplectic vector bundles* can apply it at each point of the base.

### 11. Siegel upper half space

- **Files:** `Analysis/Complex/SiegelUpperHalfSpace/Basic.lean` (the space
  $\mathcal{S}_n$ of complex symmetric matrices with positive definite
  imaginary part), `.../Action.lean` (the action of $\mathrm{Sp}(2n)$ by
  $(AZ+B)(CZ+D)^{-1}$, its holomorphy and transitivity, the stabilizer of
  $i\mathbb{1}$), `.../ComplexStructure.lean` (the equivariant bijection with
  the compatible complex structures on `StdSpace ι` and its explicit formula).
  For $n=1$ it is compared with Mathlib's `UpperHalfPlane` action and with Tau
  Ceti's `stdComplexSymplecticForm_tames_iff_im_pos`.
- **Builds on:** *Standard model*; compatibility is Tau Ceti's `Compatible`.
- **Milestones:** *Siegel upper half space*. The proof of transitivity checks
  the formula for $J(Z)$ directly, which breaks the circularity between the
  book's exercise and lemma that the plan points out. The milestone's
  smoothness conjuncts are stated as `ContDiff` of the bijection and its
  inverse in coordinates (symmetric matrices on one side, matrices on the
  other), a decision that the issue for `ComplexStructure.lean` makes
  precise.

### 12. Symplectic vector bundles (needs `design/symplectic-vector-bundles.md`)

- **Files:** `Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`
  (symplectic forms on a smooth real vector bundle, as smooth sections of the
  bundle of alternating maps, Mathlib's
  `ContMDiffVectorBundle.continuousAlternatingMap`, that are fibrewise
  nondegenerate; isomorphisms; local symplectic trivializations and the
  reduction of the structure group to $\mathrm{Sp}(2n)$),
  `Geometry/Manifold/VectorBundle/ComplexStructure.lean` (the one model of
  $C^n$ complex structures on a bundle, `SymplecticGeometry.Bundle.ContMDiffComplexStructure`,
  generalizing from $TM$ to any bundle Tau Ceti's
  `TauCeti.ContMDiffAlmostComplexStructure I n M`
  (`Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean`) with the same
  field names, `toEndomorphism` and `square_neg`, and the same `n : ℕ∞`, and
  following `TauCeti.SmoothAlmostComplexStructure`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Basic.lean` and `Topology.lean`)
  for the topology: a $C^n$ section `toEndomorphism` of the endomorphism
  bundle with square $-1$, `@[ext]` through it, the topology `frameTopology`
  induced from `ContMDiffSection.frameTopology`, and
  `isClosedEmbedding_toEndomorphism_frameTopology`; the map to Tau Ceti's
  `TauCeti.Bundle.ContinuousComplexStructure`, so that its complex bundle is
  available; and for $E=TM$, for every $n$, the identification with
  `ContMDiffAlmostComplexStructure I n M`, under which the map to
  `ContinuousComplexStructure` is Tau Ceti's
  `ContMDiffAlmostComplexStructure.toContinuousComplexStructure`
  (`AlmostComplex/ComplexTangentBundle.lean`), and for $n=\infty$, composed
  with `ContMDiffAlmostComplexStructure.smoothEquiv`, the homeomorphism with
  `SmoothAlmostComplexStructure` for the two `frameTopology`s, so that
  manifolds keep Tau Ceti's models), `.../Symplectic/ComplexStructure.lean`
  (compatible and tame ones, as subtypes like Tau Ceti's for $TM$, existence
  and contractibility, and the converse direction for forms taming a fixed
  $J$; the homotopy equivalence $\omega\mapsto J_{g,\omega}$ on sections,
  with $\mathrm{Met}(E)$ Mathlib's `Bundle.ContMDiffRiemannianMetric` and its
  topology Tau Ceti's `Bundle.ContMDiffRiemannianMetric.frameTopology`, whose
  `continuous_convexCombination_frameTopology` contracts it),
  `.../Symplectic/Classification.lean` (two symplectic bundles
  with tame complex structures are isomorphic as symplectic bundles if and
  only if they are as complex bundles),
  `Geometry/Manifold/VectorBundle/Section/Topology.lean` (the general lemma,
  in the namespace `ContMDiffSection`: for fibre maps
  $\Phi_{p,x}:V_x\to W_x$ depending on a parameter $p\in P$ whose expressions
  in trivializations are $C^n$ in the point and the fibre value, with those
  derivatives up to order $n$ continuous in $p$ as well, the induced map
  $P\times$ `Cₛ^n⟮I; F, V⟯` $\to$ `Cₛ^n⟮I; F', W⟯`, $(p,s)\mapsto\Phi_p\circ s$,
  is jointly continuous for `frameTopology`, for every $n$ including
  $\infty$. The fibre maps may be defined only on an open subset of the
  total space of $V$ that the sections take values in; openness in each
  fibre would not do, since derivatives in trivializations need an open set
  of the total space. Examples are the union over $x\in M$ of the sets
  $U_{J_0(x)}$ of *Compatible complex structures*, for a continuous
  reference section $J_0$ that is compatible at every point (one always
  exists), which contains the
  tame structures, and the fibrewise nondegenerate forms.
  Continuity in the point alone is not enough for $n\ge1$: on the trivial
  line bundle over $\mathbb{R}$, $\Phi_t(x,v)=v+t\sin(x/t)$ is continuous in
  $(t,x,v)$ with $\Phi_0=\mathrm{id}$, but $\partial_x(\Phi_t\circ s-s)=\cos(x/t)$
  does not tend to $0$. The proof goes through
  `ContMDiffSection.continuous_frameTopology_iff`; the file has the name of
  the Tau Ceti file that defines that topology, so that the two merge
  upstream),
  `Geometry/Manifold/VectorBundle/Hermitian/Surface.lean` (unitary
  trivializations along curves and over compact connected oriented surfaces
  with nonempty boundary).
- **Builds on:** *Compatible complex structures*, *Linear Moser*, Mathlib's
  smooth vector bundles and bundle metrics, Tau Ceti's bundle constructions
  (`Topology/VectorBundle/`, `Geometry/Manifold/VectorBundle/`), its section
  spaces with their topology (`Geometry/Manifold/VectorBundle/Section/`), the
  topology on bundle metrics
  (`Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`), its
  almost complex structures on $TM$ with their topology and their tame and
  compatible subtypes
  (`Geometry/Symplectic/Manifold/AlmostComplex/Topology.lean`), its $C^n$
  almost complex structures on $TM$ and their map to continuous complex
  structures (`Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean`,
  `.../AlmostComplex/ComplexTangentBundle.lean`), and its other
  results for $E=TM$ (`Geometry/Symplectic/Manifold/`), which it generalizes
  rather than duplicates.
- **Milestones:** *Symplectic vector bundles are complex vector bundles*,
  *Compatible and tame complex structures on symplectic vector bundles*,
  *Unitary trivializations over surfaces with boundary*.
- **Topology on sections.** The milestones' spaces of sections are subspaces
  of Tau Ceti's section spaces `Cₛ^n⟮I; F, V⟯` (of the bundle of
  endomorphisms, or of alternating maps) with
  `ContMDiffSection.frameTopology` (`Section/Topology.lean`): uniform
  convergence on compact sets of the frame coefficients and of all their
  derivatives up to order $n$. For $n=0$ this is the compact-open $C^0$
  topology, and for $n=\infty$ the compact-open $C^\infty$ topology; the
  milestones are stated for both. The topology is defined from a choice of
  frame domains covering $M$, and
  `ContMDiffSection.frameTopology_eq_of_covers` (`Section/FrameCover.lean`)
  shows it does not depend on the choice, so the statements fix any such
  cover. They are `ContractibleSpace` and `ContinuousMap.HomotopyEquiv` for
  these subspaces. The proofs apply the explicit linear constructions of
  *Compatible complex structures* and *Linear Moser* at each point. These
  are $C^\infty$ in the structure (and, for $J_{g,\omega}$, in $g$) on open
  neighbourhoods in the fibre spaces (for complex structures, the sets
  $U_{J_0(x)}$ of the two Cayley units, relative to a reference section
  $J_0$ that is compatible at every point), with all derivatives continuous in the time of the
  contraction; these neighbourhoods form open subsets of the total spaces
  (for the Cayley sets because $J_0$ is a continuous section, the two units
  are open conditions, and $[0,1]$ is compact), and read in trivializations the maps are $C^n$ there in the
  point and the structure,
  with derivatives continuous in the time, which is the hypothesis of the
  lemma of `Section/Topology.lean`. That lemma makes the induced maps on
  sections, and the contractions $[0,1]\times S\to S$ as a whole, continuous
  for `frameTopology`; `ContMDiffSection.continuous_totalSpace_eval` and
  `locallyConvexSpace_frameTopology` give the evaluation and the convex
  combinations.
- **The design file decides:** the details of
  `ContMDiffComplexStructure` and its subtypes; the precise form of the
  section spaces above (which bundle; the cover, which `frameTopology` takes
  as explicit frames rather than as an instance, so the file fixes once how
  the statements quantify over it); and which surface
  topology the last milestone needs (decomposition of compact surfaces with
  boundary), with an issue for each missing prerequisite.

### 13. First Chern number (needs `design/first-chern-number.md`)

- **Files:** `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean` (the
  first Chern number of a symplectic bundle over a closed connected oriented
  surface, through a splitting of the surface and the Maslov index of the
  overlap loop; the extension lemma for maps from the boundary into
  $\mathrm{Sp}(2n)$), `.../Axioms.lean` (naturality, functoriality,
  additivity, normalization, uniqueness), `.../ChernWeil.lean`,
  `.../EulerNumber.lean` (comparison with Tau Ceti's Euler class and
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`),
  `.../Clutching.lean` (comparison with Tau Ceti's `TauCeti.clutchingNumber`
  (`Topology/VectorBundle/Complex/Clutching.lean`) for the complex bundle
  given by a compatible structure, and with `TauCeti.complexEulerClass`
  (`Topology/VectorBundle/Orientation/Complex/EulerClass.lean`)).
- **Builds on:** *Maslov index* (symplectic loops), *Symplectic vector
  bundles*, Tau Ceti's degree of maps (`TauCeti.HomologicalOrientation.degree`),
  surface genus (`TauCeti.surfaceGenus`), integration of top forms
  (`Geometry/Manifold/DeRham/`), clutching numbers and Euler classes of
  complex bundles.
- **Milestones:** *First Chern number of symplectic vector bundles over
  surfaces*, *Chern–Weil formula for circle bundles over surfaces*, *First
  Chern number as an Euler number*.
- This part needs the most infrastructure that neither library has
  (decomposition of closed surfaces, degree with regular values linked to the
  splitting, principal connections on circle bundles). Its design file lists
  those prerequisites as separate issues before any of its own, and decides
  whether the Chern number is defined by the splitting, as in the book, or
  from `clutchingNumber` or `complexEulerClass`, with the book's description
  as a theorem.

## Dependencies and build order

Each part depends only on the parts listed, besides Mathlib and Tau Ceti.

| Level | Part | Builds on |
|---|---|---|
| 0 | *Standard model* | — |
| 0 | *Symplectic group* | — |
| 0 | *Linear Moser* | — |
| 1 | *Unitary group topology* | *Symplectic group* (only the file on $\mathrm{Sp}(2n)$; the other files can start at once) |
| 1 | *Symplectic vector spaces* | *Standard model* |
| 1 | *Lagrangian Grassmannian* | *Standard model* |
| 1 | *Linear nonsqueezing* | *Standard model* |
| 1 | *Linear complex structures* | *Standard model* |
| 1 | *Siegel upper half space* | *Standard model* |
| 2 | *Compatible complex structures* | *Standard model*, *Linear complex structures* |
| 2 | *Maslov index* | *Standard model*, *Symplectic group*, *Unitary group topology*; its Lagrangian issues also *Lagrangian Grassmannian* |
| 3 | *Symplectic vector bundles* | *Compatible complex structures*, *Linear Moser* |
| 4 | *First Chern number* | *Symplectic vector bundles*, the symplectic-loop issues of *Maslov index* |

The design issues of the parts marked as needing one can start at once, in
parallel with the level-0 parts.

## Milestones

Every milestone of `atlas/linear-symplectic-geometry.md` except the deferred
*Gelfand–Robbin quotient (deferred)*. "Existing" means that a declaration at
the pinned Tau Ceti already proves it in full, so the library adds no
theorem; the close-out of #3 cites that declaration. Otherwise the part named
proves it, using what is listed in the part.

| Milestone | Where |
|---|---|
| *Linear Darboux theorem* | *Symplectic vector spaces*. Existing in part: the basis over any field and evenness are `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and `LinearMap.BilinForm.IsAlt.even_finrank` (`LinearAlgebra/BilinearForm/SymplecticBasis.lean`); the real isomorphism is `TauCeti.SymplecticForm.exists_isSymplectomorphism_stdSymplecticForm_of_finrank_eq`. The library adds the isometry with `-stdSymplecticBilinForm k n` over any field and with `stdForm` over $\mathbb{R}$. |
| *Symplectic complements* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.finrank_add_finrank_orthogonal`, `orthogonal_orthogonal`, `isSymplectic_orthogonal_iff`, `IsLagrangian.two_mul_finrank`, `IsIsotropic.isLagrangian_of_finrank` (`Geometry/Symplectic/Lagrangian/Basic.lean`). The library adds "isotropic if and only if the complement is coisotropic" and states the milestone as one theorem. |
| *Lagrangian extension lemma* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.isLagrangian_iff_maximal_isIsotropic`, `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq` (`LinearAlgebra/BilinearForm/LagrangianBasis.lean`). The library adds that every isotropic subspace lies in a Lagrangian one. |
| *Linear symplectic reduction* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.reduction`, `reduction_mk`, `IsLagrangian.reduction_map` (`Geometry/Symplectic/LinearReduction.lean`), for $W/(W\cap W^\omega)$. The library adds the coisotropic statement and uniqueness. |
| *Nondegeneracy and the top exterior power* | Existing: `ContinuousAlternatingMap.wedgePow_ne_zero_iff` (`Geometry/Symplectic/Volume.lean`), for a two-form on a real space of dimension $2n$ given as a continuous alternating map (every alternating map on a finite-dimensional space is one). |
| *Unitary group as Sp ∩ O ∩ GL(n,C)* | Existing: `Matrix.symplecticGroup_inf_orthogonalGroup`, `Matrix.symplecticGroup_inf_centralizer_J`, `Matrix.orthogonalGroup_inf_centralizer_J` (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean`) identify each pairwise intersection with the image of $\mathrm{U}(n)$ under realification, and the fact that any two of the three conditions imply the third holds for matrices over an arbitrary commutative ring by `SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute`, `SymplecticGroup.commute_J_of_mem_orthogonalGroup` (`LinearAlgebra/SymplecticGroup.lean`). |
| *Spectrum of a symplectic matrix* | *Symplectic group*. |
| *Symplectic polar decomposition and the maximal compact subgroup* | *Symplectic group*. Existing parts: `SymplecticGroup.rpow_mem` (`Analysis/Matrix/Polar/Symplectic.lean`), `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`, `Matrix.isPathConnected_symplecticGroup`, `TauCeti.GLSymplectic.polarHomotopy`; the right decomposition with uniqueness in a C*-algebra (`Units.polarUnitary_mul_sqrt_star_mul`, `Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`). The library adds that the positive factor is symplectic, that the polar homotopy is the book's $f_t$ and fixes $\mathrm{U}(n)$, so that it is a deformation retraction, and the homotopy equivalence. |
| *Fundamental group of the unitary group* | *Unitary group topology*: the isomorphisms for $n\ge1$ (see `ERRATA.md`), and, as a corollary, $\mathrm{SU}(n)$ simply connected for every $n$. Existing in part: the case $\mathrm{SU}(2)$, `Matrix.instSimplyConnectedSpaceSpecialUnitaryGroupFinTwoComplex`. |
| *Maslov index for loops of symplectic matrices* | *Maslov index*. Existing parts: `TauCeti.GLSymplectic.maslovIndex` with `maslovIndex_eq_of_homotopy`, `maslovIndex_mul`, `maslovIndex_sum`, `maslovIndex_scalarRotationLoop`. The library adds the converse of the homotopy axiom and uniqueness. |
| *Lagrangian frames and the Lagrangian Grassmannian* | *Lagrangian Grassmannian*. |
| *Maslov index for loops of Lagrangian subspaces* | *Maslov index*. |
| *Crossing-form formula for the Maslov index* | *Maslov index*. |
| *Maslov index for paths of Lagrangian subspaces* | *Maslov index*. |
| *Affine nonsqueezing theorem* | *Linear nonsqueezing*. |
| *Linear symplectic rigidity* | *Linear nonsqueezing*. |
| *Simultaneous normal form of a symplectic form and an inner product* | *Linear nonsqueezing*. The basis statement is Tau Ceti's Williamson theorem `TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef` (`Geometry/Symplectic/Hamiltonian/Williamson.lean`); the library adds the ellipsoid consequences, uniqueness of the spectrum and the volume. |
| *Linear symplectic width of an ellipsoid* | *Linear nonsqueezing*. |
| *Linear complex structures are standard* | *Linear complex structures*. |
| *Characterizations of compatible complex structures* | *Compatible complex structures*. |
| *Contractibility of the space of compatible complex structures* | *Compatible complex structures*. Contractibility itself is existing: `TauCeti.SymplecticForm.instContractibleSpaceCompatible` (`Geometry/Symplectic/Cayley/Contractible.lean`). New here: on `StdSpace ι`, the compatible complex structures correspond to the symplectic matrices that are symmetric and positive definite, and the space of compatible structures is homotopy equivalent to $\mathrm{Met}(V)$, the inner products on $V$. |
| *Complex structures versus symplectic forms* | *Compatible complex structures*. |
| *Compact subgroups of the symplectic group* | *Compatible complex structures*. |
| *Contractibility of the space of tame complex structures* | *Compatible complex structures*. Contractibility is existing: `TauCeti.SymplecticForm.instContractibleSpaceTames`; the library adds that the inclusion of compatible structures is a homotopy equivalence. |
| *Linear Moser lemma* | *Linear Moser*. |
| *Siegel upper half space* | *Siegel upper half space*. |
| *Symplectic vector bundles are complex vector bundles* | *Symplectic vector bundles*. |
| *Compatible and tame complex structures on symplectic vector bundles* | *Symplectic vector bundles*, in the compact-open $C^0$ and $C^\infty$ topologies on sections (Tau Ceti's `ContMDiffSection.frameTopology`). |
| *Unitary trivializations over surfaces with boundary* | *Symplectic vector bundles*, with the surface connected, as the plan already corrects the book. |
| *First Chern number of symplectic vector bundles over surfaces* | *First Chern number*, with the surface connected, as the plan already corrects the book. |
| *Chern–Weil formula for circle bundles over surfaces* | *First Chern number*, with the surface connected for the converse, as the plan notes. |
| *First Chern number as an Euler number* | *First Chern number*. |

The two milestones that are existing in full (*Nondegeneracy and the top
exterior power* and *Unitary group as Sp ∩ O ∩ GL(n,C)*) are cited with these
declarations in the close-out of #3, and need no issue; a milestone that Tau
Ceti proves only in part gets the rest from its part, which states the
milestone as one theorem with the plan's hypotheses and conclusion.

## Departures from the plan's advice

- **Field of scalars.** The linear Darboux theorem is proved over any field,
  against `-stdSymplecticBilinForm k n` on `Fin n ⊕ Fin n → k`. The results
  about isotropic, coisotropic and Lagrangian subspaces are stated for Tau
  Ceti's real `TauCeti.SymplecticForm`, the only place where those
  predicates exist. Generalizing them to bilinear forms over a field, or
  `stdSymplecticBilinForm` from `Fin n` to an arbitrary index type, would
  change Tau Ceti, so it belongs to issues there, not here.
- **Reduction.** Tau Ceti's reduction quotients an arbitrary subspace $W$ by
  $W\cap W^\omega$. That covers the book's coisotropic case, which the library
  derives from it instead of building a second quotient.
- **Top exterior power.** $\omega^n$ is Tau Ceti's wedge power of a continuous
  alternating map, with value $n!$ on a Darboux basis, which the plan allows.
- **Loops.** Loops are paths on $[0,1]$ with equal ends, as in Tau Ceti, not
  maps from $\mathbb{R}/\mathbb{Z}$. The two are equivalent; the Maslov
  design file proves the comparison if a statement needs it.
- **Euclidean model.** All metric statements are made on `StdSpace ι`, never
  on a Lean product of two Euclidean spaces, since on the product a ball is a
  product of balls.
- **Topology on spaces of sections.** McDuff–Salamon do not say which
  topology the spaces of sections carry. The library states the bundle
  milestones twice, for continuous sections in the compact-open $C^0$
  topology and for smooth sections in the compact-open $C^\infty$ topology,
  both being Tau Ceti's `ContMDiffSection.frameTopology` (see *Symplectic
  vector bundles*): these are the topologies Tau Ceti already has, and the
  explicit fibrewise constructions, smooth in the structure, induce
  continuous maps for them by the lemma planned in `Section/Topology.lean`.
  The library does not use the Whitney topology: a continuous path in it
  changes a section only on a compact set, so over a non-compact base two
  structures that differ outside every compact set lie in different path
  components.
- **Proof routes.** The linear contractibility results go through the Cayley
  transform and the equivariant $J_{g,\omega}$, as Tau Ceti does; this keeps
  the constructions canonical for their use on bundles. For regular crossings
  the library uses Tau Ceti's signature results instead of Kato's selection
  theorem.
