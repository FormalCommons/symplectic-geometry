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
  symplectic matrix group with its polar decomposition and maximal compact
  subgroup, complex structures with compatibility and taming, the Cayley
  transform, the Maslov index of symplectic loops and of totally real loops.
  The library never redefines these notions. It adds the missing theorems
  about them, in the namespace of the notion they are about (`Matrix.…`,
  `TauCeti.SymplecticForm.…`, `TauCeti.GLSymplectic.…`), so that they can move
  into Tau Ceti unchanged, and new notions in `SymplecticGeometry`.
- **One representation per notion.** Where Tau Ceti has two models of the same
  object (for example `Matrix.symplecticGroup` and `TauCeti.GLSymplectic`),
  the library states results in the model the surrounding Tau Ceti API uses,
  and does not add a third.
- **Shared definitions come first and are few.** The only part that many
  others wait for is *Standard model*, which is small (a few hundred lines)
  and has no theorems of substance. Everything else can be built in parallel
  once its direct prerequisites are merged; the graph below has depth at most
  four.

## Conventions

The library uses the book's conventions for the linear theory, which are also
Tau Ceti's except where noted. The plan's sign conventions for manifolds
(`auxiliary/02-signs.md`) differ from the book's for Hamiltonian vector
fields and moment maps; they do not enter the linear theory, and are a
concern for the parts that later pages add.

- **The standard symplectic space.** The library's model of
  $\mathbb{R}^{2n}$ is `EuclideanSpace ℝ (ι ⊕ ι)` for a finite type `ι`
  (usually `Fin n`). The `inl` coordinates are $x$, the `inr` coordinates are
  $y$. This is the index type of Mathlib's `Matrix.J ι ℝ` and of
  `Matrix.symplecticGroup ι ℝ`, so matrices act on the model without
  reindexing, and its norm is the Euclidean norm on all of $\mathbb{R}^{2n}$,
  as nonsqueezing needs. The product `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`
  that Tau Ceti's Darboux theorems use carries the max norm, so balls there
  are products of balls; the library does not state metric results on it.
- **The standard form and complex structure.** On the model,
  $\omega_0(z,w)=\sum_j(x_jy'_j-y_jx'_j)$, the book's form. With
  `Matrix.J = fromBlocks 0 (-1) 1 0`, the book's $J_0$, this is
  $\omega_0(z,w)=-z^{T}Jw=\langle J_0z,w\rangle$. Tau Ceti's
  `stdSymplecticBilinForm` ($z^TJw$, in
  `RepresentationTheory/ClassicalGroups/Symplectic.lean`) is therefore
  $-\omega_0$; the library always uses $\omega_0$ and records the relation as
  a lemma. Its $J_0$ is `Matrix.J` acting on the model; it agrees with Tau
  Ceti's `AlmostComplexStructure.product` and `stdSymplecticForm` on
  `V × V` under the identification `inl ↦ fst`, `inr ↦ snd`.
- **The symplectic group.** `Matrix.symplecticGroup` is defined by $AJA^T=J$;
  `SymplecticGroup.mem_iff'` gives the book's $A^TJA=J$, and the two are used
  interchangeably. Topological statements (paths, loops, homotopies, the
  Maslov index) use Tau Ceti's subgroup `TauCeti.GLSymplectic ι ℝ` of
  `GL (ι ⊕ ι) ℝ`, as Tau Ceti's Maslov index does.
- **Symplectic bases.** A basis indexed by `ι ⊕ ι` whose Gram matrix is
  `Matrix.J` has the book's $u_j$ at `inr j` and $v_j$ at `inl j`. Tau Ceti's
  `TauCeti.SymplecticForm.IsDarbouxBasis` has the book's normalization. A
  statement that produces a basis says in its docstring which convention it
  uses.
- **Twisted product, symmetrized metric, Cayley transform, polar
  decomposition.** The library keeps Tau Ceti's definitions with their signs
  and factors: `twistedProd` is the negative of the book's $(-\omega)\oplus\omega$,
  `symmetrizedBilinForm` is twice the book's $g_{\omega,J}$, Tau Ceti's Cayley
  transform is the negative of the book's $W$, and Tau Ceti's matrix polar
  decomposition is the left one. A milestone whose statement involves one of
  these is stated with the book's object, which the proof obtains from Tau
  Ceti's by the sign or factor; a part that needs the book's sign often
  defines nothing new and uses `-` or `2⁻¹ •` in the statement.
- **Maslov indices.** The normalizations are the book's: index $1$ for
  $t\mapsto e^{2\pi it}$ in $\mathrm{U}(1)$ and for $t\mapsto e^{\pi it}\mathbb{R}$
  in $\mathcal{L}(1)$. The Robbin–Salamon index of paths in $\mathrm{Sp}(2n)$,
  if a later part defines it, is twice the book's on loops; its name and
  docstring say so.
- **Loops and homotopies.** A loop is a `Path x x` on the unit interval, as in
  Tau Ceti. Homotopy of loops means free homotopy through loops (a continuous
  `F : I × I → X` with `F (s, 0) = F (s, 1)`), the hypothesis of Tau Ceti's
  `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`. The *Maslov index* part
  fixes the predicate for it (reusing Tau Ceti's free loop spaces in
  `Topology/MappingSpace/FreeLoop.lean` if they fit).
- **Exterior powers.** $\omega^n$ is Tau Ceti's `ContinuousAlternatingMap.wedgePow`,
  with $\omega^n=n!$ on a Darboux basis.

## Shared definitions

These notions are used by several parts. They are all reused from Tau Ceti or
Mathlib, except the four definitions of *Standard model*.

| Notion | Representation | Where |
|---|---|---|
| Symplectic vector space $(V,\omega)$ over $\mathbb{R}$ | `[AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : TauCeti.SymplecticForm V)` | Tau Ceti |
| Symplectic form over a field `k` | `ω : LinearMap.BilinForm k V` with `ω.IsAlt` and `ω.Nondegenerate` | Mathlib |
| $W^\omega$; isotropic, coisotropic, symplectic, Lagrangian subspaces | `TauCeti.SymplecticForm.orthogonal`, `IsIsotropic`, `IsCoisotropic`, `IsSymplectic`, `IsLagrangian` | Tau Ceti |
| Linear symplectomorphism | `TauCeti.SymplecticForm.IsSymplectomorphism` | Tau Ceti |
| $\mathrm{Sp}(2n)$ | `Matrix.symplecticGroup ι ℝ`; as a topological group `TauCeti.GLSymplectic ι ℝ` | Mathlib, Tau Ceti |
| $\mathrm{U}(n)$ inside $\mathrm{Sp}(2n)$ | `Matrix.unitaryGroup ι ℂ` with `Matrix.realify`, `TauCeti.GLSymplectic.ofUnitary` | Mathlib, Tau Ceti |
| Linear complex structure | `TauCeti.AlmostComplexStructure V` | Tau Ceti |
| Compatible, tame | `TauCeti.SymplecticForm.Compatible`, `TauCeti.SymplecticForm.Tames` | Tau Ceti |
| $J_{g,\omega}$ (ambient $g$) | `TauCeti.SymplecticForm.polarComplexStructure` | Tau Ceti |
| Degree of a circle loop | `Circle.degree` (`Topology/Circle/Degree.lean`) | Tau Ceti |
| Maslov index of a symplectic loop | `TauCeti.GLSymplectic.maslovIndex` (`Analysis/Matrix/SymplecticGroup/Maslov.lean`) | Tau Ceti |
| $\mathbb{R}^{2n}$, $\omega_0$, $J_0$ | `SymplecticGeometry.StdSpace ι`, `SymplecticGeometry.stdForm`, `SymplecticGeometry.stdComplexStructure` | *Standard model* |
| $\omega_0$ on $k^{2n}$ | `SymplecticGeometry.stdBilinForm k ι` | *Standard model* |

### Standard model: the definitions and their API

- `StdSpace ι := EuclideanSpace ℝ (ι ⊕ ι)` (an `abbrev`), with
  `StdSpace.x z i := z (Sum.inl i)` and `StdSpace.y z i := z (Sum.inr i)`.
- `stdBilinForm k ι : LinearMap.BilinForm k (ι ⊕ ι → k)`, the form
  $\sum_j(x_jy'_j-y_jx'_j)$, with `stdBilinForm_apply`, `stdBilinForm_isAlt`,
  `stdBilinForm_nondegenerate`, `stdBilinForm_eq_neg_toBilin'_J` (it is
  $-$`Matrix.toBilin' (Matrix.J ι k)`), and the Gram matrix of the standard
  basis.
- `stdForm ι : TauCeti.SymplecticForm (StdSpace ι)`, the same form on the
  model, with `stdForm_apply`, `stdForm_apply_eq_inner` ($\omega_0(z,w)=\langle J_0z,w\rangle$),
  and the symplectomorphism to Tau Ceti's `stdSymplecticForm` on
  `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`.
- `stdComplexStructure ι : TauCeti.AlmostComplexStructure (StdSpace ι)`,
  `Matrix.J` acting on the model, with its apply lemma and
  `stdForm.Compatible (stdComplexStructure ι)`.
- The dictionary between matrices and maps: `A ∈ Matrix.symplecticGroup ι ℝ`
  if and only if `Matrix.toEuclideanLin A` is a symplectomorphism of
  `stdForm ι`; $\omega_0(Az,Aw)=\omega_0(z,w)$ for symplectic `A`; a real
  matrix commutes with `Matrix.J` if and only if its map is complex linear for
  `stdComplexStructure`.

## Parts

Each part lists its folder and files, what it builds on, and the milestones it
proves. Files are under `SymplecticGeometry/`. A part's files may be split
further when they grow, following `AGENTS.md`.

### 1. Standard model

- **Files:** `LinearAlgebra/Symplectic/Standard/Basic.lean` (`StdSpace`,
  `stdBilinForm`, `stdForm`, `stdComplexStructure`),
  `LinearAlgebra/Symplectic/Standard/Matrix.lean` (the matrix dictionary).
- **Builds on:** Mathlib, Tau Ceti.
- **Milestones:** none. It is the interface the other parts share.

### 2. Symplectic vector spaces

- **Files:** `LinearAlgebra/Symplectic/Darboux.lean` (the isomorphism with
  $(k^{2n},\omega_0)$ over any field, from Tau Ceti's
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and
  `Module.Basis.isometryEquivOfToMatrixEq`, with the basis reordered as in
  *Conventions*; and over $\mathbb{R}$ the same with `stdForm`),
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
  `Analysis/Matrix/SymplecticGroup/Polar.lean` (the right decomposition
  $\Psi=UP$ with uniqueness, from Tau Ceti's left one and
  `Units.polarUnitary_mul_sqrt_star_mul`; the inclusion
  $\mathrm{U}(n)\to\mathrm{Sp}(2n)$ as a `ContinuousMap.HomotopyEquiv`, from
  `TauCeti.GLSymplectic.polarHomotopy`).
- **Builds on:** Mathlib, Tau Ceti.
- **Milestones:** *Spectrum of a symplectic matrix*, *Symplectic polar
  decomposition and the maximal compact subgroup*.

### 4. Unitary group topology

- **Files:** `Topology/Algebra/Matrix/UnitaryGroup/FirstColumn.lean` (the
  first-column map $\mathrm{SU}(n+1)\to S^{2n+1}$ is locally trivial with
  fibre $\mathrm{SU}(n)$, hence a Serre fibration),
  `Topology/Algebra/Matrix/UnitaryGroup/SimplyConnected.lean`
  ($\mathrm{SU}(n)$ is simply connected, by induction along the fibration),
  `Topology/Algebra/Matrix/UnitaryGroup/FundamentalGroup.lean`
  ($\det:\mathrm{U}(n)\to S^1$ induces an isomorphism of fundamental groups
  for $n\ge1$, and $\pi_1(\mathrm{Sp}(2n))\cong\mathbb{Z}$ through *Symplectic
  group*'s homotopy equivalence between $\mathrm{U}(n)$ and $\mathrm{Sp}(2n)$).
- **Builds on:** Mathlib, Tau Ceti; the $\mathrm{Sp}(2n)$ corollary also on
  *Symplectic group*. Tau Ceti proves the quaternionic analogue
  in `Topology/Algebra/Quaternion/Symplectic/FirstColumn.lean` and
  `SimplyConnected.lean`, with the Serre fibration machinery of
  `Topology/Homotopy/SerreFibration/` and sphere connectivity of
  `AlgebraicTopology/Sphere/`; this part follows that template for
  $\mathbb{C}$. $\pi_1(S^1)$ is `Circle.fundamentalGroupMulEquiv`.
- **Milestones:** *Fundamental group of the unitary group*. For $n=0$ the
  group $\mathrm{U}(0)$ is trivial, so the isomorphism is stated for $n\ge1$.

### 5. Maslov index (needs `design/maslov-index.md`)

One part for all Maslov indices, because they share their framework (loops,
free homotopies, the axioms, the uniqueness argument). Its design file splits
it into issues; the overview fixes its folders and its dependencies.

- **Files:** `Analysis/Matrix/SymplecticGroup/Maslov/` (symplectic loops: the
  converse of the homotopy axiom from part 4, uniqueness of the axiomatic
  characterization), `Geometry/Manifold/LagrangianGrassmannian/Maslov/`
  (loops of Lagrangian subspaces: the index on loops in $\mathcal{L}(n)$, via
  $\det(U^2)$ and `Circle.degree`, transferred from Tau Ceti's
  `TauCeti.TotallyRealLoop.maslovIndex`; the product axiom for symplectic
  loops; homotopy; uniqueness; then paths relative to a Lagrangian $V$ and the
  crossing-form formulas, building on Tau Ceti's
  `Matrix.UnitaryGroup.maslovIndex` and its crossing-form theorems in
  `Analysis/Matrix/UnitaryGroup/Maslov/` and
  `Analysis/Matrix/HermitianSignature/`).
- **Builds on:** *Unitary group topology*, *Symplectic group*, *Lagrangian
  Grassmannian*, *Standard model*.
- **Milestones:** *Maslov index for loops of symplectic matrices*, *Maslov
  index for loops of Lagrangian subspaces*, *Crossing-form formula for the
  Maslov index*, *Maslov index for paths of Lagrangian subspaces*.
- **The design file decides:** how "a function on loops for every $n$" is
  stated for uniqueness (a family indexed by `n : ℕ` on `Fin n`, with the
  direct-sum axiom through `Fin (n + m) ≃ Fin n ⊕ Fin m`); whether the path
  index is real- or $\tfrac12\mathbb{Z}$-valued (Tau Ceti's is real); how a
  general reference Lagrangian $V$ reduces to $\mathbb{R}^n\times\{0\}$ by
  $\mathrm{Sp}(2n)$-transitivity (from *Lagrangian Grassmannian*); and the
  order of the issues, symplectic loops first, since they need only parts 3
  and 4.

### 6. Lagrangian Grassmannian (needs `design/lagrangian-grassmannian.md`)

- **Files:** `Geometry/Manifold/LagrangianGrassmannian/Basic.lean` (the space
  $\mathcal{L}(V,\omega)$ of Lagrangian subspaces, its topology),
  `Frame.lean` (the frame criterion $\operatorname{rank}=n$,
  $X^TY=Y^TX$; graphs of symmetric matrices, from Tau Ceti's
  `isLagrangian_graph_iff_of_pairing`), `Action.lean` (the action of
  $\mathrm{Sp}(2n)$, transitivity already for $\mathrm{U}(n)$, the stabilizer
  $\mathrm{O}(n)$ and $\mathcal{L}(n)\cong\mathrm{U}(n)/\mathrm{O}(n)$; Tau
  Ceti's Witt theorem `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`
  gives $\mathrm{Sp}$-transitivity), `Chart.lean` (the charts by symmetric
  matrices and the manifold structure of dimension $n(n+1)/2$).
- **Builds on:** *Standard model*.
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

### 8. Linear complex structures

- **Files:** `LinearAlgebra/ComplexStructure/Standard.lean` (every complex
  structure on a $2n$-dimensional space is conjugate to $J_0$ by a linear
  isomorphism $\Phi$, packaging Tau Ceti's
  `TauCeti.AlmostComplexStructure.exists_basis_apply_one_eq`),
  `Topology/Algebra/Matrix/ComplexStructure.lean` (the space
  $\mathcal{J}(\mathbb{R}^{2n})$ of matrices with square $-1$, the orbit map
  from $\mathrm{GL}(2n,\mathbb{R})$ with stabilizer the realified
  $\mathrm{GL}(n,\mathbb{C})$ — Tau Ceti's
  `Matrix.GeneralLinearGroup.mem_range_realify_iff` —, its two components,
  the component of $J_0$ and its homotopy type $\mathrm{SO}(2n)/\mathrm{U}(n)$,
  and $\mathcal{J}^+(\mathbb{R}^4)\simeq S^2$).
- **Builds on:** *Standard model*.
- **Milestones:** *Linear complex structures are standard*.

### 9. Compatible complex structures (needs `design/compatible-complex-structures.md`)

- **Files:** `LinearAlgebra/Symplectic/Compatible.lean` (the four equivalent
  characterizations and the two of the exercise, including the converse of
  Tau Ceti's `Compatible.hermitianCore`),
  `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure.lean`
  ($J_{g,\omega}$ for an arbitrary inner product $g$ given as a bilinear form,
  its equivariance under $\mathrm{GL}(V)$, generalizing Tau Ceti's
  `polarComplexStructure` for the ambient one),
  `Topology/Algebra/Module/InnerProducts.lean` (the space $\mathrm{Met}(V)$
  of inner products, a convex open subset of the symmetric bilinear forms),
  `Topology/ComplexStructure/Compatible.lean` (the identification
  $J\mapsto-J_0J$ with the symmetric positive definite symplectic matrices;
  the homotopy equivalences with $\mathrm{Met}(V)$ and between forms and
  complex structures for fixed $g$; the inclusion of compatible into tame
  structures as a homotopy equivalence, from Tau Ceti's contractibility
  instances), `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`
  (compact subgroups conjugate into $\mathrm{U}(n)$, from Tau Ceti's
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
  checks they agree), and how the GL-equivariant construction is stated so
  that *Symplectic vector bundles* can apply it fibrewise.

### 10. Linear Moser

- **Files:** `Analysis/ODE/LinearMoser.lean` (for a smooth family $\omega_t$
  of nondegenerate forms, $t\in\mathbb{R}$, a smooth family $\Psi_t$ with
  $\Psi_0=1$ and $\Psi_t^*\omega_t=\omega_0$, by solving a linear ODE whose
  coefficient comes from a fixed inner product; and the analogue for smooth
  families of complex structures).
- **Builds on:** Mathlib's ODE theory (`IsPicardLindelof`, and smooth
  dependence on the data for linear systems, which this part proves for
  linear equations if Mathlib lacks it). It uses no other part.
- **Milestones:** *Linear Moser lemma*.
- The construction must be canonical given the inner product, so that
  *Symplectic vector bundles* can apply it fibrewise.

### 11. Siegel upper half space

- **Files:** `Analysis/Complex/SiegelUpperHalfSpace/Basic.lean` (the space
  $\mathcal{S}_n$ of complex symmetric matrices with positive definite
  imaginary part), `.../Action.lean` (the action of $\mathrm{Sp}(2n)$ by
  $(AZ+B)(CZ+D)^{-1}$, its holomorphy and transitivity, the stabilizer of
  $i\mathbb{1}$), `.../ComplexStructure.lean` (the equivariant bijection with
  $\mathcal{J}(\mathbb{R}^{2n},\omega_0)$ and its explicit formula). For
  $n=1$ it is compared with Mathlib's `UpperHalfPlane` action.
- **Builds on:** *Standard model*; compatibility is Tau Ceti's `Compatible`.
- **Milestones:** *Siegel upper half space*. The proof of transitivity checks
  the formula for $J(Z)$ directly, which breaks the circularity between the
  book's exercise and lemma that the plan points out.

### 12. Symplectic vector bundles (needs `design/symplectic-vector-bundles.md`)

- **Files:** `Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`
  (symplectic forms on a smooth real vector bundle, as smooth sections of the
  bundle of alternating maps, Mathlib's `ContMDiffVectorBundle.continuousAlternatingMap`,
  that are fibrewise nondegenerate; isomorphisms; local symplectic
  trivializations and the reduction of the structure group to $\mathrm{Sp}(2n)$),
  `.../Symplectic/ComplexStructure.lean` (complex structures on bundles,
  compatible and tame ones, existence and contractibility, and the converse
  direction for forms taming a fixed $J$), `.../Symplectic/Classification.lean`
  (two symplectic bundles with tame complex structures are isomorphic as
  symplectic bundles if and only if they are as complex bundles),
  `Geometry/Manifold/VectorBundle/Hermitian/Surface.lean` (unitary
  trivializations along curves and over compact connected oriented surfaces
  with nonempty boundary).
- **Builds on:** *Compatible complex structures*, *Linear Moser*, Mathlib's
  smooth vector bundles and bundle metrics, Tau Ceti's bundle constructions
  (`Topology/VectorBundle/`, `Geometry/Manifold/VectorBundle/`) and its
  results for $E=TM$ (`Geometry/Symplectic/Manifold/`), which it generalizes
  rather than duplicates.
- **Milestones:** *Symplectic vector bundles are complex vector bundles*,
  *Compatible and tame complex structures on symplectic vector bundles*,
  *Unitary trivializations over surfaces with boundary*.
- **The design file decides:** the bundle-level definitions, which
  `atlas/almost-complex-structures.md` will reuse for $E=TM$; how
  contractibility of spaces of sections is stated (see *Departures*); and
  which surface topology the last milestone needs (decomposition of compact
  surfaces with boundary), with an issue for each missing prerequisite.

### 13. First Chern number (needs `design/first-chern-number.md`)

- **Files:** `Geometry/Manifold/VectorBundle/ChernNumber/Basic.lean` (the
  first Chern number of a symplectic bundle over a closed connected oriented
  surface, through a splitting of the surface and the Maslov index of the
  overlap loop; the extension lemma for maps from the boundary into
  $\mathrm{Sp}(2n)$), `.../Axioms.lean` (naturality, functoriality,
  additivity, normalization, uniqueness), `.../ChernWeil.lean`,
  `.../EulerNumber.lean` (comparison with Tau Ceti's Euler class and
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`).
- **Builds on:** *Maslov index* (symplectic loops), *Symplectic vector
  bundles*, Tau Ceti's degree of maps (`TauCeti.HomologicalOrientation.degree`),
  surface genus (`TauCeti.surfaceGenus`), integration of top forms
  (`Geometry/Manifold/DeRham/`).
- **Milestones:** *First Chern number of symplectic vector bundles over
  surfaces*, *Chern–Weil formula for circle bundles over surfaces*, *First
  Chern number as an Euler number*.
- This part needs the most infrastructure that neither library has
  (decomposition of closed surfaces, degree with regular values linked to the
  splitting, principal connections on circle bundles). Its design file lists
  those prerequisites as separate issues before any of its own.

## Dependencies and build order

Each part depends only on the parts listed, besides Mathlib and Tau Ceti.

| Level | Part | Builds on |
|---|---|---|
| 0 | *Standard model* | — |
| 0 | *Symplectic group* | — |
| 0 | *Unitary group topology* | — (its last issue also on *Symplectic group*) |
| 0 | *Linear Moser* | — |
| 1 | *Symplectic vector spaces* | *Standard model* |
| 1 | *Lagrangian Grassmannian* | *Standard model* |
| 1 | *Linear nonsqueezing* | *Standard model* |
| 1 | *Linear complex structures* | *Standard model* |
| 1 | *Siegel upper half space* | *Standard model* |
| 2 | *Compatible complex structures* | *Standard model*, *Linear complex structures* |
| 2 | *Maslov index* | *Symplectic group*, *Unitary group topology*; its Lagrangian issues also *Lagrangian Grassmannian* |
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
| *Linear Darboux theorem* | *Symplectic vector spaces*. Existing in part: the basis over any field and evenness are `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and `LinearMap.BilinForm.IsAlt.even_finrank` (`LinearAlgebra/BilinearForm/SymplecticBasis.lean`); the real isomorphism is `TauCeti.SymplecticForm.exists_isSymplectomorphism_stdSymplecticForm_of_finrank_eq`. The library adds the isomorphism with $(k^{2n},\omega_0)$ over any field. |
| *Symplectic complements* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.finrank_add_finrank_orthogonal`, `orthogonal_orthogonal`, `isSymplectic_orthogonal_iff`, `IsLagrangian.two_mul_finrank`, `IsIsotropic.isLagrangian_of_finrank` (`Geometry/Symplectic/Lagrangian/Basic.lean`). The library adds "isotropic if and only if the complement is coisotropic" and states the milestone as one theorem. |
| *Lagrangian extension lemma* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.isLagrangian_iff_maximal_isIsotropic`, `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq` (`LinearAlgebra/BilinearForm/LagrangianBasis.lean`). The library adds that every isotropic subspace lies in a Lagrangian one. |
| *Linear symplectic reduction* | *Symplectic vector spaces*. Existing: `TauCeti.SymplecticForm.reduction`, `reduction_mk`, `IsLagrangian.reduction_map` (`Geometry/Symplectic/LinearReduction.lean`), for $W/(W\cap W^\omega)$. The library adds the coisotropic statement and uniqueness. |
| *Nondegeneracy and the top exterior power* | Existing: `ContinuousAlternatingMap.wedgePow_ne_zero_iff` (`Geometry/Symplectic/Volume.lean`), for a two-form on a real space of dimension $2n$ given as a continuous alternating map (every alternating map on a finite-dimensional space is one). |
| *Unitary group as Sp ∩ O ∩ GL(n,C)* | Existing: `Matrix.symplecticGroup_inf_orthogonalGroup`, `Matrix.symplecticGroup_inf_centralizer_J`, `Matrix.orthogonalGroup_inf_centralizer_J` (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean`), each equal to the realified unitary group; two out of three over any commutative ring: `SymplecticGroup.mem_iff_mem_orthogonalGroup_of_commute`, `SymplecticGroup.commute_J_of_mem_orthogonalGroup` (`LinearAlgebra/SymplecticGroup.lean`). |
| *Spectrum of a symplectic matrix* | *Symplectic group*. |
| *Symplectic polar decomposition and the maximal compact subgroup* | *Symplectic group*. Existing parts: `SymplecticGroup.rpow_mem` (`Analysis/Matrix/Polar/Symplectic.lean`), `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`, `Matrix.isPathConnected_symplecticGroup`, `TauCeti.GLSymplectic.polarHomotopy`. The library adds the right decomposition with uniqueness and the packaged homotopy equivalence. |
| *Fundamental group of the unitary group* | *Unitary group topology*. |
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
| *Contractibility of the space of compatible complex structures* | *Compatible complex structures*. Contractibility itself is existing: `TauCeti.SymplecticForm.instContractibleSpaceCompatible` (`Geometry/Symplectic/Cayley/Contractible.lean`); the library adds the identification with symmetric positive definite symplectic matrices and the homotopy equivalence with $\mathrm{Met}(V)$. |
| *Complex structures versus symplectic forms* | *Compatible complex structures*. |
| *Compact subgroups of the symplectic group* | *Compatible complex structures*. |
| *Contractibility of the space of tame complex structures* | *Compatible complex structures*. Contractibility is existing: `TauCeti.SymplecticForm.instContractibleSpaceTames`; the library adds that the inclusion of compatible structures is a homotopy equivalence. |
| *Linear Moser lemma* | *Linear Moser*. |
| *Siegel upper half space* | *Siegel upper half space*. |
| *Symplectic vector bundles are complex vector bundles* | *Symplectic vector bundles*. |
| *Compatible and tame complex structures on symplectic vector bundles* | *Symplectic vector bundles*. |
| *Unitary trivializations over surfaces with boundary* | *Symplectic vector bundles*, with the surface connected, as the plan already corrects the book. |
| *First Chern number of symplectic vector bundles over surfaces* | *First Chern number*, with the surface connected, as the plan already corrects the book. |
| *Chern–Weil formula for circle bundles over surfaces* | *First Chern number*, with the surface connected for the converse, as the plan notes. |
| *First Chern number as an Euler number* | *First Chern number*. |

The two milestones that are existing in full (*Nondegeneracy and the top
exterior power* and *Unitary group as Sp ∩ O ∩ GL(n,C)*) are cited with these
declarations in the close-out of #3,
and need no issue; a milestone that Tau Ceti proves only in part gets
the rest from its part, which states the milestone as one theorem with the
plan's hypotheses and conclusion.

## Departures from the plan's advice

- **Field of scalars.** The plan asks for the linear Darboux theorem over any
  field with an alternating form; the library follows it (*Symplectic vector
  spaces*, `stdBilinForm k ι`). The other results about subspaces are stated
  for Tau Ceti's real `TauCeti.SymplecticForm`, because the predicates
  isotropic, coisotropic and Lagrangian exist only there. Moving them to
  bilinear forms over a field would be a refactor of Tau Ceti, not of this
  library; a *proposed* issue can ask for it there.
- **Reduction.** Tau Ceti reduces by an arbitrary subspace $W$, as
  $W/(W\cap W^\omega)$, which is more general than the book; the library
  states the coisotropic case as a corollary rather than a second quotient.
- **Top exterior power.** The library uses Tau Ceti's model of $\omega^n$ (the
  wedge power of a continuous alternating map), with the normalization $n!$
  on a Darboux basis, as the plan allows.
- **Loops.** Loops are paths on $[0,1]$ with equal ends, not maps from
  $\mathbb{R}/\mathbb{Z}$, as in Tau Ceti; the two are equivalent, and the
  Maslov design file proves the comparison if a statement needs it.
- **Euclidean model.** Metric statements (balls, cylinders, ellipsoids, widths)
  live on `EuclideanSpace ℝ (ι ⊕ ι)`, not on Tau Ceti's product model, whose
  max norm would change their meaning.
- **Topology on spaces of sections.** The bundle milestones speak of
  contractible spaces of sections without a topology. The library does not
  topologize spaces of sections. It states contractibility as the existence
  of a fibrewise deformation: a homotopy from the identity to a constant on
  the set of smooth sections, given at each point by a smooth map of the fibre
  of the bundle of structures, smooth in the parameter, the point and the
  structure together. Such a deformation is continuous in the compact-open
  $C^k$ and $C^\infty$ topologies, which is what the uses need, and avoids the
  Whitney topology, in which the statement fails over a non-compact base. The
  *Symplectic vector bundles* design file gives the precise definitions.
- **Proof routes.** For the linear contractibility results the library uses
  the Cayley transform and the equivariant $J_{g,\omega}$, as Tau Ceti does
  and as the plan recommends for later fibrewise use; for regular crossings it
  avoids Kato's selection theorem and uses Tau Ceti's dimension-counting
  signature results.
