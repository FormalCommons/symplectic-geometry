# Maslov index

The detailed design of part 5 of `DESIGN.md`, *Maslov index*. It fixes the
files of the part, its definitions and their API, the Lean names and
statements of its main results, what it takes from Tau Ceti, Mathlib and the
other parts, and the building issues in the order they can be done. It answers
each question that `DESIGN.md` leaves to it (see *Decisions*).

The part proves four milestones of `atlas/linear-symplectic-geometry.md`:
*Maslov index for loops of symplectic matrices*, *Maslov index for loops of
Lagrangian subspaces*, *Crossing-form formula for the Maslov index* and *Maslov
index for paths of Lagrangian subspaces*. The sources are McDuff–Salamon
[McDuffSalamon2017], §2.2 (Theorem 2.2.12) and §2.3 (Theorem 2.3.7 and
pp. 49, 53–54), and Robbin–Salamon [RobbinSalamon1993], §§1–2 and Remarks
2.5–2.6. Paths of Tau Ceti files are relative to
`.lake/packages/TauCeti/TauCeti/`; every Tau Ceti name below was checked at
commit `e0e414c`, the version pinned when this file was written;
`lakefile.toml` pins Tau Ceti `c9d170eed5a8` now.

## What exists, and what the part adds

Tau Ceti has the indices themselves; the part adds the converse halves of the
homotopy axioms, the uniqueness statements, the space $\mathcal{L}(n)$ as the
domain of the Lagrangian indices, general reference Lagrangians, and crossing
forms beyond graphs over $\mathbb{R}^n$.

- **Symplectic loops.** `TauCeti.GLSymplectic.maslovIndex`
  (`Analysis/Matrix/SymplecticGroup/Maslov.lean`) is the degree of
  `t ↦ maslovPhase (γ t)` for a loop `γ : Path A A` in
  `TauCeti.GLSymplectic ι ℝ`, and `maslovPhase` is $\det_{\mathbb{C}}$ of the
  unitary polar factor, the book's $\rho$. Proved: free homotopy invariance
  (`maslovIndex_eq_of_homotopy`) and invariance under homotopy with fixed ends
  (`maslovIndex_eq_of_homotopic`, the ← half of `maslovIndex_eq_iff_homotopic`
  below), product (`maslovIndex_mul`), direct sum
  (`maslovIndex_sum`, along `TauCeti.GLSymplectic.continuous_sum`), the value
  `Fintype.card ι` on `scalarRotationLoop ι` (`maslovIndex_scalarRotationLoop`,
  with `coe_scalarRotationLoop_apply`), the reduction to unitary loops
  (`maslovIndex_map_ofUnitary`, `maslovIndex_map_polarUnitary`), and
  `maslovIndex_trans`, `maslovIndex_symm`, `maslovIndex_inv`,
  `maslovIndex_refl`.
- **Paths of unitary frames.** `Matrix.UnitaryGroup.maslovIndex γ : ℝ`
  (`Analysis/Matrix/UnitaryGroup/Maslov.lean`) is Souriau's spectral formula
  for the Robbin–Salamon index, relative to $\mathbb{R}^n\subset\mathbb{C}^n$,
  of the path of Lagrangians `t ↦ (γ t).realImage` framed by a path `γ` in
  `unitaryGroup ι ℂ`. It depends only on the Souriau maps
  `Matrix.UnitaryGroup.souriau U = U Uᵀ` (`maslovIndex_eq_of_souriau_eq`), and
  has homotopy invariance with fixed ends (`maslovIndex_eq_of_homotopic`),
  catenation (`maslovIndex_trans`), reversal (`maslovIndex_symm`), direct sums
  (`maslovIndex_sum`), the zero axiom (`maslovIndex_eq_zero_of_finrank_eq`,
  `Maslov/Multiplicity.lean`), localization for graphs
  (`maslovIndex_eq_signature_sub_of_souriau_eq_cayley`,
  `Maslov/Localization.lean`), the comparison with crossing forms for graphs
  with regular crossings
  (`maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`,
  `Maslov/Crossing.lean`), invariance under real orthogonal matrices
  (`maslovIndex_map_mul_left`), the loop case (`maslovIndex_eq_degree`,
  `maslovIndex_eq_two_mul_degree`) and the half-turn
  (`maslovIndex_eq_card_of_halfTurn`). `Maslov/Loop.lean` compares it with the
  totally real loop index (`realImageLoop`, `maslovIndex_realImageLoop`,
  `maslovPhase_realImage`, `realImage_eq_realImage_iff_souriau_eq`) and with the
  relative index of two paths (`relativeMaslovIndex_realImagePath`).
- **Totally real loops and paths.** `TauCeti.TotallyRealLoop E`
  (`LinearAlgebra/TotallyReal/Loop.lean` and `LinearAlgebra/TotallyReal/Maslov/`)
  is a loop, in a complex space `E`, of maximal totally real subspaces that some
  continuous frame of complex-linear automorphisms moves. Its index has the
  direct-sum axiom (`TotallyRealLoop.maslovIndex_prod`, `Maslov/Prod.lean`),
  the `k`-fold half-turns (`rotationZPow`, `maslovIndex_rotationZPow`),
  `maslovIndex_const`, `maslovIndex_trans`, `maslovIndex_symm`, invariance
  under homotopies given by two-parameter frames (`maslovIndex_eq_of_homotopy`)
  and the description by the angle of the determinant of a frame
  (`sub_eq_maslovIndex_mul_pi`). `TauCeti.TotallyRealPath.transverseMaslovIndex`
  (`Maslov/Transverse.lean`) is an integer index of paths in
  `EuclideanSpace ℂ ι` whose two ends are chart subspaces
  `Matrix.lagrangianChart S` of symmetric matrices, hence transverse to
  $\mathbb{R}^n$; it has zero, catenation, reversal, homotopy and
  normalization. Decision 5 says which of these the part uses and why.
- **Signatures.** `Analysis/Matrix/HermitianSignature/` has
  `Matrix.crossingForm`, the jump of the signature at a regular crossing, and
  `ContinuousLinearMap.eventually_nondegenerate_of_crossingForm_nondegenerate`
  (regular crossings are isolated, for paths of symmetric forms).
- **Topology.** `Circle.degree`, `Circle.angleChange` and their API
  (`Topology/Circle/Degree.lean`); `Circle.fundamentalGroupMulEquiv_fromPath`
  (`AlgebraicTopology/UniversalCover/Circle/FundamentalGroup.lean`), which says
  that the degree is the isomorphism $\pi_1(S^1)\cong\mathbb{Z}$, so that two
  circle loops at one point with the same degree are homotopic;
  `Path.exists_trans_homotopic_trans_of_homotopicWith` and
  `Path.homotopicWith_trans_trans_symm` (`Topology/Homotopy/Path.lean`), which
  turn free homotopies of loops into conjugation and back;
  `Path.joined_toCircle_iff_homotopicWith` (`Topology/MappingSpace/FreeLoop.lean`);
  path-connectedness of `unitaryGroup ι ℂ`, of `GLSymplectic ι ℝ` and of
  `specialOrthogonalGroup ι ℝ`
  (`TauCeti.Matrix.instPathConnectedSpaceSpecialOrthogonalGroup`); and, for the
  path lifting that *Lagrangian Grassmannian* supplies,
  `Subgroup.localSectionTrivializationOfCosetFibers`
  (`Topology/Algebra/Group/Quotient/LocalSection.lean`) with
  `TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization` and
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`.
- **Reindexing.** Mathlib's `Matrix.GeneralLinearGroup.reindex (R) (e)`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`) with `symm_reindex`,
  `reindex_trans_reindex` and `reindex_refl`; Tau Ceti's
  `Matrix.reindex_sumCongr_J`.

Nothing in Mathlib or Tau Ceti states the converse of either homotopy axiom,
either uniqueness statement, a topology on $\mathcal{L}(n)$, an index relative
to a Lagrangian other than $\mathbb{R}^n$ for paths with arbitrary ends,
naturality under all of $\mathrm{Sp}(2n)$, the values property, or crossing
forms for paths other than graphs over $\mathbb{R}^n$ (searched by statement in
`Analysis/Matrix/`, `LinearAlgebra/TotallyReal/`, `Geometry/Symplectic/` and
Mathlib's `Topology/Homotopy/`, `LinearAlgebra/SymplecticGroup.lean`).

## Decisions

These answer the questions that `DESIGN.md` leaves to this file.

1. **Loops and free homotopy.** A loop is a `Path x x`. Two loops
   `γ : Path x x` and `γ' : Path y y` in `X` are *freely homotopic* when
   `(γ : C(I, X)).HomotopicWith (γ' : C(I, X)) fun p ↦ p 0 = p 1`. This is
   Mathlib's predicate, the one Tau Ceti's `Path.exists_trans_homotopic_trans_of_homotopicWith`
   and `Path.homotopicWith_trans_trans_symm` use, and a homotopy in it is
   exactly the data `F`, `h₀`, `h₁`, `hF` of
   `TauCeti.GLSymplectic.maslovIndex_eq_of_homotopy`. By
   `Path.joined_toCircle_iff_homotopicWith` it is the same as being joined in
   Tau Ceti's free loop space `C(Circle, X)`, so no new predicate is defined.
   Statements below write `γ ≈ γ'` for it as shorthand in this file only; the
   code spells it out.
2. **"For every n".** A function on loops for every $n$ is a family indexed by
   `n : ℕ` on `Fin n`:
   `μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ` for symplectic
   loops, and `μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ` for Lagrangian
   loops (`ℒ` is defined under *Interface with Lagrangian Grassmannian*). The
   direct sum of loops in dimensions $n$ and $m$ is read in dimension $n+m$
   through the reindexing along `finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)`.
   For the symplectic group that reindexing is new here (`GLSymplectic.reindex`
   below); for $\mathcal{L}(n)$ it comes from *Lagrangian Grassmannian*.
   Uniqueness is stated as an `iff`: a family satisfies the axioms if and only
   if it is the Maslov index. This one statement gives existence, uniqueness
   and the explicit formula.
3. **Values of the path index.** It is real-valued, as Tau Ceti's
   `Matrix.UnitaryGroup.maslovIndex`, so that every Tau Ceti result moves over
   without a cast. That it lies in $\tfrac12\mathbb{Z}$ is a theorem, in the
   finer form of the values property (`ℒ.pathMaslovIndex_add_half_sub_mem`
   below).
4. **A general reference Lagrangian.** The index relative to
   $V_0=\mathbb{R}^n\times\{0\}$ is Souriau's formula, read on $\mathcal{L}(n)$.
   For a general $V$ the definition moves $V$ to $V_0$ by a unitary matrix, not
   a symplectic one: by *Lagrangian Grassmannian*, $\mathrm{U}(n)$ already acts
   transitively, and the unitary matrices fixing $V_0$ are the real orthogonal
   ones, under which Souriau's formula is invariant (Tau Ceti's
   `Matrix.spectralAngleSum_conj`), so the definition does not depend on the
   choice. Naturality under all of $\mathrm{Sp}(2n)$ is then a theorem. Its
   proof joins $1$ to $\Psi$ by a path $P$ in $\mathrm{Sp}(2n)$, lifts
   $s\mapsto P(s)V$ to a path $U(s)$ of unitary frames, and compares the two
   ends of the square $(s,t)\mapsto U(s)^{-1}P(s)\Lambda(t)$ relative to $V_0$
   with catenation, homotopy invariance and the zero axiom: along the two side
   edges of the square the dimension of the intersection with $V_0$ does not
   change. The argument adapts Tau Ceti's proof of
   `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`.
5. **The dictionary with Tau Ceti.** All of Tau Ceti's Lagrangian Maslov
   theory lives on `EuclideanSpace ℂ ι` (or on a general complex space),
   framed by unitary or complex-linear maps. A unitary
   `U` frames the Lagrangian `(U : Matrix ι ι ℂ).realImage` there, and the
   Lagrangian `unitaryFrame U` of `StdSpace ι` here: the image of $V_0$ under
   `Matrix.toEuclideanLin (Matrix.realify U)`. These correspond under
   `complexToRealEuclidean ι` (read through `WithLp`), by Tau Ceti's
   `complexToRealEuclidean_mulVec`; `TauCeti.realSubspace ι` corresponds to
   $V_0$, and its image under multiplication by `I` to
   $V_1=\{0\}\times\mathbb{R}^n$. The part never transports a submodule by
   itself: it transfers a statement by choosing unitary frames, pointwise for
   statements about single Lagrangians and by path lifting (G3) for
   statements about paths, and then applies Tau Ceti's statement about the
   frames.

   The comparison with Tau Ceti's loop index is a theorem
   (`ℒ.maslovIndex_eq_totallyRealLoop_maslovIndex`), so that later pages can
   use Tau Ceti's results on totally real loops, such as its boundary-value
   results, for loops in `ℒ ι`. All the loop properties of
   `Maslov/Basic.lean` are read off the definition as a degree
   (`Circle.degree_*`) instead, and agree with Tau Ceti's through the
   comparison. Constancy, catenation, reversal and free homotopy invariance
   are a line each there, while transferring Tau Ceti's `maslovIndex_const`,
   `maslovIndex_trans`, `maslovIndex_symm` would need lifts of the loops, and
   transferring `maslovIndex_eq_of_homotopy` a lift of a whole free homotopy
   to frames, which path lifting does not give. The direct-sum axiom, the
   half-turns and the angle description follow in a few lines from Tau
   Ceti's `Matrix.UnitaryGroup.souriau_sum`, `detCircle_sum`,
   `detCircle_souriau` and `Circle.degree_mul`; transferring
   `TotallyRealLoop.maslovIndex_prod` would in addition need an
   identification of `EuclideanSpace ℂ (ι ⊕ κ)` with the product of the two
   spaces, on which Tau Ceti's direct sum of loops lives.

   The path index is Souriau's (`Matrix.UnitaryGroup.maslovIndex`), not
   `TotallyRealPath.transverseMaslovIndex`: the latter is defined only for
   paths whose two ends are transverse to $V_0$, and the milestone needs every
   path. The two agree where both are defined
   (`ℒ.pathMaslovIndex_eq_transverseMaslovIndex` below), so Tau Ceti's
   transverse index is a special case and not a second definition.
6. **The order of the issues.** Symplectic loops come first and need only
   parts 3 and 4. The Lagrangian issues follow, after the issues of
   *Lagrangian Grassmannian* that provide the interface below. See *Issues*.

## Interface with Lagrangian Grassmannian

This part uses the following from *Lagrangian Grassmannian*. Its design,
`design/lagrangian-grassmannian.md`, provides every item below and lists its
declarations for each in its table *Interface with Maslov index*; the names
here are the ones it gives. `ℒ ι` stands for
`LagrangianGrassmannian (stdForm ι)`, the space of Lagrangian subspaces of
`(StdSpace ι, stdForm ι)` with its topology and its coercion to
`Submodule ℝ (StdSpace ι)`, and `ℒ.` for the namespace
`SymplecticGeometry.LagrangianGrassmannian`. `DESIGN.md` §6 promises G3, G5
and G7–G9 (path lifting, direct sums and reindexing, and the transverse charts
and pairs).

- **G1.** The horizontal and vertical Lagrangians `ℒ.horizontal ι` and
  `ℒ.vertical ι` ($y=0$ and $x=0$), written `V₀ ι` and `V₁ ι` in this file.
- **G2.** The unitary frame map `ℒ.unitaryFrame : unitaryGroup ι ℂ → ℒ ι`,
  `U ↦ U • V₀ ι`, whose subspace is the image of `V₀` under
  `Matrix.toEuclideanLin (Matrix.realify U)`; continuous
  (`ℒ.continuous_unitaryFrame`) and surjective (`ℒ.unitaryFrame_surjective`,
  transitivity of $\mathrm{U}(n)$); `unitaryFrame U = unitaryFrame U'` if and
  only if `U⁻¹ * U'` is real (`ℒ.unitaryFrame_eq_unitaryFrame_iff`); and the
  homeomorphism $\mathrm{U}(n)/\mathrm{O}(n)\cong\mathcal{L}(n)$ that
  `DESIGN.md` promises (`ℒ.quotientHomeomorph`), so that a map out of `ℒ ι`
  is continuous when its composite with `unitaryFrame` is
  (`ℒ.isQuotientMap_unitaryFrame.continuous_iff`).
- **G3.** Path lifting: for every path `γ : Path Λ₀ Λ₁` in `ℒ ι` and every
  `U₀` with `unitaryFrame U₀ = Λ₀`, a path `δ` in `unitaryGroup ι ℂ` starting
  at `U₀` with `unitaryFrame (δ t) = γ t` for all `t`. The proof is that
  `unitaryFrame` is a fibration with fibre $\mathrm{O}(n)$
  (`ℒ.hasHomotopyLiftingProperty_unitaryFrame`), and the lift is Tau Ceti's
  `TauCeti.HasHomotopyLiftingProperty.exists_path_lift_fiber`. Local sections, and with
  them the trivializations of `ℒ.exists_trivialization_unitaryFrame`, come
  from the graph chart `ℒ.graphYChart`: every point of `ℒ ι` is `W • V₁ ι`
  for some unitary `W` (`MulAction.exists_smul_eq`), and on the open set
  `W • graphYChart.source` the section sends `Λ` to
  `W * ℒ.unitaryOfFrame (isLagrangian_range_fromRows_one hS)`. Here
  `S : selfAdjoint (Matrix ι ι ℝ)` is the `graphYChart` value of `W⁻¹ • Λ`,
  and `hS := isHermitian_iff_isSymm.1 S.property` is its symmetry, since the
  chart takes values in `selfAdjoint`; the Lagrangian frame `fromRows S 1`
  (complex frame $S+i$) spans $\{x=Sy\}$. Tau Ceti's
  `Subgroup.localSectionTrivializationOfCosetFibers` makes the trivializations,
  `TauCeti.hasHomotopyLiftingProperty_of_exists_trivialization` gives the
  homotopy lifting property, and
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization` the categorical
  form `ℒ.unitaryFrame_mem_serreFibrations`.
- **G4.** The actions of `GLSymplectic ι ℝ` and of `unitaryGroup ι ℂ` on
  `ℒ ι` (the `MulAction` instances of `Lagrangian/Action.lean`), the second
  through `TauCeti.GLSymplectic.ofUnitary`
  (`ℒ.unitary_smul_def : U • Λ = ofUnitary U • Λ`, with the `@[simp]` reverse
  `ℒ.ofUnitary_smul`, so that `U • Λ` is the normal form), both with
  `ContinuousSMul`, and
  `ℒ.unitaryFrame_mul : unitaryFrame (U * U') = U • unitaryFrame U'`, so that
  `ofUnitary U • unitaryFrame U' = unitaryFrame (U * U')`.
- **G5.** The direct sum `ℒ.sum : ℒ ι × ℒ κ → ℒ (ι ⊕ κ)` and the reindexing
  `ℒ.reindexHomeomorph : ℒ ι ≃ₜ ℒ κ` along `ι ≃ κ`, both continuous
  (`ℒ.continuous_sum`), compatible with `unitaryFrame`
  (the sum of `unitaryFrame U` and `unitaryFrame U'` is the frame of
  `Matrix.UnitaryGroup.sum (U, U')`, and the reindexing of `unitaryFrame U`
  is the frame of the matrix reindexed by Tau Ceti's
  `Matrix.unitaryReindexContinuousMulEquiv`), and with the action of
  `TauCeti.GLSymplectic.sum`.
- **G6.** The frame criterion: for `Z = fromRows X Y : Matrix (ι ⊕ ι) ι ℝ` of
  rank $n$, the image of `Matrix.toEuclideanLin Z` is Lagrangian if and only
  if $X^TY=Y^TX$ (`isLagrangian_range_fromRows_iff`); with it, the element
  `ℒ.ofFrame X Y` of `ℒ ι` that such a frame spans (`ℒ.coe_ofFrame`).
- **G7.** Transverse charts: every Lagrangian transverse to `V₁ ι` is the graph
  $\{(x,Sx)\}$ of a symmetric matrix `S`, and every Lagrangian transverse to
  `V₀ ι` is $\{x=Sy\}$ for a symmetric `S` (`ℒ.isCompl_vertical_iff`,
  `ℒ.isCompl_horizontal_iff`; as charts, `ℒ.graphChart` and
  `ℒ.graphYChart`). Read through G2, the latter is the image of a symmetric
  matrix under Tau Ceti's `Matrix.lagrangianChart`, of which Tau Ceti has
  only `lagrangianChart_injective` and `lagrangianChart_inf_realSubspace`
  (`LinearAlgebra/TotallyReal/Euclidean.lean`).
- **G8.** For any two Lagrangians, some Lagrangian is transverse to both
  (`ℒ.exists_isCompl_isCompl`).
- **G9.** `GLSymplectic ι ℝ` acts transitively on transverse pairs: for
  `V W : ℒ ι` with `V ⊓ W = ⊥` there is `Ψ` with `Ψ • V = V₀ ι` and
  `Ψ • W = V₁ ι` (`ℒ.exists_smul_eq_horizontal_vertical`).

If one of these names changes in *Lagrangian Grassmannian*, the change updates
this list too. If an item is ever dropped there, it is added back by its own
issue, which then blocks the Lagrangian issues here that use it (G7–G9 are
used only by issues 8, 9, 11 and 12).

## Files and declarations

Files are under `SymplecticGeometry/`. Declarations about Tau Ceti's notions go
in Tau Ceti's namespaces. Declarations about `ℒ ι`, and about paths and loops
in it, go in the namespace of its type, written `ℒ.` below. Everything else
goes in `SymplecticGeometry`: in particular the families `IsMaslovIndex` and
`IsLagrangianMaslovIndex`, the loop `symplecticRotationLoop`, and the
statements about them, which dot notation on a `GLSymplectic` or on an `ℒ ι` would not find.

Four files lie outside the folders that `DESIGN.md` §5 lists:
`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Reindex.lean`,
`Topology/Algebra/SymplecticGroup.lean`,
`Analysis/Calculus/Deriv/Matrix.lean` and `Data/Matrix/Basis.lean`.
Reindexing a symplectic group is
algebra about Tau Ceti's `GLSymplectic`, not about the Maslov index, and its
continuity is topology of that group. They go where Tau Ceti keeps the algebra
and the topology of `GLSymplectic`, so that they can move there unchanged.
The third file holds derivatives of matrix-valued functions (entrywise
derivatives, transpose, product rule, inverse), which `Crossing/Form.lean`
uses, `Crossing/Path.lean` for the inverse (`HasDerivWithinAt.matrix_inv`),
and which changes of frame `Z * g` need later; it sits beside Tau Ceti's file of
the same name, so that the two merge upstream. The fourth holds the matrix
`1 + Eᵢᵢ a` of the coordinate half-turn's frame
(`Matrix.one_add_single_eq_diagonal`, `Matrix.isUnit_one_add_single_iff`),
beside the files of the same name in Mathlib and Tau Ceti, which hold the matrix
units `Matrix.single`.
`DESIGN.md` §5 names all four, among the files outside its folders.

### `LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Reindex.lean`

In the namespace `TauCeti.GLSymplectic` (Tau Ceti has a folder of that name,
without such a file).

- `reindex (R) (e : ι ≃ κ) : GLSymplectic ι R ≃* GLSymplectic κ R`, the
  restriction of Mathlib's `Matrix.GeneralLinearGroup.reindex R
  (Equiv.sumCongr e e)`, symplectic by Tau Ceti's `Matrix.reindex_sumCongr_J`.
  API as Mathlib's: `coe_reindex` (`@[simp]`), `symm_reindex`,
  `reindex_trans_reindex`, `reindex_refl`; and `reindex_sum`, that it commutes
  with `TauCeti.GLSymplectic.sum` along `Equiv.sumCongr`.

Its continuity, `continuous_reindex`, goes in
`Topology/Algebra/SymplecticGroup.lean`, named like the Tau Ceti file that has
`continuous_sum`.

### `Analysis/Matrix/SymplecticGroup/Maslov.lean`

Symplectic loops. Named like Tau Ceti's file, which it extends. The first
three items are in the namespace `TauCeti.GLSymplectic`, the rest in
`SymplecticGeometry`.

- `maslovPhase_reindex` and `maslovIndex_reindex`: reindexing keeps $\rho$ and
  the index of a loop.
- `maslovIndex_eq_iff_homotopic {A} {γ γ' : Path A A} :
  maslovIndex γ = maslovIndex γ' ↔ γ.Homotopic γ'`. The ← half is Tau Ceti's
  `maslovIndex_eq_of_homotopic`. For `ι` empty the group is trivial.
  Otherwise, at `A = 1`: Tau Ceti's `polarHomotopy` fixes
  $\mathrm{U}(n)$ (*Symplectic group*, issue #11), so a loop at `1` is
  homotopic with fixed ends to its loop of unitary polar factors, which has the
  same index (`maslovIndex_map_polarUnitary`); on loops of `ofUnitary` the
  index is the degree of $\det$ (`maslovIndex_map_ofUnitary`), which is
  injective on homotopy classes by the isomorphism of *Unitary group topology*
  (issue #22, stated for `Fin n`; moved to `ι` along `Fintype.equivFin ι`)
  and `Circle.fundamentalGroupMulEquiv_fromPath`. A general base
  point is moved to `1` by left multiplication with `A⁻¹`.
- `homotopicWith_iff_maslovIndex_eq {A B} (γ : Path A A) (γ' : Path B B) :
  γ ≈ γ' ↔ maslovIndex γ = maslovIndex γ'`: the free form, from the previous
  statement and Tau Ceti's `Path.exists_trans_homotopic_trans_of_homotopicWith`
  and `Path.homotopicWith_trans_trans_symm` along a path from `A` to `B`. It
  holds for every `ι`, including `ι` empty.
- `symplecticRotationLoop (k : ℤ) : Path (1 : GLSymplectic (Fin 1) ℝ) 1`,
  `t ↦ ofUnitary (e^{2πikt})`, with `coe_symplecticRotationLoop_apply`
  (`@[simp]`, the value at `t`, like Tau Ceti's
  `coe_scalarRotationLoop_apply`) and `maslovIndex_symplecticRotationLoop :
  maslovIndex (symplecticRotationLoop k) = k` (`@[simp]`, by
  `maslovIndex_map_ofUnitary` and the degree of $t\mapsto e^{2\pi ikt}$, as in
  Tau Ceti's `maslovIndex_scalarRotationLoop`). The name is not
  `rotationLoop`, which would clash with Tau Ceti's unrelated
  `TauCeti.rotationLoop` of operators when both namespaces are open.
- `homotopicWith_reindex_sum_symplecticRotationLoop (γ : Path A A)`, for `A` in
  `GLSymplectic (Fin (n + 1)) ℝ`: `γ` is freely homotopic to the direct sum of
  `Path.refl 1` in dimension `n` and
  `symplecticRotationLoop (maslovIndex γ)`, reindexed along `finSumFinEquiv`. From `homotopicWith_iff_maslovIndex_eq`,
  `maslovIndex_sum`, `maslovIndex_refl` and `maslovIndex_reindex`.
- `structure IsMaslovIndex (μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ) : Prop`
  with the fields of the milestone, each for all `n` and all loops:
  `homotopicWith_iff : γ ≈ γ' ↔ μ n A γ = μ n B γ'`;
  `mul : μ n (A * B) (γ.mul γ') = μ n A γ + μ n B γ'`;
  `sum`, the direct sum `((γ.prod γ').map continuous_sum)` reindexed by
  `finSumFinEquiv`, of index `μ n A γ + μ m B γ'`;
  `normalization : μ 1 1 (symplecticRotationLoop 1) = 1`.
- **Milestone theorem** `isMaslovIndex_iff (μ) :
  IsMaslovIndex μ ↔ μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase)`.
  The right side is `maslovIndex` by `maslovIndex_def`, so the statement holds
  existence, the formula $\mu=\deg(\rho\circ\Psi)$ and uniqueness. Uniqueness:
  the product axiom gives `0` on constant loops (a constant loop at `1` is its
  own square; others are freely homotopic to it) and `k` on
  `symplecticRotationLoop k` (a pointwise power of the normalized loop, or the
  inverse of one); the sum axiom and
  `homotopicWith_reindex_sum_symplecticRotationLoop` then give every value.
  *Maslov index for loops of symplectic matrices*.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Basic.lean`

The Maslov phase on $\mathcal{L}(n)$ and the index of Lagrangian loops.

- `ℒ.souriau : ℒ ι → unitaryGroup ι ℂ`, the Souriau embedding
  $\Lambda\mapsto UU^T$ for any unitary frame `U` of `Λ`; well defined by
  `ℒ.unitaryFrame_eq_unitaryFrame_iff_souriau_eq` (from
  `Matrix.UnitaryGroup.realImage_eq_realImage_iff_souriau_eq` and G2). API:
  `souriau_unitaryFrame : souriau (unitaryFrame U) = Matrix.UnitaryGroup.souriau U`
  (`@[simp]`), `souriau_horizontal`, `continuous_souriau`, `souriau_injective`,
  `isClosedEmbedding_souriau`, `souriau_sum`, `souriau_reindex`, and
  `souriau_unitary_smul : souriau (U • Λ) = U * souriau Λ * UnitaryGroup.transpose U`
  (`@[simp]`, by `Matrix.UnitaryGroup.coe_souriau_mul_left`).
- `ℒ.maslovPhase (Λ : ℒ ι) : Circle := detCircle (souriau Λ)`, the book's
  $\rho$, with `maslovPhase_def`, `continuous_maslovPhase`,
  `maslovPhase_unitaryFrame : maslovPhase (unitaryFrame U) = detCircle U ^ 2`
  (`@[simp]`, by `Matrix.UnitaryGroup.detCircle_souriau`),
  `maslovPhase_horizontal`, `maslovPhase_sum`
  (`@[simp]`, the phase of a direct sum is the product), `maslovPhase_reindex`,
  and
  `maslovPhase_unitary_smul : maslovPhase (U • Λ) = detCircle U ^ 2 * maslovPhase Λ`.
  The reindexing lemmas here and below are stated with `ℒ.reindex e` and its
  continuity `ℒ.continuous_reindex e`, the simp normal form of
  `ℒ.reindexHomeomorph e` (`reindexHomeomorph_apply`).
- `ℒ.rootMultiplicity_one_charpoly_souriau`: the multiplicity of the eigenvalue
  `1` of `souriau Λ` is `finrank (Λ ⊓ V₀)`, from Tau Ceti's lemma of the same
  name through `ℒ.finrank_unitaryFrame_inf_horizontal` of
  `Lagrangian/Action.lean`.
- `ℒ.maslovIndex {Λ} (γ : Path Λ Λ) : ℤ := Circle.degree (γ.map continuous_maslovPhase)`,
  with `maslovIndex_def`; from the API of `Circle.degree` (Decision 5):
  `maslovIndex_eq_of_homotopy` (free homotopy, from
  `Circle.degree_eq_of_homotopy`), `maslovIndex_eq_of_homotopic`,
  `maslovIndex_refl` (`@[simp]`, zero),
  `maslovIndex_trans` (`@[simp]`), `maslovIndex_symm` (`@[simp]`),
  `maslovIndex_reindex`; and `maslovIndex_map_unitaryFrame`: for a loop of
  frames `δ`, the index of `δ.map continuous_unitaryFrame` is twice the degree
  of $\det\delta$.
- `ℒ.maslovIndex_eq_totallyRealLoop_maslovIndex`: for a path `δ` of unitary
  frames lifting a loop in `ℒ ι`, the index of the loop is the Tau Ceti index
  of the `TotallyRealLoop` that `δ` gives through
  `Matrix.UnitaryGroup.realImageLoop` (`maslovIndex_realImageLoop`,
  `maslovIndex_eq_degree`); and `ℒ.exists_realImageLoop_maslovIndex_eq`, that
  such a lift exists, by G3.
- From the degree as well (Decision 5): `ℒ.maslovIndex_sum`, the index of the
  direct sum `(γ.prod γ').map continuous_sum` of two loops (G5) is the sum;
  and `ℒ.maslovIndex_eq_sub_div_pi`: if `δ` is a path of frames of the loop
  and $\det\delta(t)=e^{i\alpha(t)}$ with `α` continuous, the index is
  $(\alpha(1)-\alpha(0))/\pi$; `ℒ.angleChange_map_detCircle`, for such a
  `δ` the angle change of $\det\delta$ is `maslovIndex γ * π`, and its
  corollary `ℒ.detCircle_inv_mul_eq_exp`, $\det(U^{-1}V)=e^{i\pi\mu(\gamma)}$
  for `δ` from `U` to `V`.
- The half-turn `ℒ.halfTurnLoop {ι} (k : ℤ) : Path (V₀ ι) (V₀ ι)`,
  `t ↦ rotate (π * k * t) (V₀ ι)`, built as `rotationPath (V₀ ι) (π * k)`
  cast along `rotate_int_mul_pi`, with `halfTurnLoop_apply`
  (not `@[simp]`, so that the phase lemma below can fire),
  `maslovPhase_halfTurnLoop :
  maslovPhase (halfTurnLoop k t) = Circle.exp (2 * Fintype.card ι * (π * k * t))`
  (`@[simp]`) and `maslovIndex_halfTurnLoop :
  maslovIndex (halfTurnLoop (ι := ι) k) = k * Fintype.card ι` (`@[simp]`), the
  degree of $t\mapsto e^{2\pi iknt}$; Tau Ceti's `rotationZPow` is the totally
  real loop that corresponds to it.
  For `ι = Fin 1` and `k = 1` this is the half-turn of the milestone, of
  index `1`.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Product.lean`

- `ℒ.maslovIndex_smul {A Λ} (Ψ : Path A A) (γ : Path Λ Λ) :
  maslovIndex ((Ψ.prod γ).map continuous_smul) = maslovIndex γ + 2 * GLSymplectic.maslovIndex Ψ`
  (`@[simp]`).
  For a loop of `ofUnitary` matrices this is `ofUnitary_smul`, then
  `maslovPhase_unitary_smul`, with
  `Circle.degree_mul`. In general, Tau Ceti's `polarHomotopy` deforms `Ψ`
  through loops of symplectic matrices to its loop of unitary polar factors;
  acting on `γ` it gives a free homotopy of Lagrangian loops (G4), and
  `maslovIndex_map_polarUnitary` keeps the symplectic index.
- `ℒ.maslovIndex_smul_const` (`@[simp]`): the case of a constant `γ`, which gives
  $\mu(\Psi V)=2\mu(\Psi)$ for the loops $t\mapsto\Psi(t)V$ that the
  symplectic crossing formula uses.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Loop.lean`

- `ℒ.maslovIndex_eq_iff_homotopic {Λ} {γ γ' : Path Λ Λ} :
  maslovIndex γ = maslovIndex γ' ↔ γ.Homotopic γ'`, that is, $\rho$ induces an
  injection of $\pi_1(\mathcal{L}(n))$ into $\pi_1(S^1)$. Proof for `ι`
  nonempty (for `ι` empty, `ℒ ι` is a point): lift a loop at `unitaryFrame U`
  to a path `δ` of frames from `U` to `U * O` with `O` real orthogonal (G3, G2).
  Multiply `δ` on the right by a path of real orthogonal matrices from `1` to
  `O⁻¹ * D`, where `D` is the identity or the reflection in one fixed
  coordinate, with `det D = det O` (`specialOrthogonalGroup ι ℝ` is path
  connected). The Lagrangians do not change (`Matrix.realImage_mul_map_ofReal`)
  and the new path ends at `U * D`. The index is the angle change of
  $\det\delta$ divided by $\pi$ (`maslovIndex_eq_sub_div_pi`), so its parity
  fixes `D`. Two loops with the same index therefore have lifts with the same
  ends and the same angle change of $\det$, which are homotopic with fixed
  ends by the isomorphism of issue #22 (stated for `Fin n`; moved to `ι` along
  `Fintype.equivFin ι`).
- `ℒ.homotopicWith_iff_maslovIndex_eq (γ : Path Λ Λ) (γ' : Path Λ' Λ')`: the
  free form, as for symplectic loops.
- `ℒ.homotopicWith_reindex_sum_halfTurnLoop (γ : Path Λ Λ)`, for `Λ` in
  `ℒ (Fin (n + 1))`: `γ` is freely homotopic to the direct sum of the constant
  loop at `V₀ (Fin n)` and `halfTurnLoop (maslovIndex γ)` in `ℒ (Fin 1)`,
  reindexed along `finSumFinEquiv`.
- `structure IsLagrangianMaslovIndex (μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ) : Prop`,
  in `SymplecticGeometry`, with the four axioms that determine the index:
  `homotopicWith_iff`; `smul`,
  `μ n _ ((Ψ.prod γ).map continuous_smul) = μ n Λ γ + 2 * GLSymplectic.maslovIndex Ψ`;
  `sum`, through G5 and `finSumFinEquiv`; and `refl : μ n Λ (Path.refl Λ) = 0`.
- **Milestone theorem**
  `isLagrangianMaslovIndex_iff_and_maslovIndex_halfTurnLoop`, in
  `SymplecticGeometry`: for every `μ`, `IsLagrangianMaslovIndex μ ↔
  μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase)`,
  stated together with the normalization
  `ℒ.maslovIndex (ℒ.halfTurnLoop (ι := Fin 1) 1) = 1`, as one conjunction, so
  that one theorem carries the whole milestone; `maslovPhase_unitaryFrame`
  gives $\rho$ explicitly. Uniqueness: on `ℒ (Fin 1)`, `halfTurnLoop (2 * j)`
  is `symplecticRotationLoop j` acting on the constant loop, of value `2 * j`
  by `smul` and `refl`; the direct sum of `halfTurnLoop k` with itself is freely
  homotopic to the direct sum of `halfTurnLoop (2 * k)` and a constant loop,
  both having index `2 * k`, so `homotopicWith_iff` and `sum` give `k` for
  `halfTurnLoop k`; `homotopicWith_reindex_sum_halfTurnLoop` does the rest.
  *Maslov index for loops of Lagrangian subspaces*.
- Supporting declarations of the file: `ℒ.maslovIndex_eq_of_homotopicWith`;
  `isLagrangianMaslovIndex_maslovIndex`; and in the namespace
  `IsLagrangianMaslovIndex`, `eq_of_maslovIndex_eq`,
  `apply_halfTurnLoop_two_mul`, `apply_halfTurnLoop` and
  `apply_eq_maslovIndex`. The proof of `maslovIndex_eq_iff_homotopic` corrects
  one lift on the right by a path in `O(n)` from `1` to `W⁻¹ W'`, where `U W`
  and `U W'` are the ends of the two lifts (joined since
  `det W = det W' = (-1)^k`, by `TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq`),
  instead of moving both ends to `U * D`, and then uses
  `Matrix.UnitaryGroup.homotopic_iff_angleChange_eq` (part *Unitary group topology*).

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Basic.lean`

The Robbin–Salamon index of paths, relative to a Lagrangian `V`.
`ℒ.pathMaslovIndex` is the only public index of paths.

- `ℒ.pathMaslovIndex {Λ Λ'} (γ : Path Λ Λ') (V : ℒ ι) : ℝ`: choose `U` with
  `unitaryFrame U = V`, move the path by `U⁻¹` (the unitary action of G4, so by
  `(ofUnitary U)⁻¹`), and take Souriau's
  formula on `ℒ ι` of the moved path `γ'` from `Λ₀` to `Λ₁`,
  `Circle.angleChange (γ'.map continuous_maslovPhase) / (2 * π) - (spectralAngleSum (souriau Λ₁) - spectralAngleSum (souriau Λ₀))`.
  API: `pathMaslovIndex_def`; `pathMaslovIndex_eq_of_unitaryFrame_eq`, any
  such `U` gives the same value (Decision 4; two choices differ by a real
  orthogonal matrix, and invariance under it is transferred from
  `Matrix.UnitaryGroup.maslovIndex_map_mul_left` through a lift to frames), which
  every other statement uses instead of the choice; and the bridge to Tau Ceti,
  `pathMaslovIndex_map_unitaryFrame (δ : Path U U') :
  pathMaslovIndex (δ.map continuous_unitaryFrame) (V₀ ι) = Matrix.UnitaryGroup.maslovIndex δ`,
  through which, with G3, all of Tau Ceti's theorems apply.
  With it: `pathMaslovIndex_horizontal` (the formula for `V = V₀`, with no
  move), `pathMaslovIndex_unitaryFrame` (the index relative to
  `unitaryFrame U` is that of the path moved by `U⁻¹`, relative to `V₀`),
  `pathMaslovIndex_congr` (paths with the same values), and for a path `δ` of
  frames of `γ`, `pathMaslovIndex_horizontal_eq_maslovIndex` and
  `pathMaslovIndex_unitaryFrame_eq_maslovIndex` (relative to `unitaryFrame W`,
  the index of `t ↦ W⁻¹ δ t`); `exists_maslovIndex_eq_pathMaslovIndex` gives
  such a `δ` by G3.
- Transferred from Tau Ceti, each for every `V` (the first four, and the
  loop statements below, are read off the formula on `ℒ ι` with the
  `Circle.angleChange` API, as Tau Ceti proves them on frames: transferring
  homotopy invariance would need a lift of the homotopy that fixes the ends):
  `ℒ.pathMaslovIndex_eq_of_homotopic` (fixed ends), `ℒ.pathMaslovIndex_trans`
  (`@[simp]`, catenation, with the corollary `ℒ.pathMaslovIndex_eq_subpath_add`
  for a split point `c`), `ℒ.pathMaslovIndex_symm` (`@[simp]`),
  `ℒ.pathMaslovIndex_refl` (`@[simp]`), `ℒ.pathMaslovIndex_sum` (the product
  property, for the sum of two paths relative to the sum of two Lagrangians,
  G5), `ℒ.pathMaslovIndex_eq_zero_of_finrank_eq` (zero: `finrank (γ t ⊓ V)`
  constant, moved to `V₀` by `ℒ.finrank_inf_unitaryFrame` of
  `Lagrangian/Transverse.lean` and `ℒ.finrank_unitaryFrame_inf_horizontal` of
  `Lagrangian/Action.lean`), `ℒ.pathMaslovIndex_graph` (localization: for `V = V₀`
  and a path of Lagrangians that are the graphs $\{(x,A(t)x)\}$ of real matrices, with no
  continuity hypothesis, since `ℒ.continuous_of_coe_eq_graph` derives it, and no symmetry
  hypothesis, since each graph is Lagrangian, half the change of
  `Matrix.signature`, from `maslovIndex_eq_signature_sub_of_souriau_eq_cayley`,
  whose frames $\mathbb{1}+iA$ span exactly these graphs).
- `ℒ.pathMaslovIndex_eq_transverseMaslovIndex`: for a path of frames `δ` whose
  ends `realImage` are chart subspaces `Matrix.lagrangianChart S₀`,
  `lagrangianChart S₁` of symmetric matrices,
  `pathMaslovIndex (δ.map continuous_unitaryFrame) (V₀ ι)` is Tau Ceti's
  `transverseMaslovIndex` of `realImagePath δ`. Proof: by
  `Matrix.UnitaryGroup.relativeMaslovIndex_realImagePath` the transverse index is the difference
  of the Souriau indices of `δ` and of a frame of the chart segment, and the
  latter vanishes by the zero axiom, the segment staying transverse to `V₀`.
- Loops: `ℒ.pathMaslovIndex_eq_maslovIndex (γ : Path Λ Λ) (V) :
  pathMaslovIndex γ V = maslovIndex γ`, for every `V`; and with
  `ℒ.maslovIndex_eq_sub_div_pi` the form of the milestone's loops clause,
  `ℒ.pathMaslovIndex_eq_sub_div_pi`: for a loop `γ`, any `V`, a path `δ` of
  unitary frames of `γ` (`unitaryFrame (δ t) = γ t`) and a continuous `α`
  with $\det\delta(t)=e^{i\alpha(t)}$,
  `pathMaslovIndex γ V = (α 1 - α 0) / π`.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Naturality.lean`

- `ℒ.pathMaslovIndex_smul (Ψ : GLSymplectic ι ℝ) (γ) (V) :
  pathMaslovIndex (γ.map (continuous_const_smul Ψ)) (Ψ • V) = pathMaslovIndex γ V`,
  by the square of Decision 4, through
  `ℒ.pathMaslovIndex_eq_of_homotopy`: a homotopy `F : C(I × I, ℒ ι)` from
  `γ₀` to `γ₁` whose ends `F (s, 0)`, `F (s, 1)` keep the dimension of their
  intersections with `V` does not change the index relative to `V` (Mathlib's
  `Path.Homotopic.map_trans_evalAt` and the zero axiom); both adapt
  the proof of Tau Ceti's `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`,
  and move dimensions to `V₀` by `ℒ.finrank_inf_unitaryFrame`.
- `ℒ.pathMaslovIndex_add_half_sub_mem (γ : Path Λ Λ') (V) :
  pathMaslovIndex γ V + (finrank (Λ ⊓ V) - finrank (Λ' ⊓ V)) / 2 ∈ Set.range (Int.cast : ℤ → ℝ)`
  (the values property), from Tau Ceti's
  `Matrix.det_eq_neg_one_pow_mul_exp_spectralAngleSum` and
  `rootMultiplicity_one_charpoly_souriau`; with the corollary
  `ℒ.two_mul_pathMaslovIndex_mem :
  2 * pathMaslovIndex γ V ∈ Set.range (Int.cast : ℤ → ℝ)`.
- `ℒ.pathMaslovIndex_eq_iff_homotopic {γ γ' : Path Λ Λ'} (V) :
  pathMaslovIndex γ V = pathMaslovIndex γ' V ↔ γ.Homotopic γ'`, from
  `ℒ.maslovIndex_eq_iff_homotopic` applied to `γ.trans γ'.symm`.
- `ℒ.pathMaslovIndex_sub_pathMaslovIndex (γ γ' : Path Λ Λ') (V V')`: the
  difference `pathMaslovIndex γ V' - pathMaslovIndex γ V` is the same for `γ'`
  (the Hörmander index depends only on the ends), since the loop
  `γ.trans γ'.symm` has the same index relative to `V` and to `V'`. The part
  defines no function for the Hörmander index: nothing here uses one.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Form.lean`

In `SymplecticGeometry`: the crossing form takes matrices and a submodule, not
an element of `ℒ ι`.

- `lagrangianCrossingForm (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) :
  QuadraticForm ℝ (V.comap (Matrix.toEuclideanLin Z))`,
  `u ↦ stdForm ι (toEuclideanLin Z u) (toEuclideanLin Z' u)`. For a frame
  $Z=\binom{X}{Y}$ with derivative $Z'$ this is
  $\langle Xu,Y'u\rangle-\langle Yu,X'u\rangle$ on the $u$ with $Zu\in V$, by
  `stdForm_apply`: Robbin–Salamon's form $Q_t$ restricted to $\Lambda\cap V$.
  API: `lagrangianCrossingForm_apply` (`@[simp]`);
  `lagrangianCrossingForm_vertical`, the value $-\langle Yu,X'u\rangle$ for
  `V = V₁` (the form of the loop formula); `lagrangianCrossingForm_graph`, the
  identification with Tau Ceti's `Matrix.crossingForm A A'` for `Z = (1; A)`
  and `V = V₀`; `lagrangianCrossingForm_smul`, homogeneity in `Z'`; and
  `lagrangianCrossingForm_eq_zero_of_inf_eq_bot`, the form is zero where the
  image of `Z` meets `V` only in `0`.
- `stdForm_toEuclideanLin_comm_of_hasDerivWithinAt`: let
  `Z : ℝ → Matrix (ι ⊕ ι) ι ℝ` have isotropic images on a set `s`,
  `stdForm ι (toEuclideanLin (Z r) u) (toEuclideanLin (Z r) v) = 0` for all
  `r ∈ s`, `u`, `v`, and let `HasDerivWithinAt Z Z' s t` with `t ∈ s` and
  `UniqueDiffWithinAt ℝ s t`. Then
  `stdForm ι (toEuclideanLin (Z t) u) (toEuclideanLin Z' v) = stdForm ι (toEuclideanLin (Z t) v) (toEuclideanLin Z' u)`
  for all `u`, `v`: the derivative within `s` of the isotropy vanishes, and
  `stdForm` is antisymmetric. It is used with `s = Icc 0 1`
  (`uniqueDiffOn_Icc`), so it covers crossings at the ends. It says that
  $(u,v)\mapsto\omega(Zu,Z'v)$ is the symmetric bilinear form that
  `QuadraticMap.associated` gives the crossing form; its `QuadraticMap.polar`
  is twice that.
- Frame independence of the form itself, `lagrangianCrossingForm_mul_apply`:
  for `Z` with isotropic image, any `g h : Matrix ι ι ℝ` and `w`
  in the domain `V.comap (toEuclideanLin (Z * g))`,
  `lagrangianCrossingForm (Z * g) (Z' * g + Z * h) V w = lagrangianCrossingForm Z Z' V ⟨toEuclideanLin g w, _⟩`,
  where the membership proof rewrites `toEuclideanLin (Z * g) w ∈ V` as
  `toEuclideanLin Z (toEuclideanLin g w) ∈ V`. The vector `Z g w` of
  $\Lambda\cap V$ has coordinates `w` in the frame `Z * g` and `g w` in the
  frame `Z`, and both frames give it the same value: the form on
  $\Lambda\cap V$ is one form, read in two coordinate systems. Proof: expand
  by `lagrangianCrossingForm_apply`; the extra term
  `stdForm ι (Z g w) (Z h w)` vanishes by isotropy. Neither step inverts
  `g`, so the lemma holds for every square `g`; only the corollary below
  needs `g` invertible. The membership step is Mathlib's
  `Matrix.toLpLin_mul_same` (`Matrix.toEuclideanLin` is an `abbrev` for
  `Matrix.toLpLin 2 2`), or `simp`; no helper is added. The statement is about
  single matrices and needs no derivative: for a change of frame `t ↦ g t`
  with `HasDerivWithinAt g g' (Icc 0 1) t`, the product rule gives the
  derivative `Z' t * g t + Z t * g'` of `Z * g` within `Icc 0 1`, and this
  lemma applies at every `t ∈ Icc 0 1`, ends included. A constant `g` is
  `h = 0`. For the use sites, the corollary
  `lagrangianCrossingForm_mul_equivalent`, for `g : GL ι ℝ`,
  `(lagrangianCrossingForm Z Z' V).Equivalent (lagrangianCrossingForm (Z * ↑g) (Z' * ↑g + Z * h) V)`,
  follows: the linear equivalence `w ↦ g w` of the two domains, with inverse
  `u ↦ g⁻¹ u` (Mathlib's `LinearEquiv.ofSubmodules`), is an isometry by
  `lagrangianCrossingForm_mul_apply` at `↑g`.
- Naturality, `lagrangianCrossingForm_symplectic_mul_apply`: for `Ψ`
  symplectic and `u` with `hu : toEuclideanLin Z u ∈ V`,
  `lagrangianCrossingForm (Ψ * Z) (Ψ * Z') (V.map (toEuclideanLin Ψ)) ⟨u, _⟩ = lagrangianCrossingForm Z Z' V ⟨u, hu⟩`,
  where the membership proof is `Submodule.mem_map_of_mem hu` after rewriting
  `toEuclideanLin (Ψ * Z) u` as `toEuclideanLin Ψ (toEuclideanLin Z u)`,
  again by `Matrix.toLpLin_mul_same`. The
  two domains are the same subspace (`toEuclideanLin Ψ` is injective), and
  the forms agree on it because `Ψ` preserves `stdForm ι`. The corollary
  `lagrangianCrossingForm_symplectic_mul_equivalent`,
  `(lagrangianCrossingForm Z Z' V).Equivalent (lagrangianCrossingForm (Ψ * Z) (Ψ * Z') (V.map (toEuclideanLin Ψ)))`,
  takes the identity on underlying vectors as its isometry.
- The use sites take signatures from
  `QuadraticMap.Equivalent.signature_eq`, and nondegeneracy from
  Tau Ceti's `QuadraticMap.IsometryEquiv.nondegenerate_iff`; the part adds no
  signature corollaries of the two isometries.
- `ℒ.eventually_not_crossing_of_regular`: regular crossings are isolated. For
  a path `γ` in `ℒ ι` with a frame `Z` as in
  `ℒ.pathMaslovIndex_eq_crossing_sum` below, with
  `HasDerivWithinAt Z (Z' t₀) (Icc 0 1) t₀` at some `t₀ ∈ Icc 0 1` and a
  nondegenerate form there, `γ t ⊓ V = ⊥` for `t ≠ t₀` near `t₀` in
  `Icc 0 1`. Proof: `γ` is extended to `ℝ` by `Set.IccExtend`. On each side
  of `t₀` that `Icc 0 1` reaches, `Z` is a frame of the extension near `t₀`,
  and its derivative within `Icc 0 1` is a one-sided one (the two sets agree
  near `t₀` on that side), so the one-sided forms below give the times before
  and after `t₀`.
- `ℒ.eventually_nhdsLT_not_crossing_of_regular`,
  `ℒ.eventually_nhdsGT_not_crossing_of_regular` and
  `ℒ.eventually_nhdsNE_not_crossing_of_regular`: the same for a family
  `Λ : ℝ → ℒ ι`. The one-sided forms take a frame of `Λ` on `Iic r₀` (or
  `Ici r₀`) near `r₀`, eventually in `𝓝[≤] r₀` (or `𝓝[≥] r₀`), and a derivative
  within `Iic r₀` (or `Ici r₀`), and conclude in `𝓝[<] r₀` (or `𝓝[>] r₀`);
  the two-sided one takes a frame of `Λ` eventually in `𝓝 r₀`, `HasDerivAt Z Z' r₀`, and
  concludes in `𝓝[≠] r₀`, from the two one-sided forms. Proof of the
  one-sided forms, without graphs or symplectic changes of coordinates: G8
  gives a Lagrangian `W` transverse to `V` and to `Λ r₀`; let `P` be the
  projection onto `V` along `W` (Mathlib's `Submodule.projection`). For each
  `r`, take the bilinear form `β r (u, v) = ω₀(P (Z r u), Z r v)` on `ℝ^ι`, as
  a matrix. It is symmetric wherever the image of `Z r` is isotropic, since
  `V` and `W` are; where it is nondegenerate, the image of `Z r` meets `V`
  only in `0`, since `P` fixes `V`; and its one-sided derivative at `r₀`
  comes from that of `Z` by the product rule. At `r₀` its kernel is the
  preimage of `V` under `Z r₀` (the image of `Z r₀` is Lagrangian and meets
  `W` only in `0`), and `LinearEquiv.ofSubmodules` on that kernel is an
  isometry from the crossing form of `Z r₀` and `Z'` to Tau Ceti's
  `ContinuousLinearMap.crossingForm` of `β` at `r₀`, which is therefore
  nondegenerate. Tau Ceti's one-sided
  `ContinuousLinearMap.eventually_nhdsLT_nondegenerate_of_crossingForm_nondegenerate`
  and `eventually_nhdsGT_nondegenerate_of_crossingForm_nondegenerate`
  conclude. Their symmetry hypotheses hold because `β r` is symmetric at
  every `r` where `Z r` is a frame of `Λ r`, so eventually on that side.

Signatures are `QuadraticForm.signature Q`, the integer `(sigPos Q : ℤ) - sigNeg Q`
of `LinearAlgebra/QuadraticForm/Signature.lean`, which Tau Ceti's crossing theorem
writes out; the part adds no signature function.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Path.lean`

- `ℒ.pathMaslovIndex_eq_crossing_sum`: let `γ : Path Λ Λ'`, `V : ℒ ι`, and
  `Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ` with image `γ t` for each `t : I`
  (`LinearMap.range (toEuclideanLin (Z t)) = γ t`), and, at each crossing
  `t : I` (`γ t ⊓ V ≠ ⊥`), `HasDerivWithinAt Z (Z' t) (Icc 0 1) t` and a
  nondegenerate `lagrangianCrossingForm (Z t) (Z' t) V`. Then
  `pathMaslovIndex γ V` is half the sum of the signatures at `0` and `1` plus
  `∑ᶠ t ∈ Ioo 0 1` of the signatures, exactly the shape of Tau Ceti's
  `maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`. Neither
  continuity of `Z` nor injectivity of `Z t` is assumed: the second follows
  from the image being Lagrangian, and the proof reads continuity off `γ`.
  Proof: the crossings are finite (`ℒ.finite_setOfPred_inf_ne_bot_of_regular`,
  from `ℒ.eventually_not_crossing_of_regular` in a compact interval), and the
  signatures vanish elsewhere (`lagrangianCrossingForm_eq_zero_of_inf_eq_bot`).
  Near each time `t₀` choose a Lagrangian `W` transverse to both
  `V` and `γ t₀` (G8), and a symplectic matrix taking `V` to `V₀` and `W` to
  `V₁` (G9); where `γ t` is transverse to `W`, the moved path is transverse to
  `V₁`, hence of the form $t\mapsto\operatorname{graph}A(t)$ over `V₀` with
  $A=YX^{-1}$ for the blocks of the moved frame (G7, with
  `StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian`
  for the invertibility of $X$); `A` is continuous as `γ` read in
  `ℒ.graphChart`, and differentiable wherever `Z` is
  (`HasDerivWithinAt.matrix_inv`). Cut `[0, 1]` into pieces that each lie in
  one such neighbourhood (`exists_monotone_Icc_subset_open_cover_unitInterval`;
  a cut may fall on a crossing, which then counts half on each side),
  reparametrize each piece by `[0, 1]` (which scales the crossing forms by a
  positive constant, `lagrangianCrossingForm_smul`), apply Tau Ceti's graph
  theorem to each through `ℒ.pathMaslovIndex_smul`, the naturality of the
  form, `lagrangianCrossingForm_graph` and
  `ℒ.pathMaslovIndex_graph_eq_crossing_sum` (the graph case relative to `V₀`,
  read through unitary frames as `ℒ.pathMaslovIndex_graph` is), and add the
  pieces with `ℒ.pathMaslovIndex_trans`.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Loop.lean`

- `ℒ.maslovIndex_eq_crossing_sum`: let `γ : Path Λ Λ` be a loop and
  `Z = (X; Y) : ℝ → Matrix (ι ⊕ ι) ι ℝ` a frame of it (image `γ t` for
  `t ∈ [0, 1]`) that closes up to a constant change of frame:
  `Z (t + 1) = Z t * g` for all `t`, for a fixed real matrix `g`. Continuity
  of `Z`, injectivity of `Z t` and invertibility of `g` are not assumed: the
  path formula needs none of the first two, and `g` is invertible because
  `Z 1 = Z 0 * g` spans a Lagrangian. Assume that `Z` has a derivative `Z' t`
  (`HasDerivAt`) at each crossing `t ∈ [0, 1)` with `V₁` ($\det X(t)=0$),
  where the forms
  $-\langle Yu,X'u\rangle$ on $\ker X(t)$ are nondegenerate. Then the index of
  `γ` is the `∑ᶠ t ∈ Ico 0 1` of their signatures. Proof:
  `ℒ.pathMaslovIndex_eq_crossing_sum_Ico` with `V = V₁` and
  `ℒ.pathMaslovIndex_eq_maslovIndex`. At `1` the frame is `Z 0 * g` with
  derivative `Z' 0 * g`, so by frame independence (constant `g`) the forms at
  `0` and at `1` have the same signature, and the correction term, half their
  difference, vanishes. A periodic frame is the case `g = 1`, but a loop of odd index has none:
  on the half-turn of `ℒ (Fin 1)` every real frame is
  $r(t)(\cos\pi t,\sin\pi t)$ with $r$ real, continuous and never zero, so
  that `Z 1 = Z 0 * g` with `g = -r 1 / r 0`, and `g = 1` would make $r$
  change sign. The plan's unitary frames
  $X+iY$ are a special case: a unitary lift `U` of the loop has
  `U 1 = U 0 * O` with `O` real orthogonal, and its real frame satisfies the
  hypothesis with `g = O` once extended by `U (t + 1) = U t * O`.
- `TauCeti.GLSymplectic.maslovIndex_eq_half_crossing_sum`: for a 1-periodic
  `Ψ : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ` of symplectic matrices with
  blocks $A,B,C,D$ (`Matrix.toBlocks₁₂` is $B$, `toBlocks₂₂` is $D$), and a
  loop `γ` in `GLSymplectic ι ℝ` with `γ t = Ψ t`, if `Ψ` has a derivative at
  each `t ∈ [0, 1)` with $\det B(t)=0$ and the forms $-\langle B'y,Dy\rangle$ on
  $\ker B(t)$ are nondegenerate, then `maslovIndex γ` is half the
  `∑ᶠ t ∈ Ico 0 1` of their signatures. Proof: the loop
  $t\mapsto\Psi(t)V_1$ is framed by $\binom{B}{D}$, periodic since `Ψ` is (the
  case `g = 1` above), its crossing forms relative to $V_1$ are these, and its
  index is twice that of `γ` (`ℒ.maslovIndex_smul_const`). The factor
  $\tfrac12$ is the one the plan explains by Robbin–Salamon's normalization.
- **Milestone theorem** `maslovIndex_eq_crossing_sum_and_half_crossing_sum`,
  in `SymplecticGeometry`: the conjunction of
  `ℒ.maslovIndex_eq_crossing_sum` and
  `TauCeti.GLSymplectic.maslovIndex_eq_half_crossing_sum`, in the order of the
  name.
  *Crossing-form formula for the Maslov index*.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/RegularPieces.lean`

The pieces of regular paths, each with an explicit frame and its crossing
forms relative to `V₀`.

- `ℒ.rotationPath` (defined in `Topology/Grassmannian/Lagrangian/Quotient.lean`),
  a rotation $s\mapsto e^{\varepsilon sJ_0}\Lambda$ off a
  Lagrangian `Λ`, with the frame $e^{\varepsilon sJ_0}Z_0$ (`rotationFrame`): its
  crossing form is $\pm\varepsilon\lvert Zu\rvert^2$ by
  `stdForm_apply_stdComplexStructure`, definite,
  so the crossing at `s = 0` is regular, and for small $\varepsilon$ there is
  no other (`ℒ.eventually_rotationPath_inf_eq_bot`;
  `lagrangianCrossingForm_smul_J_mul_apply`, in `SymplecticGeometry` since it is
  about matrices).
- Segments inside Tau Ceti's chart `Matrix.lagrangianChart` of the
  Lagrangians transverse to `V₀` (G7, `lagrangianChart_inf_realSubspace`):
  between any two such Lagrangians there is a path with a smooth frame and no
  crossing at all (`ℒ.exists_chartPath`; smoothness for the entrywise norm
  `Matrix.Norms.Elementwise`, as in Tau Ceti's `ContDiff.matrix_mul`).
- The single-coordinate half-turn
  $s\mapsto\operatorname{diag}(e^{i\pi s},1,\dots,1)V_1$
  (`ℒ.coordinateHalfTurn`): its only crossing, at $s=\tfrac12$, has the
  one-dimensional form $\pi$, and its index is `1`
  (`ℒ.pathMaslovIndex_coordinateHalfTurn`). The file imports
  `Data/Matrix/Basis.lean` for the matrix `1 + Eᵢᵢ a` of its frame, and
  `Analysis/Matrix/UnitaryGroup/Basic.lean` (*Unitary group topology*) for
  the diagonal unitary `Matrix.UnitaryGroup.detSection ι i (Circle.exp θ)` that
  turns the `i`-th coordinate plane.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Regular.lean`

- `ℒ.exists_homotopic_regular (γ : Path Λ Λ') (V)`: `γ` is homotopic with
  fixed ends to a path with a smooth frame as in
  `ℒ.pathMaslovIndex_eq_crossing_sum`, all of whose crossings with `V` are
  regular. The proof avoids transversality theory. By
  `ℒ.pathMaslovIndex_eq_iff_homotopic` it suffices to build, for the given
  ends, one such path of each value that the values property allows; by
  `ℒ.pathMaslovIndex_smul` one may take `V = V₀`. The path is a concatenation
  of the pieces of `Path/RegularPieces.lean`, joined at times that are not
  crossings: a rotation off the first end and the reverse rotation onto the
  last end; chart segments from the rotated first end to `V₁` and from `V₁`
  to the rotated last end; and at `V₁` copies of `ℒ.coordinateHalfTurn` or of
  its reverse, so that every value of the allowed coset is reached. At a
  junction both pieces span the same Lagrangian, so a constant change of
  frame on the later piece makes the frame continuous, and a
  reparametrization that is flat at the junctions makes it smooth. The
  file imports `Analysis/SpecialFunctions/SmoothTransition.lean` (*Smooth
  families*) for `TauCeti.deriv_collaredSmoothTransition_pos` and the
  eventual constancy of `TauCeti.collaredSmoothTransition`, which that
  reparametrization uses, and `Analysis/Calculus/ContDiff/Concat.lean` (*Smooth
  families*) for `curveTrans`, the glued frame.
- **Milestone theorem** `pathMaslovIndex_eq_crossing_sum_and_properties`, in
  `SymplecticGeometry` like the other three milestone theorems: one
  conjunction of `ℒ.eventually_not_crossing_of_regular`,
  `ℒ.pathMaslovIndex_eq_crossing_sum`, `ℒ.exists_homotopic_regular`, the frame
  independence of the crossing form itself
  as the pointwise identity `lagrangianCrossingForm_mul_apply` (the
  `Equivalent` corollary alone would only say equal signatures), and the properties of `Path/Basic.lean` and
  `Path/Naturality.lean` (naturality, catenation, product, localization,
  homotopy, zero, values, dependence on `V`, and loops in the angle form
  `ℒ.pathMaslovIndex_eq_sub_div_pi`), each for every `V`.
  *Maslov index for paths of Lagrangian subspaces*.

## Milestones

| Milestone | Theorem | File |
|---|---|---|
| *Maslov index for loops of symplectic matrices* | `SymplecticGeometry.isMaslovIndex_iff` | `Analysis/Matrix/SymplecticGroup/Maslov.lean` |
| *Maslov index for loops of Lagrangian subspaces* | `SymplecticGeometry.isLagrangianMaslovIndex_iff_and_maslovIndex_halfTurnLoop` | `…/Lagrangian/Maslov/Loop.lean` |
| *Crossing-form formula for the Maslov index* | `SymplecticGeometry.maslovIndex_eq_crossing_sum_and_half_crossing_sum` | `…/Lagrangian/Maslov/Crossing/Loop.lean` |
| *Maslov index for paths of Lagrangian subspaces* | `SymplecticGeometry.pathMaslovIndex_eq_crossing_sum_and_properties` | `…/Lagrangian/Maslov/Path/Regular.lean` |

Each statement holds for every `n`, including `n = 0`, where all spaces are
points and all indices vanish; no entry in `ERRATA.md` is needed. The
milestones hold in the plan's form: the path index is real-valued (Decision 3)
and loops are paths on `[0, 1]` (`DESIGN.md`, *Departures*), both equivalent
readings of the plan's statements. The crossing-form theorems ask for a
derivative only at the crossings, which is weaker than the smoothness of the
sources, and the loop formula allows any frame that closes up to a constant
change of frame, which contains the plan's unitary frames.

## Issues

In order; each is a few hundred lines. Blockers are the issues listed and,
for the Lagrangian ones, the issues of *Lagrangian Grassmannian* that provide
the interface items named.

1. **Symplectic loops: classification.** `maslovIndex_eq_iff_homotopic`,
   `homotopicWith_iff_maslovIndex_eq`. Blocked by #11 and #22. (Part of #34.)
2. **Symplectic loops: uniqueness.** `GLSymplectic.reindex` with its API and
   continuity (in their own files), `symplecticRotationLoop`,
   `homotopicWith_reindex_sum_symplecticRotationLoop`, `maslovPhase_reindex`,
   `maslovIndex_reindex`, `IsMaslovIndex`,
   `isMaslovIndex_iff`. Blocked by 1.
   (Part of #34; with 1 it completes the symplectic milestone.)
3. **Lagrangian loops: phase and index.** `Maslov/Basic.lean`. Blocked by
   G1, G2, G3, G4 (for `maslovPhase_unitary_smul`) and G5.
4. **Lagrangian loops: product axiom.** `Maslov/Product.lean`. Blocked by 3
   and G4.
5. **Lagrangian loops: classification and uniqueness.** `Maslov/Loop.lean`.
   Blocked by 2 (for `symplecticRotationLoop`), 4, G3 and #22.
6. **Paths: definition and transferred properties.** `Maslov/Path/Basic.lean`.
   Blocked by 3, G3 and G4 (the definition moves the path by
   `(ofUnitary U)⁻¹`).
7. **Paths: naturality, values, homotopy, dependence on `V`.**
   `Maslov/Path/Naturality.lean`. Blocked by 5 and 6.
8. **Crossing forms.** `Maslov/Crossing/Form.lean`, with
   `Analysis/Calculus/Deriv/Matrix.lean`. Blocked by G1, G4 and G6–G9;
   can go in parallel with 3–7.
9. **Crossing-form formula for paths.** `Maslov/Crossing/Path.lean`. Blocked
   by 7 and 8.
10. **Crossing-form formula for loops.** `Maslov/Crossing/Loop.lean`. Blocked
    by 4 and 9.
11. **Regular pieces.** `Maslov/Path/RegularPieces.lean`: the rotations, the
    chart segments and the coordinate half-turn with their frames and crossing
    forms. Blocked by 6 and 8 (and G7).
12. **Regular representatives and the path milestone.**
    `Maslov/Path/Regular.lean`: the gluing of frames, the flat
    reparametrization, `ℒ.exists_homotopic_regular` and the milestone
    conjunction. Blocked by 9 and 11.

Issues 3–12 are the parts of #35, which asks for this split. Issue 9 is the
largest; if it exceeds the size limit, its reduction to graph charts (the
cutting of `[0, 1]` and the change of chart) becomes an issue of its own
before it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.2 (Theorem 2.2.12) and §2.3 (Theorem 2.3.7, the crossing forms on pp. 49
  and 53–54).
* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993],
  Theorem 1.1, §2 (crossing forms, Theorems 2.3 and 2.4, Remarks 2.5 and 2.6).
