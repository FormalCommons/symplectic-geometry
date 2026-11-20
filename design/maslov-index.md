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
`.lake/packages/TauCeti/TauCeti/`; every Tau Ceti name below was checked at the
pinned commit `e0e414c`.

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
  (`maslovIndex_eq_of_homotopy`), product (`maslovIndex_mul`), direct sum
  (`maslovIndex_sum`, along `TauCeti.GLSymplectic.continuous_sum`), the value
  `Fintype.card ι` on `scalarRotationLoop ι` (`maslovIndex_scalarRotationLoop`),
  the reduction to unitary loops (`maslovIndex_map_ofUnitary`,
  `maslovIndex_map_polarUnitary`), and `maslovIndex_trans`, `maslovIndex_symm`,
  `maslovIndex_inv`, `maslovIndex_refl`.
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
  `maslovPhase_realImage`, `realImage_eq_realImage_iff_souriau_eq`).
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
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization`.

Nothing in Mathlib or Tau Ceti states the converse of either homotopy axiom,
either uniqueness statement, a topology on $\mathcal{L}(n)$, an index relative
to a Lagrangian other than $\mathbb{R}^n$, naturality under all of
$\mathrm{Sp}(2n)$, the values property, or crossing forms for paths
other than graphs over $\mathbb{R}^n$ (searched by statement in
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
   finer form of the values property (`pathMaslovIndex_add_half_sub_mem`
   below).
4. **A general reference Lagrangian.** The index relative to
   $V_0=\mathbb{R}^n\times\{0\}$ is Souriau's formula, read on $\mathcal{L}(n)$.
   For a general $V$ the definition moves $V$ to $V_0$ by a unitary matrix, not
   a symplectic one: by *Lagrangian Grassmannian*, $\mathrm{U}(n)$ already acts
   transitively, and the unitary matrices fixing $V_0$ are the real orthogonal
   ones, under which Souriau's formula is invariant (Tau Ceti's
   `Matrix.spectralAngleSum_conj`), so the definition does not depend on the
   choice. Naturality under all of $\mathrm{Sp}(2n)$ is then a theorem. Its
   proof joins a symplectic matrix fixing $V_0$,
   $\begin{pmatrix}A&B\\0&A^{-T}\end{pmatrix}$, to a real orthogonal one inside
   the stabilizer of $V_0$ (shrink $B$ to $0$, then deform $A$ to its
   orthogonal polar factor), and compares the two ends with catenation,
   homotopy invariance and the zero axiom: along the two side edges of the
   square the dimension of the intersection with $V_0$ does not change.
5. **The dictionary with Tau Ceti.** All of Tau Ceti's Lagrangian Maslov
   theory lives on `EuclideanSpace ℂ ι`, framed by unitary matrices. A unitary
   `U` frames the Lagrangian `(U : Matrix ι ι ℂ).realImage` there, and the
   Lagrangian `unitaryFrame U` of `StdSpace ι` here: the image of $V_0$ under
   `Matrix.toEuclideanLin (Matrix.realify U)`. These correspond under
   `complexToRealEuclidean ι` (read through `WithLp`), by Tau Ceti's
   `complexToRealEuclidean_mulVec`; `TauCeti.realSubspace ι` corresponds to
   $V_0$, and its image under multiplication by `I` to
   $V_1=\{0\}\times\mathbb{R}^n$. The part never transports a submodule by
   itself: it transfers a statement by choosing unitary frames, pointwise for
   statements about single Lagrangians and by path lifting for statements about
   paths, and then applies Tau Ceti's statement about the frames. The one
   comparison with Tau Ceti's `TotallyRealLoop` is a theorem
   (`maslovIndex_eq_totallyRealLoop_maslovIndex`), so that later pages can use
   Tau Ceti's boundary-value results.
6. **The order of the issues.** Symplectic loops come first and need only
   parts 3 and 4. The Lagrangian issues follow, after the issues of
   *Lagrangian Grassmannian* that provide the interface below. See *Issues*.

## Interface with Lagrangian Grassmannian

`design/lagrangian-grassmannian.md` is not written yet. This part needs the
following from it, under the names that design chooses; below, `ℒ ι` stands
for its space of Lagrangian subspaces of `(StdSpace ι, stdForm ι)` with its
topology, with a coercion to `Submodule ℝ (StdSpace ι)`.

- **G1.** The horizontal and vertical Lagrangians `V₀ ι`, `V₁ ι : ℒ ι`
  ($y=0$ and $x=0$).
- **G2.** The unitary frame map `unitaryFrame : unitaryGroup ι ℂ → ℒ ι`,
  `U ↦ (Matrix.toEuclideanLin (Matrix.realify U)) '' V₀`; continuous and
  surjective (transitivity of $\mathrm{U}(n)$); `unitaryFrame U = unitaryFrame U'`
  if and only if `U⁻¹ * U'` is real (`Matrix.map` of a real orthogonal matrix);
  and the homeomorphism $\mathrm{U}(n)/\mathrm{O}(n)\cong\mathcal{L}(n)$ that
  `DESIGN.md` promises, so that a map out of `ℒ ι` is continuous when its
  composite with `unitaryFrame` is.
- **G3.** Path lifting: for every path `γ : Path Λ Λ'` in `ℒ ι` and every `U`
  with `unitaryFrame U = Λ`, a path `δ` in `unitaryGroup ι ℂ` starting at `U`
  with `unitaryFrame (δ t) = γ t` for all `t`. The natural proof is that
  `unitaryFrame` is a Serre fibration with fibre $\mathrm{O}(n)$: local sections
  come from the graph charts (the frame $\mathbb{1}+iS$ of the graph of a
  symmetric $S$, made unitary by Tau Ceti's `realOrthonormalize`), and Tau
  Ceti's `Subgroup.localSectionTrivializationOfCosetFibers` and
  `TauCeti.TopCat.mem_serreFibrations_of_exists_trivialization` do the rest.
- **G4.** The action of `GLSymplectic ι ℝ` on `ℒ ι`, with
  `ContinuousSMul`, and `ofUnitary U • unitaryFrame U' = unitaryFrame (U * U')`.
- **G5.** The direct sum `ℒ ι × ℒ κ → ℒ (ι ⊕ κ)` and the reindexing
  `ℒ ι ≃ₜ ℒ κ` along `ι ≃ κ`, both continuous, compatible with `unitaryFrame`
  (the sum of `unitaryFrame U` and `unitaryFrame U'` is the frame of
  `Matrix.UnitaryGroup.sum (U, U')`, and the reindexing of `unitaryFrame U`
  is the frame of the reindexed matrix), and with the action of
  `TauCeti.GLSymplectic.sum`.
- **G6.** The frame criterion: for `Z : Matrix (ι ⊕ ι) ι ℝ` of rank $n$, the
  image of `Matrix.toEuclideanLin Z` is Lagrangian if and only if
  $X^TY=Y^TX$; with it, the element of `ℒ ι` that such a frame spans.

If the design of *Lagrangian Grassmannian* leaves out one of these, it is
added there by its own issue, which then blocks the Lagrangian issues here.

## Files and declarations

Files are under `SymplecticGeometry/`. Declarations about Tau Ceti's notions go
in Tau Ceti's namespaces; those about `ℒ ι` go in the namespace of its type,
written `ℒ.` below; everything else in `SymplecticGeometry`.

### `Analysis/Matrix/SymplecticGroup/Maslov.lean`

Symplectic loops, in the namespace `TauCeti.GLSymplectic`. Named like Tau
Ceti's file, which it extends.

- `maslovPhase_reindex` and `maslovIndex_reindex`: reindexing (below) keeps
  $\rho$ and the index of a loop. The reindexing itself is algebra, and goes
  in its own file `LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Reindex.lean`
  (Tau Ceti has a folder of that name, without such a file), in the namespace
  `TauCeti.GLSymplectic`: `reindex (e : ι ≃ κ) : GLSymplectic ι R ≃* GLSymplectic κ R`,
  the restriction of Tau Ceti's `Equiv.reindexGL` along `Equiv.sumCongr e e`,
  symplectic by Tau Ceti's `Matrix.reindex_sumCongr_J`, with `coe_reindex`
  (`@[simp]`), `reindex_symm`, `reindex_trans` and `reindex_sum` (it commutes
  with `TauCeti.GLSymplectic.sum` along `Equiv.sumCongr`); its continuity,
  `continuous_reindex`, goes in `Topology/Algebra/SymplecticGroup.lean`, named
  like the Tau Ceti file that has `continuous_sum`.
- `maslovIndex_eq_iff_homotopic {A} {γ γ' : Path A A} :
  maslovIndex γ = maslovIndex γ' ↔ γ.Homotopic γ'`. For `ι` empty the group is
  trivial. Otherwise, at `A = 1`: Tau Ceti's `polarHomotopy` fixes
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
- The standard loops: `rotationLoop (k : ℤ) : Path (1 : GLSymplectic (Fin 1) ℝ) 1`,
  `t ↦ ofUnitary (e^{2πikt})`, of index `k`; every loop in
  `GLSymplectic (Fin (n + 1)) ℝ` is freely homotopic to the direct sum of the
  constant loop in dimension `n` and `rotationLoop k`, reindexed, with `k` its
  index.
- `structure IsMaslovIndex (μ : (n : ℕ) → (A : GLSymplectic (Fin n) ℝ) → Path A A → ℤ) : Prop`
  with the fields of the milestone, each for all `n` and all loops:
  `homotopicWith_iff : γ ≈ γ' ↔ μ n A γ = μ n B γ'`;
  `mul : μ n (A * B) (γ.mul γ') = μ n A γ + μ n B γ'`;
  `sum`, the direct sum `((γ.prod γ').map continuous_sum)` reindexed by
  `finSumFinEquiv`, of index `μ n A γ + μ m B γ'`;
  `normalization : μ 1 1 ((scalarRotationLoop (Fin 1)).map continuous_ofUnitary) = 1`.
- **Milestone theorem** `isMaslovIndex_iff (μ) :
  IsMaslovIndex μ ↔ μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase)`.
  The right side is `maslovIndex` by `maslovIndex_def`, so the statement holds
  existence, the formula $\mu=\deg(\rho\circ\Psi)$ and uniqueness. Uniqueness:
  the product axiom gives `0` on constant loops (a constant loop at `1` is its
  own square; others are freely homotopic to it) and `k` on `rotationLoop k`
  (a pointwise power of the normalized loop, or the inverse of one); the sum
  axiom and the standard loops then give every value.
  *Maslov index for loops of symplectic matrices*.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Basic.lean`

The Maslov phase on $\mathcal{L}(n)$ and the index of Lagrangian loops.

- `ℒ.souriau : ℒ ι → unitaryGroup ι ℂ`, the Souriau embedding
  $\Lambda\mapsto UU^T$ for any unitary frame `U` of `Λ`; well defined by
  `Matrix.UnitaryGroup.realImage_eq_realImage_iff_souriau_eq` and G2. API:
  `souriau_unitaryFrame : souriau (unitaryFrame U) = Matrix.UnitaryGroup.souriau U`
  (`@[simp]`), `continuous_souriau`, `souriau_injective`, `souriau_sum`.
- `ℒ.maslovPhase (Λ : ℒ ι) : Circle := detCircle (souriau Λ)`, the book's
  $\rho$, with `maslovPhase_def`, `continuous_maslovPhase`,
  `maslovPhase_unitaryFrame : maslovPhase (unitaryFrame U) = detCircle U ^ 2`
  (by `Matrix.UnitaryGroup.detCircle_souriau`), `maslovPhase_sum` (the phase
  of a direct sum is the product), `maslovPhase_reindex`, and
  `maslovPhase_ofUnitary_smul : maslovPhase (ofUnitary U • Λ) = detCircle U ^ 2 * maslovPhase Λ`.
- `ℒ.maslovIndex {Λ} (γ : Path Λ Λ) : ℤ := Circle.degree (γ.map continuous_maslovPhase)`,
  with `maslovIndex_def`; `maslovIndex_eq_of_homotopy` (free homotopy, from
  `Circle.degree_eq_of_homotopy`), `maslovIndex_refl` (zero),
  `maslovIndex_trans`, `maslovIndex_symm`, `maslovIndex_sum`,
  `maslovIndex_reindex`, and `maslovIndex_map_unitaryFrame`: for a loop of
  frames `δ`, the index of `δ.map continuous_unitaryFrame` is twice the degree
  of $\det\delta$.
- The half-turn `ℒ.halfTurnLoop (k : ℤ) : Path (V₀ ι) (V₀ ι)`,
  `t ↦ unitaryFrame (e^{iπkt} • 1)`, with `maslovIndex_halfTurnLoop :
  maslovIndex (halfTurnLoop k) = k * Fintype.card ι` (from Tau Ceti's
  `maslovIndex_eq_card_of_halfTurn` and `maslovIndex_eq_degree`, or directly
  from `Circle.degree_eq_of_sub_eq`). For `ι = Fin 1` and `k = 1` this is the
  half-turn of the milestone, of index `1`.
- `maslovIndex_eq_totallyRealLoop_maslovIndex`: the index of a loop in `ℒ ι`
  is the Tau Ceti index of the `TotallyRealLoop` that a lift of it to unitary
  frames gives through `Matrix.UnitaryGroup.realImageLoop`
  (`maslovIndex_realImageLoop`, `maslovIndex_eq_degree`). It needs G3.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Product.lean`

- `ℒ.maslovIndex_smul {A Λ} (Ψ : Path A A) (γ : Path Λ Λ) :
  maslovIndex ((Ψ.prod γ).map continuous_smul) = maslovIndex γ + 2 * GLSymplectic.maslovIndex Ψ`.
  For a loop of `ofUnitary` matrices this is `maslovPhase_ofUnitary_smul` with
  `Circle.degree_mul`. In general, Tau Ceti's `polarHomotopy` deforms `Ψ`
  through loops of symplectic matrices to its loop of unitary polar factors;
  acting on `γ` it gives a free homotopy of Lagrangian loops (G4), and
  `maslovIndex_map_polarUnitary` keeps the symplectic index.
- `ℒ.maslovIndex_smul_const`: the case of a constant `γ`, which gives
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
  $\det\delta$ divided by $\pi$, so its parity fixes `D`. Two loops with the
  same index therefore have lifts with the same ends and the same angle change
  of $\det$, which are homotopic with fixed ends by the isomorphism of issue
  #22 (stated for `Fin n`; moved to `ι` along `Fintype.equivFin ι`).
- `ℒ.homotopicWith_iff_maslovIndex_eq (γ : Path Λ Λ) (γ' : Path Λ' Λ')`: the
  free form, as for symplectic loops.
- The standard loops: every loop in `ℒ (Fin (n + 1))` is freely homotopic to
  the direct sum of the constant loop at `V₀ (Fin n)` and `halfTurnLoop k` in
  `ℒ (Fin 1)`, reindexed, where `k` is its index.
- `structure ℒ.IsMaslovIndex (μ : (n : ℕ) → (Λ : ℒ (Fin n)) → Path Λ Λ → ℤ) : Prop`
  with the four axioms that determine the index: `homotopicWith_iff`; `smul`,
  `μ n _ ((Ψ.prod γ).map continuous_smul) = μ n Λ γ + 2 * GLSymplectic.maslovIndex Ψ`;
  `sum`, through G5 and `finSumFinEquiv`; and `refl : μ n Λ (Path.refl Λ) = 0`.
- **Milestone theorem** `ℒ.isMaslovIndex_iff_and_maslovIndex_halfTurnLoop`:
  for every `μ`, `IsMaslovIndex μ ↔
  μ = fun _ _ γ ↦ Circle.degree (γ.map continuous_maslovPhase)`,
  stated together with the normalization
  `maslovIndex (halfTurnLoop (ι := Fin 1) 1) = 1`, as one conjunction, so that
  one theorem carries the whole milestone; `maslovPhase_unitaryFrame` gives
  $\rho$ explicitly. Uniqueness: on `ℒ (Fin 1)`, `halfTurnLoop (2 * j)` is
  `rotationLoop j` acting on the constant loop, of value `2 * j` by `smul` and
  `refl`; the direct sum of `halfTurnLoop k` with itself is freely homotopic to
  the direct sum of `halfTurnLoop (2 * k)` and a constant loop, both having
  index `2 * k`, so `homotopicWith_iff` and `sum` give `k` for
  `halfTurnLoop k`; the standard loops do the rest.
  *Maslov index for loops of Lagrangian subspaces*.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Basic.lean`

The Robbin–Salamon index of paths, relative to a Lagrangian `V`.

- `ℒ.pathMaslovIndexHorizontal {Λ Λ'} (γ : Path Λ Λ') : ℝ`, relative to `V₀`,
  defined by Souriau's formula on `ℒ ι`:
  `Circle.angleChange (γ.map continuous_maslovPhase) / (2 * π) - (spectralAngleSum (souriau Λ') - spectralAngleSum (souriau Λ))`,
  with the `_def` lemma and `pathMaslovIndexHorizontal_map_unitaryFrame`: for
  a path `δ` of frames it is `Matrix.UnitaryGroup.maslovIndex δ` (unfolding
  both definitions). This is how all of Tau Ceti's theorems apply, through G3.
- `ℒ.pathMaslovIndex {Λ Λ'} (γ : Path Λ Λ') (V : ℒ ι) : ℝ`: choose `U` with
  `unitaryFrame U = V` and take `pathMaslovIndexHorizontal` of
  `γ.map (continuous_const_smul (ofUnitary U)⁻¹)`.
  `pathMaslovIndex_eq_of_unitaryFrame_eq` says that any such `U` gives the
  same value (Decision 4), and `pathMaslovIndex_horizontal` that for `V = V₀` it is
  `pathMaslovIndexHorizontal`. Every other statement uses these, not the
  choice.
- Transferred from Tau Ceti, each for every `V`: `pathMaslovIndex_eq_of_homotopic`
  (fixed ends), `pathMaslovIndex_trans` (catenation, with the corollary
  `pathMaslovIndex_eq_subpath_add` for a split point `c`), `pathMaslovIndex_symm`,
  `pathMaslovIndex_refl`, `pathMaslovIndex_sum` (the product property, for the
  sum of two paths relative to the sum of two Lagrangians, G5),
  `pathMaslovIndex_eq_zero_of_finrank_eq` (zero: `finrank (γ t ⊓ V)` constant),
  `pathMaslovIndex_graph` (localization: for `V = V₀` and the path of graphs
  $\{(x,A(t)x)\}$ of a path of symmetric matrices, half the change of
  `Matrix.signature`, from `maslovIndex_eq_signature_sub_of_souriau_eq_cayley`,
  whose frames $\mathbb{1}+iA$ span exactly these graphs).
- Loops: `pathMaslovIndex_eq_maslovIndex (γ : Path Λ Λ) (V) :
  pathMaslovIndex γ V = maslovIndex γ`, for every `V`; and
  `maslovIndex_eq_sub_div_pi`: if `δ` is a path of frames of the loop and
  $\det\delta(t)=e^{i\alpha(t)}$ with `α` continuous, the index is
  $(\alpha(1)-\alpha(0))/\pi$.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Naturality.lean`

- `pathMaslovIndex_smul (Ψ : GLSymplectic ι ℝ) (γ) (V) :
  pathMaslovIndex (γ.map (continuous_const_smul Ψ)) (Ψ • V) = pathMaslovIndex γ V`,
  by the stabilizer argument of Decision 4.
- `pathMaslovIndex_add_half_sub_mem (γ : Path Λ Λ') (V) :
  pathMaslovIndex γ V + (finrank (Λ ⊓ V) - finrank (Λ' ⊓ V)) / 2 ∈ Set.range (Int.cast : ℤ → ℝ)`
  (the values property), from Tau Ceti's
  `Matrix.det_eq_neg_one_pow_mul_exp_spectralAngleSum` and
  `rootMultiplicity_one_charpoly_souriau`; with the corollary that `2 •` the
  index is an integer.
- `pathMaslovIndex_eq_iff_homotopic {γ γ' : Path Λ Λ'} (V) :
  pathMaslovIndex γ V = pathMaslovIndex γ' V ↔ γ.Homotopic γ'`, from
  `maslovIndex_eq_iff_homotopic` applied to `γ.trans γ'.symm`.
- `pathMaslovIndex_sub_pathMaslovIndex (γ γ' : Path Λ Λ') (V V')`: the
  difference `pathMaslovIndex γ V' - pathMaslovIndex γ V` is the same for `γ'`
  (the Hörmander index depends only on the ends), since the loop
  `γ.trans γ'.symm` has the same index relative to `V` and to `V'`. The part
  defines no function for the Hörmander index: nothing here uses one.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Form.lean`

- `lagrangianCrossingForm (Z Z' : Matrix (ι ⊕ ι) ι ℝ) (V : Submodule ℝ (StdSpace ι)) :
  QuadraticForm ℝ (V.comap (Matrix.toEuclideanLin Z))`,
  `u ↦ stdForm ι (toEuclideanLin Z u) (toEuclideanLin Z' u)`. For a frame
  $Z=\binom{X}{Y}$ with derivative $Z'$ this is
  $\langle Xu,Y'u\rangle-\langle Yu,X'u\rangle$ on the $u$ with $Zu\in V$, by
  `stdForm_apply`: Robbin–Salamon's form $Q_t$ restricted to $\Lambda\cap V$.
  API: `lagrangianCrossingForm_apply` (`@[simp]`); that the associated bilinear
  form is symmetric when `Z t` spans a Lagrangian for all `t` and has
  derivative `Z'`; `lagrangianCrossingForm_vertical`, the value
  $-\langle Yu,X'u\rangle$ for `V = V₁` (the form of the loop formula);
  `lagrangianCrossingForm_graph`, the identification with Tau Ceti's
  `Matrix.crossingForm A A'` for `Z = (1; A)` and `V = V₀`.
- Frame independence: for a second frame `Z * g` with `g t` invertible and
  differentiable, the two forms are isometric (the term with `g'` vanishes
  because the frame spans a Lagrangian), so `sigPos` and `sigNeg` agree
  (`sigPos_lagrangianCrossingForm_mul`, `sigNeg_lagrangianCrossingForm_mul`).
- Naturality: for `Ψ` symplectic, the form of `Ψ * Z` relative to `Ψ • V` is
  isometric to that of `Z` relative to `V`.
- Regular crossings are isolated (`eventually_not_crossing_of_regular`): reduce
  to a graph chart by naturality and apply Tau Ceti's
  `ContinuousLinearMap.eventually_nondegenerate_of_crossingForm_nondegenerate`.

Signatures are `(sigPos Q : ℤ) - sigNeg Q`, as in Tau Ceti's crossing theorem;
the part adds no signature function.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Path.lean`

- `pathMaslovIndex_eq_crossing_sum`: let `γ : Path Λ Λ'`, `V : ℒ ι`, and
  `Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ` with `Z` continuous on `Icc 0 1`, each `Z t`
  injective with image `γ t`, and, at each crossing `t ∈ Icc 0 1`
  (`γ t ⊓ V ≠ ⊥`), `HasDerivWithinAt Z (Z' t) (Icc 0 1) t` and a nondegenerate
  `lagrangianCrossingForm (Z t) (Z' t) V`. Then `pathMaslovIndex γ V` is half
  the sum of the signatures at `0` and `1` plus `∑ᶠ t ∈ Ioo 0 1` of the
  signatures, exactly the shape of Tau Ceti's
  `maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`. Proof: the
  crossings are finite (isolated, in a compact interval). Near each time `t₀`
  choose a Lagrangian `W` transverse to both `V` and `γ t₀`, and a symplectic
  matrix taking `V` to `V₀` and `W` to `V₁`; near `t₀` the moved path is
  transverse to `V₁`, hence of the form $t\mapsto\operatorname{graph}A(t)$
  over `V₀`, with `A` differentiable wherever `Z` is. Cut `[0, 1]` at non-crossing times into
  pieces that each lie in one such neighbourhood, apply Tau Ceti's graph
  theorem to each through `pathMaslovIndex_smul`, the naturality of the form,
  `pathMaslovIndex_graph` and `lagrangianCrossingForm_graph`, and add the
  pieces with `pathMaslovIndex_trans`.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Crossing/Loop.lean`

- `ℒ.maslovIndex_eq_crossing_sum`: let `γ : Path Λ Λ` be a loop and
  `Z = (X; Y) : ℝ → Matrix (ι ⊕ ι) ι ℝ` a 1-periodic continuous frame of it
  (each `Z t` injective, with image `γ t` for `t ∈ [0, 1]`), with a derivative
  at each crossing with `V₁` ($\det X(t)=0$), where the forms
  $-\langle Yu,X'u\rangle$ on $\ker X(t)$ are nondegenerate. Then the index of
  `γ` is the `∑ᶠ t ∈ Ico 0 1` of their signatures:
  `pathMaslovIndex_eq_crossing_sum` with `V = V₁` and
  `pathMaslovIndex_eq_maslovIndex`; the two half weights at `0` and `1` add
  up, the frame being periodic. Unitary frames $X+iY$, the plan's form, are a
  special case; the symplectic formula below needs frames that are not
  unitary.
- `TauCeti.GLSymplectic.maslovIndex_eq_half_crossing_sum`: for a 1-periodic
  continuous `Ψ : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ` of symplectic matrices with
  blocks $A,B,C,D$ (`Matrix.toBlocks₁₂` is $B$, `toBlocks₂₂` is $D$), and a
  loop `γ` in `GLSymplectic ι ℝ` with `γ t = Ψ t`, if `Ψ` has a derivative at
  each `t` with $\det B(t)=0$ and the forms $-\langle B'y,Dy\rangle$ on
  $\ker B(t)$ are nondegenerate, then `maslovIndex γ` is half the
  `∑ᶠ t ∈ Ico 0 1` of their signatures. Proof: the loop
  $t\mapsto\Psi(t)V_1$ is framed by $\binom{B}{D}$, its crossing forms relative
  to $V_1$ are these, and its index is twice that of `γ`
  (`maslovIndex_smul_const`). The factor $\tfrac12$ is the one the plan
  explains by Robbin–Salamon's normalization.
- **Milestone theorem**: the two formulas as one conjunction.
  *Crossing-form formula for the Maslov index*.

### `LinearAlgebra/Symplectic/Lagrangian/Maslov/Path/Regular.lean`

- `exists_homotopic_regular (γ : Path Λ Λ') (V)`: `γ` is homotopic with fixed
  ends to a path with a smooth frame as in `pathMaslovIndex_eq_crossing_sum`,
  all of whose crossings with `V` are regular. The proof avoids transversality
  theory. By `pathMaslovIndex_eq_iff_homotopic` it suffices to build, for the
  given ends, one such path of each value that the values property allows; by
  `pathMaslovIndex_smul` one may take `V = V₀`. The path is a concatenation of
  pieces, joined at times that are not crossings:
  - a rotation $s\mapsto e^{\varepsilon sJ_0}\Lambda$ off the first end, and
    the reverse rotation onto the last end: for the frame
    $e^{\varepsilon sJ_0}Z_0$ the crossing form is
    $\pm\varepsilon\lvert Zu\rvert^2$ by `stdForm_apply_eq_inner`, definite,
    so the crossing at the end is regular, and for small $\varepsilon$ there
    is no other;
  - segments inside Tau Ceti's chart `Matrix.lagrangianChart` of the
    Lagrangians transverse to `V₀` (`lagrangianChart_inf_realSubspace`), which
    have no crossings at all, from the rotated first end to `V₁` and from `V₁`
    to the rotated last end;
  - at `V₁`, copies of the loop
    $s\mapsto\operatorname{diag}(e^{i\pi s},1,\dots,1)V_1$ or of its reverse:
    its only crossing, at $s=\tfrac12$, has the one-dimensional form $\pm\pi$,
    and its index is $\pm1$, so every value of the allowed coset is reached.

  At a junction both pieces span the same Lagrangian, so a constant change of
  frame on the later piece makes the frame continuous, and a reparametrization
  that is flat at the junctions makes it smooth.
- **Milestone theorem** for *Maslov index for paths of Lagrangian subspaces*:
  one conjunction of `pathMaslovIndex_eq_crossing_sum`,
  `exists_homotopic_regular`, the frame independence of the crossing form, and
  the properties of `Path/Basic.lean` and `Path/Naturality.lean` (naturality,
  catenation, product, localization, homotopy, zero, values, loops, dependence
  on `V`), each for every `V`.

## Milestones

| Milestone | Theorem | File |
|---|---|---|
| *Maslov index for loops of symplectic matrices* | `TauCeti.GLSymplectic.isMaslovIndex_iff` | `Analysis/Matrix/SymplecticGroup/Maslov.lean` |
| *Maslov index for loops of Lagrangian subspaces* | `ℒ.isMaslovIndex_iff_and_maslovIndex_halfTurnLoop` | `…/Lagrangian/Maslov/Loop.lean` |
| *Crossing-form formula for the Maslov index* | one conjunction in `…/Maslov/Crossing/Loop.lean` | `…/Lagrangian/Maslov/Crossing/Loop.lean` |
| *Maslov index for paths of Lagrangian subspaces* | the conjunction in `…/Maslov/Path/Regular.lean` | `…/Lagrangian/Maslov/Path/Regular.lean` |

Each statement holds for every `n`, including `n = 0`, where all spaces are
points and all indices vanish; no entry in `ERRATA.md` is needed. The
milestones hold in the plan's form: the path index is real-valued (Decision 3)
and loops are paths on `[0, 1]` (`DESIGN.md`, *Departures*), both equivalent
readings of the plan's statements. The crossing-form theorems ask for a
derivative only at the crossings, which is weaker than the smoothness of the
sources.

## Issues

In order; each is a few hundred lines. Blockers are the issues listed and,
for the Lagrangian ones, the issues of *Lagrangian Grassmannian* that provide
G1–G6.

1. **Symplectic loops: classification.** `maslovIndex_eq_iff_homotopic`,
   `homotopicWith_iff_maslovIndex_eq`. Blocked by #11 and #22. (Part of #34.)
2. **Symplectic loops: uniqueness.** `GLSymplectic.reindex` with its API (in
   its own file), the standard loops, `IsMaslovIndex`, `isMaslovIndex_iff`.
   Blocked by 1.
   (Part of #34; with 1 it completes the symplectic milestone.)
3. **Lagrangian loops: phase and index.** `Maslov/Basic.lean`. Blocked by
   G1, G2, G5 (G3 for the comparison with `TotallyRealLoop`).
4. **Lagrangian loops: product axiom.** `Maslov/Product.lean`. Blocked by 3
   and G4.
5. **Lagrangian loops: classification and uniqueness.** `Maslov/Loop.lean`.
   Blocked by 4, G3 and #22.
6. **Paths: definition and transferred properties.** `Maslov/Path/Basic.lean`.
   Blocked by 3 and G3.
7. **Paths: naturality, values, homotopy, dependence on `V`.**
   `Maslov/Path/Naturality.lean`. Blocked by 5 and 6.
8. **Crossing forms.** `Maslov/Crossing/Form.lean`. Blocked by G4 and G6; can
   go in parallel with 3–7.
9. **Crossing-form formula for paths.** `Maslov/Crossing/Path.lean`. Blocked
   by 7 and 8.
10. **Crossing-form formula for loops.** `Maslov/Crossing/Loop.lean`. Blocked
    by 4 and 9.
11. **Regular representatives and the path milestone.**
    `Maslov/Path/Regular.lean`. Blocked by 9.

Issues 3–11 are the parts of #35, which asks for this split. Issue 9 is the
largest; if it exceeds the size limit, its reduction to graph charts (the
cutting of `[0, 1]` and the change of chart) becomes an issue of its own
before it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.2 (Theorem 2.2.12) and §2.3 (Theorem 2.3.7, the crossing forms on pp. 49
  and 53–54).
* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993],
  Theorem 1.1, §2 (crossing forms, Theorems 2.3 and 2.4, Remarks 2.5 and 2.6).
