# Compatible complex structures

The detailed design of part 9 of `DESIGN.md`. It covers the five milestones
of `atlas/linear-symplectic-geometry.md` that the overview gives this part:
*Characterizations of compatible complex structures*, *Contractibility of the
space of compatible complex structures*, *Complex structures versus
symplectic forms*, *Compact subgroups of the symplectic group* and
*Contractibility of the space of tame complex structures*
(McDuff–Salamon [McDuffSalamon2017], §2.5: Proposition 2.5.4, Exercise 2.5.3,
Lemma 2.5.5, Proposition 2.5.6, Corollary 2.5.7, Proposition 2.5.8,
Proposition 2.5.13).

All statements about Tau Ceti were checked against the pinned `v4.37.0-rc1`
(commit `e0e414c`). Tau Ceti paths are relative to
`.lake/packages/TauCeti/TauCeti/`, and the library's paths are relative to
`SymplecticGeometry/`.

## What exists, and what this part adds

Tau Ceti already has the notions and much of the theory. The part reuses it
and does not redefine any of it:

- `TauCeti.AlmostComplexStructure V`, its topology
  (`Geometry/Symplectic/AlmostComplex/Topology.lean`: induced from
  `V →L[ℝ] V` by `isEmbedding_toContinuousLinearMap`, on a finite-dimensional
  normed space), `transport`, `IsComplexLinearMap`.
- `TauCeti.SymplecticForm.Compatible`, `Tames`, `Invariant`,
  `associatedBilinForm` ($g_J$), `complexAssociatedForm` ($H$),
  `Compatible.hermitianCore`, `Compatible.innerProductCore`,
  `Compatible.associatedBilinForm_isSymm`, `compatible_iff`,
  `Compatible.transport`, `IsSymplectomorphism`, `IsDarbouxBasis`,
  `exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`
  (`Geometry/Symplectic/WeightDecomposition.lean`), `exists_compatible`.
- The polar complex structure for the ambient inner product,
  `TauCeti.SymplecticForm.polarComplexStructure`
  (`Geometry/Symplectic/PolarCompatible.lean`), with
  `compatible_polarComplexStructure`, `inner_polarComplexStructure_apply_apply`,
  `polarComplexStructure_eq_of_apply_eq_inner`, `polarComplexStructure_transport`,
  its expression through the metric-change transport
  `conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`, and
  `exists_compatible_forall_isComplexLinearMap` (an invariant compatible
  structure for a compact group).
- The metric-change transport `ContinuousLinearMap.metricChangeTransport` of a
  continuous bilinear form, with `isStrictlyPositive_continuousLinearMapOfBilin_iff`
  and its smoothness, `contDiffOn_metricChangeTransport`,
  `contDiffOn_sqrt_continuousLinearMapOfBilin`
  (`Analysis/InnerProductSpace/Positive/MetricChange/`), and the smoothness of the
  square root, `contDiffOn_sqrt`
  (`Analysis/InnerProductSpace/Positive/FunctionalCalculus.lean`).
- On continuous bilinear forms (`Topology/Algebra/Module/BilinearForm.lean`):
  `TauCeti.convex_setOfPred_symm_pos`,
  `TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos`,
  `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm`.
- The Cayley transform (`Geometry/Symplectic/Cayley/`): `cayleyFormula`,
  `cayleyPathFormula`, `contDiffAt_cayleyPathFormula`,
  `Compatible.cayleyEquiv`, `Compatible.cayleyInterp`,
  `Compatible.cayleyContraction`, `Compatible.compatibleCayleyContraction`,
  `Compatible.toContinuousLinearMap_cayleyContraction`,
  `Tames.isUnit_one_sub_mul_of_toLinearMap`,
  `Compatible.isUnit_one_sub_smul_cayleyFormula`,
  `ContinuousLinearEquiv.apply_cayleyPathFormula_apply`, and the instances
  `instContractibleSpaceTames`, `instContractibleSpaceCompatible`.
- The unitary group inside the symplectic group:
  `TauCeti.GLSymplectic.ofUnitary`,
  `Matrix.symplecticGroup_inf_centralizer_J`.

What is missing, and what this part adds:

1. the converse implications of the characterizations: a symplectic basis
   of the form $(v_k, Jv_k)$ gives compatibility, as does a symplectomorphism
   with $(\omega_0,J_0)$, as does condition (4), as does a symmetric positive
   $g_J$, as does a Hermitian $H$;
2. $J_{g,\omega}$ for an inner product $g$ that is not the ambient one, as a
   map of $(g,\omega)$, with its characterization, naturality and smoothness;
3. topologies on the inner products and the symplectic forms of $V$;
4. the homeomorphism of Lemma 2.5.5, the homotopy equivalences of
   Proposition 2.5.6 and Corollary 2.5.7, and the inclusion of compatible
   into tame structures as a homotopy equivalence;
5. the conjugation of a compact subgroup into $\mathrm{U}(n)$.

## Decisions

These settle the questions that `DESIGN.md` leaves to this file.

### Topologies

- **Complex structures.** The part uses Tau Ceti's topology on
  `AlmostComplexStructure V` and introduces no other. That topology is
  induced from the operator norm on `V →L[ℝ] V`. On a finite-dimensional
  space, every norm gives the same topology, so this is the finite-dimensional
  topology of $\mathrm{End}(V)$, and no comparison lemma is needed. The spaces
  of the milestones are Tau Ceti's subtypes `{J // ω.Compatible J}` and
  `{J // ω.Tames J}`, with the subspace topology.
- **Bilinear forms.** Inner products and symplectic forms are seen as
  continuous bilinear forms `V →L[ℝ] V →L[ℝ] ℝ`, with the operator norm. This
  is how Mathlib's `Bundle.RiemannianMetric` and Tau Ceti's metric change
  present them, so the bundle part can use the same maps. A
  `LinearMap.BilinForm ℝ V` on a finite-dimensional space becomes one by
  Mathlib's `LinearMap.BilinForm.toContinuousBilinearMap`.
- **The inner products** $\mathrm{Met}(V)$ are the set
  `SymplecticGeometry.innerProducts V` of continuous bilinear forms that are
  symmetric and positive on nonzero vectors. This is exactly the set of
  `TauCeti.convex_setOfPred_symm_pos`. It is a type through its coercion to a
  subtype.
- **The symplectic forms** $\Omega(V)$ are `TauCeti.SymplecticForm V`, with
  the topology induced by `ω ↦ ω.toBilinForm.toContinuousBilinearMap`, an
  instance in the namespace `TauCeti.SymplecticForm`. It is defined in the
  same way as Tau Ceti's instance on `AlmostComplexStructure V`.

All topological statements assume `[NormedAddCommGroup V] [NormedSpace ℝ V]
[FiniteDimensional ℝ V]`, as Tau Ceti's topology does. Only the smoothness
proofs of $J_{g,\omega}$ use an inner product, and they use it only after
transport to a Euclidean space, so no statement asks for an
`InnerProductSpace` instance on `V`.

### Smoothness and diffeomorphisms

There is no manifold structure on complex structures, here or in Tau Ceti. A
milestone's smoothness conjunct is stated in one of two ways:

- **By formulas on open sets.** A map is given by a formula that is defined
  on a vector space of endomorphisms or bilinear forms (with junk values
  outside the domain). The statement is `ContDiffOn ℝ n` of that formula on an
  open set, for every `n : WithTop ℕ∞`, together with a lemma that identifies
  the formula with the map on the structures. This is how Tau Ceti states
  smoothness of the Cayley chart (`Compatible.contDiff_cayleyEquiv_symm`) and
  of the metric change. It is also what the lemma `Section/Topology.lean`
  of *Symplectic vector bundles* needs: fibre maps on open subsets of total
  spaces.
- **By linear restriction.** The map $J\mapsto-J_0J$ of Lemma 2.5.5 and its
  inverse $P\mapsto J_0P$ are restrictions of linear automorphisms of the
  ambient spaces of endomorphisms and matrices. The milestone states the
  homeomorphism together with these two formulas. This says more than
  "diffeomorphism" does for subsets of vector spaces, so no `ERRATA.md` entry
  is needed.

### Representation of $J_{g,\omega}$

`SymplecticGeometry.metricPolarComplexStructure g ω`, for
`g : innerProducts V` and `ω : TauCeti.SymplecticForm V`, is defined by a
characterization rather than by a choice of coordinates. It is the unique
complex structure that is $g$-orthogonal and $\omega$-compatible.

Here is the uniqueness argument, which is short. Let $A$ be the operator with
$g(Au,v)=\omega(u,v)$. If $J$ is $g$-orthogonal and preserves $\omega$, then
$J$ commutes with $A$. Then $Q=-JA$ is $g$-self-adjoint, and
$g(Qv,v)=\omega(v,Jv)>0$, so $A=JQ$ is a polar decomposition of $A$. By the
uniqueness of polar decompositions, $J$ is the polar factor of $A$. Existence
is Tau Ceti's `polarComplexStructure` on $(V,g)$, transported along a
$g$-isometry with a Euclidean space.

The characterization makes naturality under every linear isomorphism
immediate, and it identifies the result with Tau Ceti's construction when $g$
is the ambient inner product. The ambient case of the characterization,
`TauCeti.SymplecticForm.polarComplexStructure_eq_iff`, is proved first, in
Tau Ceti's namespace. It is the input for the general case.

### Statements that the bundle part applies fibrewise

*Symplectic vector bundles* gets three explicit formulas, each smooth on an
open set and natural under continuous linear equivalences, so that the
expressions in two trivializations agree:

1. `metricPolarFormula`, the formula for $(g,\omega)\mapsto J_{g,\omega}$, on
   the open set `polarDomain V` of pairs of continuous bilinear forms. The
   formula symmetrizes its first argument and skew-symmetrizes its second
   before applying the construction. So it is defined, and smooth, on a set
   that is open in the space of all pairs of bilinear forms, and not only
   relative to symmetric and alternating forms. On an inner product and a
   symplectic form it equals $J_{g,\omega}$.
2. The Cayley path `TauCeti.cayleyPathFormula b A B`, on the open set
   `SymplecticGeometry.cayleyDomain` of triples $(b,A,B)$ where its two
   denominators are invertible. The `B` with `(b, J₀, B)` in it for all
   $b\in[0,1]$ form the set $U_{J_0}$ of `DESIGN.md`. The domain contains
   $[0,1]\times\{(J_0,J)\}$ for $J_0$ $\omega$-compatible and $J$ $\omega$-tame. The reference structure is a
   variable of the formula, so the bundle part can let it vary with the
   point. Tau Ceti's compatible and tame contractions are this formula at
   $b=1-t$ (`Compatible.toContinuousLinearMap_cayleyContraction`).
3. The homotopies of Proposition 2.5.6 and Corollary 2.5.7. Each is given
   with a lemma that writes it through `metricPolarFormula`,
   `cayleyPathFormula` and continuous (bi)linear operations. Its smoothness
   in the data, and in the time, therefore follows from items 1 and 2 by
   composition.

### Statement of the milestones

Each milestone is one theorem, with the plan's hypotheses and its conclusion.
Where the plan lists several properties, the theorem is their conjunction,
and each part is also a lemma of its own. The plan asks that $V$ be
even-dimensional for the milestone *Complex structures versus symplectic
forms*. The library drops that hypothesis: in odd dimension all the spaces
involved are empty, and the statements still hold.

### Dependencies

The part uses only two things from other parts:

- *Standard model* (`StdSpace`, `stdForm`, `stdComplexStructure`, and the
  matrix dictionary of #8). It is used in condition (3), in Lemma 2.5.5 and in
  the compact-subgroup theorem.
- The Lagrangian extension lemma of *Symplectic vector spaces*
  (`LinearAlgebra/Symplectic/Subspace.lean`, #25), used only in the
  implication from (4) to (1). An isotropic plane containing $v$ and $w$ is
  extended to a Lagrangian subspace.

The part uses nothing from *Linear complex structures*. The same pull
request updates `DESIGN.md` to match: part 9 builds on *Standard model* and
*Symplectic vector spaces*.

## Files, definitions and results

Namespaces follow `AGENTS.md`. A result about Tau Ceti's notions goes in
their namespace, so that it can move there unchanged: `Compatible` lemmas in
`TauCeti.SymplecticForm`, and the instance on `SymplecticForm V`. New notions
go in `SymplecticGeometry`. The statements below are written with
`variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
{ω : TauCeti.SymplecticForm V} {J : TauCeti.AlmostComplexStructure V}`, and
with the normed variables of *Topologies* in the topological files.

### `LinearAlgebra/Symplectic/Compatible.lean`

These are the characterizations (Proposition 2.5.4 and Exercise 2.5.3), in
`TauCeti.SymplecticForm`.

- `compatible_iff_exists_isDarbouxBasis : ω.Compatible J ↔ ∃ (n : ℕ)
  (b : Module.Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧ ∀ k,
  b (k, 1) = J (b (k, 0))`. This is condition (2), with $v_k=$ `b (k, 0)` and
  $Jv_k=$ `b (k, 1)`, in Tau Ceti's normalization, which is the book's. The
  forward direction is `exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`
  with an empty family. The converse checks invariance and positivity on the
  basis.
- `invariant_of_isSymm_associatedBilinForm : (ω.associatedBilinForm J).IsSymm →
  ω.Invariant J`. Symmetry of $g_J$ already forces invariance: put $Jw$ for
  $w$. With Tau Ceti's `Invariant.associatedBilinForm_isSymm` this gives
  `invariant_iff_isSymm_associatedBilinForm`.
- `compatible_iff_associatedBilinForm : ω.Compatible J ↔
  (ω.associatedBilinForm J).IsSymm ∧
  (ω.associatedBilinForm J).toQuadraticMap.PosDef ∧
  ∀ v w, ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w`.
  This is the first condition of the exercise.
- `invariant_iff_complexAssociatedForm_conj_symm : ω.Invariant J ↔ ∀ v w,
  starRingEnd ℂ (ω.complexAssociatedForm J w v) = ω.complexAssociatedForm J v w`.
- `compatible_iff_exists_innerProductCore : ω.Compatible J ↔
  ∃ c : (letI := J.complexModule; InnerProductSpace.Core ℂ V), ∀ v w,
  c.inner v w = ω.complexAssociatedForm J v w`. This is the second condition
  of the exercise, and the converse of `Compatible.hermitianCore`. Conjugate
  symmetry gives invariance, and positivity of `re (H v v) = ω v (J v)`
  gives tameness.
- `compatible_iff_exists_isSymplectomorphism_stdForm {ι : Type*} [Fintype ι]
  [DecidableEq ι] (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
  ω.Compatible J ↔ ∃ Ψ : StdSpace ι ≃ₗ[ℝ] V,
  IsSymplectomorphism (stdForm ι) ω Ψ ∧
  IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap`. This is
  condition (3). The direction from (2) sends `b (k, 0)` to the basis vector
  of `StdSpace ι` at `inl`, and `b (k, 1)` to the one at `inr`, after a
  bijection `Fin n ≃ ι`. Then $\omega_0(e_{\mathrm{inl}\,i},e_{\mathrm{inr}\,j})=\delta_{ij}$
  and $J_0e_{\mathrm{inl}\,i}=e_{\mathrm{inr}\,i}$, by `stdForm_apply` and
  `stdComplexStructure_x`/`_y`. The converse is `Compatible.transport` of
  `stdForm_compatible`.
- `compatible_iff_tames_and_isLagrangian_map : ω.Compatible J ↔ ω.Tames J ∧
  ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap)`.
  This is condition (4). Forward, an invariant $J$ is a symplectomorphism,
  so it maps Lagrangian subspaces to Lagrangian subspaces. Backward, if
  $\omega(v,w)=0$, extend the isotropic span of $v,w$ to a Lagrangian $L$
  (#25). Then $\omega(Jv,Jw)=0$. So for each $v$ the functional
  $\omega(Jv,J\cdot)$ vanishes on the kernel of $\omega(v,\cdot)$, hence is
  $\lambda_v\,\omega(v,\cdot)$. Comparing $v$, $w$ and $v+w$ shows that
  $\lambda$ is constant. Evaluating at $(v,Jv)$ gives $\lambda=1$, by
  tameness. Dimension zero is trivial.
- **Milestone** `compatible_tfae (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
  List.TFAE [ω.Compatible J, (2), (3), (4), (g_J condition), (H condition)]`,
  with the six conditions written as in the lemmas above. Its docstring ends
  with "Milestone: *Characterizations of compatible complex structures*."

### `Topology/Algebra/Module/InnerProducts.lean`

This is $\mathrm{Met}(V)$, in `SymplecticGeometry`.

- `innerProducts (V) : Set (V →L[ℝ] V →L[ℝ] ℝ) :=
  {g | (∀ v w, g v w = g w v) ∧ ∀ v, v ≠ 0 → 0 < g v v}`, with
  `mem_innerProducts` (`@[simp]`).
- `convex_innerProducts` (Tau Ceti's `convex_setOfPred_symm_pos`), and
  `innerProducts_eq_inter`, which writes the set as the intersection of the
  closed subspace of symmetric forms with the open set of
  `isOpen_setOf_forall_bilinear_apply_self_pos`. So it is open in the
  symmetric forms.
- `innerProducts_nonempty` (pull back a Euclidean inner product along
  `ContinuousLinearEquiv.ofFinrankEq`), and the instances `Nonempty` and
  `ContractibleSpace (innerProducts V)` (Mathlib's `Convex.contractibleSpace`).
- `innerProducts.pullback (e : V ≃L[ℝ] W) : innerProducts W ≃ₜ innerProducts V`,
  `g ↦ g.bilinearComp e e`, with `@[simp]` `pullback_apply`, `pullback_symm`,
  `pullback_trans`. This is the action of $\mathrm{GL}(V)$ that equivariance
  uses.
- `TauCeti.SymplecticForm.Compatible.associatedBilinForm_mem_innerProducts (h :
  ω.Compatible J) : (ω.associatedBilinForm J).toContinuousBilinearMap ∈
  innerProducts V`.

### `Topology/Algebra/Module/SymplecticForms.lean`

This is $\Omega(V)$, in `TauCeti.SymplecticForm`.

- `instance : TopologicalSpace (SymplecticForm V)`, induced by
  `toContinuousBilinearMap ω := ω.toBilinForm.toContinuousBilinearMap`, with
  `isEmbedding_toContinuousBilinearMap` and `continuous_iff`.
- `range_toContinuousBilinearMap`: the alternating forms that are
  nondegenerate. With `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm`,
  this makes the range open in the alternating forms.
- `ofContinuousBilinearMap` (an alternating nondegenerate continuous form as
  a `SymplecticForm`), with `toContinuousBilinearMap_ofContinuousBilinearMap`.
- `continuous_transport (e : V ≃L[ℝ] W)`: `ω ↦ ω.transport e.toLinearEquiv`
  is continuous.

### `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/Basic.lean`

This is $J_{g,\omega}$. `DESIGN.md` names a single file,
`Analysis/InnerProductSpace/Symplectic/PolarComplexStructure.lean`. The part
splits it into a folder from the start, because the smooth formula is a topic
of its own.

- `TauCeti.SymplecticForm.polarComplexStructure_eq_iff` (when `V` is an
  `InnerProductSpace ℝ V` of finite dimension):
  `ω.polarComplexStructure = J ↔ (∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫) ∧ ω.Compatible J`.
  The proof is the polar-decomposition argument of *Decisions*.
- `SymplecticGeometry.metricPolarComplexStructure (g : innerProducts V)
  (ω : SymplecticForm V) : AlmostComplexStructure V`, on a finite-dimensional
  normed `V`. It is defined from the unique existence statement
  `existsUnique_metricPolarComplexStructure`.
- `metricPolarComplexStructure_eq_iff : metricPolarComplexStructure g ω = J ↔
  (∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (J u) (J v) = g u v) ∧ ω.Compatible J`, the
  characterizing lemma.
- `compatible_metricPolarComplexStructure`, and
  `metricPolarComplexStructure_apply_apply` (orthogonality for `g`). These
  are the first bullet of Proposition 2.5.6.
- `metricPolarComplexStructure_associatedBilinForm (h : ω.Compatible J) :
  metricPolarComplexStructure ⟨_, h.associatedBilinForm_mem_innerProducts⟩ ω = J`.
  This is the second bullet.
- `metricPolarComplexStructure_transport (e : V ≃L[ℝ] W) :
  metricPolarComplexStructure (innerProducts.pullback e.symm g)
  (ω.transport e.toLinearEquiv) =
  (metricPolarComplexStructure g ω).transport e.toLinearEquiv`. This is
  $\mathrm{GL}$-equivariance, and more generally naturality.
- `metricPolarComplexStructure_inner` (for `V` an inner product space and
  `g` its inner product): it is `ω.polarComplexStructure`.

### `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/Smooth.lean`

- `SymplecticGeometry.polarDomain (V) : Set ((V →L[ℝ] V →L[ℝ] ℝ) ×
  (V →L[ℝ] V →L[ℝ] ℝ))`: the pairs whose first entry is positive on nonzero
  vectors and whose second entry has a nondegenerate skew part
  $\tfrac12(s-s^{\mathrm{flip}})$. It comes with `isOpen_polarDomain`.
- `metricPolarFormula (g s : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V`. On
  `polarDomain V` it is the endomorphism of `metricPolarComplexStructure`
  for the symmetric part of `g` and the skew part of `s`, and outside the
  domain it is `0`. It comes with `metricPolarFormula_def`.
- `metricPolarFormula_eq (g : innerProducts V) (ω : SymplecticForm V) :
  metricPolarFormula g ω.toContinuousBilinearMap =
  LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap`.
- `contDiffOn_metricPolarFormula {n : WithTop ℕ∞} :
  ContDiffOn ℝ n (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain V)`. The
  proof transports to `EuclideanSpace ℝ (Fin (finrank ℝ V))` and uses
  `conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`,
  `contDiffOn_metricChangeTransport`, `contDiffOn_sqrt` and the smoothness of
  `Ring.inverse` at units.
- `metricPolarFormula_conj (e : V ≃L[ℝ] W)`: transporting both forms along `e`
  conjugates the formula by `e`. This is naturality on the whole domain.
- `continuous_metricPolarComplexStructure`: jointly continuous on
  `innerProducts V × SymplecticForm V`.

### `Analysis/Normed/Ring/Cayley.lean`

The domain of the Cayley path, in a complete normed `ℝ`-algebra `R`, in
`SymplecticGeometry`.

- `cayleyDomain (R) : Set (ℝ × R × R) := {q | IsUnit (1 - q.2.1 * q.2.2) ∧
  IsUnit (1 - q.1 • cayleyFormula q.2.1 q.2.2)}`, with `isOpen_cayleyDomain`
  and `contDiffOn_cayleyPathFormula` (from `contDiffAt_cayleyPathFormula`).
- `isOpen_setOf_forall_Icc_mem_cayleyDomain`: the pairs $(A,B)$ with
  $(b,A,B)$ in the domain for every $b\in[0,1]$ form an open set, by
  compactness of $[0,1]$. Its slice at $A=J_0$ is the set $U_{J_0}$ of
  `DESIGN.md`.
- `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain (h₀ : ω.Compatible J₀)
  (h : ω.Tames J) (hb : |b| ≤ 1)`: the triple of `b` and the endomorphisms of
  `J₀` and `J` lies in the domain. This combines
  `Tames.isUnit_one_sub_mul_of_toLinearMap` and
  `Compatible.isUnit_one_sub_smul_cayleyFormula`.

### `Topology/ComplexStructure/Compatible/Matrix.lean`

This is Lemma 2.5.5, on `StdSpace ι`, in `SymplecticGeometry`.

- `compatibleEquivPosDefSymplectic ι : {J : AlmostComplexStructure (StdSpace ι)
  // (stdForm ι).Compatible J} ≃ₜ {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ //
  P ∈ Matrix.symplecticGroup ι ℝ ∧ P.PosDef}`, with the `@[simp]` lemmas
  `coe_compatibleEquivPosDefSymplectic_apply`, which is
  `-(Matrix.J ι ℝ) * Matrix.toEuclideanLin.symm J.toLinearMap`, and
  `compatibleEquivPosDefSymplectic_symm_apply_toLinearMap`, which is
  `Matrix.toEuclideanLin (Matrix.J ι ℝ * P)`.
- The underlying facts, each a lemma. Since
  $\omega_0(z,w)=\langle J_0z,w\rangle$ (`stdForm_apply_eq_inner`), the
  matrix $P=-J_0J$ is the Gram matrix of $g_J$. So $P$ is symmetric if and
  only if $J$ is $\omega_0$-invariant (by `invariant_iff_isSymm_associatedBilinForm`),
  and positive definite if and only if $J$ is tame. A symmetric $P$ is
  symplectic if and only if $(J_0P)^2=-1$. The matrix dictionary of #8
  translates between matrices and maps.

### `Topology/ComplexStructure/Compatible/Metric.lean`

This is Corollary 2.5.7, in `SymplecticGeometry`.

- `compatibleMetric ω : C({J // ω.Compatible J}, innerProducts V)`, the map
  $J\mapsto g_J$. It is continuous by Tau Ceti's
  `toContinuousBilinearMap_associatedBilinForm`.
- `metricHomotopyEquiv ω : ContinuousMap.HomotopyEquiv {J // ω.Compatible J}
  (innerProducts V)`. Its forward map is `compatibleMetric ω`, and its
  inverse is `g ↦ metricPolarComplexStructure g ω`. One composite is the
  identity, by `metricPolarComplexStructure_associatedBilinForm`. The other
  is homotopic to the identity by the straight-line homotopy
  `metricStraightHomotopy`, $(t,g)\mapsto(1-t)\,g_{J_{g,\omega}}+t\,g$,
  inside the convex set. Its value is a stated formula, so the bundle part
  can read it off.
- **Milestone** `compatible_contractible_and_homotopyEquiv`. It states three
  things. First, `Nonempty {J // ω.Compatible J} ∧ ContractibleSpace
  {J // ω.Compatible J}` (Tau Ceti's `exists_compatible` and instance).
  Second, there is a homotopy equivalence with `innerProducts V` whose maps
  are $J\mapsto g_J$ and $g\mapsto J_{g,\omega}$. Third, for every finite
  type `ι` with decidable equality, there is a homeomorphism of the
  `(stdForm ι)`-compatible structures with the symmetric positive definite
  symplectic matrices, given in both directions by the two linear formulas
  above. Its docstring ends with "Milestone: *Contractibility of the space of
  compatible complex structures*."

### `Topology/ComplexStructure/Compatible/SymplecticForms.lean`

This is Proposition 2.5.6, for a fixed `g : innerProducts V`, in
`SymplecticGeometry`.

- `metricSymplecticForm g J : SymplecticForm V`, the form
  $\omega_{g,J}=\tfrac12\big(g(J\cdot,\cdot)-g(\cdot,J\cdot)\big)$, built
  with Tau Ceti's `SymplecticForm.ofTames`, since
  $\omega_{g,J}(v,Jv)=\tfrac12\big(g(Jv,Jv)+g(v,v)\big)>0$. It comes with
  `metricSymplecticForm_apply` (`@[simp]`), `tames_metricSymplecticForm`,
  `metricSymplecticForm_eq_of_apply_apply` (it is $g(J\cdot,\cdot)$ for
  $g$-orthogonal $J$) and `continuous_metricSymplecticForm`.
- `metricComplexStructures g : Set (AlmostComplexStructure V)`
  ($\mathcal{J}(V,g)$, the $g$-orthogonal structures) and
  `metricSymplecticForms g : Set (SymplecticForm V)` ($\Omega(V,g)$, the forms
  $g(J\cdot,\cdot)$ for $J\in\mathcal{J}(V,g)$), with their membership
  lemmas.
- `polarHomotopyEquiv g : ContinuousMap.HomotopyEquiv (SymplecticForm V)
  (AlmostComplexStructure V)`, with maps $\omega\mapsto J_{g,\omega}$ and
  $J\mapsto\omega_{g,J}$. There are two homotopies:
  - On forms, the straight line from $\omega$ to $\omega_{g,J_{g,\omega}}$.
    Both forms are tamed by $J_{g,\omega}$, and taming is convex in the form,
    so the line stays nondegenerate.
  - On complex structures, the Cayley path relative to
    $J_{g,\omega_{g,J}}$ (compatible with $\omega_{g,J}$) towards $J$ (tame
    for $\omega_{g,J}$). Its formula is
    `cayleyPathFormula b (metricPolarFormula g (metricSymplecticForm g J)) J`,
    which lies in `cayleyDomain` by `Compatible.mem_cayleyDomain`.
- `metricComplexStructuresHomotopyEquiv g` and
  `metricSymplecticFormsHomotopyEquiv g`, whose forward maps are the
  inclusions. Their inverses are $J\mapsto J_{g,\omega_{g,J}}$ and
  $\omega\mapsto\omega_{g,J_{g,\omega}}$, and the homotopies are the two
  above. On the subsets, the inverses fix every point, by
  `metricPolarComplexStructure_eq_iff`.
- **Milestone** `metricPolarComplexStructure_properties`, the conjunction of
  the following:
  - smoothness: `contDiffOn_metricPolarFormula` and `metricPolarFormula_eq`;
  - naturality: `metricPolarComplexStructure_transport`;
  - compatibility with both $\omega$ and $g$;
  - the value at $g=g_J$;
  - the existence of the three homotopy equivalences, with the stated maps.

  No parity hypothesis on `finrank ℝ V` is needed, as said above. Its
  docstring ends with "Milestone: *Complex structures versus symplectic
  forms*."

### `Topology/ComplexStructure/Compatible/Tame.lean`

This is Proposition 2.5.13, beyond what Tau Ceti has, in `SymplecticGeometry`.

- `compatibleTamesHomotopyEquiv (h₀ : ω.Compatible J₀) :
  ContinuousMap.HomotopyEquiv {J // ω.Compatible J} {J // ω.Tames J}`. Its
  forward map is the inclusion and its inverse is the constant at $J_0$. The
  homotopies are Tau Ceti's `Compatible.compatibleCayleyContraction` and
  `Compatible.cayleyContraction`, whose formula is `cayleyPathFormula` by
  `toContinuousLinearMap_cayleyContraction`.
- **Milestone** `contractibleSpace_tames_and_homotopyEquiv`, which states
  `ContractibleSpace {J // ω.Tames J}` (Tau Ceti's instance) and that the
  inclusion is the forward map of a homotopy equivalence. Its docstring ends
  with "Milestone: *Contractibility of the space of tame complex structures*."

### `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`

This is Proposition 2.5.8, in `TauCeti.GLSymplectic`, since it is about Tau
Ceti's group.

- **Milestone** `exists_map_conj_le_range_ofUnitary {K : Subgroup
  (GLSymplectic ι ℝ)} (hK : IsCompact (K : Set (GLSymplectic ι ℝ))) :
  ∃ P : GLSymplectic ι ℝ, K.map (MulAut.conj P⁻¹).toMonoidHom ≤
  (ofUnitary (n := ι)).range`. Its docstring ends with "Milestone: *Compact
  subgroups of the symplectic group*."
- The proof runs as follows:
  1. $K$ acts continuously on `StdSpace ι` by `Matrix.toEuclideanLin`,
     preserving `stdForm ι` (matrix dictionary, #8).
  2. `exists_compatible_forall_isComplexLinearMap` gives a compatible $J$
     that commutes with $K$.
  3. Condition (3) gives a symplectomorphism $\Psi$ with $\Psi J_0=J\Psi$,
     whose matrix $P$ is symplectic.
  4. Each $P^{-1}AP$ is then symplectic and commutes with `Matrix.J`, so it
     lies in the realified $\mathrm{U}(n)$, by
     `Matrix.symplecticGroup_inf_centralizer_J`. Its membership in the range
     of `ofUnitary` follows from `coe_ofUnitary`.

## Building issues

They are listed in an order in which each issue's blockers come before it.
Each is a few hundred lines. External blockers are given by issue number.

1. **Compatible structures: symplectic bases, $g_J$ and the Hermitian form.**
   The first part of `LinearAlgebra/Symplectic/Compatible.lean`:
   `compatible_iff_exists_isDarbouxBasis`,
   `invariant_of_isSymm_associatedBilinForm`,
   `invariant_iff_isSymm_associatedBilinForm`,
   `compatible_iff_associatedBilinForm`,
   `invariant_iff_complexAssociatedForm_conj_symm`,
   `compatible_iff_exists_innerProductCore`. Blockers: none.
2. **Compatible structures: the standard model, Lagrangians, and the
   characterization milestone.** The rest of the file:
   `compatible_iff_exists_isSymplectomorphism_stdForm`,
   `compatible_iff_tames_and_isLagrangian_map`, `compatible_tfae`.
   Blockers: 1, #7, #25.
3. **Inner products and symplectic forms as topological spaces.**
   `Topology/Algebra/Module/InnerProducts.lean` and
   `Topology/Algebra/Module/SymplecticForms.lean`. Blockers: none.
4. **$J_{g,\omega}$ for an arbitrary inner product.**
   `PolarComplexStructure/Basic.lean`. Blockers: 3.
5. **Smoothness of $J_{g,\omega}$.** `PolarComplexStructure/Smooth.lean`.
   Blockers: 4.
6. **The Cayley domain and the tame milestone.**
   `Analysis/Normed/Ring/Cayley.lean` and
   `Topology/ComplexStructure/Compatible/Tame.lean`. Blockers: none.
7. **Compatible structures on $\mathbb{R}^{2n}$ as positive symplectic
   matrices.** `Topology/ComplexStructure/Compatible/Matrix.lean`. Blockers:
   1, #7, #8.
8. **The homotopy equivalence with $\mathrm{Met}(V)$ and the contractibility
   milestone.** `Topology/ComplexStructure/Compatible/Metric.lean`. Blockers:
   5, 7.
9. **Complex structures versus symplectic forms.**
   `Topology/ComplexStructure/Compatible/SymplecticForms.lean`. Blockers: 5,
   6.
10. **Compact subgroups of the symplectic group.**
    `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`. Blockers:
    2, #8.

Issues 1, 3 and 6 can start at once. *Symplectic vector bundles* needs 5, 6,
8 and 9.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.5.
