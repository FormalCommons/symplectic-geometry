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
- The polar complex structure as $A\,(\sqrt{-A^2})^{-1}$, for the operator $A$
  of $\omega$ through the ambient inner product,
  `toContinuousLinearMap_polarComplexStructure` (same file).
- The metric-change transport `ContinuousLinearMap.metricChangeTransport` of a
  continuous bilinear form, with
  `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff`
  and its smoothness, `contDiffOn_metricChangeTransport`,
  `contDiffOn_sqrt_continuousLinearMapOfBilin`
  (`Analysis/InnerProductSpace/Positive/MetricChange/`), and the smoothness of the
  square root, `ContinuousLinearMap.contDiffOn_sqrt`
  (`Analysis/InnerProductSpace/Positive/FunctionalCalculus.lean`).
- The symplectic form $\langle J\cdot,\cdot\rangle$ of an orthogonal complex
  structure on an inner product space,
  `TauCeti.AlmostComplexStructure.symplecticForm`
  (`Geometry/Symplectic/CompatibleMetric.lean`).
- The coordinate map of a Darboux basis, `Module.Basis.darbouxBasisEquiv`,
  with `IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv` and
  `darbouxBasisEquiv_apply_zero`/`_one`
  (`Geometry/Symplectic/Darboux/EuclideanBasis.lean`).
- The uniqueness of the polar factor, `LinearMap.eq_polarFactor_iff`
  (`Analysis/InnerProductSpace/Polar/Finite.lean`).
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
- The unitary group inside the symplectic group, and the maximal compact
  subgroups: `TauCeti.GLSymplectic.inf_unitarySubgroup` and
  `TauCeti.GLSymplectic.inf_range_realify`
  (`LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Unitary.lean`),
  `TauCeti.GLSymplectic.maximal_isCompact_unitarySubgroup`
  (`.../Symplectic/MaximalCompact.lean`), and the conjugation statements
  `Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup` and
  `Matrix.SpecialLinearGroup.exists_conj_smul_le_comap_unitarySubgroup`, whose
  shape the compact-subgroup milestone follows.

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
  Mathlib's `LinearMap.toContinuousBilinearMap`
  (`Topology/Algebra/Module/FiniteDimensionBilinear.lean`).
- **The inner products** $\mathrm{Met}(V)$ are the set
  `SymplecticGeometry.innerProducts V` of continuous bilinear forms that are
  symmetric and positive on nonzero vectors. This is exactly the set of
  `TauCeti.convex_setOfPred_symm_pos`. It is a type through its coercion to a
  subtype.
- **The symplectic forms** $\Omega(V)$ are `TauCeti.SymplecticForm V`, with
  the topology induced by the map `ω ↦ ω.toBilinForm.toContinuousBilinearMap`,
  written inline with no named wrapper. Tau Ceti already states its lemmas
  in this form (`isInvertible_toContinuousBilinearMap`,
  `toContinuousBilinearMap_associatedBilinForm`). The instance lives in the
  namespace `TauCeti.SymplecticForm` and is built as Tau Ceti builds the one
  on `AlmostComplexStructure V`.

All topological statements assume `[NormedAddCommGroup V] [NormedSpace ℝ V]
[FiniteDimensional ℝ V]`, as Tau Ceti's topology does. The definition and the
characterization of $J_{g,\omega}$ need no inner product on `V`. The explicit
formula `metricPolarFormula` is Tau Ceti's coordinate expression. That
expression uses the Riesz map `continuousLinearMapOfBilin` of an inner product
space, so the formula and its smoothness are stated on a space `W` with
`[InnerProductSpace ℝ W]`. The inner product of `W` is only an auxiliary
choice: on the domain the formula equals $J_{g,\omega}$, which does not depend
on it. The general API and the milestones never ask for an
`InnerProductSpace ℝ V` instance on the space `V` they are about. Such an
instance must induce the norm that `V` already carries, so it would exclude
every space whose norm does not come from an inner product. They reach the
formula through a linear isomorphism `V ≃L[ℝ] W` instead. The only
exceptions are the lemmas that compare the general construction with Tau
Ceti's ambient one, and so are about an inner product space by their nature:
`innerSL_mem_innerProducts`, `polarComplexStructure_eq_iff`,
`metricPolarComplexStructure_innerSL` and `metricSymplecticForm_innerSL`.

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
$g(Qv,v)=\omega(v,Jv)>0$, so $A=JQ$ is a polar decomposition of $A$. Tau
Ceti's `LinearMap.eq_polarFactor_iff`, applied on $(V,g)$, says the polar
factor is unique, so $J$ is the polar factor of $A$. Existence
is Tau Ceti's `polarComplexStructure` on $(V,g)$, transported along a
$g$-isometry with a Euclidean space.

The same argument shows that this structure is the formula of the milestone
*Complex structures versus symplectic forms*. Take $A$ as above and let $Q$ be
the $g$-self-adjoint, $g$-positive operator with $Q^2=-A^2$. Then the
structure equals $Q^{-1}A$. The design states this as the lemma
`metricPolarComplexStructure_eq_inverse_mul` and makes it a conjunct of the
milestone. The milestone is then about the plan's $J_{g,\omega}$ itself, and
not only about some structure with the same properties. The lemma gives the
square root by its defining properties, since `V` has no inner product of its
own for `CFC.sqrt` to use. When $g$ is the ambient inner product of an inner
product space, Tau Ceti's `toContinuousLinearMap_polarComplexStructure`
writes the ambient structure as `A * Ring.inverse (CFC.sqrt (-(A * A)))`,
with the factors in the opposite order. The comparison with Tau Ceti does
not go through this formula: `metricPolarComplexStructure_innerSL` follows
from the characterization, since Tau Ceti's polar structure is orthogonal
for the inner product and compatible with the form. So no commutation of $Q$
with $A$ is planned. Where a statement needs it for `CFC.sqrt`, Mathlib's
`Commute.cfcₙ_nnreal` gives it directly.

The characterization makes naturality under every linear isomorphism
immediate, and it identifies the result with Tau Ceti's construction when $g$
is the ambient inner product. The ambient case of the characterization,
`TauCeti.SymplecticForm.polarComplexStructure_eq_iff`, is proved first, in
Tau Ceti's namespace. It is the input for the general case.

### Statements that the bundle part applies fibrewise

*Symplectic vector bundles* gets two explicit formulas, each smooth on an
open set and natural under continuous linear equivalences, so that the
expressions in two trivializations agree:

1. `TauCeti.metricPolarFormula`, the formula for $(g,\omega)\mapsto J_{g,\omega}$, on
   the open set `TauCeti.polarDomain W` of pairs of continuous bilinear forms. It is
   Tau Ceti's coordinate expression for the polar structure, the right-hand
   side of `conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`,
   applied to the symmetric part of its first argument and the skew part of
   its second. Here `W` is an auxiliary inner product space. So it is
   defined, and smooth, on a set
   that is open in the space of all pairs of bilinear forms, and not only
   relative to symmetric and alternating forms. Every inner product and
   symplectic form lie in that set (`mem_polarDomain`), and there the
   formula equals $J_{g,\omega}$. For a space `V` with no inner product, a
   pair on `V` is carried to `W` along any `e : V ≃L[ℝ] W`, and the value
   there is $J_{g,\omega}$ conjugated by `e`.
2. The Cayley path `TauCeti.cayleyPathFormula b A B`, on the open set
   `TauCeti.cayleyDomain` of triples $(b,A,B)$ where its two
   denominators are invertible. The `B` with `(b, J₀, B)` in it for all
   $b\in[0,1]$ form the set $U_{J_0}$ of `DESIGN.md`. The domain contains
   $[0,1]\times\{(J_0,J)\}$ for $J_0$ $\omega$-compatible and $J$ $\omega$-tame. The reference structure is a
   variable of the formula, so the bundle part can let it vary with the
   point. Tau Ceti's compatible and tame contractions are this formula at
   $b=1-t$ (`Compatible.toContinuousLinearMap_cayleyContraction`).

The homotopies of Proposition 2.5.6 and Corollary 2.5.7 get no such
formula lemma: no other part uses them, and their own API is the `@[simp]`
lemma that gives each one's value.

### Statement of the milestones

Each milestone is one theorem, with the plan's hypotheses and its conclusion.
Where the plan lists several properties, the theorem is their conjunction,
and each part is also a lemma of its own. The plan asks that $V$ be
even-dimensional for the milestone *Complex structures versus symplectic
forms*. The library drops that hypothesis: in odd dimension all the spaces
involved are empty, and the statements still hold.

### Dependencies

The part uses only two things from other parts:

- *Standard model* (`StdSpace`, `stdForm`, `stdComplexStructure`, the
  comparison with Tau Ceti's product model, and the matrix dictionary of #8).
  It is used in condition (3), in Lemma 2.5.5 and in the compact-subgroup
  theorem.
- The Lagrangian extension lemma of *Symplectic vector spaces*
  (`IsIsotropic.exists_le_isLagrangian` in `LinearAlgebra/Symplectic/Subspace.lean`), used only in the
  implication from (4) to (1). An isotropic plane containing $v$ and $w$ is
  extended to a Lagrangian subspace.

The part uses nothing from *Linear complex structures*. The same pull
request updates `DESIGN.md` to match: part 9 builds on *Standard model* and
*Symplectic vector spaces*.

## Files, definitions and results

Namespaces follow `AGENTS.md`. A declaration that mentions only Tau Ceti's
notions goes in their namespace, so that it can move there unchanged. That
covers the `Compatible` lemmas and the instance on `SymplecticForm V` (in
`TauCeti.SymplecticForm`), the Cayley domain and the polar formula
`metricPolarFormula` with its domain (in `TauCeti`), and the tame
homotopy equivalence (in `TauCeti.SymplecticForm`). Declarations that involve
the library's own notions (`innerProducts`, `StdSpace`,
`metricPolarComplexStructure`) go in `SymplecticGeometry`. The statements
below are written with `variable {V : Type*} [AddCommGroup V] [Module ℝ V]
{ω : TauCeti.SymplecticForm V} {J : TauCeti.AlmostComplexStructure V}`, and
with the normed variables of *Topologies* in the topological files. Only the
statements that need it get `[FiniteDimensional ℝ V]`.

### Departures from the file list of `DESIGN.md`

The file list of part 9 in the overview came before this design. This pull
request updates it to the files below. Each change, with its reason:

- **`Topology/ComplexStructure/Compatible.lean` becomes a folder**,
  `Compatible/{Matrix,Metric,SymplecticForms,Tame}.lean`. The overview put
  four topics in that one file: the matrix model of Lemma 2.5.5, the homotopy
  equivalence with $\mathrm{Met}(V)$, the one between forms and complex
  structures, and the tame inclusion. Each is a few hundred lines and has a
  building issue of its own, and `AGENTS.md` asks for one file per topic.
- **`PolarComplexStructure.lean` becomes a folder**, `Basic.lean` and
  `Smooth.lean`. The explicit formula and its smoothness are a topic of their
  own, with their own building issue. They also need an inner product space,
  and the definition does not.
- **New `Topology/Algebra/Module/SymplecticForms.lean`.** The homotopy
  equivalence between forms and complex structures needs a topology on
  `SymplecticForm V`. Neither Tau Ceti nor the overview gives one. It is a
  topic parallel to `InnerProducts.lean`.
- **New `Geometry/Symplectic/Cayley/Domain.lean`.** The open set where the
  Cayley path is smooth is used by two files of this part and by *Symplectic
  vector bundles*. It involves only Tau Ceti's `cayleyPathFormula`, so it goes
  in the folder of Tau Ceti's `Cayley/Smooth.lean`, which it extends, and can
  move there unchanged.
- **Lemma 2.5.5 without `Compatible.cayleyEquiv`.** The overview suggested
  that equivalence. It maps the *tame* structures onto Tau Ceti's Cayley ball.
  It does not map the compatible structures onto the positive symplectic
  matrices, so it does not give $J\mapsto-J_0J$. That map and its inverse
  $P\mapsto J_0P$ are restrictions of linear maps, which gives the
  homeomorphism directly.
- **$\mathrm{Met}(V)$ without coordinates.** The overview got convexity from
  `TauCeti.convex_setOfPred_posDef` in coordinates. Tau Ceti's
  `convex_setOfPred_symm_pos` states it for continuous bilinear forms on `V`
  itself, so coordinates are not needed.

### `LinearAlgebra/Symplectic/Compatible.lean`

These are the characterizations (Proposition 2.5.4 and Exercise 2.5.3), in
`TauCeti.SymplecticForm`. The results about $g_J$ and $H$ hold in every
dimension, as their Tau Ceti counterparts such as
`Invariant.associatedBilinForm_isSymm` do, and carry no finite-dimensionality
hypothesis. Only the Darboux-basis, standard-model, Lagrangian and TFAE
statements assume `[FiniteDimensional ℝ V]`.

- `compatible_iff_exists_isDarbouxBasis [FiniteDimensional ℝ V] :
  ω.Compatible J ↔ ∃ (n : ℕ)
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
- `compatible_iff_exists_isSymplectomorphism_stdForm [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]
  [DecidableEq ι] (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
  ω.Compatible J ↔ ∃ Ψ : StdSpace ι ≃ₗ[ℝ] V,
  IsSymplectomorphism (stdForm ι) ω Ψ ∧
  IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap`. This is
  condition (3). The map is not built by hand. From (2), Tau Ceti's
  `b.darbouxBasisEquiv` is a symplectomorphism onto `stdSymplecticForm` on
  `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`
  (`IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv`). It sends
  `b (k, 0)` to `(single k 1, 0)` and `b (k, 1)` to `(0, single k 1)`
  (`darbouxBasisEquiv_apply_zero`/`_one`), so it carries $J$ to
  `AlmostComplexStructure.product`, which maps `(x, 0)` to `(0, x)`. $\Psi$ is
  its inverse, composed with the reindexing along a bijection `Fin n ≃ ι` and
  with `EuclideanSpace.sumEquivProd`, which is a symplectomorphism from
  `stdForm ι` to that product model carrying `stdComplexStructure ι` to
  `AlmostComplexStructure.product` (`isSymplectomorphism_sumEquivProd` and
  `stdComplexStructure_transport_sumEquivProd`). The converse is `Compatible.transport` of
  `stdForm_compatible`.
- `compatible_iff_tames_and_isLagrangian_map [FiniteDimensional ℝ V] :
  ω.Compatible J ↔ ω.Tames J ∧
  ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap)`.
  This is condition (4). Forward, an invariant $J$ is a symplectomorphism,
  so it maps Lagrangian subspaces to Lagrangian subspaces. Backward, if
  $\omega(v,w)=0$, extend the isotropic span of $v,w$ to a Lagrangian $L$
  (`IsIsotropic.exists_le_isLagrangian`). Then $\omega(Jv,Jw)=0$. So for each $v$ the functional
  $\omega(Jv,J\cdot)$ vanishes on the kernel of $\omega(v,\cdot)$, hence is
  $\lambda_v\,\omega(v,\cdot)$. Comparing $v$, $w$ and $v+w$ shows that
  $\lambda$ is constant. Evaluating at $(v,Jv)$ gives $\lambda=1$, by
  tameness. Dimension zero is trivial.
- **Milestone** `compatible_tfae [FiniteDimensional ℝ V] (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
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
- `innerProducts.transport (e : V ≃L[ℝ] W) : innerProducts V ≃ₜ innerProducts W`,
  `g ↦ g.bilinearComp e.symm e.symm`, with `@[simp]` `transport_apply`
  (`transport e g w w' = g (e.symm w) (e.symm w')`), `transport_symm`,
  `transport_trans` and `transport_refl`. It pushes forward along `e`, in the
  same direction as Tau Ceti's `SymplecticForm.transport` and
  `AlmostComplexStructure.transport`, so equivariance statements use one
  direction throughout. (The name `pullback` is avoided: Tau Ceti's
  `SymplecticForm.pullback` is a different operation.) This is the action of
  $\mathrm{GL}(V)$ that equivariance uses.
- `innerSL_mem_innerProducts` (for `V` an inner product space):
  `innerSL ℝ ∈ innerProducts V`, the ambient inner product as an element.
- `TauCeti.SymplecticForm.Compatible.associatedBilinForm_mem_innerProducts (h :
  ω.Compatible J) : (ω.associatedBilinForm J).toContinuousBilinearMap ∈
  innerProducts V`.

### `Topology/Algebra/Module/SymplecticForms.lean`

This is $\Omega(V)$, in `TauCeti.SymplecticForm`.

- `instance : TopologicalSpace (SymplecticForm V)`, induced by
  `fun ω ↦ ω.toBilinForm.toContinuousBilinearMap` (Mathlib's
  `LinearMap.toContinuousBilinearMap`, with no new wrapper), with
  `isEmbedding_toContinuousBilinearMap` and `continuous_iff`, named and
  stated as Tau Ceti's `isEmbedding_toContinuousLinearMap` and
  `continuous_iff` for `AlmostComplexStructure V`.
- `range_toContinuousBilinearMap`: the range of that map is the set of
  alternating forms that are nondegenerate. With
  `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm`, this makes the
  range open in the alternating forms.
- `ofContinuousBilinearMap` (an alternating nondegenerate continuous form as
  a `SymplecticForm`), with `@[simp]` `ofContinuousBilinearMap_apply` and
  `toBilinForm_toContinuousBilinearMap_ofContinuousBilinearMap`.
- `continuous_transport (e : V ≃L[ℝ] W)`: `ω ↦ ω.transport e.toLinearEquiv`
  is continuous.

### `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/Basic.lean`

This is $J_{g,\omega}$, the first file of the folder (see *Departures from
the file list of `DESIGN.md`*).

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
  `apply_metricPolarComplexStructure_apply :
  (g : V →L[ℝ] V →L[ℝ] ℝ) (metricPolarComplexStructure g ω u)
  (metricPolarComplexStructure g ω v) = g u v` (orthogonality for `g`; the
  name leads with the head symbol `g` of the left-hand side, as Tau Ceti's
  `inner_polarComplexStructure_apply_apply` leads with `inner`). These
  are the first bullet of Proposition 2.5.6.
- `metricPolarComplexStructure_eq_inverse_mul {A Q : V →L[ℝ] V}
  (hA : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (A u) v = ω u v)
  (hQs : ∀ u v, (g : V →L[ℝ] V →L[ℝ] ℝ) (Q u) v = g u (Q v))
  (hQp : ∀ v, v ≠ 0 → 0 < (g : V →L[ℝ] V →L[ℝ] ℝ) (Q v) v)
  (hQ : Q * Q = -(A * A)) :
  LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap =
  Ring.inverse Q * A`. This is the plan's definition $J_{g,\omega}=Q^{-1}A$,
  with $Q$ the $g$-positive square root of $-A^2$ given by its defining
  properties. Proof: for $J=J_{g,\omega}$, the operator $-JA$ has the same
  three properties, since $J$ is $g$-orthogonal and commutes with $A$. So it
  is $Q$, by uniqueness of positive square roots (Mathlib's `CFC.sqrt_eq_iff`,
  on $(V,g)$ carried to a Euclidean space). Then $A=JQ$, and $J$ commutes
  with $Q$ (as $Q=-JA$), so $Q^{-1}A=J$. The commutation of $J$ with $A$ is
  a public lemma:
  - `commute_metricPolarComplexStructure` (with the hypothesis `hA` above):
    `Commute (LinearMap.toContinuousLinearMap
    (metricPolarComplexStructure g ω).toLinearMap) A`.
- `metricPolarComplexStructure_associatedBilinForm (h : ω.Compatible J) :
  metricPolarComplexStructure ⟨_, h.associatedBilinForm_mem_innerProducts⟩ ω = J`.
  This is the second bullet.
- `metricPolarComplexStructure_transport (e : V ≃L[ℝ] W) :
  metricPolarComplexStructure (innerProducts.transport e g)
  (ω.transport e.toLinearEquiv) =
  (metricPolarComplexStructure g ω).transport e.toLinearEquiv`. This is
  $\mathrm{GL}$-equivariance, and more generally naturality. Both sides push
  forward along `e`.
- `metricPolarComplexStructure_innerSL` (for `V` an inner product space):
  `metricPolarComplexStructure ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ ω =
  ω.polarComplexStructure`. It follows from
  `metricPolarComplexStructure_eq_iff` with Tau Ceti's
  `inner_polarComplexStructure_apply_apply` and
  `compatible_polarComplexStructure`; no order of factors is involved.

### `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/Smooth.lean`

Here `W` is a finite-dimensional real inner product space, and `s♯` is Tau
Ceti's Riesz map `continuousLinearMapOfBilin s`, as in Tau Ceti's file.

The domain, the formula and their smoothness and naturality mention only
continuous bilinear forms and Tau Ceti's operations on them
(`metricChangeTransport`, `continuousLinearMapOfBilin`, `CFC.sqrt`,
`Ring.inverse`), so by the namespace rule above they go in `TauCeti`, next
to `cayleyPathFormula`. Only `mem_polarDomain`, `metricPolarFormula_eq` and
`continuous_metricPolarComplexStructure`, which involve `innerProducts` and
`metricPolarComplexStructure`, are in `SymplecticGeometry`.

- `TauCeti.polarDomain (W) : Set ((W →L[ℝ] W →L[ℝ] ℝ) ×
  (W →L[ℝ] W →L[ℝ] ℝ))`: the pairs whose first entry is positive on nonzero
  vectors and whose second entry has a nondegenerate skew part
  $\tfrac12(s-s^{\mathrm{flip}})$. It comes with `isOpen_polarDomain` and
  `mem_polarDomain_iff`.
- `SymplecticGeometry.mem_polarDomain (g : innerProducts W)
  (ω : SymplecticForm W) :
  ((g : W →L[ℝ] W →L[ℝ] ℝ), ω.toBilinForm.toContinuousBilinearMap) ∈
  polarDomain W`. Every inner product and symplectic form lie in the domain,
  so the smoothness statement covers all of them. It is in
  `SymplecticGeometry` because it mentions `innerProducts`.
- `TauCeti.metricPolarFormula (g s : W →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] W`,
  defined as Tau Ceti's expression
  `R * (R * s'♯ * R * Ring.inverse (CFC.sqrt (-(R * s'♯ * R * (R * s'♯ * R))))) * CFC.sqrt g'♯`,
  with `R = g'.metricChangeTransport`, for the symmetric part
  $g'=\tfrac12(g+g^{\mathrm{flip}})$ of `g` and the skew part
  $s'=\tfrac12(s-s^{\mathrm{flip}})$ of `s`. No case split is needed:
  `Ring.inverse`, `CFC.sqrt` and `metricChangeTransport` already have junk
  values off the domain. It comes with `metricPolarFormula_def`.
- `SymplecticGeometry.metricPolarFormula_eq (g : innerProducts W)
  (ω : SymplecticForm W) :
  metricPolarFormula g ω.toBilinForm.toContinuousBilinearMap =
  LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap`.
  It is derived from Tau Ceti's
  `conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`, taken
  with `V := W` and `K := g.metricChangeEquiv hg : W ≃L[ℝ] W`, where `hg`,
  positivity of `g♯`, comes from
  `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff`. No
  Euclidean space and no orthonormal basis is built. Tau Ceti gives
  `K.symm = CFC.sqrt g♯` (`coe_metricChangeEquiv_symm`) and
  `⟪√g♯ u, √g♯ v⟫ = g u v` (`inner_sqrt_apply_sqrt_apply`), which is that
  theorem's hypothesis on `g`; its hypothesis on `s` holds for the form
  `ω.transport K.symm.toLinearEquiv`. So the right-hand side of the theorem is
  the polar structure of that form, conjugated by `K`. By
  `metricPolarComplexStructure_innerSL` and
  `metricPolarComplexStructure_transport` along `K`, which carries the ambient
  inner product to `g`, this is $J_{g,\omega}$. The formula is not derived a
  second time.
- `TauCeti.contDiffOn_metricPolarFormula {n : WithTop ℕ∞} :
  ContDiffOn ℝ n (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain W)`. The
  proof composes the symmetrization (a continuous linear map),
  `contDiffOn_metricChangeTransport`, `contDiffOn_sqrt_continuousLinearMapOfBilin`,
  `ContinuousLinearMap.contDiffOn_sqrt` and the smoothness of `Ring.inverse`
  at units. It is the `ContDiffOn` form of the argument of Tau Ceti's private
  `contMDiffAt_metricChangeTransport_mul_mul_sqrt`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`). That lemma is
  private and stated for families on a manifold, so it cannot be used here.
  The library states the pointwise version once, in Tau Ceti's style and
  namespace, so that it can replace the private lemma upstream.
- `TauCeti.metricPolarFormula_conj (e : W ≃L[ℝ] W')`: on `polarDomain W`,
  transporting both forms along `e` conjugates the formula by `e`. The proof
  is `metricPolarFormula_eq` and `metricPolarComplexStructure_transport`, since
  the symmetric and skew parts commute with transport. This is naturality on
  the whole domain, and it does not depend on the inner products of `W` and
  `W'`. Because this proof uses `SymplecticGeometry` lemmas, moving the
  lemma to Tau Ceti would need a direct proof from the formula.
- `SymplecticGeometry.continuous_metricPolarComplexStructure`: jointly
  continuous on `innerProducts V × SymplecticForm V`.

### `Geometry/Symplectic/Cayley/Domain.lean`

The domain of the Cayley path, in a complete normed `ℝ`-algebra `R`. Every
declaration here is about Tau Ceti's `cayleyFormula` and `cayleyPathFormula`
alone, so they go in `TauCeti`, next to `TauCeti.contDiffAt_cayleyPathFormula`,
and `Compatible.mem_cayleyDomain` in `TauCeti.SymplecticForm`.

- `cayleyDomain (R) : Set (ℝ × R × R) := {q | IsUnit (1 - q.2.1 * q.2.2) ∧
  IsUnit (1 - q.1 • cayleyFormula q.2.1 q.2.2)}`, with `@[simp]`
  `mem_cayleyDomain`, `isOpen_cayleyDomain`
  and `contDiffOn_cayleyPathFormula` (from `contDiffAt_cayleyPathFormula`).
- `isOpen_setOf_forall_Icc_mem_cayleyDomain`: the pairs $(A,B)$ with
  $(b,A,B)$ in the domain for every $b\in[0,1]$ form an open set, by
  compactness of $[0,1]$. Its slice at $A=J_0$ is the set $U_{J_0}$ of
  `DESIGN.md`.
- `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain [FiniteDimensional ℝ V]
  (h₀ : ω.Compatible J₀)
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
  $J\mapsto g_J$, with `@[simp]` `coe_compatibleMetric_apply`
  (its value is `(ω.associatedBilinForm J).toContinuousBilinearMap`). It is
  continuous by Tau Ceti's `toContinuousBilinearMap_associatedBilinForm`.
- `metricHomotopyEquiv ω : ContinuousMap.HomotopyEquiv {J // ω.Compatible J}
  (innerProducts V)`. Its forward map is `compatibleMetric ω`, and its
  inverse is `g ↦ metricPolarComplexStructure g ω`. They come with `@[simp]`
  `metricHomotopyEquiv_toFun` and `metricHomotopyEquiv_invFun`, which state
  the two maps. One composite is the identity, by
  `metricPolarComplexStructure_associatedBilinForm`. The other is homotopic to
  the identity by the straight-line homotopy `metricStraightHomotopy ω`,
  $(t,g)\mapsto(1-t)\,g_{J_{g,\omega}}+t\,g$, inside the convex set. Its value
  is the `@[simp]` lemma `coe_metricStraightHomotopy_apply`, which states it
  as an explicit formula.
- **Milestone** `contractibleSpace_compatible_and_homotopyEquiv`, named like
  its sibling `contractibleSpace_tames_and_homotopyEquiv`. It states three
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
- `metricSymplecticForm_innerSL` (for `V` an inner product space and `J`
  orthogonal for its inner product, `hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫`):
  `metricSymplecticForm ⟨innerSL ℝ, innerSL_mem_innerProducts⟩ J =
  J.symplecticForm hJ`. So for the ambient inner product and an orthogonal
  $J$ the form is Tau Ceti's `AlmostComplexStructure.symplecticForm`, as
  `metricPolarComplexStructure_innerSL` does for the complex structure.
- `metricComplexStructures g : Set (AlmostComplexStructure V)`
  ($\mathcal{J}(V,g)$, the $g$-orthogonal structures) and
  `metricSymplecticForms g : Set (SymplecticForm V)` ($\Omega(V,g)$, the forms
  $g(J\cdot,\cdot)$ for $J\in\mathcal{J}(V,g)$), with their `@[simp]`
  membership lemmas `mem_metricComplexStructures` and
  `mem_metricSymplecticForms`.
- `polarHomotopyEquiv g : ContinuousMap.HomotopyEquiv (SymplecticForm V)
  (AlmostComplexStructure V)`, with maps $\omega\mapsto J_{g,\omega}$ and
  $J\mapsto\omega_{g,J}$, stated by the `@[simp]` lemmas
  `polarHomotopyEquiv_toFun` and `polarHomotopyEquiv_invFun`. There are two
  homotopies:
  - On forms, the straight line from $\omega$ to $\omega_{g,J_{g,\omega}}$.
    Both forms are tamed by $J_{g,\omega}$, and taming is convex in the form,
    so the line stays nondegenerate.
  - On complex structures, the Cayley path relative to
    $J_{g,\omega_{g,J}}$ (compatible with $\omega_{g,J}$) towards $J$ (tame
    for $\omega_{g,J}$). Its endomorphism at time $b$ is
    `cayleyPathFormula b A B`, with `A` and `B` the endomorphisms of
    `metricPolarComplexStructure g (metricSymplecticForm g J)` and of `J`.
    The triple lies in `cayleyDomain` by `Compatible.mem_cayleyDomain`.

  Each homotopy comes with a `@[simp]` lemma for its value.
- `metricComplexStructuresHomotopyEquiv g` and
  `metricSymplecticFormsHomotopyEquiv g`, whose forward maps are the
  inclusions. Their inverses are $J\mapsto J_{g,\omega_{g,J}}$ and
  $\omega\mapsto\omega_{g,J_{g,\omega}}$, and the homotopies are the two
  above. Each comes with `@[simp]` `_toFun` and `_invFun` lemmas that state
  these maps. On the subsets, the inverses fix every point, by
  `metricPolarComplexStructure_eq_iff`.
- **Milestone** `metricPolarComplexStructure_eq_inverse_mul_and_homotopyEquiv`,
  named after its first and last conjuncts. Its `V` carries only
  `[NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]`, and no
  inner product: an `InnerProductSpace ℝ V` instance would have to induce the
  norm `V` already has, which fails for a sup norm or a normed bundle fibre.
  It is the conjunction of the following:
  - the plan's definition: `metricPolarComplexStructure_eq_inverse_mul`;
  - smoothness, through an auxiliary space: for every real inner product
    space `W` and every `e : V ≃L[ℝ] W`, `polarDomain W` is open
    (`isOpen_polarDomain`), `contDiffOn_metricPolarFormula` holds on it, and,
    for all `g` and `ω`, the transported pair lies in it (`mem_polarDomain`)
    and the value of
    `metricPolarFormula` at `innerProducts.transport e g` and at the
    continuous bilinear form of `ω.transport e.toLinearEquiv` is
    `e.conjContinuousAlgEquiv` of the endomorphism of
    `metricPolarComplexStructure g ω`. The second part is
    `metricPolarFormula_eq` combined with
    `metricPolarComplexStructure_transport`. Such a pair `(W, e)` always
    exists (for instance `EuclideanSpace ℝ (Fin (finrank ℝ V))`, with `e` from
    Mathlib's `ContinuousLinearEquiv.ofFinrankEq`), so the conjunct is not
    vacuous;
  - naturality: `metricPolarComplexStructure_transport`;
  - compatibility with both $\omega$ and $g$;
  - the value at $g=g_J$;
  - the existence of the three homotopy equivalences, with the stated maps.

  No parity hypothesis on `finrank ℝ V` is needed, as said above. Its
  docstring ends with "Milestone: *Complex structures versus symplectic
  forms*."

### `Topology/ComplexStructure/Compatible/Tame.lean`

This is Proposition 2.5.13, beyond what Tau Ceti has. Its declarations
mention only Tau Ceti's notions, so they go in `TauCeti.SymplecticForm`.

- `Compatible.tamesHomotopyEquiv (h₀ : ω.Compatible J₀) :
  ContinuousMap.HomotopyEquiv {J // ω.Compatible J} {J // ω.Tames J}`. Its
  forward map is the inclusion and its inverse is the constant at $J_0$,
  stated by the `@[simp]` lemmas `Compatible.tamesHomotopyEquiv_toFun` and
  `Compatible.tamesHomotopyEquiv_invFun`. The
  homotopies are Tau Ceti's `Compatible.compatibleCayleyContraction` and
  `Compatible.cayleyContraction`, whose formula is `cayleyPathFormula` by
  `toContinuousLinearMap_cayleyContraction`.
- **Milestone** `contractibleSpace_tames_and_homotopyEquiv`, which states
  `ContractibleSpace {J // ω.Tames J}` (Tau Ceti's instance) and that the
  inclusion is the forward map of a homotopy equivalence. Its docstring ends
  with "Milestone: *Contractibility of the space of tame complex structures*."

### `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`

This is Proposition 2.5.8, in `TauCeti.GLSymplectic`, since it is about Tau
Ceti's group. It takes the shape of Tau Ceti's maximal-compact family
(`Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`,
`Matrix.SpecialLinearGroup.exists_conj_smul_le_comap_unitarySubgroup`), with
the maximal compact subgroup of `GLSymplectic.maximal_isCompact_unitarySubgroup`,
and starts no parallel API.

- **Milestone** `exists_conj_smul_le_unitarySubgroup {K : Subgroup
  (GLSymplectic ι ℝ)} (hK : IsCompact (K : Set (GLSymplectic ι ℝ))) :
  ∃ g : GLSymplectic ι ℝ, MulAut.conj g • K ≤
  (unitarySubgroup (GL (ι ⊕ ι) ℝ)).subgroupOf (GLSymplectic ι ℝ)`. The
  subgroup on the right is the realified $\mathrm{U}(n)$, by Tau Ceti's
  `GLSymplectic.inf_unitarySubgroup`. Its docstring says so, and ends with
  "Milestone: *Compact subgroups of the symplectic group*."
- The proof runs as follows:
  1. $K$ acts continuously on `StdSpace ι` by `Matrix.toEuclideanLin`,
     preserving `stdForm ι` (matrix dictionary, #8).
  2. `exists_compatible_forall_isComplexLinearMap` gives a compatible $J$
     that commutes with $K$.
  3. Condition (3) gives a symplectomorphism $\Psi$ with $\Psi J_0=J\Psi$,
     whose matrix $P$ is symplectic. Take $g=P^{-1}$.
  4. Each $P^{-1}AP$ is then symplectic and commutes with `Matrix.J`, so it
     lies in the range of `realify` (`mem_range_realify_iff`). By
     `GLSymplectic.inf_range_realify` it lies in the realified
     $\mathrm{U}(n)$, and by `GLSymplectic.inf_unitarySubgroup` in
     `unitarySubgroup (GL (ι ⊕ ι) ℝ)`.

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
   Blockers: 1 (#7 and #25 are merged).
3. **Inner products and symplectic forms as topological spaces.**
   `Topology/Algebra/Module/InnerProducts.lean` and
   `Topology/Algebra/Module/SymplecticForms.lean`. Blockers: none.
4. **$J_{g,\omega}$ for an arbitrary inner product.**
   `PolarComplexStructure/Basic.lean`. Blockers: 3.
5. **Smoothness of $J_{g,\omega}$.** `PolarComplexStructure/Smooth.lean`.
   Blockers: 4.
6. **The Cayley domain and the tame milestone.**
   `Geometry/Symplectic/Cayley/Domain.lean` and
   `Topology/ComplexStructure/Compatible/Tame.lean`. Blockers: none.
7. **Compatible structures on $\mathbb{R}^{2n}$ as positive symplectic
   matrices.** `Topology/ComplexStructure/Compatible/Matrix.lean`. Blockers:
   1, #8.
8. **The homotopy equivalence with $\mathrm{Met}(V)$ and the contractibility
   milestone.** `Topology/ComplexStructure/Compatible/Metric.lean`. Blockers:
   5, 7.
9. **Forms versus complex structures for a fixed metric.** The first part of
   `Topology/ComplexStructure/Compatible/SymplecticForms.lean`:
   `metricSymplecticForm` and its API, `metricSymplecticForm_innerSL`, and
   `polarHomotopyEquiv` with its two homotopies. Blockers: 5, 6.
10. **The metric subsets and the milestone *Complex structures versus
    symplectic forms*.** The rest of the file: `metricComplexStructures`,
    `metricSymplecticForms`, their two homotopy equivalences, and the
    milestone. Blockers: 9.
11. **Compact subgroups of the symplectic group.**
    `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`. Blockers:
    2, #8.

Issues 1, 3 and 6 can start at once. *Symplectic vector bundles* needs 4, 5
and 6, and nothing from issues 7 to 11:

- issue 4: `metricPolarComplexStructure_transport` and
  `metricPolarComplexStructure_innerSL`;
- issue 5: `polarDomain` and `metricPolarFormula`, their smoothness and
  naturality, and `metricPolarFormula_eq`;
- issue 6: `cayleyDomain`, `isOpen_setOf_forall_Icc_mem_cayleyDomain` and
  `Compatible.mem_cayleyDomain`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.5.
