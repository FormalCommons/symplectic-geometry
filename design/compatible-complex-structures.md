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
  The symmetric part of a continuous bilinear map,
  `ContinuousLinearMap.symmetrizeBilinear`
  (`Topology/Algebra/Module/SymmetricBilinear/Basic.lean`). Its complement,
  the skew part $\tfrac12(s-s^{\mathrm{flip}})$, is not in Tau Ceti; the
  library adds it next to `toContinuousBilinearMap_toBilinForm`, in its own
  `Topology/Algebra/Module/BilinearForm.lean`, as
  `ContinuousLinearMap.skewSymmetrizeBilinear`, with `_def`, `_apply`,
  `flip_skewSymmetrizeBilinear`, `skewSymmetrizeBilinear_of_flip_eq_neg`,
  `skewSymmetrizeBilinear_eq_self_iff`, `skewSymmetrizeBilinear_eq_zero_iff`,
  `skewSymmetrizeBilinear_of_isAlt`, idempotence
  (`skewSymmetrizeBilinear_skewSymmetrizeBilinear`),
  `skewSymmetrizeBilinear_bilinearComp`,
  `symmetrizeBilinear_add_skewSymmetrizeBilinear`,
  `isAlt_toBilinForm_skewSymmetrizeBilinear` and
  `nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff` (nondegenerate
  exactly when $s-s^{\mathrm{flip}}$ is, by Tau Ceti's
  `TauCeti.BilinForm.nondegenerate_smul_iff`), and
  `isOpen_setOf_nondegenerate_toBilinForm_sub_flip` (in finite dimension,
  the $s$ with $s-s^{\mathrm{flip}}$ nondegenerate are open). In the same file, carrying a form along a continuous linear
  equivalence `e` in both arguments, `ContinuousLinearEquiv.bilinearCongr`:
  `ContinuousLinearEquiv.toBilinForm_bilinearCongr` (as a bilinear
  form it is `LinearMap.BilinForm.congr` along `e`) and
  `ContinuousLinearEquiv.nondegenerate_bilinearCongr_sub_flip_iff` (it keeps
  $s-s^{\mathrm{flip}}$ nondegenerate or degenerate). Also in that file, for
  *Symplectic neighbourhoods*, the adjoint of a map for two forms,
  `ContinuousLinearMap.bilinAdjoint`, with `coe_bilinAdjoint`.
- For an alternating sesquilinear map $B$, $B-B^{\mathrm{flip}}=2\cdot B$,
  `LinearMap.IsAlt.sub_flip_eq_two_smul`, which Mathlib lacks; the library
  adds it in `LinearAlgebra/SesquilinearForm.lean`.
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
  present them. A
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

### Explicit formulas on open sets

The part states smoothness through two explicit formulas, each smooth on
an open set and natural under continuous linear equivalences, so that they
could also be read in trivializations of a bundle. *Symplectic vector
bundles* applies Tau Ceti's linear `cayleyPathFormula` and
`SymplecticForm.polarComplexStructure` fibrewise, but reads
`metricPolarFormula` in trivializations of its bundle of bilinear forms,
which gives the smoothness of its $J_{g,\omega}$ and of $J_{g,\omega_{g,B}}$
on its endomorphism bundle. Its existence issue waits for issues 4 and 5
below, its contractibility issue for issue 6, and its homotopy-equivalence
issue for issues 4, 5 and 6.
The two formulas:

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
   variable of the formula, which is smooth in it too. Tau Ceti's compatible
   and tame contractions are this formula at $b=1-t$
   (`Compatible.toContinuousLinearMap_cayleyContraction`).

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

The part uses the following from other parts:

- *Standard model* (`StdSpace`, `stdForm`, `stdComplexStructure`, the
  comparison with Tau Ceti's product model, and the matrix dictionary of #8).
  It is used in condition (3), in Lemma 2.5.5 and in the compact-subgroup
  theorem.
- The Lagrangian extension lemma of *Symplectic vector spaces*
  (`IsIsotropic.exists_le_isLagrangian` in `LinearAlgebra/Symplectic/Subspace.lean`), used only in the
  implication from (4) to (1). An isotropic plane containing $v$ and $w$ is
  extended to a Lagrangian subspace.
- From *Linear complex structures*, only merged files.
  `Compatible.lean` imports `LinearAlgebra/ComplexStructure/Action.lean`,
  which imports only Mathlib and Tau Ceti, for
  `AlmostComplexStructure.transport_eq_iff_isComplexLinearMap`, used in
  `compatible_of_isSymplectomorphism_stdForm` and
  `compatible_iff_exists_isSymplectomorphism_stdForm`.
  It also imports `LinearAlgebra/ComplexStructure/Hom.lean`, which imports
  only Tau Ceti, for `IsComplexLinearMap.symm_linearEquiv`.
  `Topology/ComplexStructure/Compatible/Matrix.lean` imports
  `Topology/ComplexStructure/Basic.lean`, which besides `Action.lean` imports
  only Tau Ceti and the merged `LinearAlgebra/Matrix/NonsingularInverse.lean`
  and `Analysis/CStarAlgebra/Matrix.lean` (which import only Mathlib and
  merged files that do), for `AlmostComplexStructure.homeomorphMatrix` and
  `coe_homeomorphMatrix` in `compatibleEquivPosDefSymplectic`.
  `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean` imports
  `LinearAlgebra/ComplexStructure/Standard.lean`, for
  `stabilizer_stdComplexStructure`; besides `Action.lean` and `Hom.lean`, that
  file imports this part's `Compatible.lean`, `Symplectic/Standard/Matrix.lean` of
  *Standard model*, the library's `Geometry/Symplectic/Orientation.lean`
  (which imports only Tau Ceti) and Tau Ceti.
  `Topology/ComplexStructure/Compatible/SymplecticForms.lean` imports
  `Topology/ComplexStructure/Orthogonal.lean`, for
  `orthogonalComplexStructures` and
  `mem_orthogonalComplexStructures_iff_inner` in
  `metricComplexStructures_innerSL`; that file imports only
  `Topology/ComplexStructure/Basic.lean`,
  `LinearAlgebra/Symplectic/Standard/Basic.lean` of *Standard model*,
  `Analysis/Matrix/Polar/Deformation.lean` of *Symplectic group* and Tau
  Ceti, none of which imports a file of this part. So `Compatible.lean` is
  imported by `Standard.lean` of *Linear complex structures* while it
  imports that part's `Action.lean`: each part uses a merged file of the
  other. Since all of these files are merged, the part waits for nothing of
  *Linear complex structures*; `DESIGN.md` lists them with that note.
- From *Symplectic group*, only the merged file
  `LinearAlgebra/Matrix/SymplecticGroup/Basic.lean`, which imports only
  Mathlib and Tau Ceti. `Compatible/Matrix.lean` uses
  `Matrix.IsSymm.mem_symplecticGroup_iff` from it.

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
- **New `LinearAlgebra/SesquilinearForm.lean`.** It holds
  `LinearMap.IsAlt.sub_flip_eq_two_smul`, for
  `toContinuousBilinearMap_sub_flip`. The identity is linear algebra on
  Mathlib's alternating maps alone, so it sits in the file named after
  Mathlib's `LinearAlgebra/SesquilinearForm/Basic.lean`, which defines
  `LinearMap.IsAlt`.
- **`Tames.lineMap` in `LinearAlgebra/Symplectic/Compatible.lean`.** The
  straight line between two forms that tame one complex structure is used by
  this part's homotopy on forms. It is
  linear algebra on Tau Ceti's types alone, so it sits in the part's linear
  file, in `TauCeti.SymplecticForm`, and not with the topology on
  `SymplecticForm V`.
- **New `Geometry/Symplectic/Cayley/Domain.lean`.** The open set where the
  Cayley path is smooth is used by two files of this part. *Symplectic
  vector bundles* uses this file, for `TauCeti.cayleyDomain`, the openness
  lemma `TauCeti.isOpen_setOf_forall_Icc_mem_cayleyDomain` and
  `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`; of the other files
  of this part it uses only the two of `PolarComplexStructure/`.
  It involves only Tau Ceti's `cayleyPathFormula`, so it goes in the folder
  of Tau Ceti's `Cayley/Smooth.lean`, which it extends, and can
  move there unchanged.
- **New `Geometry/Symplectic/Darboux/EuclideanBasis.lean`.** The complex
  linearity of `b.darbouxBasisEquiv` for a basis adapted to $J$ is stated
  with Tau Ceti's notions alone and does not need a symplectic form, so it
  sits in the folder of Tau Ceti's `Darboux/EuclideanBasis.lean`, which
  defines `darbouxBasisEquiv`, and can move there unchanged.
- **Lemma 2.5.5 without `Compatible.cayleyEquiv`.** The overview suggested
  that equivalence. It maps the *tame* structures onto Tau Ceti's Cayley ball.
  It does not map the compatible structures onto the positive symplectic
  matrices, so it does not give $J\mapsto-J_0J$. That map and its inverse
  $P\mapsto J_0P$ are restrictions of linear maps, which gives the
  homeomorphism directly.
- **New `Analysis/InnerProductSpace/LinearMap.lean`.** It holds the
  `@[simp]` lemma `innerSL_real_apply_apply`, which `InnerProducts.lean`
  and the files that use the ambient inner product as an element of
  `innerProducts V` need. It mentions only Mathlib's `innerSL`, so it sits in
  the root namespace, in the file named after Mathlib's
  `Analysis/InnerProductSpace/LinearMap.lean`, and can move there unchanged.
- **$\mathrm{Met}(V)$ without coordinates.** The overview got convexity from
  `TauCeti.convex_setOfPred_posDef` in coordinates. Tau Ceti's
  `convex_setOfPred_symm_pos` states it for continuous bilinear forms on `V`
  itself, so coordinates are not needed.

### `LinearAlgebra/Symplectic/Compatible.lean`

These are the characterizations (Proposition 2.5.4 and Exercise 2.5.3), in
`TauCeti.SymplecticForm`, except those that involve `StdSpace`. The results
about $g_J$ and $H$ hold in every
dimension, as their Tau Ceti counterparts such as
`Invariant.associatedBilinForm_isSymm` do, and carry no finite-dimensionality
hypothesis. Only the Darboux-basis, standard-model and TFAE
statements assume `[FiniteDimensional ℝ V]`.

- `compatible_iff_exists_isDarbouxBasis [FiniteDimensional ℝ V] :
  ω.Compatible J ↔ ∃ (n : ℕ)
  (b : Module.Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧ ∀ k,
  b (k, 1) = J (b (k, 0))`. This is condition (2), with $v_k=$ `b (k, 0)` and
  $Jv_k=$ `b (k, 1)`, in Tau Ceti's normalization, which is the book's. The
  forward direction is `exists_isDarbouxBasis_forall_apply_eq_of_pairwise_commute`
  with an empty family. The converse checks invariance and positivity on the
  basis.
- `isDarbouxBasis_iff_apply_apply_eq_ite (hbJ : ∀ k, b (k, 1) = J (b (k, 0))) :
  ω.IsDarbouxBasis b ↔ ∀ x y, ω (b x) (J (b y)) = if x = y then 1 else 0`:
  a basis adapted to `J` is a Darboux basis exactly when it is orthonormal
  for $g_J$. The forward direction is `IsDarbouxBasis.apply_apply_eq_ite`.
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
  {ι : Type*} [Fintype ι] (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
  ω.Compatible J ↔ ∃ Ψ : StdSpace ι ≃ₗ[ℝ] V,
  IsSymplectomorphism (stdForm ι) ω Ψ ∧
  IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap`, in
  `SymplecticGeometry`, since it involves `StdSpace`. This is
  condition (3). The map is not built by hand. From (2), Tau Ceti's
  `b.darbouxBasisEquiv` is a symplectomorphism onto `stdSymplecticForm` on
  `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`
  (`IsDarbouxBasis.isSymplectomorphism_darbouxBasisEquiv`). It sends
  `b (k, 0)` to `(single k 1, 0)` and `b (k, 1)` to `(0, single k 1)`
  (`darbouxBasisEquiv_apply_zero`/`_one`), so it carries $J$ to
  `AlmostComplexStructure.product`, which maps `(x, 0)` to `(0, x)`
  (`Module.Basis.isComplexLinearMap_darbouxBasisEquiv`, in
  `Geometry/Symplectic/Darboux/EuclideanBasis.lean`). $\Psi$ is
  its inverse, complex linear by
  `TauCeti.IsComplexLinearMap.symm_linearEquiv`
  (`LinearAlgebra/ComplexStructure/Hom.lean`), composed with the reindexing along a bijection `Fin n ≃ ι`,
  which commutes with $J_0$ (`stdComplexStructure_piLpCongrLeft_sumCongr` and
  `isComplexLinearMap_piLpCongrLeft_sumCongr`, in
  `LinearAlgebra/Symplectic/Standard/Basic.lean`), and
  with `EuclideanSpace.sumEquivProd`, which is a symplectomorphism from
  `stdForm ι` to that product model carrying `stdComplexStructure ι` to
  `AlmostComplexStructure.product` (`isSymplectomorphism_sumEquivProd` and
  `stdComplexStructure_transport_sumEquivProd`, with complex linearity
  `isComplexLinearMap_sumEquivProd`); the three complex linear maps compose
  by `IsComplexLinearMap.comp`. The converse,
  `compatible_of_isSymplectomorphism_stdForm`, needs no dimension hypothesis
  and is `Compatible.transport` of `stdForm_compatible`.
- `compatible_iff_tames_and_isLagrangian_map :
  ω.Compatible J ↔ ω.Tames J ∧
  ∀ L : Submodule ℝ V, ω.IsLagrangian L → ω.IsLagrangian (L.map J.toLinearMap)`,
  in every dimension, since neither direction uses a finite dimension.
  This is condition (4). Forward, an invariant $J$ is a symplectomorphism,
  so it maps Lagrangian subspaces to Lagrangian subspaces
  (`Invariant.isLagrangian_map`). Backward, if
  $\omega(v,w)=0$, extend the isotropic span of $v,w$ to a Lagrangian $L$
  (`IsIsotropic.exists_le_isLagrangian`). Then $\omega(Jv,Jw)=0$
  (`apply_apply_eq_zero_of_forall_isLagrangian_map`, stated for any linear
  map between two symplectic spaces that sends Lagrangians to Lagrangians). So for each $v\ne0$ the
  functional $\omega(Jv,J\cdot)$ vanishes on the kernel of $\omega(v,\cdot)$,
  hence is $c_v\,\omega(v,\cdot)$ (Mathlib's `mem_span_of_iInf_ker_le_ker`).
  Evaluating at $Jv$ gives $c_v\,\omega(v,Jv)=\omega(v,Jv)$, so $c_v=1$ by
  tameness, with no need to compare different $v$
  (`Tames.invariant_of_forall_isLagrangian_map`).
- **Milestone** `compatible_tfae [FiniteDimensional ℝ V] (hι : Module.finrank ℝ V = 2 * Fintype.card ι) :
  List.TFAE [ω.Compatible J, (2), (3), (4), (g_J condition), (H condition)]`,
  in `SymplecticGeometry`,
  with the six conditions written as in the lemmas above. Its docstring ends
  with "Milestone: *Characterizations of compatible complex structures*."

The file also holds the straight line between two forms that tame one
complex structure, in a section with only `[AddCommGroup V] [Module ℝ V]`.

- `TauCeti.SymplecticForm.Tames.lineMap (h₀ : ω₀.Tames J) (h₁ : ω₁.Tames J)
  (ht : t ∈ Set.Icc (0 : ℝ) 1) : SymplecticForm V`, with `t` implicit: the
  form $(1-t)\,\omega_0+t\,\omega_1$. A combination of alternating forms is
  alternating, and $J$ tames it, since
  $(1-t)\,\omega_0(v,Jv)+t\,\omega_1(v,Jv)>0$ for $v\ne0$ when the two weights
  are nonnegative and add up to one; so it is built with Tau Ceti's
  `SymplecticForm.ofTames`. The name follows Mathlib's `AffineMap.lineMap`,
  whose value at `t` is the same combination. Its API:
  - `@[simp] Tames.toBilinForm_lineMap : (h₀.lineMap h₁ ht).toBilinForm =
    (1 - t) • ω₀.toBilinForm + t • ω₁.toBilinForm`. As for `ofTames`, the
    `toBilinForm` equation is the simp lemma; a pointwise
    `Tames.lineMap_apply` (the value at `v w`), if added, is not, since the
    coercion of a form to a function unfolds to `toBilinForm`.
  - `Tames.tames_lineMap : (h₀.lineMap h₁ ht).Tames J`, from Tau Ceti's
    `tames_ofTames`.
  - `@[simp] Tames.lineMap_zero : h₀.lineMap h₁ ht = ω₀` for
    `ht : (0 : ℝ) ∈ Set.Icc 0 1`, and `@[simp] Tames.lineMap_one`, whose
    value is `ω₁`, both by `toBilinForm_injective`. They give the endpoints
    of a homotopy built from the line.

  The statement mentions only Tau Ceti's types and uses neither a metric nor
  a topology. Tau Ceti has neither this definition nor a convexity lemma for
  the forms that tame one structure; its convexity results are about the
  Cayley ball (`Geometry/Symplectic/Cayley/`). The homotopy on forms of
  `Topology/ComplexStructure/Compatible/SymplecticForms.lean` and the
  fibrewise line of `exists_homotopyEquiv_polarComplexStructure` in
  `design/symplectic-vector-bundles.md` both take their values from it, so
  neither builds a value with `ofTames` itself.

### `Analysis/InnerProductSpace/LinearMap.lean`

This complements Mathlib's file of `innerSL`, and imports only it.

- `innerSL_real_apply_apply` (`@[simp]`, in the root namespace): `innerSL ℝ`,
  coerced at the real bilinear type `V →L[ℝ] V →L[ℝ] ℝ` (the ambient type of
  `innerProducts V`), evaluates to `⟪u, v⟫`. Mathlib's `innerSL_apply_apply`
  is stated at the conjugate-linear type, so `simp` does not use it there.

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
  `g ↦ e.bilinearCongr g`, with `@[simp]` `transport_apply`
  (`transport e g w w' = g (e.symm w) (e.symm w')`), `transport_symm`,
  `transport_trans` and `transport_refl`. It pushes forward along `e`, in the
  same direction as Tau Ceti's `SymplecticForm.transport` and
  `AlmostComplexStructure.transport`, so equivariance statements use one
  direction throughout. (The name `pullback` is avoided: Tau Ceti's
  `SymplecticForm.pullback` is a different operation.) This is the action of
  $\mathrm{GL}(V)$ that equivariance uses.
- `innerSL_mem_innerProducts` (for `V` an inner product space):
  `innerSL ℝ ∈ innerProducts V`, the ambient inner product as an element.
- `simp` evaluates `⟨innerSL ℝ, innerSL_mem_innerProducts⟩` applied to `u`
  and `v` to `⟪u, v⟫` by `innerSL_real_apply_apply`, from
  `Analysis/InnerProductSpace/LinearMap.lean` above.
- `innerProducts.exists_transport_eq_innerSL (g : innerProducts V)`, for
  finite-dimensional `V`: some `e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V))`
  has `transport e g = ⟨innerSL ℝ, innerSL_mem_innerProducts⟩`. It is
  `ContinuousLinearEquiv.ofFinrankEq` followed by the inverse of Tau Ceti's
  `metricChangeEquiv` of the pushed-forward form, so no orthonormal basis is
  built. `PolarComplexStructure/Basic.lean` uses it to reduce statements about
  `g` to the ambient case.
- `innerProducts.ext_apply_right`: an inner product separates points
  through its first argument.
- `innerProducts.forall_transport_apply_transport_iff`: `J` preserves `g`
  exactly when `J.transport e` preserves `transport e g`.
- `innerProducts.transport_eq_innerSL_iff (e : V ≃L[ℝ] E) (g)`, for `E` an
  inner product space: `transport e g = ⟨innerSL ℝ, _⟩ ↔
  ∀ u v, ⟪e u, e v⟫ = g u v`.
- `symmetrizeBilinear_mem_innerProducts {g : V →L[ℝ] V →L[ℝ] ℝ}
  (hg : ∀ v, v ≠ 0 → 0 < g v v) :
  (ContinuousLinearMap.symmetrizeBilinear g).val ∈ innerProducts V`: the
  symmetric part of a form that is positive on nonzero vectors is an inner
  product. `PolarComplexStructure/Smooth.lean` uses it on `polarDomain`.
- `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear
  [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {g : W →L[ℝ] W →L[ℝ] ℝ}
  (hg : ∀ v, v ≠ 0 → 0 < g v v) :
  IsStrictlyPositive (continuousLinearMapOfBilin (symmetrizeBilinear g).val)`:
  the same fact in Tau Ceti's terms, by
  `isStrictlyPositive_continuousLinearMapOfBilin_iff`, for the positivity
  step of `contDiffOn_metricPolarFormula`.
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
- `toContinuousBilinearMap_sub_flip (ω : SymplecticForm V)`: writing `B` for
  `ω.toBilinForm.toContinuousBilinearMap`, `B - B.flip = (2 : ℝ) • B`, from
  `LinearMap.IsAlt.sub_flip_eq_two_smul`; and
  `@[simp] skewSymmetrizeBilinear_toContinuousBilinearMap (ω : SymplecticForm V)`:
  `B.skewSymmetrizeBilinear = B`, so the skew part of a symplectic form is
  the form itself, by `skewSymmetrizeBilinear_of_isAlt`.
  `PolarComplexStructure/Smooth.lean` uses the second.
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
  are the first bullet of Proposition 2.5.6. With them,
  `apply_metricPolarComplexStructure_left : (g : V →L[ℝ] V →L[ℝ] ℝ)
  (metricPolarComplexStructure g ω u) v = -g u (metricPolarComplexStructure g ω v)`,
  skew-adjointness for `g`, from Tau Ceti's
  `AlmostComplexStructure.bilinForm_apply_left_eq_neg_apply_right`.
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
  - `exists_operator_and_sqrt_neg_mul_self (g ω) : ∃ A Q : V →L[ℝ] V,` the
    four hypotheses `hA`, `hQs`, `hQp` and `Q * Q = -(A * A)` above. So the
    formula applies to every `g` and `ω`. Proof: carry `g` to a Euclidean
    space with `innerProducts.exists_transport_eq_innerSL` (and
    `innerProducts.transport_eq_innerSL_iff` for the isometry), take Tau
    Ceti's `innerOperator` of the transported form and its `operatorAbs`
    there (`operatorAbs_mul_self_of_adjoint_eq_neg` gives the square;
    `apply_polarComplexStructure` and `compatible_polarComplexStructure`
    give positive definiteness, as `ω'` tames its polar complex structure),
    and pull both back.
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

Here `V` is a real normed space, `W` and `W'` are finite-dimensional real
inner product spaces, and `s♯` is Tau Ceti's Riesz map
`continuousLinearMapOfBilin s`, as in Tau Ceti's file. The skew part of `s`
is `ContinuousLinearMap.skewSymmetrizeBilinear s`.

The domain, the formula and their smoothness and naturality mention only
continuous bilinear forms and Tau Ceti's operations on them
(`metricChangeTransport`, `continuousLinearMapOfBilin`, `CFC.sqrt`,
`Ring.inverse`), so by the namespace rule above they go in `TauCeti`, next
to `cayleyPathFormula`. The declarations that involve `innerProducts` or
`metricPolarComplexStructure` (`mem_polarDomain`, `metricPolarFormula_eq`,
`metricPolarFormula_eq_of_toContinuousBilinearMap_eq`,
`metricPolarFormula_eq_of_mem` and `continuous_metricPolarComplexStructure`)
are in `SymplecticGeometry`.

The file uses helpers stated in their own files:
`SymplecticGeometry.symmetrizeBilinear_mem_innerProducts` and
`InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear`
(`Topology/Algebra/Module/InnerProducts.lean`), and
`TauCeti.SymplecticForm.skewSymmetrizeBilinear_toContinuousBilinearMap`
(`Topology/Algebra/Module/SymplecticForms.lean`), and the lemmas on
`ContinuousLinearMap.skewSymmetrizeBilinear`
(`Topology/Algebra/Module/BilinearForm.lean`).

- `TauCeti.polarDomain (V) : Set ((V →L[ℝ] V →L[ℝ] ℝ) ×
  (V →L[ℝ] V →L[ℝ] ℝ))`, for any real normed space `V`, since it uses no
  inner product: `{p | (∀ v, v ≠ 0 → 0 < p.1 v v) ∧
  (p.2 - p.2.flip).toBilinForm.Nondegenerate}`. The condition is on
  `s - s.flip`, twice the skew part, as in the `polarFormulaDomain` of
  `design/symplectic-vector-bundles.md`. It comes with
  - `@[simp] mem_polarDomain_iff`, which unfolds it;
  - `nondegenerate_toBilinForm_of_mem_polarDomain (h : (g, s) ∈ polarDomain V) :
    (skewSymmetrizeBilinear s).toBilinForm.Nondegenerate`, by
    `nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff`;
  - `isOpen_polarDomain (V) [FiniteDimensional ℝ V] : IsOpen (polarDomain V)`,
    from Tau Ceti's `isOpen_setOf_forall_bilinear_apply_self_pos` and
    `isOpen_setOf_nondegenerate_toBilinForm_sub_flip`.
- `SymplecticGeometry.mem_polarDomain [FiniteDimensional ℝ V]
  (g : innerProducts V) (ω : SymplecticForm V) :
  ((g : V →L[ℝ] V →L[ℝ] ℝ), ω.toBilinForm.toContinuousBilinearMap) ∈
  polarDomain V`. Every inner product and symplectic form lie in the domain,
  so the smoothness statement covers all of them. Its proof uses
  `nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff` and
  `skewSymmetrizeBilinear_toContinuousBilinearMap`. It is in `SymplecticGeometry` because
  it mentions `innerProducts`.
- `TauCeti.metricPolarFormula (g s : W →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] W`. With
  `g' := (symmetrizeBilinear g).val` (Tau Ceti's
  `ContinuousLinearMap.symmetrizeBilinear`), `R := g'.metricChangeTransport`
  and `A := R * (skewSymmetrizeBilinear s)♯ * R`, it is Tau Ceti's expression
  `R * (A * Ring.inverse (CFC.sqrt (-(A * A)))) * CFC.sqrt g'♯`. No case
  split is needed: `Ring.inverse`, `CFC.sqrt` and `metricChangeTransport`
  already have junk values off the domain. It comes with
  `metricPolarFormula_def`, which states the body with the same `let`s.
- `SymplecticGeometry.metricPolarFormula_eq (g : innerProducts W)
  (ω : SymplecticForm W) :
  metricPolarFormula g ω.toBilinForm.toContinuousBilinearMap =
  LinearMap.toContinuousLinearMap (metricPolarComplexStructure g ω).toLinearMap`.
  It is derived from Tau Ceti's
  `conjContinuousAlgEquiv_toContinuousLinearMap_polarComplexStructure`, taken
  with `V := W` and `K := g.metricChangeEquiv hg : W ≃L[ℝ] W`, where `hg`,
  positivity of `g♯`, comes from
  `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_iff`. No
  Euclidean space and no orthonormal basis is built. The hypothesis of that
  theorem on `g` follows from Tau Ceti's `metricChangeEquiv_symm_apply` and
  `inner_sqrt_apply_sqrt_apply`; its hypothesis on `s` holds for the form
  `ω.transport K.toLinearEquiv.symm`. So the right-hand side of the theorem
  is the polar structure of that form, conjugated by `K`. By
  `metricPolarComplexStructure_innerSL` and
  `metricPolarComplexStructure_transport` along `K`, which carries the ambient
  inner product to `g`, this is $J_{g,\omega}$. On the left, the symmetric
  part of `g` is `g` (Tau Ceti's `symmetrizeBilinear_coe`) and the skew part
  of `ω` is `ω` (`skewSymmetrizeBilinear_toContinuousBilinearMap`). The
  formula is not derived a second time.
- `TauCeti.contDiffOn_metricPolarFormula {n : WithTop ℕ∞} :
  ContDiffOn ℝ n (fun p ↦ metricPolarFormula p.1 p.2) (polarDomain W)`. The
  proof composes the symmetrization (a continuous linear map),
  `ContDiffOn.metricChangeTransport`,
  `ContDiffOn.sqrt_continuousLinearMapOfBilin`,
  `ContinuousLinearMap.contDiffOn_sqrt`, and `contDiffAt_ringInverse` at the
  unit that `CFC.isUnit_sqrt_iff` gives. On the domain `g'♯` is strictly
  positive by
  `InnerProductSpace.isStrictlyPositive_continuousLinearMapOfBilin_symmetrizeBilinear`
  (`Topology/Algebra/Module/InnerProducts.lean`), and `-A²` by Tau
  Ceti's `isStrictlyPositive_neg_mul_self_metricChangeTransport`, applied to
  the skew part as a symplectic form (`ofContinuousBilinearMap` with
  `nondegenerate_toBilinForm_of_mem_polarDomain`). It is the `ContDiffOn`
  form of the argument of Tau Ceti's private
  `contMDiffAt_metricChangeTransport_mul_mul_sqrt`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`). That lemma is
  private and stated for families on a manifold, so it cannot be used here.
  The library states the pointwise version once, in Tau Ceti's style and
  namespace, so that it can replace the private lemma upstream.
- `TauCeti.metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear
  (g s : W →L[ℝ] W →L[ℝ] ℝ) :
  metricPolarFormula (symmetrizeBilinear g).val (skewSymmetrizeBilinear s) =
  metricPolarFormula g s`: the formula depends only on the symmetric part of
  `g` and the skew part of `s`, by idempotence of both parts.
- `SymplecticGeometry.metricPolarFormula_eq_of_toContinuousBilinearMap_eq
  {g s : W →L[ℝ] W →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v)
  {ω : SymplecticForm W}
  (hω : ω.toBilinForm.toContinuousBilinearMap = skewSymmetrizeBilinear s) :
  metricPolarFormula g s = LinearMap.toContinuousLinearMap
  (metricPolarComplexStructure ⟨_, symmetrizeBilinear_mem_innerProducts hg⟩ ω).toLinearMap`,
  by `metricPolarFormula_eq` and the previous lemma.
- `SymplecticGeometry.metricPolarFormula_eq_of_mem {g s : W →L[ℝ] W →L[ℝ] ℝ}
  (h : (g, s) ∈ polarDomain W) : metricPolarFormula g s =
  LinearMap.toContinuousLinearMap (metricPolarComplexStructure
  ⟨_, symmetrizeBilinear_mem_innerProducts (mem_polarDomain_iff.1 h).1⟩
  (SymplecticForm.ofContinuousBilinearMap _ _
  (nondegenerate_toBilinForm_of_mem_polarDomain h))).toLinearMap`: on the
  domain, the formula is $J_{g',\omega'}$, for the symmetric part `g'` of `g`
  and the symplectic form `ω'` whose bilinear form is the skew part of `s`.
- `TauCeti.metricPolarFormula_conj (e : W ≃L[ℝ] W') {g s : W →L[ℝ] W →L[ℝ] ℝ}
  (h : (g, s) ∈ polarDomain W) :
  metricPolarFormula (e.bilinearCongr g) (e.bilinearCongr s) =
  e.conjContinuousAlgEquiv (metricPolarFormula g s)`: on `polarDomain W`,
  pushing both forms forward along `e` conjugates the formula by `e`. The
  proof is `metricPolarFormula_eq_of_mem`,
  `metricPolarFormula_symmetrizeBilinear_skewSymmetrizeBilinear` with Tau
  Ceti's `symmetrizeBilinear_bilinearComp` and
  `skewSymmetrizeBilinear_bilinearComp`, then `metricPolarFormula_eq` and
  `metricPolarComplexStructure_transport`, since the symmetric and skew parts
  commute with transport. This is naturality on the whole domain, and it
  does not depend on the inner products of `W` and `W'`. Because this proof
  uses `SymplecticGeometry` lemmas, moving the lemma to Tau Ceti would need
  a direct proof from the formula.
- `SymplecticGeometry.continuous_metricPolarComplexStructure
  [FiniteDimensional ℝ V] :
  Continuous fun p : innerProducts V × SymplecticForm V ↦
  metricPolarComplexStructure p.1 p.2`, for a normed space `V` with no inner
  product. It carries `V` to `EuclideanSpace ℝ (Fin (finrank ℝ V))` along
  `ContinuousLinearEquiv.ofFinrankEq` and uses the formula there. Its
  composition form `Continuous.metricPolarComplexStructure` (continuous
  families `g x`, `ω x` give a continuous `J_{g x, ω x}`) gives continuity in
  `ω` for fixed `g`.

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
- `map_mem_cayleyDomain_iff`: an algebra isomorphism `f` gives
  `(b, f A, f B) ∈ cayleyDomain S ↔ (b, A, B) ∈ cayleyDomain R`; and the ends
  of the path, `cayleyPathFormula_zero` (`= A`) and `cayleyPathFormula_one`
  (`= B` when `A * A = -1` and `1 - A * B` is a unit), in any `ℝ`-algebra.
  *Symplectic vector bundles* added them with its issue 7, which reads the
  domain through trivializations and needs the ends of its contraction.
- `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain_of_continuousLinearEquiv`
  and `Compatible.exists_toLinearMap_eq_cayleyPathFormula`, for a topological
  vector space `W` with `L : W ≃L[ℝ] F`, `F` a finite-dimensional normed
  space: the first is `Compatible.mem_cayleyDomain` read through `L`, the
  second says that `cayleyPathFormula (smoothTransition t) A B` represents an
  `ω`-tame structure, `ω`-compatible when the endpoint is. Both transport
  along `L` (Tau Ceti's `Geometry/Symplectic/SymplecticTransport.lean`, which
  the file imports), and the second uses Tau Ceti's linear
  `Compatible.cayleyPath`. The same issue 7 added them, for the fibres of a
  vector bundle.

### `Geometry/Symplectic/Darboux/EuclideanBasis.lean`

- `Module.Basis.isComplexLinearMap_darbouxBasisEquiv
  {b : Basis (Fin n × Fin 2) ℝ V} (hbJ : ∀ k, b (k, 1) = J (b (k, 0)))`:
  `b.darbouxBasisEquiv` is complex linear from `J` to
  `AlmostComplexStructure.product`. The proof checks the identity of linear
  maps on the basis and concludes with Tau Ceti's
  `isComplexLinearMap_iff_apply`, so it does not use the body of
  `IsComplexLinearMap`.

### `Topology/ComplexStructure/Compatible/Matrix.lean`

This is Lemma 2.5.5, on `StdSpace ι`, in `SymplecticGeometry`.

- `compatibleEquivPosDefSymplectic ι : {J : AlmostComplexStructure (StdSpace ι)
  // (stdForm ι).Compatible J} ≃ₜ {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ //
  P ∈ Matrix.symplecticGroup ι ℝ ∧ P.PosDef}`, with the `@[simp]` lemmas
  `coe_compatibleEquivPosDefSymplectic_apply`, which is
  `-(Matrix.J ι ℝ) * Matrix.toEuclideanLin.symm J.toLinearMap`, and
  `compatibleEquivPosDefSymplectic_symm_apply_toLinearMap`, which is
  `Matrix.toEuclideanLin (Matrix.J ι ℝ * P)`.
- The underlying facts use no topology, so they are lemmas of the
  *Standard model* file `LinearAlgebra/Symplectic/Standard/Matrix.lean`,
  which imports `LinearAlgebra/Symplectic/Compatible.lean` for them:
  `stdForm_apply_toEuclideanLin` ($\omega_0(v,Aw)=v^T(-J_0A)w$),
  `associatedBilinForm_stdForm_apply` and
  `toMatrix_associatedBilinForm_stdForm` (the matrix $P=-J_0J$ is the Gram
  matrix of $g_J$), `invariant_stdForm_iff_isSymm` ($P$ is symmetric if and
  only if $J$ is $\omega_0$-invariant, by
  `invariant_iff_isSymm_associatedBilinForm`), `tames_stdForm_iff`, and
  `compatible_stdForm_iff_posDef` ($J$ is compatible if and only if $P$ is
  positive definite, by `compatible_iff_isSymm_and_posDef_associatedBilinForm`).
  The same file proves `posDef_toBlocks₂₁_of_compatible` from the last one
  and `Matrix.neg_J_mul_eq_fromBlocks`, as a principal submatrix, and
  `toBlocks₂₂_eq_neg_transpose_of_invariant` from the symmetry of $P$ and the
  same block lemma. This file adds that a symmetric $P$ is
  symplectic if and only if $(J_0P)^2=-1$, and the topology.

### `Topology/ComplexStructure/Compatible/Metric.lean`

This is Corollary 2.5.7, in `SymplecticGeometry`.

- `compatibleMetric ω : C({J // ω.Compatible J}, innerProducts V)`, the map
  $J\mapsto g_J$, with `@[simp]` `coe_compatibleMetric_apply`
  (its value is `(ω.associatedBilinForm J).toContinuousBilinearMap`). It is
  continuous by Tau Ceti's `toContinuousBilinearMap_associatedBilinForm`.
- `compatiblePolar ω : C(innerProducts V, {J // ω.Compatible J})`, the map
  `g ↦ metricPolarComplexStructure g ω`, with `@[simp]`
  `coe_compatiblePolar_apply` (its value is
  `metricPolarComplexStructure g ω`).
- `metricHomotopyEquiv ω : ContinuousMap.HomotopyEquiv {J // ω.Compatible J}
  (innerProducts V)`. Its forward map is `compatibleMetric ω`, and its
  inverse is `compatiblePolar ω`. They come with `@[simp]`
  `metricHomotopyEquiv_toFun` and `metricHomotopyEquiv_invFun`, which state
  the two maps as continuous maps, and `@[simp]`
  `metricHomotopyEquiv_symm_apply`, `(metricHomotopyEquiv ω).symm g =
  compatiblePolar ω g`. One composite is the identity, by
  `metricPolarComplexStructure_associatedBilinForm`. The other is homotopic to
  the identity by the straight-line homotopy `metricStraightHomotopy ω`,
  $(t,g)\mapsto(1-t)\,g_{J_{g,\omega}}+t\,g$, inside the convex set. Its value
  is the `@[simp]` lemma `coe_metricStraightHomotopy_apply`, which gives it
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
  `toBilinForm_metricSymplecticForm` (`@[simp]`), the pointwise
  `metricSymplecticForm_apply` that follows from it, `tames_metricSymplecticForm`,
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
  `mem_metricSymplecticForms`, `mem_metricComplexStructures_innerSL` (for `V`
  an inner product space, `J ∈ metricComplexStructures ⟨innerSL ℝ, _⟩ ↔
  ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫`), `metricSymplecticForms_eq_image`, and
  `compatible_metricSymplecticForm`,
  `metricPolarComplexStructure_metricSymplecticForm` and
  `metricSymplecticForm_metricPolarComplexStructure`, by which the inverses
  below fix the subsets.
- `metricComplexStructures_innerSL n`: for the standard inner product of
  `EuclideanSpace ℝ n`, `metricComplexStructures ⟨innerSL ℝ,
  innerSL_mem_innerProducts⟩ = orthogonalComplexStructures n`, the set of
  *Linear complex structures* in `Topology/ComplexStructure/Orthogonal.lean`.
- `polarHomotopyEquiv g : ContinuousMap.HomotopyEquiv (SymplecticForm V)
  (AlmostComplexStructure V)`, with maps $\omega\mapsto J_{g,\omega}$ and
  $J\mapsto\omega_{g,J}$, stated by the `@[simp]` lemmas
  `polarHomotopyEquiv_toFun` and `polarHomotopyEquiv_symm_apply` (Mathlib's
  simp normal form `⇑h.symm` of `⇑h.invFun`). Mathlib's
  `ContinuousMap.HomotopyEquiv` keeps its homotopies only as the `Prop`s
  `left_inv` and `right_inv`, so the two homotopies are public definitions of
  their own, placed before `polarHomotopyEquiv g`, which takes `left_inv` from
  the first and `right_inv` from the second. Like `metricStraightHomotopy`,
  each runs from the composite at time $0$ to the identity at time $1$, the
  direction of `left_inv` and `right_inv`. The composites are written as
  `ContinuousMap`s, continuous by `continuous_metricSymplecticForm` and
  `Continuous.metricPolarComplexStructure`. Each homotopy is from the
  `ContinuousMap.comp` of the two maps of `polarHomotopyEquiv g`, so `left_inv`
  and `right_inv` take the homotopies as they are, with no cast.
  - `polarStraightHomotopy g`, a `ContinuousMap.Homotopy` from
    $\omega\mapsto\omega_{g,J_{g,\omega}}$ to `ContinuousMap.id
    (SymplecticForm V)`: the straight line
    $(t,\omega)\mapsto(1-t)\,\omega_{g,J_{g,\omega}}+t\,\omega$, from
    $\omega_{g,J_{g,\omega}}$ at `t = 0` to $\omega$ at `t = 1`.
    Both forms are tamed by $J_{g,\omega}$, by
    `tames_metricSymplecticForm` and
    `(compatible_metricPolarComplexStructure g ω).tames`, so its value at
    `(t, ω)` is `Tames.lineMap` of `LinearAlgebra/Symplectic/Compatible.lean`,
    taken with these two proofs, in this order, and the weight `t.2`, as
    `polarCayleyHomotopy g` takes its value from Tau Ceti's
    `Compatible.cayleyInterp`. No value is built inline with
    `SymplecticForm.ofTames`. Its value is the `@[simp]` lemma
    `toBilinForm_polarStraightHomotopy_apply`, an equation of bilinear forms:
    `(polarStraightHomotopy g (t, ω)).toBilinForm = (1 - (t : ℝ)) •
    (metricSymplecticForm g (metricPolarComplexStructure g ω)).toBilinForm +
    (t : ℝ) • ω.toBilinForm`, which is `Tames.toBilinForm_lineMap`.
    It is stated on `toBilinForm` and not on `⇑`: Tau Ceti's `CoeFun` on
    `SymplecticForm V` unfolds to a lambda, so a simp lemma on `⇑` would get
    no useful key and would not fire on `polarStraightHomotopy g (t, ω) v w`.
    Tau Ceti makes the same choice with `ofTames_toBilinForm`. A pointwise
    `polarStraightHomotopy_apply_apply`, not `@[simp]`, follows from it. The
    endpoints come from `Tames.lineMap_zero` and `_one`, and joint continuity
    in $(t,\omega)$ from `continuous_iff` of `SymplecticForm V`, Mathlib's
    `ContinuousMap.Homotopy.affine` and the two continuity results above.
  - `polarCayleyHomotopy g`, a `ContinuousMap.Homotopy` from
    $J\mapsto J_{g,\omega_{g,J}}$ to `ContinuousMap.id
    (AlmostComplexStructure V)`. Its value at `(t, J)` is Tau Ceti's
    `Compatible.cayleyInterp`, taken with
    `compatible_metricPolarComplexStructure g (metricSymplecticForm g J)`,
    `tames_metricSymplecticForm g J` and the weight `t.2`; the endpoints are
    `Compatible.cayleyInterp_zero` and `_one`. This is the `@[simp]` value
    lemma `polarCayleyHomotopy_apply`, named like Mathlib's
    `ContinuousMap.Homotopy.trans_apply`. It is the Cayley path relative to
    $J_{g,\omega_{g,J}}$ (compatible with $\omega_{g,J}$) towards $J$ (tame
    for $\omega_{g,J}$). Its endomorphism at time $b$ is
    `cayleyPathFormula b A B`, with `A` and `B` the endomorphisms of
    `metricPolarComplexStructure g (metricSymplecticForm g J)` and of `J`, by
    Tau Ceti's `Compatible.toContinuousLinearMap_cayleyInterp`; its joint
    continuity in $(t,J)$ comes from `contDiffOn_cayleyPathFormula`.
    The triple lies in `cayleyDomain` by `Compatible.mem_cayleyDomain`.
- `metricComplexStructuresHomotopyEquiv g` and
  `metricSymplecticFormsHomotopyEquiv g`, whose forward maps are the
  inclusions. Their inverses are $J\mapsto J_{g,\omega_{g,J}}$ and
  $\omega\mapsto\omega_{g,J_{g,\omega}}$. Each is Tau Ceti's
  `ContinuousMap.HomotopyEquiv.ofDeformationRetraction`, and comes with a
  `@[simp]` `_toFun` lemma (the forward map is `ContinuousMap.subtypeVal _`),
  an `_apply` lemma, and, for the inverse, a `@[simp]` `coe_…_symm_apply`
  lemma, in Mathlib's simp normal form `⇑h.symm` of `⇑h.invFun` as
  `polarHomotopyEquiv_symm_apply` is; its `coe_` is the inclusion of the
  subset, since the inverse maps into it. Neither has a homotopy of its
  own, nor a restriction of one. On the subsets, the inverses fix every
  point, by `metricPolarComplexStructure_eq_iff` (and, on
  `metricSymplecticForms g`, `metricSymplecticForm_eq_of_apply_apply`), so the composite on the
  subset is equal to the identity and `left_inv` is
  `ContinuousMap.Homotopic.refl` after `ContinuousMap.ext`. The composite on
  the whole space is $J\mapsto J_{g,\omega_{g,J}}$, respectively
  $\omega\mapsto\omega_{g,J_{g,\omega}}$, so `right_inv` is
  `polarCayleyHomotopy g`, respectively `polarStraightHomotopy g`, unchanged
  and with no cast. Their values are thus
  `polarCayleyHomotopy_apply` and `toBilinForm_polarStraightHomotopy_apply`.
- **Milestone** `metricPolarComplexStructure_eq_inverse_mul_and_homotopyEquiv`,
  named after its first and last conjuncts. Its `V` carries only
  `[NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]`, and no
  inner product: an `InnerProductSpace ℝ V` instance would have to induce the
  norm `V` already has, which fails for a sup norm or a normed bundle fibre.
  It is the conjunction of the following:
  - the plan's definition: `metricPolarComplexStructure_eq_inverse_mul`,
    with the existence of `A` and `Q`,
    `exists_operator_and_sqrt_neg_mul_self`;
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

- **Supporting file** `Topology/Algebra/Matrix/GeneralLinearGroup.lean`,
  in the namespace `Matrix.GeneralLinearGroup` and importing only Mathlib
  and Tau Ceti: `contRep 𝕜 ι : ContRepresentation 𝕜 (GL ι 𝕜)
  (EuclideanSpace 𝕜 ι)`, in which a matrix acts by `toEuclideanCLM`
  (`contRep_apply`, simp), and `continuous_contRep`. A subgroup such as $K$
  acts through `ContRepresentation.restrict`, which is how step 1 below gets
  its continuous action. Tau Ceti's
  `LinearAlgebra/Matrix/GeneralLinearGroup/MaximalCompact.lean` builds the
  same representation privately for a subgroup; this file is the public
  version for the whole group, and is meant to move upstream next to that
  file.
- **Milestone** `exists_conj_smul_le_unitarySubgroup {K : Subgroup
  (GLSymplectic ι ℝ)} (hK : IsCompact (K : Set (GLSymplectic ι ℝ))) :
  ∃ g : GLSymplectic ι ℝ, MulAut.conj g • K ≤
  (unitarySubgroup (GL (ι ⊕ ι) ℝ)).subgroupOf (GLSymplectic ι ℝ)`. The
  subgroup on the right is the realified $\mathrm{U}(n)$, by Tau Ceti's
  `GLSymplectic.inf_unitarySubgroup`. Its docstring says so, and ends with
  "Milestone: *Compact subgroups of the symplectic group*."
- The proof runs as follows:
  1. $K$ acts continuously on `StdSpace ι` through
     `(contRep ℝ (ι ⊕ ι)).restrict ((GLSymplectic ι ℝ).subtype.comp K.subtype)`,
     a matrix acting by `toEuclideanCLM`, with continuity from
     `continuous_contRep`; the action preserves `stdForm ι` (matrix
     dictionary, #8).
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
   `compatible_iff_exists_innerProductCore`, and `Tames.lineMap` with
   `Tames.toBilinForm_lineMap`, `Tames.tames_lineMap`, `Tames.lineMap_zero`
   and `Tames.lineMap_one`. Blockers: none.
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
   `polarStraightHomotopy` with `toBilinForm_polarStraightHomotopy_apply`,
   `polarCayleyHomotopy` with `polarCayleyHomotopy_apply`, and
   `polarHomotopyEquiv`. Blockers: 1, 5, 6.
10. **The metric subsets and the milestone *Complex structures versus
    symplectic forms*.** The rest of the file: `metricComplexStructures`,
    `metricSymplecticForms`, their two homotopy equivalences
    `metricComplexStructuresHomotopyEquiv` and
    `metricSymplecticFormsHomotopyEquiv` (homotopies: the identity, and
    `polarCayleyHomotopy` or `polarStraightHomotopy`), and the
    milestone. Blockers: 9.
11. **Compact subgroups of the symplectic group.**
    `Topology/Algebra/Matrix/SymplecticGroup/CompactSubgroup.lean`. Blockers:
    2, #8.

Issues 1, 3 and 6 can start at once. The contractibility issue of
*Symplectic vector bundles* uses the same open set of Cayley units over
$[0,1]$ as issue 6 here, through
`TauCeti.isOpen_setOf_forall_Icc_mem_cayleyDomain`, and the tame structures
lie in it by `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`, so it
waits for issue 6. That part's existence issue (building issue 6 of
`design/symplectic-vector-bundles.md`) proves the smoothness of its
$J_{g,\omega}$ from `metricPolarFormula` on `polarDomain` with its
smoothness, so it waits for issues 4 and 5. That part's
homotopy-equivalence issue uses `cayleyDomain` and `metricPolarFormula`
both, so it waits for issues 4, 5 and 6. No other issue of that part waits for this part.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.5.
