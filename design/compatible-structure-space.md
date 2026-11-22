# Space of compatible complex structures

The detailed design of part 28 of `DESIGN.md`, *Space of compatible complex
structures*. It serves the milestone *Kähler structure on the space of
compatible linear complex structures* of `atlas/almost-complex-structures.md`
(McDuff–Salamon [McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7, with
§2.5 for the Cayley transform and the Siegel upper half space). It fixes the
files of the part, its definitions and their API, the Lean names and
statements of its results, what it takes from Tau Ceti, Mathlib and the other
parts, and the building issues in the order they can be done. It settles the
two questions that `DESIGN.md` leaves to it: the curvature convention
(decision 5) and the type that carries the manifold structure (decision 1).

Files are under `SymplecticGeometry/`. Paths of Tau Ceti files are relative to
`.lake/packages/TauCeti/TauCeti/`. Every Tau Ceti and Mathlib name below was
checked at the pinned versions. Throughout, `V` is a real normed space of finite
dimension (`[NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]`,
the setting of Tau Ceti's topology on `AlmostComplexStructure V`), and
`ω : TauCeti.SymplecticForm V`. In this document `𝒥 ω` abbreviates
`{J : TauCeti.AlmostComplexStructure V // ω.Compatible J}`; a file may
introduce it as a `local notation`, never as a global name. `𝓘` abbreviates
`𝓘(ℝ, ω.compatibleModel)` (decision 2).

## What exists, and what the part adds

Tau Ceti has the space and its linear algebra, but no manifold:

- the type `𝒥 ω` with the operator-norm topology
  (`Geometry/Symplectic/AlmostComplex/Topology.lean`) and
  `TauCeti.SymplecticForm.instContractibleSpaceCompatible`;
- the tangent spaces `TauCeti.SymplecticForm.compatibleTangentSpace ω J :
  Submodule ℝ (Module.End ℝ V)`, with `mem_compatibleTangentSpace`,
  `mem_compatibleTangentSpace_iff_isSelfAdjoint`,
  `Invariant.mul_mem_tangentSpace_and_isSelfAdjoint`, and the description as
  velocities of curves,
  `Compatible.mem_compatibleTangentSpace_iff_exists_hasDerivAt` and
  `mem_compatibleTangentSpace_of_hasFDerivAt`
  (`Geometry/Symplectic/Cayley/Tangent.lean`);
- the global Cayley transform `Compatible.compatibleCayleyEquiv h₀ :
  𝒥 ω ≃ ω.compatibleCayleyBall J₀`, with inverse `C ↦ J₀(1 + C)(1 - C)⁻¹`,
  its convexity and balance, and its smoothness in operator-norm coordinates
  (`Compatible.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap`,
  `Compatible.contDiff_compatibleCayleyEquiv_symm`,
  `Tames.contMDiff_cayley`, `Compatible.contMDiff_of_contMDiff_cayley`,
  in `Geometry/Symplectic/Cayley/Basic.lean` and `Smooth.lean`);
- the exponential paths `t ↦ e^{tB} J e^{-tB}`, `B = ½ J Ŷ`
  (`AlmostComplexStructure.tangentPath`, `hasDerivAt_tangentPath`,
  `Compatible.tangentPath`, in
  `Geometry/Symplectic/AlmostComplex/StructureVariation.lean`);
- for manifolds: `SmoothAlmostComplexStructure`, `chartPushforward`,
  `SmoothTwoForm`, `IsKahler`, `IsPseudoholomorphic`,
  `SmoothAlmostComplexStructure.ofComplexManifold`; Riemannian geometry with
  `CovariantDerivative.curvatureTensor`, `sectionalCurvature`,
  `CovariantDerivative.addOneForm` and its curvature formula,
  `CovariantDerivative.alongCurve`, geodesics `TauCeti.Manifold.IsGeodesicCurve`
  and `IsGeodesicCurveOnFrom`, `IsGeodesicallyCompleteAt`, the Hopf–Rinow
  theorem `completeSpace_iff_isGeodesicallyCompleteAt`, Riemannian
  isometries `TauCeti.RiemannianIsometry`, and smooth embeddings
  `Manifold.IsSmoothEmbedding` with `ContMDiff.isImmersion_of_injective_mfderiv`.

The *Siegel upper half space* part (merged) has `SiegelUpperHalfSpace ι` with
its topology, the open embedding `toSymm` into the complex symmetric
matrices, the bijection `SiegelUpperHalfSpace.compatibleEquiv` onto
`𝒥 (stdForm ι)`, and smoothness of both formulas in matrix coordinates
(`contDiffOn_complexStructureMatrix`, `contDiffOn_ofComplexStructureMatrix`).
It has no manifold structure.

The part adds: the manifold structure on `𝒥 ω` and its embedding in
`V →L[ℝ] V`; the dimension of the tangent spaces; the complex structure
$\hat J\mapsto-J\hat J$, the form $\Omega$ and the trace metric on the
manifold; the Levi-Civita connection, the curvature and the geodesics; the
complex manifold structure on $\mathcal S_n$ and the holomorphic
diffeomorphism. No Mathlib or Tau Ceti notion is redefined.

## Decisions

1. **The type** (the second question `DESIGN.md` leaves here). The manifold is
   Tau Ceti's subtype `𝒥 ω` itself, not a subtype of `V →L[ℝ] V` and not a
   new structure. `DESIGN.md`'s principles keep one representation of a
   complex structure, `TauCeti.AlmostComplexStructure`, and on this subtype
   Tau Ceti already has the topology, the contractibility instance and the
   Cayley equivalence, which a subtype of `V →L[ℝ] V` would have to be
   reconnected to. The inclusion into `V →L[ℝ] V` is a named map,
   `ω.compatibleCLM` (decision 3). The instances are stated on the subtype;
   since the declarations are about a Tau Ceti type, they live in the
   namespace `TauCeti.SymplecticForm`, as the Cayley API does, so that they
   can move there.
2. **The model and the one chart.** Tau Ceti's compatible Cayley transform
   is a bijection of all of `𝒥 ω` onto a set that is open in a linear space,
   so one chart covers the manifold. The base point is
   `ω.compatibleBase : 𝒥 ω`, chosen from `ω.exists_compatible`. The model
   space is `ω.compatibleModel`, the tangent space at the base point read in
   `V →L[ℝ] V` (a finite-dimensional normed space, as a submodule of the
   operator space). For an anticommuting endomorphism, self-adjointness for
   $g_{J_0}$ is skew-adjointness for $\omega$
   (`mem_compatibleTangentSpace_iff_isSelfAdjoint`), so the compatible Cayley
   ball is exactly the set of strict contractions in this model. The chart is
   the Cayley coordinate map, an open embedding, and the instances come from
   Mathlib's `Topology.IsOpenEmbedding.singletonChartedSpace` and
   `Topology.IsOpenEmbedding.isManifold_singleton`. The tangent bundle is then
   trivial in a single chart, and every computation below is made in that
   chart or through the embedding. The base point is a choice. Nothing stated
   depends on it except the model's name: the Cayley chart at any other
   compatible structure is a smooth chart too (by `contMDiff_iff` of
   decision 3), and every result is stated through the embedding. Two
   alternatives were rejected: an atlas with one chart at each point (the
   models would differ from point to point, and transition maps are not
   needed), and Siegel coordinates through a Darboux basis, which also needs
   a choice and exists only after a transport to `StdSpace ι`.
3. **The embedding.** `ω.compatibleCLM : 𝒥 ω → V →L[ℝ] V` sends `J` to
   `LinearMap.toContinuousLinearMap J.1.toLinearMap`. It is a smooth
   embedding (`isSmoothEmbedding_compatibleCLM`), so a map into `𝒥 ω` is
   smooth exactly when its composite with `compatibleCLM` is
   (`contMDiff_compatibleCLM_comp_iff`, from Tau Ceti's
   `Manifold.IsSmoothEmbedding.contMDiff_iff_comp`). The range of its
   differential at `J` is Tau Ceti's `compatibleTangentSpace ω J`, read in
   `V →L[ℝ] V`. This is the milestone's submanifold statement. Every
   formula of the milestone is then stated on *ambient readings*: for a
   tangent vector `a` at `J`, its reading is
   `Ĵ = mfderiv 𝓘 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J a`.
4. **The complex structure, and integrability from the Cayley chart.** In
   Cayley coordinates $J=J_0(1+C)(1-C)^{-1}$ the differential is
   $\dot C\mapsto 2J_0(1-C)^{-1}\dot C(1-C)^{-1}$, and since $C$ and $\dot C$
   anticommute with $J_0$, it carries $\dot C\mapsto-J_0\dot C$ to
   $\hat J\mapsto -J\hat J$. So the structure $\hat J\mapsto-J\hat J$ of the
   milestone is, in the global chart, the *constant* linear structure
   $-J_0\cdot$ of the model. It is defined that way
   (`ω.compatibleSpaceComplexStructure`), and the book's formula is the
   lemma `mfderiv_compatibleCLM_compatibleSpaceComplexStructure`. The global
   chart is then a chart in which the structure is constant, which is
   *Nijenhuis tensor*'s `IsIntegrable` at once, and `IsKahler` follows from
   `IsIntegrable.nijenhuis_eq_zero`. The Cayley chart is the bounded model
   of $\mathcal S_n$ (the Siegel disc), so this is the page's advice, to
   obtain integrability from holomorphic coordinates rather than from Lemma
   4.2.5 and the integrability theorem, carried out in the chart the
   manifold already has. `DESIGN.md` §28 said the coordinates of
   $\mathcal S_n$; this file changes that line. The diffeomorphism with
   $\mathcal S_n$ is still proved holomorphic, as the milestone's last item.
5. **The curvature convention** (the first question). The curvature is Tau
   Ceti's `CovariantDerivative.curvatureTensor`, whose convention is Lee's
   (*Introduction to Riemannian Manifolds*, 2nd ed., Ch. 7):
   $R(X,Y)Z=\nabla_X\nabla_YZ-\nabla_Y\nabla_XZ-\nabla_{[X,Y]}Z$, with
   Mathlib's `VectorField.mlieBracket`, the usual bracket. This is the
   convention under which the page checked the formula
   $R(\hat J_1,\hat J_2)\hat J_3=-\tfrac14[[\hat J_1,\hat J_2],\hat J_3]$, so
   the formula is stated with no change of sign. The sectional curvature is
   Tau Ceti's `CovariantDerivative.sectionalCurvature`,
   $\langle R(u,v)v,u\rangle/\det\mathrm{Gram}(u,v)$. Then
   $\langle R(u,v)v,u\rangle=\tfrac18\operatorname{tr}([\hat u,\hat v]^2)$,
   which is $\le0$ because the commutator of two $g_J$-self-adjoint maps is
   $g_J$-skew-adjoint, and the Gram determinant is $\ge0$. The quotient is
   therefore $\le 0$ for *all* `u v`, dependent pairs included, so the
   statement needs no independence hypothesis. (These formulas, the
   Christoffel map of decision 7 and the Siegel formulas of decision 9 were
   checked numerically on `StdSpace (Fin 2)` while writing this file.)
6. **The form and the metric.** $\Omega$ is the pull-back along
   `compatibleCLM` of an ambient two-form on `V →L[ℝ] V`,
   `ContinuousLinearMap.traceTwoForm V`, whose value at $A$ is
   $(X,Y)\mapsto\tfrac14(\operatorname{tr}(XAY)-\operatorname{tr}(YAX))$. On
   $T_J$ the two traces are opposite, so the pull-back is
   $\tfrac12\operatorname{tr}(\hat J_1J\hat J_2)$. Closedness comes from
   naturality of $d$: in the vector space, $d$ of the ambient form at $A$ is
   $(X,Y,Z)\mapsto\tfrac34\operatorname{tr}(X[Z,Y])$, and on $T_J$ this
   vanishes, since $X$ anticommutes with $J$ while $[Z,Y]$ commutes with it,
   and the trace of such a product is zero. This replaces the book's route
   through Lemma 4.2.5 and the Levi-Civita connection; it is a choice of
   proof, not an error, and needs no entry in `ERRATA.md`. Compatibility of
   $\Omega$ with $\hat J\mapsto-J\hat J$ is
   $\Omega(\hat J_1,-J\hat J_2)=\tfrac12\operatorname{tr}(\hat J_1\hat J_2)$
   and positivity of $\operatorname{tr}(\hat J^2)$ for a nonzero
   $g_J$-self-adjoint $\hat J$. The metric is then *Almost complex
   manifolds*' `TauCeti.SmoothTwoForm.Compatible.metric` of the compatible
   pair, $g(a,b)=\Omega(a,J b)$, which is the page's and `DESIGN.md`'s
   convention $g_J(v,w)=\omega(v,Jw)$; the trace formula is a lemma. It is
   installed as a global `RiemannianBundle` instance on the tangent bundle
   of `𝒥 ω`, as Tau Ceti does for its model geometries (`Riemannian/Nil/`,
   `Riemannian/SL2Tilde/`), because it is the canonical metric of the space
   and Tau Ceti's geodesic API reads the Levi-Civita connection from that
   instance. `DESIGN.md`'s rule of local instances concerns the metric $g_J$
   of a pair on an arbitrary manifold, and is unaffected; §28 of `DESIGN.md`
   records this exception.
7. **The connection.** In the global chart the Levi-Civita connection is the
   flat derivative plus the symmetric Christoffel map
   $\Gamma_C(a,b)=aKb+bKa$ with $K=C(1-C^2)^{-1}$, which lies in the model
   because $K$, like $C$, anticommutes with $J_0$ and is self-adjoint for
   $g_{J_0}$. The
   connection is built as Mathlib's `CovariantDerivative.addOneForm` of the
   flat connection of the chart by $\Gamma$. It is torsion free because
   $\Gamma$ is symmetric, and metric because the extra term
   $-\tfrac12J(\hat X\hat Y+\hat Y\hat X)$ of its ambient reading commutes
   with $J$, so it is orthogonal to $T_J$ for the trace form. Mathlib's
   `IsLeviCivitaConnection.uniqueness` identifies it with
   `leviCivitaConnection 𝓘 (𝒥 ω)`. Its ambient reading is the book's formula
   $\widehat{\nabla_XY}=D_X\hat Y-\tfrac12J(\hat Y\hat X+\hat X\hat Y)$, and
   along a curve
   $\widehat{\nabla_tW}=\partial_t\hat W-\tfrac12J(\hat W\dot J+\dot J\hat W)$.
   The curvature is computed from the ambient reading, not from $\Gamma$: in
   $R(X,Y)Z$ every term with a derivative of a field cancels, by symmetry of
   the second derivative of the chart's inverse (which gives
   $\widehat{[X,Y]}=D_X\hat Y-D_Y\hat X$), and the remaining terms reduce to
   $-\tfrac14[[\hat X,\hat Y],\hat Z]$ using $D_XJ=\hat X$ and the
   anticommutation of $\hat X,\hat Y,\hat Z$ with $J$.
8. **Geodesics and completeness.** The geodesic through `J` with velocity
   $\hat J$ is Tau Ceti's exponential path: `tangentPath` is
   $e^{tB}Je^{-tB}$ with $B=\tfrac12J\hat J$, and since $B$ anticommutes with
   $J$, $e^{tB}J=Je^{-tB}$, so it is $J\exp(-J\hat Jt)$, the book's form.
   That identity is a new lemma. With $A=-J\hat J$ one has $\dot J(t)=J(t)A$,
   $\ddot J(t)=J(t)A^2$ and $J(t)\dot J(t)^2=J(t)A^2$, so the ambient
   acceleration $\ddot J-J\dot J^2$ vanishes. The curve is defined on all of
   `ℝ`, which gives Tau Ceti's `IsGeodesicallyCompleteAt` at every point.
   These curves are all the geodesics: by Tau Ceti's uniqueness lemmas
   `IsGeodesicCurveOnFrom.eq_maximalGeodesic_of_univ` and
   `IsGeodesicCurveOnFrom.eqOn_maximalGeodesic`, the maximal geodesic with
   initial data $(J,\hat J)$ is this curve, and any geodesic on an open
   interval around $0$ with the same initial data agrees with it there. The
   page's completeness of the metric is then Tau Ceti's Hopf–Rinow theorem
   `completeSpace_iff_isGeodesicallyCompleteAt`, for the Riemannian distance
   `EMetricSpace.ofRiemannianMetric`. Tau Ceti's
   `completeSpace_ofRiemannianMetric_of_isPretransitive_isom`, with
   transitivity of the isometries of decision 10, is a second route.
9. **$\mathcal S_n$ as a complex manifold.** `SiegelUpperHalfSpace ι` gets the
   complex manifold structure of an open subset of the complex symmetric
   matrices, through `IsOpenEmbedding.singletonChartedSpace`. The model is
   Mathlib's submodule of symmetric matrices,
   `selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)`, whose membership
   lemma `mem_selfAdjointMatricesSubmodule` reduces to `IsSymm` by `simp`.
   The chart is the merged open embedding `toSymm`, composed with the
   homeomorphism of `{Z // Z.IsSymm}` onto that submodule given by Mathlib's
   `Homeomorph.subtype` of the identity; no second inclusion is added.
   Matrices carry the $L^\infty$ operator norm
   `Matrix.Norms.Operator`, which the Siegel part's smoothness lemmas use, so
   they apply without a change of norm; the smooth structure does not depend
   on the norm, but an instance must name one. The model is a complex normed
   space, so Tau Ceti's `ofComplexManifold` gives the almost complex
   structure $\hat Z\mapsto i\hat Z$. The milestone's diffeomorphism is
   `compatibleEquiv` with its smooth structure. Holomorphy and the metric
   formula are proved from the derivative of the block formula
   $J(Z)$ at a general $Z$, by two matrix identities:
   $dJ_Z(i\hat Z)=-J(Z)\,dJ_Z(\hat Z)$ and
   $\tfrac12\operatorname{tr}(dJ_Z(\hat Z)^2)=
   \operatorname{tr}((Y^{-1}\hat X)^2+(Y^{-1}\hat Y)^2)$. The building issue
   may instead reduce both to $Z=i\mathbb 1$ by equivariance, if the direct
   identities are unwieldy in Lean; the statements do not change.
10. **Invariance.** A linear symplectomorphism $\Psi$ acts on `𝒥 ω` by Tau
    Ceti's `AlmostComplexStructure.transport`, which preserves compatibility
    (`compatible_transport_iff` with `isSymplectomorphism_iff_transport_eq`).
    Its ambient reading is $A\mapsto\Psi A\Psi^{-1}$, a continuous linear map
    of `V →L[ℝ] V`, so it is a diffeomorphism by decision 3
    (`ω.compatibleTransport`). It is pseudoholomorphic, pulls $\Omega$ back to
    itself (the ambient trace form is conjugation invariant), and is a
    Riemannian isometry. These maps act transitively, by
    `compatible_iff_exists_isSymplectomorphism_stdForm` of *Compatible complex
    structures* applied to two compatible structures.
11. **Dimension zero and odd dimension.** A symplectic `V` has even dimension
    (`ω.even_finrank`). If `V = 0`, `𝒥 ω` has one point, the model is zero
    and $n(n+1)=0$; no statement needs a case split or `Nonempty`. The
    dimension statement takes `n` with `finrank ℝ V = 2 * n`.
12. **Comparison with `DESIGN.md`.** §28 lists `Manifold.lean`, `Kahler.lean`
    and `Geodesic.lean` in `Geometry/Symplectic/CompatibleSpace/`. Following
    the note of the approving review of #838, the manifold structure follows
    the layout of *Lagrangian Grassmannian*: it is
    `Geometry/Manifold/Instances/CompatibleComplexStructures.lean`, with its
    linear algebra under `LinearAlgebra/Symplectic/CompatibleTangent/` and
    its topology in `Topology/ComplexStructure/Compatible/Cayley.lean`, next
    to *Compatible complex structures*' files there. The complex manifold
    $\mathcal S_n$ is `Geometry/Manifold/Instances/SiegelUpperHalfSpace.lean`.
    `Kahler.lean` and `Geodesic.lean` stay in
    `Geometry/Symplectic/CompatibleSpace/`; their content is split, by size,
    into `ComplexStructure.lean`, `Kahler.lean`, `LeviCivita.lean`,
    `Curvature.lean`, `Geodesic.lean` and `Siegel.lean`. The part also uses
    *Almost complex manifolds*' `AlmostComplex/Metric.lean` (decision 6),
    a level-0 part, so the part stays at level 1. This pull request records
    the files, that dependency and decision 4 in §28 and in the build-order
    row.

## Files and their contents

### `LinearAlgebra/BilinearForm/SelfAdjoint.lean`

The self-adjoint counterpart of Tau Ceti's
`LinearMap.BilinForm.trace_mul_self_nonpos_of_posDef`, which
`Compatible.trace_mul_self_pos` below needs:
`LinearMap.BilinForm.trace_mul_self_nonneg_of_posDef` and
`LinearMap.BilinForm.trace_mul_self_pos_of_posDef`, for an endomorphism
self-adjoint for a symmetric positive-definite form `B` over an ordered field.

### `LinearAlgebra/Symplectic/CompatibleTangent/Basic.lean`

The tangent spaces as algebra, in `Module.End ℝ V` for `V` a finite-dimensional
real vector space, in the namespaces of Tau Ceti's notions. Imports
Mathlib, Tau Ceti and `LinearAlgebra/BilinearForm/SelfAdjoint.lean`.

- `TauCeti.AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace
  (hY : Y ∈ J.tangentSpace) (hW : Commute W J.toLinearMap) :
  LinearMap.trace ℝ V (Y * W) = 0`: conjugating by `J` changes the sign of
  `Y` and fixes `W`. Used for closedness, for metric compatibility of the
  connection, and for the curvature.
- `TauCeti.SymplecticForm.Invariant.mul_mem_compatibleTangentSpace
  (h : ω.Invariant J) (hY : Y ∈ ω.compatibleTangentSpace J) :
  J.toLinearMap * Y ∈ ω.compatibleTangentSpace J`, from Tau Ceti's
  `Invariant.mul_mem_tangentSpace_and_isSelfAdjoint` and
  `mem_compatibleTangentSpace_iff_isSelfAdjoint`. It makes
  $\hat J\mapsto-J\hat J$ an endomorphism of $T_J$.
- `TauCeti.AlmostComplexStructure.trace_mul_mul_eq_neg_of_mem_tangentSpace
  (hY : Y ∈ J.tangentSpace) (Z) :
  trace (Y * J * Z) = -trace (Z * J * Y)` (alternation of $\Omega$). It needs
  neither compatibility nor a hypothesis on `Z`.
- `TauCeti.SymplecticForm.Compatible.trace_mul_self_pos (hJ : ω.Compatible J)
  (hY : Y ∈ ω.compatibleTangentSpace J) (h0 : Y ≠ 0) : 0 < trace (Y * Y)`:
  `Y` is self-adjoint for the inner product $g_J$, so `trace (Y * Y)` is the
  sum of the squares of its entries in a $g_J$-orthonormal basis.
- `TauCeti.SymplecticForm.Compatible.trace_commutator_sq_nonpos`:
  `trace (⁅Y, Z⁆ * ⁅Y, Z⁆) ≤ 0` for `Y Z` in the tangent space (the
  commutator is $g_J$-skew-adjoint).
- `TauCeti.SymplecticForm.IsSymplectomorphism.conj_mem_compatibleTangentSpace_iff`:
  for a linear symplectomorphism `e : V ≃ₗ[ℝ] W` from `ω` to `ω₂`,
  `e.conj Y ∈ ω₂.compatibleTangentSpace (J.transport e) ↔ Y ∈ ω.compatibleTangentSpace J`.

### `Algebra/Star/Module.lean`

`selfAdjoint.instModuleFinite`: `Module.Finite R (selfAdjoint A)` for a finite
star module `A` over a Noetherian ring `R` with trivial star, through Mathlib's
`selfAdjoint.submodule`. `Finrank.lean` imports it for the finiteness of
`selfAdjoint (Matrix ι ι ℝ)`.

### `LinearAlgebra/Symplectic/CompatibleTangent/Finrank.lean`

- `TauCeti.SymplecticForm.Compatible.finrank_compatibleTangentSpace
  (hJ : ω.Compatible J) (hn : Module.finrank ℝ V = 2 * n) :
  Module.finrank ℝ (ω.compatibleTangentSpace J) = n * (n + 1)`.

  Proof: `compatible_iff_exists_isSymplectomorphism_stdForm` (with
  `ι = Fin n`) moves `(ω, J)` to `(stdForm, stdComplexStructure)` and, by the
  conjugation lemma above, the tangent space to the one at $J_0$. There a
  linear equivalence `stdTangentEquiv ι : selfAdjoint (Matrix ι ι ℝ) ×
  selfAdjoint (Matrix ι ι ℝ) ≃ₗ[ℝ] (stdForm ι).compatibleTangentSpace
  (stdComplexStructure ι)` sends `(X, Y)` to the map of
  `fromBlocks X (-Y) (-Y) (-X)`; the dimension is twice
  `Matrix.finrank_selfAdjoint` (*Lagrangian Grassmannian*'s merged
  `LinearAlgebra/Matrix/SelfAdjoint.lean`). The equivalence is in the
  namespace `SymplecticGeometry`, since it involves `StdSpace`.

### `Topology/ComplexStructure/Compatible/Cayley.lean`

Cayley coordinates as an open embedding. For `V` a finite-dimensional real
normed space:

- `TauCeti.SymplecticForm.compatibleTangentSpaceCLM ω J : Submodule ℝ (V →L[ℝ] V)`,
  the comap of `compatibleTangentSpace ω J` along
  `ContinuousLinearMap.coeLM ℝ`, with `mem_compatibleTangentSpaceCLM`
  (`@[simp]`).
- `TauCeti.SymplecticForm.isOpen_setOf_strictContraction ω J₀ :
  IsOpen {C : V →L[ℝ] V | ∀ v, v ≠ 0 → ω (C v) (J₀ (C v)) < ω v (J₀ v)}`,
  with no tameness hypothesis: the condition is positivity on the diagonal of
  the form $\omega(v,J_0w)-\omega(Cv,J_0Cw)$, which depends continuously on
  `C` (Tau Ceti's `isOpen_setOf_forall_bilinear_apply_self_pos`).
- `TauCeti.SymplecticForm.Compatible.cayleyCoord (h₀ : ω.Compatible J₀) :
  𝒥 ω → ω.compatibleTangentSpaceCLM J₀`, `J ↦ J₀.cayley J` read as a
  continuous map, with `coe_cayleyCoord`, `cayleyCoord_self` (`J₀ ↦ 0`),
  `range_cayleyCoord` (the strict contractions of the model, an open set),
  `toContinuousLinearMap_eq_of_cayleyCoord_eq`
  (the inverse is `C ↦ J₀ (1 + C) (1 - C)⁻¹`, from
  `compatibleCayleyEquiv_symm_apply_toContinuousLinearMap`) and
  `Compatible.isOpenEmbedding_cayleyCoord`, from continuity of both
  directions (`AlmostComplexStructure.toContinuousLinearMap_cayley`,
  `contMDiffAt_cayleyFormula_of_isUnit`, `contMDiffAt_mul_one_add_ringInverse`).
- `TauCeti.SymplecticForm.compatibleBase ω : 𝒥 ω`, chosen from
  `ω.exists_compatible`, and `TauCeti.SymplecticForm.compatibleModel ω :=
  ω.compatibleTangentSpaceCLM (ω.compatibleBase : AlmostComplexStructure V)`,
  with `compatibleModel_def` and `compatibleBase_def`.

### `Analysis/Calculus/FDeriv/Cayley.lean`

A general file that serves `CompatibleComplexStructures.lean`; imports
Mathlib. `SymplecticGeometry.hasFDerivAt_mul_one_add_ringInverse`: in a
normed algebra with summable geometric series, `x ↦ A (1 + x) (1 - x)⁻¹` has
derivative $\dot X\mapsto2A(1-C)^{-1}\dot X(1-C)^{-1}$ at `C` with `1 - C`
invertible.

### `Geometry/Manifold/Instances/CompatibleComplexStructures.lean`

The manifold, in `TauCeti.SymplecticForm`. Besides Mathlib, Tau Ceti,
`CompatibleTangent/Finrank.lean` and `Compatible/Cayley.lean`, it imports
`Analysis/Calculus/FDeriv/Cayley.lean` and *Linear complex structures*'
`Topology/ComplexStructure/Basic.lean`.

- `instance : ChartedSpace ω.compatibleModel (𝒥 ω)` and
  `instance : IsManifold 𝓘 n (𝒥 ω)` for every `n`, from the open embedding
  `ω.cayleyChart : 𝒥 ω → ω.compatibleModel`, the map
  `ω.compatibleBase.2.cayleyCoord` with values in the model
  (`isOpenEmbedding_cayleyChart`). API: `chartAt_eq` (the chart is
  `ω.cayleyChart`), `compatibleCLM_chartAt_symm_apply` (on the chart's
  target, `compatibleCLM` of the inverse chart is `J₀ (1 + C) (1 - C)⁻¹`).
- `ω.compatibleCLM : 𝒥 ω → V →L[ℝ] V`, with `compatibleCLM_apply`, and
  `contMDiff_compatibleCLM`.
- `hasMFDerivAt_compatibleCLM_chartAt_symm`: in the chart, the ambient
  reading has derivative $\dot C\mapsto2J_0(1-C)^{-1}\dot C(1-C)^{-1}$ at
  `C`; `injective_mfderiv_compatibleCLM`;
  `range_mfderiv_compatibleCLM (J : 𝒥 ω) : LinearMap.range (mfderiv 𝓘
  𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J) = ω.compatibleTangentSpaceCLM J`, from
  Tau Ceti's `mem_compatibleTangentSpace_of_hasFDerivAt` (inclusion),
  injectivity and the two dimensions of `Finrank.lean`.
- `ω.compatibleTangentEquiv J : TangentSpace 𝓘 J ≃L[ℝ] ω.compatibleTangentSpaceCLM J`,
  the differential onto its range, with `coe_compatibleTangentEquiv_apply`.
- `isSmoothEmbedding_compatibleCLM : Manifold.IsSmoothEmbedding 𝓘
  𝓘(ℝ, V →L[ℝ] V) n ω.compatibleCLM` for every `n`, from
  `ContMDiff.isImmersion_of_injective_mfderiv` and Tau Ceti's
  `isEmbedding_toContinuousLinearMap` restricted to the subtype;
  `contMDiff_compatibleCLM_comp_iff` and `contMDiffAt_compatibleCLM_comp_iff`.
- `finrank_compatibleModel (hn : finrank ℝ V = 2 * n) :
  Module.finrank ℝ ω.compatibleModel = n * (n + 1)`.
- `ω.compatibleTransport (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv) :
  𝒥 ω ≃ₘ⟮𝓘, 𝓘⟯ 𝒥 ω`
  for `Ψ : V ≃L[ℝ] V`, `J ↦ J.transport Ψ.toLinearEquiv`, with `compatibleCLM_compatibleTransport`
  (`Ψ A Ψ⁻¹`), `mfderiv_compatibleCLM_compatibleTransport` (the reading of
  its differential is conjugation by `Ψ`) and
  `exists_compatibleTransport_eq (J J' : 𝒥 ω)` (transitivity, decision 10).

### `Geometry/Manifold/ContMDiff/Submodule.lean`

A general file that serves `SiegelUpperHalfSpace.lean`; imports Mathlib and
Tau Ceti's `Geometry/Manifold/SmoothEmbedding/Basic.lean`.
In `Submodule.ClosedComplemented`:

- `contMDiff_iff_subtypeL_comp` (with its `WithinAt`, `At` and `On` forms):
  for `p.ClosedComplemented`, a map into `p` is `C^n`, for every `n`, exactly
  when its composite with `p.subtypeL` is; `p` may be a submodule over a ring
  other than the field of smoothness, through a scalar tower.

### `Geometry/Manifold/Instances/SiegelUpperHalfSpace.lean`

With `open scoped Matrix.Norms.Operator` and Tau Ceti's
`Matrix.linftyOpTopologicalSpace` as a local instance, in
`SymplecticGeometry.SiegelUpperHalfSpace`:

writing `𝒮ι` for `selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)` (a local
notation of the file):

- `instance : ChartedSpace 𝒮ι (SiegelUpperHalfSpace ι)`, from
  `isOpenEmbedding_toSymm` composed with the homeomorphism of decision 9,
  `instance : IsManifold 𝓘(𝕜, 𝒮ι) n _` for every `n` and every
  `[NormedAlgebra 𝕜 ℂ]`, which gives the complex and the real structure;
  `chartAt_eq`;
- `contMDiff_coe`, `contMDiff_iff_coe_comp` (smoothness of maps in and out,
  read through the inclusion into matrices).

### `Geometry/Symplectic/CompatibleSpace/ComplexStructure.lean`

- `ω.compatibleModelComplexStructure : AlmostComplexStructure ω.compatibleModel`,
  `C ↦ -J₀ C` (well defined by `Invariant.mul_mem_compatibleTangentSpace`).
- `ω.compatibleSpaceComplexStructure : SmoothAlmostComplexStructure 𝓘 (𝒥 ω)`,
  the constant section `compatibleModelComplexStructure` in the global chart.
  API: `compatibleSpaceComplexStructure_apply` (its value in the model) and
  `mfderiv_compatibleCLM_compatibleSpaceComplexStructure : d J (j J a) =
  -(ω.compatibleCLM J ∘L d J a)`, writing `d J` for the differential of
  `compatibleCLM` at `J` and `j` for the structure. The proof is the
  computation of decision 4 in the chart.
- `chartPushforward_compatibleSpaceComplexStructure`: in the global chart the
  pushed-forward structure is `compatibleModelComplexStructure` everywhere;
  `isIntegrable_compatibleSpaceComplexStructure`, with *Nijenhuis tensor*'s
  `IsIntegrable`; `nijenhuis_compatibleSpaceComplexStructure` (`= 0`), by
  `IsIntegrable.nijenhuis_eq_zero`.
- `isPseudoholomorphic_compatibleTransport (hΨ)`: the transport maps of
  `CompatibleComplexStructures.lean` are pseudoholomorphic for this structure.

### `Geometry/Symplectic/CompatibleSpace/Kahler.lean`

- `ContinuousLinearMap.traceTwoForm V : SmoothTwoForm 𝓘(ℝ, V →L[ℝ] V) (V →L[ℝ] V)`,
  in the namespace of Mathlib's `ContinuousLinearMap` since it involves only
  Mathlib's operator space, with `traceTwoForm_apply` (the value
  $\tfrac14(\operatorname{tr}(XAY)-\operatorname{tr}(YAX))$ at `A`),
  `mextDeriv_traceTwoForm_apply` (the formula of decision 6), and
  `traceTwoForm_conj`: invariance under `A ↦ Ψ A Ψ⁻¹` for any `Ψ : V ≃L[ℝ] V`.
- `ω.compatibleSpaceForm : SmoothTwoForm 𝓘 (𝒥 ω)`, the pull-back of
  `traceTwoForm V` along `compatibleCLM` (Tau Ceti's `SmoothForm.mpullback`),
  with `compatibleSpaceForm_apply`:
  $\Omega_J(a,b)=\tfrac12\operatorname{tr}(\hat a J\hat b)$ (as the
  `bilinFormAt` of the form).
- `isClosed_compatibleSpaceForm`, by Tau Ceti's naturality of `mextDeriv`
  under pull-back (`Geometry/Manifold/DifferentialForm/Naturality.lean`) and
  `trace_mul_eq_zero_of_mem_tangentSpace`.
- `compatible_compatibleSpaceForm : ω.compatibleSpaceForm.Compatible
  ω.compatibleSpaceComplexStructure` and
  `isKahler_compatibleSpaceForm : ω.compatibleSpaceForm.IsKahler
  ω.compatibleSpaceComplexStructure`.
- `ω.compatibleSpaceMetric := compatible_compatibleSpaceForm.metric`, the
  `instance : RiemannianBundle (fun J : 𝒥 ω ↦ TangentSpace 𝓘 J)` from it,
  with its `IsContMDiffRiemannianBundle` and `IsContinuousRiemannianBundle`
  instances, and `inner_compatibleSpace (a b : TangentSpace 𝓘 J) :
  ⟪a, b⟫_ℝ = 2⁻¹ * trace (d J a * d J b)`.
- `mpullback_compatibleTransport_compatibleSpaceForm` (`Ω` is invariant) and
  `ω.compatibleTransportIsometry (hΨ) : RiemannianIsometry 𝓘 𝓘 (𝒥 ω) (𝒥 ω)`,
  with `MulAction.IsPretransitive (Isom 𝓘 (𝒥 ω)) (𝒥 ω)`.

### `Geometry/Symplectic/CompatibleSpace/LeviCivita.lean`

- `ω.compatibleChristoffel`, the map $\Gamma$ of decision 7 on the model, with
  its smoothness on the range of the chart, its symmetry, and
  `compatibleChristoffel_mem`.
- `leviCivitaConnection_compatibleSpace_apply`: for a vector field `Y`
  differentiable at `J`, the ambient reading of
  `leviCivitaConnection 𝓘 (𝒥 ω) Y J a` is
  `mfderiv (fun J ↦ d J (Y J)) J a - 2⁻¹ • (ω.compatibleCLM J * (d J (Y J) * d J a + d J a * d J (Y J)))`.
  It is proved for the explicit connection (flat plus $\Gamma$, by
  `CovariantDerivative.addOneForm`), which is torsion free and metric, and
  transferred by `IsLeviCivitaConnection.uniqueness`.
- `alongCurve_leviCivitaConnection_compatibleSpace`: the same formula for a
  field `W` along a curve `γ : ℝ → 𝒥 ω`, with Tau Ceti's
  `CovariantDerivative.alongCurve`, $\partial_t$ being `deriv` of the
  ambient reading of `W` and $\dot J$ the derivative of `compatibleCLM ∘ γ`.

### `Geometry/Symplectic/CompatibleSpace/Curvature.lean`

- `curvatureTensor_leviCivitaConnection_compatibleSpace (a b c) :
  d J ((leviCivitaConnection 𝓘 (𝒥 ω)).curvatureTensor J a b c) =
  -(4⁻¹ : ℝ) • ⁅⁅d J a, d J b⁆, d J c⁆`, by `curvatureTensor_apply` on smooth
  extensions of `a b c` and the computation of decision 7.
- `inner_curvatureTensor_compatibleSpace`: $\langle R(u,v)v,u\rangle=
  \tfrac18\operatorname{tr}([\hat u,\hat v]^2)$, and
  `sectionalCurvature_compatibleSpace_nonpos (u v) :
  sectionalCurvature … J u v ≤ 0`, by `trace_commutator_sq_nonpos` and
  nonnegativity of the Gram determinant.

### `Geometry/Symplectic/CompatibleSpace/Geodesic.lean`

- `TauCeti.AlmostComplexStructure.toContinuousLinearMap_tangentPath_eq_mul_exp
  (hY : Y ∈ J.tangentSpace)`: `tangentPath J Y t` is `J * exp (-(J * Y) * t)`
  (the identity $e^{tB}J=Je^{-tB}$ for $B$ anticommuting with $J$), in Tau
  Ceti's namespace.
- `ω.compatibleGeodesic J a : ℝ → 𝒥 ω`, Tau Ceti's `Compatible.tangentPath`
  with `Y = d J a`, with `compatibleCLM_compatibleGeodesic` (the form
  $J\exp(-J\hat Jt)$).
- `isGeodesicCurveOnFrom_compatibleGeodesic : IsGeodesicCurveOnFrom 𝓘
  (ω.compatibleGeodesic J a) univ J a`, from the ambient formula of
  `LeviCivita.lean` and the computation of decision 8.
- `maximalGeodesic_compatibleSpace : maximalGeodesic 𝓘 (𝒥 ω) J a =
  ω.compatibleGeodesic J a`, by `IsGeodesicCurveOnFrom.eq_maximalGeodesic_of_univ`,
  and `eqOn_compatibleGeodesic (hγ : IsGeodesicCurveOnFrom 𝓘 γ (Ioo s t) J a) :
  EqOn γ (ω.compatibleGeodesic J a) (Ioo s t)`, by
  `IsGeodesicCurveOnFrom.eqOn_maximalGeodesic`: these curves are all the
  geodesics.
- `isGeodesicallyCompleteAt_compatibleSpace (J) :
  IsGeodesicallyCompleteAt 𝓘 (𝒥 ω) J`, and
  `completeSpace_compatibleSpace : letI := EMetricSpace.ofRiemannianMetric 𝓘 (𝒥 ω);
  CompleteSpace (𝒥 ω)`, by Hopf–Rinow.

### `Geometry/Symplectic/CompatibleSpace/Siegel.lean`

For `ι` finite with decidable equality, `V = StdSpace ι`, `ω = stdForm ι`:

- `SiegelUpperHalfSpace.hasFDerivAt_complexStructureMatrix`: the derivative of
  the block formula `complexStructureMatrix` at a matrix with invertible
  imaginary part, in the Siegel part's namespace;
- `SiegelUpperHalfSpace.compatibleDiffeomorph ι : SiegelUpperHalfSpace ι ≃ₘ⟮𝓘(ℝ,
  selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)),
  𝓘(ℝ, (stdForm ι).compatibleModel)⟯
  𝒥 (stdForm ι)`, with underlying map `compatibleEquiv`
  (`coe_compatibleDiffeomorph`), smooth in both directions by
  `contMDiff_compatibleCLM_comp_iff`, `contDiffOn_complexStructureMatrix` and
  `contDiffOn_ofComplexStructureMatrix`;
- `isPseudoholomorphic_compatibleDiffeomorph`, with Tau Ceti's
  `ofComplexManifold` on the source;
- `inner_mfderiv_compatibleDiffeomorph`: the pulled-back metric is
  `trace ((Z.im⁻¹ * Ẑ.re) ^ 2 + (Z.im⁻¹ * Ẑ.im) ^ 2)`, with `Ẑ.re` and
  `Ẑ.im` the real and imaginary parts of the symmetric matrix `Ẑ`;
- the milestone, `TauCeti.SymplecticForm.compatibleSpace_properties`, below.

## The milestone

One theorem in `Siegel.lean`, where its last ingredient is. Writing `d J` for
`mfderiv 𝓘 𝓘(ℝ, V →L[ℝ] V) ω.compatibleCLM J`, `j` for
`ω.compatibleSpaceComplexStructure`, `Ω` for `ω.compatibleSpaceForm` and
`∇` for `leviCivitaConnection 𝓘 (𝒥 ω)` (local notations of the file):

```lean
theorem compatibleSpace_properties (ω : SymplecticForm V) {n : ℕ}
    (hn : Module.finrank ℝ V = 2 * n) :
    Manifold.IsSmoothEmbedding 𝓘 𝓘(ℝ, V →L[ℝ] V) ∞ ω.compatibleCLM ∧
    Module.finrank ℝ ω.compatibleModel = n * (n + 1) ∧
    (∀ J, LinearMap.range (d J) = ω.compatibleTangentSpaceCLM J) ∧
    (∀ J a, d J (j J a) = -(ω.compatibleCLM J ∘L d J a)) ∧
    (∀ J a b, Ω.bilinFormAt J a b =
      2⁻¹ * LinearMap.trace ℝ V (d J a * ω.compatibleCLM J * d J b)) ∧
    (∀ J (a b : TangentSpace 𝓘 J), ⟪a, b⟫_ℝ = 2⁻¹ * LinearMap.trace ℝ V (d J a * d J b)) ∧
    Ω.IsKahler j ∧ j.IsIntegrable ∧
    (∀ (Ψ : V ≃L[ℝ] V) (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv),
      IsPseudoholomorphic j j (ω.compatibleTransport hΨ) ∧
      Ω.mpullback (ω.compatibleTransport hΨ) _ = Ω ∧
      ∀ J (a b : TangentSpace 𝓘 J),
        ⟪mfderiv 𝓘 𝓘 (ω.compatibleTransport hΨ) J a,
          mfderiv 𝓘 𝓘 (ω.compatibleTransport hΨ) J b⟫_ℝ = ⟪a, b⟫_ℝ) ∧
    (∀ (γ : ℝ → 𝒥 ω) (W : Π t, TangentSpace 𝓘 (γ t)) t, … →
      d (γ t) (∇.alongCurve γ W t) =
        deriv (fun s ↦ d (γ s) (W s)) t - 2⁻¹ • (ω.compatibleCLM (γ t) *
          (d (γ t) (W t) * deriv (ω.compatibleCLM ∘ γ) t +
            deriv (ω.compatibleCLM ∘ γ) t * d (γ t) (W t)))) ∧
    (∀ J a, IsGeodesicCurveOnFrom 𝓘 (ω.compatibleGeodesic J a) univ J a ∧
      ∀ t, ω.compatibleCLM (ω.compatibleGeodesic J a t) =
        ω.compatibleCLM J * NormedSpace.exp ℝ (-(t • (ω.compatibleCLM J * d J a)))) ∧
    (∀ J a (γ : ℝ → 𝒥 ω) s t, IsGeodesicCurveOnFrom 𝓘 γ (Ioo s t) J a →
      EqOn γ (ω.compatibleGeodesic J a) (Ioo s t)) ∧
    (∀ J, IsGeodesicallyCompleteAt 𝓘 (𝒥 ω) J) ∧
    (letI := EMetricSpace.ofRiemannianMetric 𝓘 (𝒥 ω); CompleteSpace (𝒥 ω)) ∧
    (∀ J a b c, d J (∇.curvatureTensor J a b c) = -(4⁻¹ : ℝ) • ⁅⁅d J a, d J b⁆, d J c⁆) ∧
    (∀ J u v, ∇.sectionalCurvature _ J u v ≤ 0) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      (∀ Z, SiegelUpperHalfSpace.compatibleDiffeomorph ι Z =
        SiegelUpperHalfSpace.compatibleEquiv Z) ∧
      IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold _ _)
        (stdForm ι).compatibleSpaceComplexStructure
        (SiegelUpperHalfSpace.compatibleDiffeomorph ι) ∧
      ∀ Z Ẑ, ‖mfderiv _ _ (SiegelUpperHalfSpace.compatibleDiffeomorph ι) Z Ẑ‖ ^ 2 =
        Matrix.trace ((Z.im⁻¹ * Ẑ.re) ^ 2 + (Z.im⁻¹ * Ẑ.im) ^ 2)
```

The `…` in the connection conjunct is the differentiability of `γ` and of the
ambient reading of `W` at `t`, which the building issue states as
`alongCurve` needs. The squared norm in the last line is that of the global
instance of `Kahler.lean`. The docstring ends with "Milestone: *Kähler
structure on the space of compatible linear complex structures*."

The statement has the page's hypotheses (a symplectic vector space of
dimension $2n$; for the last item $\mathbb R^{2n}$ with $\omega_0$, for any
finite index type) and its conclusions, in the library's conventions: the
manifold is `𝒥 ω` with the Cayley structure, the submanifold statement is
the smooth embedding with the stated tangent spaces, the dimension is that of
the model, "the metric is complete" is both geodesic completeness and
completeness of the Riemannian distance, and the curvature sign is decision
5's. The invariance, which the page derives rather than takes from the book,
is the conjunct on `compatibleTransport`. No entry in `ERRATA.md` is needed.

## What the part uses

- *Standard model* (merged): `StdSpace`, `stdForm`, `stdComplexStructure`,
  `Matrix.toEuclideanLin` dictionary.
- *Compatible complex structures* (merged):
  `compatible_iff_exists_isSymplectomorphism_stdForm`
  (`LinearAlgebra/Symplectic/Compatible.lean`).
- *Siegel upper half space* (merged): `SiegelUpperHalfSpace`, `toSymm`,
  `isOpenEmbedding_toSymm`, `complexStructureMatrix`,
  `ofComplexStructureMatrix`, `compatibleEquiv` and its two coercion lemmas,
  `contDiffOn_complexStructureMatrix`, `contDiffOn_ofComplexStructureMatrix`,
  `Matrix.isSelfAdjoint_one_iff_isSymm` (`LinearAlgebra/Matrix/Symmetric.lean`);
  and from Mathlib `selfAdjointMatricesSubmodule`,
  `mem_selfAdjointMatricesSubmodule` and `Homeomorph.subtype`.
- *Lagrangian Grassmannian* (merged): `Matrix.finrank_selfAdjoint`
  (`LinearAlgebra/Matrix/SelfAdjoint.lean`).
- *Nijenhuis tensor* (#862, not merged): `IsIntegrable`,
  `IsIntegrable.nijenhuis_eq_zero` (`Geometry/Manifold/Complex/Integrable.lean`).
- *Almost complex manifolds* (#860, not merged):
  `TauCeti.SmoothTwoForm.Compatible.metric` and `Compatible.metric_inner`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean`).
- Tau Ceti: the declarations of *What exists* above; also
  `AlmostComplexStructure.transport`, `compatible_transport_iff`,
  `isSymplectomorphism_iff_transport_eq`, `SymplecticForm.exists_compatible`,
  `SymplecticForm.even_finrank`, `SmoothForm.mpullback` with its naturality
  lemmas, `SmoothForm.bilinFormAt`, `Manifold.IsSmoothEmbedding.contMDiff_iff_comp`,
  `EMetricSpace.ofRiemannianMetric`, `Matrix.linftyOpTopologicalSpace`.
  Models that the building issues credit:
  `Geometry/Manifold/Instances/PositiveDefiniteMatrix.lean` (a matrix
  manifold with a chosen matrix norm), `Riemannian/Nil/Basic.lean` and
  `Riemannian/Nil/Connection.lean` (a global metric instance and its
  Levi-Civita connection in one chart).
- Mathlib: `Topology.IsOpenEmbedding.singletonChartedSpace`,
  `Topology.IsOpenEmbedding.isManifold_singleton`,
  `CovariantDerivative.addOneForm`, `IsLeviCivitaConnection.uniqueness`,
  `leviCivitaConnection`, `NormedSpace.exp`, `LinearMap.trace`,
  `Matrix.Norms.Operator`.

## Building issues

Sub-issues of #872, *Build the part Space of compatible complex structures*,
to be created in this order. The sizes are estimates. An issue may start once
its blockers are merged.

1. **Tangent spaces as algebra.**
   `LinearAlgebra/Symplectic/CompatibleTangent/Basic.lean`, with
   `LinearAlgebra/BilinearForm/SelfAdjoint.lean`. About 200 lines.
   No blockers.
2. **Dimension of the tangent spaces.**
   `LinearAlgebra/Symplectic/CompatibleTangent/Finrank.lean`. About 250 lines.
   Blocked by 1.
3. **Cayley coordinates.** `Topology/ComplexStructure/Compatible/Cayley.lean`.
   About 250 lines. Blocked by 1.
4. **The manifold.** `Geometry/Manifold/Instances/CompatibleComplexStructures.lean`.
   About 450 lines. Blocked by 2 and 3.
5. **The Siegel upper half space as a complex manifold.**
   `Geometry/Manifold/Instances/SiegelUpperHalfSpace.lean`, modelled on
   Mathlib's `selfAdjointMatricesSubmodule (1 : Matrix ι ι ℂ)` through
   `toSymm` (decision 9). About 200 lines.
   No blockers.
6. **The complex structure and its integrability.**
   `Geometry/Symplectic/CompatibleSpace/ComplexStructure.lean`. About 350
   lines. Blocked by 4 and #862.
7. **The Kähler form and the metric.**
   `Geometry/Symplectic/CompatibleSpace/Kahler.lean`. About 450 lines.
   Blocked by 6 and #860.
8. **The Levi-Civita connection.**
   `Geometry/Symplectic/CompatibleSpace/LeviCivita.lean`. About 450 lines.
   Blocked by 7.
9. **The curvature.** `Geometry/Symplectic/CompatibleSpace/Curvature.lean`.
   About 350 lines. Blocked by 8.
10. **Geodesics and completeness.**
    `Geometry/Symplectic/CompatibleSpace/Geodesic.lean`, including the
    uniqueness statements `maximalGeodesic_compatibleSpace` and
    `eqOn_compatibleGeodesic`. About 300 lines.
    Blocked by 8.
11. **The diffeomorphism with the Siegel upper half space, and the
    milestone.** `Geometry/Symplectic/CompatibleSpace/Siegel.lean`. About 400
    lines. Blocked by 5, 9 and 10.

Notes for these issues from the approving review of #838: the layout follows
`Geometry/Manifold/Instances/LagrangianGrassmannian.lean` (decision 12), and
the integrability statement uses `IsIntegrable` from *Nijenhuis tensor*'s
`Integrable.lean` (issue 6, blocked by #862).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.5 (the Cayley transform, Sévennec's proof of Proposition 2.5.13),
  Example 4.3.6 and Exercise 4.3.7.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM
  176, 2018, Chapters 5 and 7, for the conventions of the connection and the
  curvature (not in the plan's `references.bib`; cited in full).
* C. L. Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943), 1–86, for
  the metric on $\mathcal S_n$ (not in the plan's `references.bib`; cited in
  full).
