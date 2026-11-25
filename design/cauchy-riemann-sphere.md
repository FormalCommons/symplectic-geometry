# Cauchy–Riemann operators on the sphere

This is the detailed design of part 45 of `DESIGN.md`, *Cauchy–Riemann
operators on the sphere*. The part has no milestone. It serves *Diffeomorphisms
of the 2-sphere* (part 46), whose milestone *Diffeomorphisms of the 2-sphere
form a trivial principal bundle over the complex structures* needs, for every
almost complex structure $J$ on $S^2$ compatible with the orientation, a
complex plane $E_J$ of smooth sections of a degree-one line bundle, each of
whose nonzero elements has a single, simple zero, and the continuity of
$J\mapsto E_J$ in the $C^\infty$ topology. The plan is
`auxiliary/diffeomorphisms-of-the-2-sphere.md`, the proof of that milestone,
steps 1 and 2, with its formalization notes on step 1 and on the zero count.
The analysis follows McDuff–Salamon [McDuffSalamon2012], Appendices B and C
(real Cauchy–Riemann operators, their Sobolev realization, the a priori
estimate and the Fredholm property). The statement the part serves is the
genus-zero case of Earle–Eells [EarleEells1967]; through part 46 it gives
Smale's theorem [Smale1959].

Paths of new files are under `SymplecticGeometry/`. Tau Ceti paths are
relative to `.lake/packages/TauCeti/TauCeti/`. Every Tau Ceti declaration
named below was checked against the pinned version `c9d170eed5a8`.

## Notation

- $S^2$ is `OnePoint ℂ`, with Tau Ceti's complex manifold structure, and
  $i$ is its complex structure
  `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)`,
  over the model `𝓘(ℝ, ℂ)`.
- $L=\mathcal O(1)$ is Tau Ceti's `OnePoint.twistCore 1`, with fibres
  `(OnePoint.twistCore 1).Fiber x = ℂ`; a section is a function
  `OnePoint ℂ → ℂ`, read in the affine and in the inverted frame
  (`Geometry/Manifold/Instances/OnePoint/LineBundle.lean`).
- The parameter space is `{J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ) // σ.Tames J}`
  for a nondegenerate `σ : TauCeti.SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)` that
  tames $i$, written $\mathcal J_\sigma$, with Tau Ceti's
  `SmoothAlmostComplexStructure.frameTopology e U hU` for any frames
  `e`, `U` covering the sphere (Decision 1).
- $W^{k,2}$ is `TauCeti.SobolevSection A volume 2 k` and its $(0,1)$-forms
  `TauCeti.zeroOneSobolevSections A volume 2 k`, for one finite bundle atlas
  `A` of $L$ fixed once (Decision 3).

## What there is, and what is missing

Tau Ceti has the standard sphere, the operators, their Sobolev spaces and the
Fredholm theory; it lacks the realization for a varying $J$, the a priori
estimate, the regularity of the kernel and everything about $J\ne i$.

- **The bundle and its holomorphic sections.** `OnePoint.twistCore`,
  `OnePoint.contMDiff_section_twistCore_iff`, `OnePoint.identitySection`
  (the section $z$, vanishing only at $0$), `OnePoint.monomialSection`;
  `OnePoint.holomorphicTwistSections` with
  `OnePoint.finrank_holomorphicTwistSections` (dimension $n+1$) and the zero
  count `OnePoint.finsum_twistOrderAt_eq`
  (`Instances/OnePoint/LineBundle/Sections.lean`, `…/Zeros.lean`).
- **Real Cauchy–Riemann operators.**
  `TauCeti.SmoothAlmostComplexStructure.zeroOnePart` and `IsZeroOneForm`
  (`VectorBundle/CauchyRiemann/Basic.lean`);
  `IsCovariantDerivativeOn.isRealCauchyRiemannOperator_zeroOnePart`,
  `IsCovariantDerivativeOn.isComplexLinearOperator_zeroOnePart` and
  `TauCeti.IsRealCauchyRiemannOperator.tensorialAt_sub_zeroOnePart`
  (`…/Connection.lean`); `SmoothAlmostComplexStructure.dbarFunction`
  (`…/Trivial.lean`); local holomorphic frames for the fixed complex
  structure (`…/HolomorphicFrame/`); the holomorphic bundle of a complex
  linear line operator `IsComplexCauchyRiemannLineOperator`
  (`…/LineBundle.lean`), which this part does not need.
- **Connections.** The flat connection of a local frame
  `TauCeti.Manifold.frameCovariantDerivative` with
  `isCovariantDerivativeOn_frameCovariantDerivative`
  (`VectorBundle/CovariantDerivative/LocalFrame.lean`), and gluing by a
  partition of unity,
  `PartitionOfUnity.IsSubordinate.isCovariantDerivativeOn_finsum_smul`
  (`…/CovariantDerivative/Existence.lean`).
- **Sobolev sections** (`VectorBundle/Sobolev/`). The spaces
  `TauCeti.SobolevSection A μ p k`, with the max-norm over charts
  (`Basic.lean`); `TauCeti.FiniteBundleAtlas.nonempty`
  (`FiniteBundleAtlas/Basic.lean`); `zeroOneSobolevSections` with the
  projection `zeroOnePartSobolevL` (`ZeroOneForm.lean`); the realization
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL`, order one to order zero,
  for an operator of the fixed complex structure, with
  `chartValueL_sobolevL_ae` and `chartValueL_sobolevL_sub_ae`
  (`CauchyRiemann.lean`); multiplication by smooth functions
  `SobolevSection.contMDiffSMulL` (`SMul.lean`) and by rough order-zero hom
  sections `SobolevSection.homMulL` (`HomMultiplication.lean`); density of
  smooth sections `SobolevSection.dense_ofContMDiffSection_contMDiff`
  (`Density.lean`); Rellich, `SobolevSection.isCompactOperator_lowerOrderL`
  and `isCompactOperator_zeroOneLowerOrdersL` (`Rellich.lean`,
  `Rellich/ZeroOneForm.lean`); Morrey and the embedding into `Cʲ` chart
  expressions (`Morrey.lean`, `CriticalEmbedding.lean`); independence of the
  atlas, `SobolevSection.atlasEquiv` and `SobolevSection.transfersTo`
  (`AtlasEquiv.lean`). On charts, `TauCeti.Wkp.contDiffOnCLMApplyL`
  (`Analysis/Sobolev/Wkp/SmoothCoefficients.lean`).
- **Fredholm theory** (`Analysis/Fredholm/`, `Analysis/Normed/Operator/`).
  Peetre's argument `ContinuousLinearMap.isClosed_range_of_compact_estimate`
  (`Analysis/Normed/Operator/Compact/Estimate.lean`); along a preconnected
  family of operators with closed range and finite-dimensional kernel into a
  Hilbert space, Fredholmness spreads from one member,
  `ContinuousOn.isFredholm_of_isPreconnected` (`SemiFredholm.lean`); the
  index is then constant, `ContinuousOn.index_eq_of_isPreconnected` and
  `Continuous.index_eq_of_preconnectedSpace` (`ContinuousFamily.lean`);
  `ContinuousLinearMap.index_comp_equiv` and `index_equiv_comp`
  (`Topology/Algebra/Module/ContinuousLinearMap/Index.lean`). Mathlib:
  `ContinuousLinearEquiv.isOpen`, `NormedRing.inverse_continuousAt` (for
  the inverse of an operator near an invertible one) and
  `Submodule.ClosedComplemented.of_finiteDimensional`.
- **The plane.** The $L^2$ Beurling transform `TauCeti.beurlingL2` with
  `norm_beurlingL2_le` and `beurlingL2_toLp_conjWirtingerDerivCLM`, which
  sends $\bar\partial u$ to $\partial u$ for Schwartz $u$
  (`Analysis/Complex/Wirtinger/Beurling/`); Weyl's lemma
  `TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq`
  (`Analysis/Complex/Wirtinger/Weyl.lean`); a local smooth solution of
  $\bar\partial g=f$,
  `TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`
  (`Analysis/Complex/Wirtinger/Potential.lean`).
- **The standard $\bar\partial$ on functions.**
  `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`, on
  `ℙ ℂ (Fin 2 → ℂ)`, carried to `OnePoint ℂ` by
  `OnePoint.diffeomorphProjectivization`
  (`DifferentialForm/Dolbeault/ProjectiveLine/Cohomology.lean`,
  `Instances/OnePoint/Projectivization.lean`).
- **Zeros and the Euler number.**
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`,
  `sectionIndex_eq_analyticOrderNatAt` and `sectionIndex_pos_of_analyticAt`
  (`Topology/VectorBundle/Orientation/SectionIndex/Holomorphic.lean`): over
  a compact oriented surface, the Euler number of an oriented plane bundle
  is the sum of the orders of the zeros of a section that is complex
  analytic in oriented charts and frames.
- **This library.** Isothermal charts for every smooth $J$,
  `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`,
  and `isIntegrable_of_finrank_eq_two`
  (`Geometry/Manifold/Complex/Isothermal.lean`); contractibility of the
  tamed structures,
  `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleSpace_tames`
  (`Geometry/Symplectic/Manifold/AlmostComplex/Contractible.lean`); the
  orientation of a complex curve,
  `SymplecticGeometry.complexManifoldHomologicalOrientation`
  (`Geometry/Manifold/Complex/HomologicalOrientation.lean`), and local
  orientations in centered charts
  (`AlgebraicTopology/Singular/LocalHomology/OrientedChart.lean`).

Missing, and built here: the fixed connection on $L$ and the operators $D_J$;
the realization of a covariant derivative and of a smooth zeroth-order term
on Sobolev sections at every order; a Hilbert norm on $W^{k,2}$; the
$L^2$ estimate for $\bar\partial+\mu\partial$ with $|\mu|<1$ in the plane and
the a priori estimate for $D_J$; the local form of solutions in an
isothermal chart, with the regularity of the kernel and the zero count; the
standard sphere; the index, the dimension of $E_J$, and the continuous family.

## Decisions

These settle the points of *The design file decides* of part 45.

1. **The parameter space.** Results are stated for
   $J\in\mathcal J_\sigma$, for any nondegenerate smooth two-form `σ` that
   tames $i$; part 46 takes its $\mathcal J$ of this form, as the
   conventions *Fibrations, connections and diffeomorphism groups* of
   `DESIGN.md` say. Three facts follow from taming alone. At every point $J$
   is not $-i$: if $J_x v=-i v$ for some $v\ne0$, then $\sigma(v,J_xv)$ and
   $\sigma(v,iv)$ have opposite signs. At every point the complex
   orientations of $J$ and of $i$ on the tangent plane agree, since both are
   the orientation of $\sigma$
   (`TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_toVectorBundleOrientation_volumeOrientation`);
   the first fact does not give this one. And $\mathcal J_\sigma$ is
   contractible, hence preconnected, for every frame topology
   (`contractibleSpace_tames`). Continuity statements are for
   `SmoothAlmostComplexStructure.frameTopology e U hU` with arbitrary
   covering frames, compared with the atlas norms through Tau Ceti's
   `ContMDiffSection.withSeminorms_finiteAtlasSeminorm`
   (`VectorBundle/Section/FiniteAtlas.lean`).
2. **$D_J$, and how it meets Tau Ceti's realization: by the projection, not
   by a complex atlas for $J$.** Fix a complex linear connection $\nabla$ on
   $L$ (Decision 4). The smooth operator is $D_Js=J.\mathrm{zeroOnePart}(\nabla s)$,
   a real Cauchy–Riemann operator for $J$. On Sobolev sections it is
   realized as $\mathcal D_J=\pi^{0,1}_i\circ\Phi_J\circ\nabla$, where
   $\Phi_J$ is the smooth field of endomorphisms
   $\eta\mapsto J.\mathrm{zeroOnePart}\,\eta$ of $\mathrm{Hom}(TS^2,L)$ and
   $\pi^{0,1}_i$ is `zeroOnePartSobolevL`. On a $J$-(0,1)-form, $\pi^{0,1}_i$
   is injective at every point (Decision 1, as the plan's note on the
   constancy of the index says), so $\ker\mathcal D_J$ is the kernel of $D_J$
   itself. Tau Ceti's `sobolevL` is not used: it is the realization of an
   operator that is Cauchy–Riemann for $i$, which $\pi^{0,1}_i\circ D_J$ is
   not, since its Leibniz term is $\pi^{0,1}_i(\bar\partial_Jg)\otimes\xi$.
   For the same reason `chartValueL_sobolevL_sub_ae` and
   `tensorialAt_sub_zeroOnePart`, which compare two operators of one complex
   structure through a zeroth-order term, do not give the continuity in
   $J$: $D_J-D_{J_0}$ is of first order.
   A complex atlas defined by $J$ is rejected too: isothermal charts are not
   chosen continuously in $J$, so the continuity in $J$ would be lost in the
   comparison of the spaces. The continuity of $J\mapsto\mathcal D_J$ in the
   operator norm reduces to that of $J\mapsto\Phi_J$ in $C^k$ on the closed
   chart images, which the frame topology gives.
3. **Sobolev spaces: $p=2$, at every order.** The spaces are
   $W^{k+1,2}(L)\to W^{k,2}(\Lambda^{0,1}_i\otimes L)$ for every `k : ℕ`.
   Order one with $W^{1,p}$, $p>2$, and Morrey would give continuous
   kernels, but not the $C^\infty$ continuity of $J\mapsto E_J$ that part 46
   needs; that needs every order, through the Sobolev embedding of
   `CriticalEmbedding.lean` and `Morrey.lean`. And $p=2$, because Tau Ceti's
   propagation of Fredholmness along a family,
   `ContinuousOn.isFredholm_of_isPreconnected`, needs a Hilbert target; the
   target is made one by a continuous linear equivalence onto a Hilbert
   space (`Sobolev/Hilbert.lean` below), and indices are moved across it by
   `index_equiv_comp`. The atlas is `A := Classical.choice
   (TauCeti.FiniteBundleAtlas.nonempty …)`, fixed once; no comparison
   between atlases is made, so `Sobolev/AtlasEquiv.lean` is not needed.
4. **The connection** is glued from the flat connections
   `frameCovariantDerivative` of the affine and the inverted frame of $L$
   by a smooth partition of unity subordinate to the two charts
   (`isCovariantDerivativeOn_finsum_smul`). Each flat connection is complex
   linear, and its $(0,1)$-part for $i$ reads as `dbarFunction` of the
   coordinate. Since the transition $z\mapsto z^{-1}$ is holomorphic, the
   $(0,1)$-parts of the two agree on the overlap, so $D_i$ reads as
   $\bar\partial$ of the coordinate in both frames, and its smooth kernel is
   `OnePoint.holomorphicTwistSections 1`. Tau Ceti's `CauchyRiemann/LineBundle.lean`
   and `Trivial.lean` were checked: neither gives an operator on
   `twistCore 1`, so none is defined twice.
5. **The a priori estimate.** In a chart of `A` the reading of
   $\mathcal D_J u$ is $c_2(\bar\partial u+\mu\,\partial u)+Zu$, where $c_2$,
   $\mu$ and $Z$ are smooth and $c_2\ne0$; and $|\mu|<1$ at every point.
   Write $\nu$ for the Beltrami coefficient of $J$ in the chart, so that the
   $(1,0)$-forms of $J$ are spanned by $dz+\nu\,d\bar z$. Then
   $\mu=-\nu$, and $|\nu|<1$ exactly where $J$ induces the orientation of
   the chart, $|\nu|>1$ where it induces the other one; $J=-i$ is the limit
   $\nu\to\infty$, so $|\mu|=1$ never occurs. The charts of $A$ are
   `chartAt` of `OnePoint ℂ`, which are holomorphic and so carry the complex
   orientation of $i$, and $J$ induces that orientation by the second fact
   of Decision 1. So the bound comes from taming through the orientation,
   not from $J\ne-i$: the structure $-J'$, for a $J'$ that differs from $i$
   at every point and induces the orientation of $i$, is nowhere $-i$, yet
   $|\mu|>1$ everywhere. On the compact closure of a chart image $\sup|\mu|<1$, and for compactly
   supported $v$ the plane gives
   $\|\partial v\|_{L^2}\le\|\bar\partial v\|_{L^2}$ (the $L^2$ Beurling
   transform has norm one), hence
   $\|\bar\partial v\|_{L^2}\le(1-\sup|\mu|)^{-1}\|\bar\partial v+\mu\,\partial v\|_{L^2}$.
   Cut-offs, the Leibniz rule and induction on the order, applied to the
   derivatives of the chart data, give
   $\|u\|_{W^{k+1,2}}\le C\,(\|\mathcal D_Ju\|_{W^{k,2}}+\|u\|_{W^{k,2}})$,
   with $C$ depending on $J$. With Rellich this gives closed range and
   finite-dimensional kernel at every order, by Peetre's argument. Neither
   the Calderón–Zygmund $L^p$ theory nor the pseudodifferential calculus is
   needed.
6. **Elliptic regularity is needed only for the kernel.** A solution
   $u\in W^{1,2}$ of $\mathcal D_Ju=0$ is smooth. In an isothermal chart of
   $J$ (`exists_isothermal_partialDiffeomorph`) and a frame of $L$, the
   reading $v$ satisfies $\bar\partial v+Bv=0$ weakly, with $B$ smooth;
   with a smooth $g$ such that $\bar\partial g=B$ near the point
   (`exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`), the
   product $e^{g}v$ is weakly holomorphic, hence holomorphic by Weyl's lemma.
   So $u$ is near each point $e^{-g}h$ with $h$ holomorphic: this *local
   form* gives smoothness, and also the zero count (Decision 7). Regularity
   of the inhomogeneous equation is not needed: surjectivity at every order
   follows from the index (Decision 8).
7. **The zero count** is Tau Ceti's
   `evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`, not the
   library's `VectorBundle/ChernNumber/EulerNumber.lean`, which counts
   transverse zeros with signs. Orient $S^2$ by
   `complexManifoldHomologicalOrientation` and $L$ by
   `TauCeti.VectorBundleOrientation.complex`. For a nonzero $s\in E_J$, the
   local form shows that the zeros are isolated (a section vanishing on an
   open set vanishes on the connected sphere), so finite, and that in the
   isothermal chart and the frame rescaled by $e^{g}$ the section is the
   holomorphic $h$. The isothermal chart is orientation preserving because
   $\sigma$ tames both $J$ and $i$, and the rescaled frame keeps the complex
   orientation. So the Euler number of $L$ is the sum of the orders of the
   zeros of $s$, each at least one. Applied to `OnePoint.identitySection`
   for $J=i$, which has one simple zero, the same theorem gives Euler
   number one. Hence $s$ has exactly one zero, of order one.
8. **Index, dimension and surjectivity.** At every order $k$,
   $\mathcal D_i$ is onto: its range is closed (Decision 5) and contains the
   smooth $(0,1)$-forms (`Standard.lean`), which are dense. Its kernel is
   spanned over $\mathbb C$ by the sections $1$ and $z$, of real dimension
   $4$, so its real index is $4$. By Decision 1,
   Decision 5 and `ContinuousOn.isFredholm_of_isPreconnected`, every
   $\mathcal D_J$ is Fredholm, and by
   `Continuous.index_eq_of_preconnectedSpace` its real index is $4$.
   Evaluation at $0$ and $\infty$ is injective on $E_J$, since a nonzero element has only one
   zero, so $\dim_{\mathbb R}E_J\le4$. Hence $\dim_{\mathbb R}E_J=4$,
   $\dim_{\mathbb C}E_J=2$ and $\mathcal D_J$ is onto at every order.
   Indices are real: Tau Ceti's Sobolev spaces are real Banach spaces, and
   $E_J$ is a complex subspace of the smooth sections because $\nabla$ is
   complex linear.
9. **The continuous family: the inverse of a stabilized operator, not Tau
   Ceti's kernel parametrization.** Fix $J_0$ and a continuous projection
   $P$ of $W^{1,2}$ onto $E_{J_0}$ (finite-dimensional, hence complemented).
   At every order $k$, $\mathcal D_J\oplus P$ from $W^{k+1,2}$ to
   $W^{k,2}\times E_{J_0}$ is invertible when $J=J_0$; invertibility is an
   open condition (`ContinuousLinearEquiv.isOpen`), so it holds on some open
   $U_k\ni J_0$, and
   $T_J e=(\mathcal D_J\oplus P)^{-1}(0,e)$ is the unique $s\in E_J$ with
   $Ps=e$, so it does not depend on $k$. As $J\mapsto T_Je$ is continuous on
   $U_k$ into $W^{k+1,2}$ for every $k$, and $W^{k+2,2}$ embeds in $C^k$ on a
   surface,
   $J\mapsto T_Je$ is continuous at $J_0$ into the smooth sections with
   their `ContMDiffSection.frameTopology`. Tau Ceti's
   `ContinuousLinearMap.IsFredholm.exists_continuousOn_ker_parametrization`
   gives a parametrization for one order at a time, chosen by the theorem,
   so the parametrizations at different orders could not be compared; it is
   not used. This is the plan's step 2.

## Departures from `DESIGN.md`

The overview's part 45 is corrected in the same pull request where this file
departs from it: the Sobolev file realizes $D_J$ at every order with $p=2$
and does not go through `sobolevL` (Decisions 2 and 3); the continuous family
is built from the inverse of $\mathcal D_J\oplus P$, not from
`exists_continuousOn_ker_parametrization` (Decision 9); the zero count
uses Tau Ceti's Euler number formula for holomorphic sections instead of
`EulerNumber.lean`, and reads the kernel in isothermal charts of $J$ rather
than through Tau Ceti's `HolomorphicFrame/`, which is for the fixed complex
structure (Decisions 6 and 7); and the index is stated over $\mathbb R$, as
four (Decision 8). The milestone table of `DESIGN.md` lists
`exists_continuousOn_ker_parametrization` among the existing inputs of the
first milestone of part 46; that entry is removed. No dependency between
parts changes: *First Chern number*, which owns `EulerNumber.lean`, was never
among the parts this one builds on.

## Files and their contents

| File | Contents | Issue |
|---|---|---|
| `Geometry/Manifold/VectorBundle/Sobolev/Hilbert.lean` | $W^{k,2}$ and its $(0,1)$-forms are isomorphic to Hilbert spaces | 1 |
| `Geometry/Manifold/VectorBundle/Sobolev/SmoothHomMul.lean` | a smooth section of a hom bundle acting on $W^{k,p}$, with a bound by its $C^k$ norm | 2 |
| `Geometry/Manifold/VectorBundle/Sobolev/CovariantDerivative.lean` | a smooth covariant derivative realized from $W^{k+1,p}$ to $W^{k,p}$ of one-forms | 3 |
| `Analysis/Complex/Wirtinger/Beurling/Estimate.lean` | $\|\partial v\|_2\le\|\bar\partial v\|_2$ and the estimate for $\bar\partial+\mu\partial$ | 4 |
| `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/Basic.lean` | the connection, $D_J$, the projection | 5 |
| `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/Sobolev.lean` | $\mathcal D_J$, continuity in $J$ (issue 6); the a priori estimate, closed range, finite kernel (issue 7); regularity of the kernel (issue 8) | 6, 7, 8 |
| `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/LocalForm.lean` | solutions in an isothermal chart are $e^{-g}h$ with $h$ holomorphic | 8 |
| `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/Standard.lean` | $D_i$: kernel $H^0(\mathcal O(1))$, onto on smooth forms, Fredholm of index $4$ at every order | 9 |
| `Geometry/Manifold/Instances/OnePoint/CauchyRiemann/Kernel.lean` | the zero count (issue 10); index, $\dim_{\mathbb C}E_J=2$, surjectivity (issue 11); the continuous family (issue 12) | 10, 11, 12 |

The first three files are about Tau Ceti's Sobolev sections and nothing of
this part: they sit at Tau Ceti's paths, in Tau Ceti's namespaces, with names
that no Tau Ceti file has, so that they can move upstream as they are. Their
statements are for a manifold modelled on any finite-dimensional real inner
product space and any $1\le p<\infty$ unless they need more.
The files of `OnePoint/CauchyRiemann/` are in the namespace
`SymplecticGeometry`.

### `VectorBundle/Sobolev/Hilbert.lean`

- `TauCeti.SobolevSection.exists_continuousLinearEquiv_innerProductSpace`:
  for `p = 2` and every `k` there are a real Hilbert space `H` and
  `SobolevSection A μ 2 k ≃L[ℝ] H`. The intended route: the norm of
  $W^{k,2}$ is equivalent to one built from the $L^2$ norms of the chart
  components and of their weak derivatives up to order $k$ (the issue checks
  this against `Analysis/Sobolev/Wkp/Basic.lean`), so these, put in a
  `WithLp 2` product of `Lp` spaces, give a map that is bounded below,
  whose range is a closed, hence complete, subspace of a Hilbert space.
- `TauCeti.exists_continuousLinearEquiv_innerProductSpace_zeroOneSobolevSections`:
  the same for `zeroOneSobolevSections A μ 2 k`, a closed subspace.

About 200 lines.

### `VectorBundle/Sobolev/SmoothHomMul.lean`

For bundles `V`, `W`, an atlas `A` of `V` whose chart domains also give the
atlas `A.ofBaseSet h` of `W`, and a smooth section `Φ` of $\mathrm{Hom}(V,W)$:

- `TauCeti.SobolevSection.contMDiffHomMulL A h μ p k hΦ : SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k`,
  built chartwise from `TauCeti.Wkp.contDiffOnCLMApplyL` as
  `SobolevSection.contMDiffSMulL` is from `Wkp.contDiffOnSMulL`; its
  docstring credits that construction.
- `chartValueL_contMDiffHomMulL_ae` and `chartValueL_contMDiffHomMulL_ae_coord`:
  the chart data are $\Phi_i u_i$.
- `exists_norm_contMDiffHomMulL_le`: the operator norm is at most a constant,
  depending on `A`, `h`, `k`, `p`, times the maximum over charts of the
  `C^k` norms of the chart readings of `Φ` on the closed chart images. With
  linearity in `Φ` this gives continuity in `Φ` for the `C^k` atlas norm.

Issue 6 needs only `W = V` with `h = A.closure_dom_subset_baseSet`, where
`A.ofBaseSet h` is `A`, for `V` the bundle
`A.tangentHom` of `ZeroOneForm.lean`; if atlases of two bundles on the same
charts are awkward to state, the issue proves that case alone. About 300
lines.

### `VectorBundle/Sobolev/CovariantDerivative.lean`

- `IsCovariantDerivativeOn.sobolevL`: for a smooth covariant derivative `cov`
  on `V` (`ContMDiffCovariantDerivativeOn F ∞ cov univ`), a continuous linear
  map `SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A.tangentHom μ p k`,
  whose chart data are $du_i+\Gamma_iu_i$, with $du_i$ from the weak
  derivative (`SectionChartData.chartDerivDataL`) and $\Gamma_i$ the chart
  reading of `cov` on the frame of chart `i`. It adapts the proof of
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL`
  (`Sobolev/CauchyRiemann.lean`) from the antilinear part of the derivative
  to the whole derivative and from order one to every order, and its module
  docstring says so.
- `IsCovariantDerivativeOn.chartValueL_sobolevL_ae`, and
  `IsCovariantDerivativeOn.chartValueL_sobolevL_ofContMDiffSection_ae`: on smooth sections
  it is `cov`.

About 350 lines.

### `Analysis/Complex/Wirtinger/Beurling/Estimate.lean`

For `F` a complete complex inner product space:

- `TauCeti.eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv`: for a
  Schwartz function $v$ on `ℂ`, $\|\partial v\|_{L^2}\le\|\bar\partial v\|_{L^2}$,
  from `beurlingL2_toLp_conjWirtingerDerivCLM` and `norm_beurlingL2_le`;
  `TauCeti.HasWeakFDerivOn.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart`
  gives it, by density, for a compactly supported $v$ of class $W^{1,2}$,
  with $\partial v$ and $\bar\partial v$ the complex-linear and
  complex-antilinear parts of a weak derivative in $L^2$.
- `TauCeti.eLpNorm_conjWirtingerDeriv_le_of_norm_le`, and for $W^{1,2}$
  `TauCeti.HasWeakFDerivOn.eLpNorm_complexAntilinearPart_le_of_norm_le`: for a
  measurable $\mu$ with $|\mu|\le m$,
  $(1-m)\|\bar\partial v\|_{L^2}\le\|\bar\partial v+\mu\,\partial v\|_{L^2}$.

Tau Ceti has no weak Wirtinger derivative $\partial$, so the $W^{1,2}$ forms
are stated for `TauCeti.HasWeakFDerivOn`. About 200 lines.

### `OnePoint/CauchyRiemann/Basic.lean`

- `twistOneConnection`, the connection of Decision 4, with
  `isCovariantDerivativeOn_twistOneConnection`,
  `contMDiffCovariantDerivativeOn_twistOneConnection` and its complex
  linearity.
- `twistOneConnection_zeroOnePart_eq`: in the affine and in the inverted
  frame, the $(0,1)$-part for $i$ reads as `dbarFunction` of the coordinate.
- `twistOneDelBar J s := J.zeroOnePart (twistOneConnection s)`, with
  `isRealCauchyRiemannOperator_twistOneDelBar`,
  `isComplexLinearOperator_twistOneDelBar` and its smoothness
  (`ContMDiffCovariantDerivativeOn`).
- `twistOneKernel J : Submodule ℂ (OnePoint ℂ → ℂ)`, the smooth sections
  with `twistOneDelBar J s = 0`, with `mem_twistOneKernel_iff`; this is
  $E_J$.
- Used here from `Geometry/Symplectic/Manifold/AlmostComplex/Tames.lean`,
  in the namespace `TauCeti.SmoothAlmostComplexStructure`:
  `injOn_zeroOnePart_of_tames`: if `σ` tames `J` and `K`, then at every
  point the $(0,1)$-projection for `K` is injective on the $(0,1)$-forms
  for `J` with values in a complex vector bundle, applied with $K=i$; and
  `ne_neg_of_tames` (Decision 1).
- `norm_beltrami_lt_one_of_tames`: if `σ` tames `J` and $i$, then at every
  point of a chart of `A` the Beltrami coefficient $\nu$ of Decision 5 has
  $|\nu|<1$, so that $|\mu|=|\nu|<1$, from the agreement of the complex
  orientations of `J` and $i$ (Decision 1); `ne_neg_of_tames` does not give
  it. Issue 7 uses it.

About 350 lines.

### `OnePoint/CauchyRiemann/Sobolev.lean`

Issue 6:

- `twistOneDelBarSobolev J k : SobolevSection A volume 2 (k + 1) →L[ℝ] zeroOneSobolevSections A volume 2 k`,
  the composite of Decision 2, from issues 2 and 3;
  `chartValueL_twistOneDelBarSobolev_ofContMDiffSection_ae_coord`: on a
  smooth section, its chart data agree a.e. with the chart readings of the
  `(0,1)`-part for $i$ of `twistOneDelBar J`.
- `continuous_twistOneDelBarSobolev`: for every `k`,
  `J ↦ twistOneDelBarSobolev J k` is continuous from $\mathcal J_\sigma$
  with any covering frame topology to the operator norm.

Issue 7:

- `exists_norm_le_twistOneDelBarSobolev`: the estimate of Decision 5, with
  the lower order norm, from `norm_beltrami_lt_one_of_tames`.
- `isClosed_range_twistOneDelBarSobolev` and
  `finiteDimensional_ker_twistOneDelBarSobolev`, by Rellich and
  `isClosed_range_of_compact_estimate`.

Issue 8:

- `contMDiff_of_twistOneDelBarSobolev_eq_zero`: an element of the kernel, at
  any order, is a smooth section (through `toSection`), from
  `LocalForm.lean`; and `ker_twistOneDelBarSobolev_eq`: the kernel is the
  image of `twistOneKernel J`.

About 450 lines in all.

### `OnePoint/CauchyRiemann/LocalForm.lean`

For `J` smooth, an isothermal partial diffeomorphism `ψ` of `J` at `x` and a
frame of $L$ near `x`:

- A section whose coordinates are $W^{1,2}$ near `x` and which solves
  $D_Js=0$ weakly there has, near `ψ x`, the reading $e^{-g}h$ with $g$
  smooth and $h$ holomorphic (Decision 6). Its reading through `ψ` has the
  transported weak derivative by Tau Ceti's change of variables
  `TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`
  (`Analysis/Sobolev/W1p/ChangeOfVariables.lean`), and the weak equation is
  stated with `TauCeti.HasWeakConjWirtingerDerivOn`.
- The same for smooth sections in the kernel, with the frame rescaled by
  $e^{g}$, in the form that the hypotheses `hA` and `ho` of
  `evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt` take.
- The zeros of a nonzero smooth element of `twistOneKernel J` are
  isolated: an element vanishing on a nonempty open set is zero, since the
  set of points near which it vanishes is open and closed in the connected
  sphere.

About 350 lines.

### `OnePoint/CauchyRiemann/Standard.lean`

- `twistOneKernel_ofComplexManifold`: `twistOneKernel i` is
  `OnePoint.holomorphicTwistSections 1`, from Decision 4 and
  `contMDiff_section_twistCore_iff`; so it has complex dimension two.
- `exists_twistOneDelBar_eq`: every smooth $(0,1)$-form for $i$ with values
  in $L$ is $D_i$ of a smooth section. Split the form with a partition of
  unity into a part vanishing near $0$ and a part vanishing near $\infty$;
  divide them by `OnePoint.identitySection` and by the constant section
  `monomialSection 1 0`, which vanish only at $0$ and only at $\infty$; solve
  the two equations on functions with
  `TauCeti.SmoothForm.IsOfType.exists_delBar_eq_projectivization`, carried
  to `OnePoint ℂ` by `OnePoint.diffeomorphProjectivization`; multiply back.
- `twistOneDelBarSobolev_ofComplexManifold_surjective` and
  `isFredholm_twistOneDelBarSobolev_ofComplexManifold` with index $4$, at
  every order (Decision 8).

About 350 lines.

### `OnePoint/CauchyRiemann/Kernel.lean`

Issue 10:

- `eulerNumber_twistCore_one`: the Euler number of $L$, for the orientations
  of Decision 7, is $1$, from `OnePoint.identitySection`.
- `existsUnique_eq_zero_of_mem_twistOneKernel`: for `J` tamed by `σ`, a
  nonzero `s ∈ twistOneKernel J` has exactly one zero; and its order there
  is one, stated as the invertibility of the derivative of the reading of
  `s` in a chart and a frame at the zero
  (`TauCeti.sectionLinearization` is onto).

Issue 11:

- `isFredholm_twistOneDelBarSobolev` and `index_twistOneDelBarSobolev`
  (`= 4`), for every `J` tamed by `σ` and every `k`, through
  `Sobolev/Hilbert.lean` and `ContinuousOn.isFredholm_of_isPreconnected`.
- `finrank_twistOneKernel : finrank ℂ (twistOneKernel J) = 2`, and
  `twistOneDelBarSobolev_surjective`.

Issue 12:

- `exists_continuousAt_twistOneKernelFamily`: for `J₀` there are a
  neighbourhood `U` of `J₀` in $\mathcal J_\sigma$ and maps
  `T J : twistOneKernel J₀ →ₗ[ℂ] (OnePoint ℂ → ℂ)` with
  `T J` an isomorphism onto `twistOneKernel J` for `J ∈ U`, `T J₀` the
  inclusion, and `J ↦ T J e` continuous at `J₀` into
  `Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, (OnePoint.twistCore 1).Fiber⟯` with
  `ContMDiffSection.frameTopology`, for every `e` (Decision 9). The bound of
  `C^k` chart norms by $W^{k+2,2}$ norms is taken from
  `CriticalEmbedding.lean` and `Morrey.lean`; where only the existence of
  `Cʲ` representatives is there, the bound follows from the closed graph
  theorem. Since every `J₀` is covered, part 46 gets continuity at every
  point.

About 700 lines in all.

## What the part uses

- Tau Ceti, as listed under *What there is*.
- This library: *Isothermal coordinates* (`Geometry/Manifold/Complex/Isothermal.lean`),
  *Symplectic vector bundles* (`Geometry/Symplectic/Manifold/AlmostComplex/Contractible.lean`)
  and the orientation files named above.
- Mathlib: as above, with `WithLp` and `MeasureTheory.Lp`.

## Building issues

In this order. All are sub-issues of #2371, *Build the part Cauchy–Riemann
operators on the sphere*. Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Sobolev sections at $p=2$ are isomorphic to Hilbert spaces | `VectorBundle/Sobolev/Hilbert.lean` | — | 200 |
| 2 | Multiplication of Sobolev sections by a smooth hom section, at every order | `VectorBundle/Sobolev/SmoothHomMul.lean` | — | 300 |
| 3 | The Sobolev realization of a smooth covariant derivative | `VectorBundle/Sobolev/CovariantDerivative.lean` | 2 | 350 |
| 4 | The $L^2$ estimate for $\bar\partial+\mu\partial$ in the plane | `Analysis/Complex/Wirtinger/Beurling/Estimate.lean` | — | 200 |
| 5 | The connection on $\mathcal O(1)$ and the operators $D_J$ | `OnePoint/CauchyRiemann/Basic.lean` | — | 350 |
| 6 | $D_J$ on Sobolev sections, continuous in $J$ | `OnePoint/CauchyRiemann/Sobolev.lean` | 2, 3, 5 | 200 |
| 7 | The a priori estimate for $D_J$, closed range and finite kernel | `OnePoint/CauchyRiemann/Sobolev.lean` | 4, 6 | 250 |
| 8 | The local form of solutions, and regularity of the kernel | `OnePoint/CauchyRiemann/LocalForm.lean`, `…/Sobolev.lean` | 6 | 400 |
| 9 | The standard sphere: kernel, surjectivity, Fredholm | `OnePoint/CauchyRiemann/Standard.lean` | 7, 8 | 350 |
| 10 | The zero count | `OnePoint/CauchyRiemann/Kernel.lean` | 8 | 300 |
| 11 | Index four, $\dim_{\mathbb C}E_J=2$, surjectivity | `OnePoint/CauchyRiemann/Kernel.lean` | 1, 7, 9, 10 | 200 |
| 12 | The continuous family of kernels | `OnePoint/CauchyRiemann/Kernel.lean` | 11 | 250 |

Issues 1, 2, 4 and 5 can start at once. Part 46 needs issues 10, 11 and 12.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed.][McDuffSalamon2012], Appendix B (the Cauchy and Beurling
  transforms), Appendix C (real Cauchy–Riemann operators, their Sobolev
  realization, the a priori estimate and the Fredholm property, and
  Riemann–Roch).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd
  ed.][McDuffSalamon2017], Theorem 4.2.6 (integrability on surfaces).
* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967].
* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959].
