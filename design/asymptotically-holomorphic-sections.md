# Asymptotically holomorphic sections

This is the detailed design of part 64 of `DESIGN.md`, *Asymptotically
holomorphic sections*, for §7.4 of `atlas/constructing-symplectic-manifolds.md`
up to the hypersurface theorem. It settles what `DESIGN.md` leaves to this
file:

- how the estimates that depend on $k$ are written;
- how Auroux's avoidance estimate is split into issues;
- which prerequisite issues give a Hermitian line bundle $L$ with
  $c_1(L)=a$ and a unitary connection of curvature $-2\pi i\omega$;
- which issue of *Poincaré duals of submanifolds* `ZeroSet.lean` waits for.

The part proves six milestones: *Symplectic zero set criterion for a line
bundle section*, *Asymptotically holomorphic peak sections*, *Local
quantitative transversality for approximately holomorphic functions*,
*Global uniform transversality of asymptotically holomorphic sections*,
*Lefschetz connectivity of asymptotically holomorphic hypersurfaces* and
*Donaldson's symplectic hypersurface theorem*.

Sources: McDuff–Salamon [McDuffSalamon2017], §7.4 (Theorem 7.4.1,
Lemma 7.4.2); Donaldson [Donaldson1996]; Auroux [Auroux2002] (the
local-to-global scheme, Lemmas 1–2, Propositions 2–3, Theorem 1), Auroux
[Auroux2000] (Propositions 2 and 3: the avoidance estimate and the
separated-cover estimate), Auroux [Auroux1997] (Proposition 2 and §5.1: the
connectivity). These have keys in the plan's `references.bib`. The
prerequisites also follow J. M. Lee, *Introduction to Smooth Manifolds*, 2nd
ed., Theorem 18.14 (the de Rham theorem by Mayer–Vietoris induction), and
A. Hatcher, *Algebraic Topology*, §4.2–4.3 (the Hopf fibration and maps into
$\mathbb CP^N$); module docstrings cite them in full.

All statements about Tau Ceti and Mathlib below were checked against the
pinned versions. Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`.

## The decisions

### The folder

The part's files are in `Geometry/Symplectic/AsymptoticallyHolomorphic/`,
named after the mathematics rather than after Donaldson, as the approving
review of #3195 suggested. `DESIGN.md` is corrected to this folder.

### The setting

Throughout, `M` is a compact, connected, boundaryless smooth manifold
modelled on `EuclideanSpace ℝ (Fin (2 * n))`, with a symplectic form
`ω : TauCeti.SmoothTwoForm I M` (`ω.IsSymplectic`) and an almost complex
structure `J : TauCeti.SmoothAlmostComplexStructure I M` with
`ω.Compatible J` (one exists by Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`).
Its metric $g_J$, with $g_J(u,v)=\omega(u,Jv)$, is Tau Ceti's `TauCeti.SmoothTwoForm.Compatible.metric`.
An integral lift of $[\omega]$ is an element $a$ of $H^2(M;\mathbb Z)$, as the
conventions *Blowups, sums and Donaldson hypersurfaces* of `DESIGN.md` say:
its image in real singular cohomology is `TauCeti.deRhamHom` of $[\omega]$.
Integral classes are read with `ULift ℤ` values, as Tau Ceti's
`TauCeti.complexEulerClass` is, and moved to `ℤ` through the library's
`TopCat.uliftIntegralCohomologyIso` where a statement of *Poincaré duals of
submanifolds* needs it. The coefficient ring of the dual classes is the one
that `design/poincare-duals.md` (#3278) fixes. The statements here follow it.

A Hermitian line bundle is, as in the library's
`Geometry/Manifold/VectorBundle/Hermitian/`, a smooth complex vector bundle
`L` with model fibre `ℂ` and a smooth real bundle metric
`h : Bundle.ContMDiffRiemannianMetric` that multiplication by `Complex.I`
preserves. Its fibres are complex inner product spaces through Tau Ceti's
`h.complexInnerProductSpace hI`. Its unitary frames form the principal
`Circle`-bundle `P` of `Hermitian/CircleBundle.lean`.

### Connections, and the powers $L^{\otimes k}$

A unitary connection on $L$ is a connection form
`α : SmoothForm _ (ManifoldTotalSpace Circle P) ℝ 1` with
`SymplecticGeometry.IsCircleConnectionForm α`, as in the merged
`Principal/CircleConnection.lean`. In the library's normalization the form
takes the value `1` on the fundamental field of `circleLieGenerator`. So
McDuff–Salamon's curvature is $i\,F_\alpha$, and the curvature
$-2\pi i\omega$ of the page is `hα.curvature = -(2 * π) • ω`, a form on the
base. This agrees with `realFirstChernClass_def`: the real class is then
$[\omega]$.

The powers are not iterated tensor products. Neither library has a
connection on a tensor product bundle, and the model fibres of iterated
`TauCeti.ProjectiveTensor`s change type with $k$. Instead,
`L k` is Tau Ceti's associated bundle `TauCeti.AssociatedBundle Circle P ℂ`
for the action $g\cdot z=g^kz$, with the vector bundle structure of
`Topology/VectorBundle/Associated/Basic.lean` and the Hermitian metric of
`Topology/VectorBundle/Associated/Metric.lean`. Its sections are the
functions $u:P\to\mathbb C$ with $u(p\,g)=g^{-k}u(p)$, by Tau Ceti's
dictionary (`Geometry/Manifold/FiberBundle/Associated/Section.lean`). The
connection on `L k` is a Mathlib `CovariantDerivative` on the real bundle
underlying `L k`. In a local unitary frame $\sigma$ of $P$ it is
$d+ik\,\sigma^*\alpha$, and it is complex linear and metric
(`CovariantDerivative.IsMetricCompatible`). Two facts tie `L k` to $L$:
`L 1` is isomorphic to `L`, and `L (k + l)` is isomorphic to Tau Ceti's
tensor product of `L k` and `L l`. With the library's
`TauCeti.complexEulerClass_tensorProduct` (over a compact base) this gives
$c_1(L^{\otimes k})=k\,c_1(L)$.

For a section $s$ of `L k` and a point $x$, $\partial s(x)$ and
$\bar\partial s(x)$ are Tau Ceti's `TauCeti.complexLinearPart` and
`TauCeti.complexAntilinearPart` of $Ds(x):T_xM\to L_x$ (from
`LinearAlgebra/Complex/LinearPart.lean`), for $J_x$ and multiplication by
`Complex.I`. Their norms are operator norms for $g_J$ and $h$. The rescaled
norms of the page, for $g_k=k\Omega(\cdot,J\cdot)$ with $\Omega=2\pi\omega$,
are $(2\pi k)^{-1/2}$ times these. They are written as such factors, and no
metric $g_k$ is introduced.

### How the $k$-dependent estimates are written

The estimates use explicit constants, with `∀ᶠ k in Filter.atTop` for "$k$
large". They do not use `Asymptotics.IsBigO`. The bounds must be uniform in
the centre $x$, the point $y$ and the order $r$ of derivatives at once, and
the iteration over colours chooses its constants in a fixed order ($R$ first,
then $k$). A statement $\exists C,\ \forall^\infty k,\ \forall x\,y,\ \dots\le
C\,k^{-1/2}$ says this directly. An `IsBigO` along `atTop` for functions of
$k$ alone would need a supremum over $x$ and $y$ before it could be stated.

Higher derivatives are measured in charts, not by iterated covariant
derivatives, which would need connections on $L^{\otimes k}\otimes
T^*M^{\otimes r}$ that neither library has. The part builds a family of
**rescaled unitary charts**: for $k\ge k_0$ and every $x\in M$, a chart
$\psi_{k,x}$ from a ball of radius proportional to $\sqrt k$ in `StdSpace (Fin n)`
onto a neighbourhood of $x$, with $\psi_{k,x}(0)=x$ and
$\psi_{k,x}^*(k\Omega)=\omega_0$. Its differential at $0$ is complex linear
for $J_0$ and $J_x$. It comes with a unitary frame of `L k` over its image
whose connection form is exactly the model $A_0$ with curvature
$-i\omega_0$. Such a frame exists because the chart is exactly Darboux.
For any unitary frame $\sigma_0$ over the ball, the connection form in
$\sigma_0$ and $A_0$ have the same curvature. So they differ by a closed,
hence exact, one-form $d\theta$ (the Poincaré lemma), and the frame
$e^{i\theta}\sigma_0$ has connection form $A_0$. No parallel transport is
needed. In it the pulled-back structure $J_{k,x}$
satisfies $\|J_{k,x}-J_0\|\le Ck^{-1/2}|z|$, and each derivative of fixed
positive order is at most $C_rk^{-1/2}$, uniformly in $k$ and $x$. A section
$s$ of `L k` reads in this chart as a function $f_{k,x}:B\to\mathbb C$. Its
**$r$-jet norm at $x$**, `jetNorm k r s x`, is
$\sum_{j\le r}\|D^jf_{k,x}(0)\|$, Mathlib's `iteratedFDeriv` at the centre.
The same is done for $\bar\partial s$, read as the antilinear part of
$df_{k,x}+A_0f_{k,x}$ for $J_{k,x}$. A norm at $y$ always uses the chart
centred at $y$. The page's $C^r$ bounds on balls follow, since a point of a
chart ball is the centre of its own chart and the transition between the
charts at $x$ and $y$ has $C^r$ norms bounded by a polynomial in
$d_k(x,y)$. Here $d_k=\sqrt{2\pi k}\,d_{g_J}$, with $d_{g_J}$ Mathlib's
`Manifold.riemannianEDist` for the metric $g_J$.

With these, a sequence $(s_k)_{k}$ of sections of `L k` is **asymptotically
holomorphic** (`IsAsymptoticallyHolomorphic`) when for every $r$ there is a
$C$ with, for large $k$ and every $x$, `jetNorm k r (s k) x ≤ C` and
`jetNorm k r (∂̄ (s k)) x ≤ C * k ^ (-1/2 : ℝ)`. It is **uniformly
transverse** with constant $\eta>0$ (`IsUniformlyTransverse η`) when for
large $k$ and every $x$,
$\max(|s_k(x)|,(2\pi k)^{-1/2}\|\partial s_k(x)\|)\ge\eta$. These pointwise
quantities need no chart. The definitions depend on the chosen chart family
only through constants. The part proves this independence only where a
proof needs it, namely for two families built by the existence theorem. The
right-inverse form of transversality on the page is not built, since no
milestone states it.

### The class of the line bundle: the prerequisites

Three facts are missing from both libraries, and the part plans them as
prerequisite issues (issues 1–5 below):

1. **The de Rham theorem in degree two.** `TauCeti.deRhamHom` is injective
   on a compact manifold. Without it, an integral lift of $[\omega]$ says
   nothing about de Rham classes, and the curvature of the connection cannot
   be corrected to $-2\pi\omega$. The route is Lee's Mayer–Vietoris
   induction: Tau Ceti's `TauCeti.mayerVietoris_induction`
   (`Topology/MayerVietoris.lean`), its Mayer–Vietoris sequences in de Rham
   (`Geometry/Manifold/DeRham/MayerVietoris.lean`) and smooth singular
   (`Geometry/Manifold/SmoothSingular/MayerVietoris.lean`) cohomology, the
   Poincaré lemma on convex sets (`Geometry/Manifold/DeRham/Euclidean.lean`)
   and `SmoothSingular/Contractible.lean`, with the five lemma at each step.
   It proves bijectivity in every degree, since the induction needs the
   neighbouring degrees.
2. **Integral classes of degree two are first Chern classes.** For a compact
   manifold $M$ and $a\in H^2(M;\mathbb Z)$ there is a smooth Hermitian line
   bundle $L$ with `complexEulerClass L = a`. The route goes through
   classifying maps. $M$ has finite CW type (Tau Ceti's
   `TauCeti.FiniteCWType.of_isManifold`). $\mathbb CP^N$ has $\pi_1=0$,
   $\pi_2=\mathbb Z$ and $\pi_j=0$ for $3\le j\le 2N$, by the long exact
   sequence of the Hopf map, whose total space is $S^{2N+1}$. So for $2N\ge\dim M$ obstruction
   theory over the skeleta gives a map $f:M\to\mathbb CP^N$ with $f^*h=a$.
   It is made smooth up to homotopy by Tau Ceti's
   `ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`
   (`Geometry/Manifold/SmoothApprox/`), and $L$ is the pull-back of Tau
   Ceti's `twistCore 1`, whose Euler class is $h$ by the library's
   `Projectivization.complexEulerClass_twistCore_one`, with
   `TauCeti.complexEulerClass_pullback` and homotopy invariance. Tau Ceti's
   cellular tools for Eilenberg–Mac Lane spaces
   (`AlgebraicTopology/EilenbergMacLane/Extension.lean`, `Uniqueness.lean`)
   and the relative skeleton lemmas
   (`AlgebraicTopology/Homotopy/Relative/Skeleton.lean`) are searched first
   for the extension step.
3. **Chern–Weil in degree two.** For this $L$ and every connection form
   $\alpha$, `deRhamHom (realFirstChernClass P)` is the real image of
   `complexEulerClass L`. Both sides are natural under the smooth map $f$,
   so it suffices to prove it for `twistCore 1` on $\mathbb CP^N$. There
   restriction to a line $\mathbb CP^1$ is injective on $H^2(-;\mathbb R)$,
   and on $\mathbb CP^1$ the merged
   `SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature` gives it.

`LineBundle.lean` then corrects the curvature. Take any connection form
(`SymplecticGeometry.exists_isCircleConnectionForm`). By 1 and 3 its real
class is $[\omega]$, so by
`IsCircleConnectionForm.mk_sub_mk_eq_smul_realFirstChernClass_iff` the
difference from $-2\pi\omega$ is exact. Adding the pull-back of a primitive
(`IsCircleConnectionForm.add_mpullback`, `curvature_add_mpullback`) makes
the curvature exactly $-2\pi\omega$.

*Minimal coupling* (#2265) is still open, but this part uses only its merged
`RealChernClass.lean` and the merged `CircleConnection.lean` and
`Connection/Circle.lean`. So no issue here waits for #2265.

### Auroux's avoidance estimate, split

The local transversality milestone follows Auroux's Proposition 3
[Auroux2002], from the avoidance estimate of Proposition 2 [Auroux2000]. For
a map $G:B^+\subset\mathbb C^n\to\mathbb C^{n+1}$ with bounded $C^1$ norm and
$\|\bar\partial G\|_{C^1}\le\epsilon$, it gives a $w$ with $|w|\le\delta$ at
distance at least $c\,\delta(\log(1/\delta))^{-p_0}$ from $G(B)$. The proof
has four independent steps and one assembly, each an issue (issues 15–19):

- **Holomorphic approximation.** On a polydisc, a $C^1$ function with small
  $\bar\partial$ in $C^2$ is close in $C^1$, on a smaller polydisc, to a
  holomorphic function. The constant times $\|\bar\partial f\|_{C^2}$
  bounds the distance. The route iterates the one-variable Cauchy–Pompeiu
  formula, one coordinate at a time. The boundary term of the last step is
  Tau Ceti's polydisc Cauchy integral
  (`Analysis/Complex/CauchyIntegralPolydisc.lean`), which is holomorphic.
  The area terms are bounded by Tau Ceti's Cauchy transform
  (`Analysis/Complex/Pompeiu/Basic.lean`). This avoids the
  several-variable $\bar\partial$-equation.
- **Polynomial truncation.** A holomorphic function bounded by $1$ on a
  polydisc of radius $\rho$ differs on the polydisc of radius $\rho/2$ from
  its Taylor polynomial of degree $d$ by at most $C_n(d+1)^n2^{-d}$ in $C^1$, by
  Cauchy estimates on the polydisc, which Tau Ceti's polydisc Cauchy
  integral gives.
- **Algebraic dependence.** The image of a polynomial map
  $\mathbb C^n\to\mathbb C^{n+1}$ of degree at most $d$ lies in the zero set
  of a nonzero polynomial of degree at most $C_nd^{\,n}$. This is a
  dimension count. For $D$ of that size, the polynomials of degree $\le D$
  in $n+1$ variables outnumber those of degree $\le Dd$ in $n$ variables,
  so the linear map $Q\mapsto Q\circ P$ has a nonzero kernel. It uses Mathlib's
  `MvPolynomial.restrictDegree` and its rank.
- **Tube volumes.** In the unit ball of $\mathbb C^{m}$, the
  $t$-neighbourhood of the zero set of a nonzero polynomial of degree $D$
  has volume at most $C_m D^{2m}t$ for $t\le1$. Any bound of the form
  $C_mD^at^b$ with $b>0$ suffices, since $D$ grows only as a power of
  $\log(1/\delta)$. The issue follows the bound that Auroux's proof uses.
  It may instead take R. Wongkew's bound for tubes around real algebraic
  varieties (Pacific J. Math. 159, 1993), and it fixes the exponents. The
  bound that uses only the Lipschitz constant of the map is too weak. It
  gives $\epsilon$ of order $\delta^{n+1}$, and the iteration over colours
  needs $\epsilon$ nearly linear in $\delta$.
- **Assembly.** These give the avoidance estimate. The volume of the
  $\delta$-ball of parameters exceeds the volume of the thin neighbourhood
  of the image, after rescaling by $\delta$.

### The zero set file waits for *Poincaré duals*

`ZeroSet.lean` is two issues. The first proves that the section is
transverse and that its zero set is a symplectic submanifold. It waits for
no other part. The second proves the class of the zero set, and with it the
milestone. It waits for the issue that `design/poincare-duals.md` assigns to
`Geometry/Manifold/VectorBundle/ZeroSet/DualClass.lean`. That design is
#3278 and is not merged, so the issue does not exist yet. Until it does, the
second issue is blocked by #3278. The agent who splits #3291 marks it as
blocked by the issue that #3278's design creates for `ZeroSet/DualClass.lean`.

### Connectivity by Tau Ceti's Morse–Bott theory

`Connectivity.lean` follows the page's Morse argument and does not go
through Giroux's Weinstein complement, as `DESIGN.md` says. Near $Z_k$,
$|s_k|^2$ is Morse–Bott with $Z_k$ a critical submanifold of index $0$. Away
from $Z_k$ the critical points have index at least $n$, after a small
perturbation that makes them nondegenerate. Tau Ceti has the tools for
both:

- the Morse–Bott normal form and the attachment across a critical level
  (`Geometry/Manifold/Morse/Bott/Tubular.lean`, `RelCWComplex.lean`, with
  `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_relCWComplex_sublevel_deformation`);
- the relative CW models of regular bands with one cell per critical point
  (`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`,
  `Geometry/Manifold/Morse/CWModel.lean`);
- generic Morse perturbations (`Geometry/Manifold/Morse/Generic/`);
- the connectivity of the inclusion of a relative CW complex without
  low cells (`TauCeti.isNConnected_inclusion_skeletonLT`,
  `AlgebraicTopology/Homotopy/Relative/Skeleton.lean`), stated with Tau
  Ceti's `ContinuousMap.IsNConnected`.

### Nonempty zero sets without cup products

The hypersurface theorem needs $Z_k\ne\emptyset$. The page argues through
the pairing of $a$ with $[\omega]^{n-1}$, which needs the compatibility of
`deRhamHom` with cup products. The library argues instead that a nowhere
zero section of `L k` gives a global unitary frame $\sigma$ of $P$. Then
$d(\sigma^*\alpha)=-2\pi\omega$, so $\omega$ is exact, and so is $\omega^n$.
Its integral over the closed manifold $M$ then vanishes (Tau Ceti's Stokes
theorem), against `TauCeti.SmoothTwoForm.IsSymplectic` and the positivity of
the Liouville volume.

## Files

New files of the part, in `Geometry/Symplectic/AsymptoticallyHolomorphic/`,
and the prerequisites, placed by topic.

### Prerequisites

- `Geometry/Manifold/SmoothSingular/DeRhamTheorem.lean`:
  `TauCeti.bijective_deRhamHom` (for manifolds that have a finite good cover, or
  a second-countable one through `mayerVietoris_induction`),
  `TauCeti.injective_deRhamHom`. If Tau Ceti's `deRhamHom` lands in smooth
  singular cohomology, the file also compares it with continuous singular
  cohomology, unless `SmoothSingular/Smoothing.lean` already does.
- `Geometry/Manifold/Instances/ComplexProjectiveSpace/HomotopyGroups.lean`:
  the Hopf map from $S^{2N+1}$ onto $\mathbb CP^N$ as a Serre fibration (Tau
  Ceti's `Topology/Homotopy/SerreFibration/`), and
  `ComplexProjectiveSpace.subsingleton_homotopyGroup` for $3\le j\le 2N$,
  with $\pi_1=0$ and $\pi_2\cong\mathbb Z$.
- `AlgebraicTopology/Cohomology/ProjectiveSpaceClassifying.lean`: for a
  finite CW complex $X$ of dimension at most $2N$, every class of
  $H^2(X;\mathbb Z)$ is $f^*h$ for some $f:X\to\mathbb CP^N$
  (`exists_continuousMap_projectivization_pullback_eq`).
- `Geometry/Manifold/VectorBundle/Hermitian/Realization.lean`: on a compact
  manifold every integral class of degree two is the Euler class of a smooth
  Hermitian line bundle pulled back from `twistCore 1` along a smooth map
  (`exists_hermitianLineBundle_complexEulerClass_eq`).
- `Geometry/Manifold/VectorBundle/Hermitian/ChernWeil.lean`: for line
  bundles pulled back from `twistCore 1` along smooth maps,
  `deRhamHom (realFirstChernClass IB P)` is the real image of the Euler
  class (`deRhamHom_realFirstChernClass_eq`).
- `LinearAlgebra/Complex/DominantLinearPart.lean`: for a real-linear
  $F=A+B:V\to\mathbb C$ on a Hermitian space $(V,\omega,J)$, with $A$
  complex linear, $B$ antilinear and $\|B\|<\|A\|$, $F$ is surjective, its
  kernel is a symplectic subspace, and its kernel orientation agrees with
  the one induced by $\omega$ (through the path $A+tB$). Main results:
  `surjective_of_norm_lt`, `isSymplectic_ker_of_norm_lt`,
  `orientation_ker_eq_of_norm_lt`.
- `Combinatorics/SimpleGraph/GreedyColoring.lean`: a locally finite graph
  of maximal degree at most $\Delta$ is $(\Delta+1)$-colourable
  (`SimpleGraph.colorable_of_maxDegree_le`). Mathlib has no such bound.
- `Topology/MetricSpace/SeparatedSum.lean`: for a $1$-separated set $S$ in
  a space with the doubling bound $\#(S\cap B(y,r))\le C(1+r)^{2n}$, sums
  $\sum_{x\in S}P(d(x,y))e^{-c\,d(x,y)^2}$ are bounded uniformly in $y$,
  and by $C'e^{-c'R^2}$ over $d(x,y)\ge R$. The proof sums over distance
  shells and uses Tau Ceti's `one_add_pow_mul_exp_neg_mul_sq_le`.
- `Analysis/Complex/Polydisc/HolomorphicApproximation.lean`,
  `Analysis/Complex/Polydisc/TaylorTruncation.lean`,
  `RingTheory/MvPolynomial/ImageHypersurface.lean`,
  `MeasureTheory/Measure/AlgebraicTube.lean` and
  `Analysis/Complex/Avoidance.lean`: the five steps of the avoidance
  estimate above, with main results `exists_differentiableOn_dist_le`,
  `norm_sub_taylorPolynomial_le`, `exists_mvPolynomial_ne_zero_aeval_eq_zero`,
  `volume_thickening_zeroLocus_le` and `exists_infDist_image_ge`.

### Files of the part

- `LineBundle.lean`: `exists_prequantumLineBundle`: for compact $M$ and an
  integral lift $a$ of $[\omega]$, there is a Hermitian line bundle $L$ with
  `complexEulerClass L = a` and a connection form $\alpha$ on its unitary
  frame bundle with `hα.curvature = -(2 * π) • ω`.
- `Power.lean`: `L k`, the associated bundle for $g\cdot z=g^kz$; its
  Hermitian metric; `powerOneEquiv : L 1 ≃ L`, `powerAddEquiv` with Tau
  Ceti's tensor product; `complexEulerClass_power` ($=k\,a$, as `k • _`).
- `PowerConnection.lean`: the connection $D_k$ on `L k` as a Mathlib
  `CovariantDerivative`. It is complex linear and metric, has the local
  formula $d+ik\,\sigma^*\alpha$ in a unitary frame
  (`powerConnection_apply_frame`) and curvature $ik\,F_\alpha$. The file
  also defines $\partial$ and $\bar\partial$ of a section, with
  `partial_add_dbar`.
- `ZeroSet.lean`: for any Hermitian line bundle with a complex-linear
  metric connection $D$ on a closed manifold with compatible $J$:
  `isTransverse_of_norm_dbar_lt` (surjective
  `TauCeti.sectionLinearization` at the zeros, so the zero set is a
  submanifold by Tau Ceti's `exists_isManifold_sectionZero_of_contMDiff`),
  `isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`, and
  the milestone `dualClass_zeroSet_eq_complexEulerClass_of_norm_dbar_lt`:
  with the symplectic orientation, the zero set has dual class
  `complexEulerClass L`, so its fundamental class is $\mathrm{PD}(c_1(L))$.
  At a zero, $Ds$ is the intrinsic linearization for every $D$, so the
  statement holds for every $D$.
- `RescaledChart.lean`: the rescaled unitary charts. `CenteredDarbouxCharts`
  are charts centred at every point with derivative at the centre complex
  linear for $J$, with uniform $C^r$ bounds. They come from finitely many of
  Tau Ceti's `IsSymplectic.exists_standardDarbouxChart_of_isInteriorPoint`
  charts, composed with translations and unitary symplectic linear maps,
  by compactness. `RescaledUnitaryCharts k₀ ρ₀` adds the rescaling and the
  radial-gauge frames, with `jStruct_sub_le`, `iteratedFDeriv_jStruct_le` and
  `connectionForm_eq_model`. The existence theorem is
  `exists_rescaledUnitaryCharts`, and `dist_comparison` compares $d_k$ with
  chart distances.
- `AsymptoticallyHolomorphic.lean`: `jetNorm`, `IsAsymptoticallyHolomorphic`,
  `IsUniformlyTransverse`, closure under sums and under products with
  sequences of bounded functions, and `jetNorm_le_of_chart_change` (a
  polynomial in $d_k(x,y)$ bounds the change between the charts at $x$ and
  $y$).
- `PeakSection.lean`: `peakSection k x` and `peakSection_mul k x j`, the
  cut-off Gaussians $\chi(|z|/k^{1/6})e^{-|z|^2/4}$ and $z_j$ times them in
  the chart at $x$, extended by zero. The milestone
  `exists_peakSection_estimates` gives the lower bound near $x$, and the
  Gaussian bounds: `jetNorm` of the sections at $y$ is at most
  $P_r(d_k(x,y))e^{-c\,d_k(x,y)^2}$, and that of $\bar\partial$ of them at
  most $k^{-1/2}$ times it, uniformly in $k$, $x$ and $y$.
- `LocalTransversality.lean`: the milestone
  `exists_norm_le_max_ge_of_dbar_le`, with $B^+$ of radius $11/10$, $B$ the
  unit ball, $\epsilon=\delta(\log(1/\delta))^{-p}$ and
  $f_w=f-w_0-\sum_jw_jz_j$, as on the page. It is derived from
  `exists_infDist_image_ge` for the map
  $G=(f-\sum_jz_j\partial_jf,\partial_1f,\dots,\partial_nf)$.
- `GlobalTransversality.lean`: the local correction on one ball, by division
  by `peakSection` (`exists_local_correction`), and the iteration over
  colours (`exists_isUniformlyTransverse`, the milestone). The logarithms
  $u_j=\log(1/b_j)$ of the lower bounds obey a recurrence
  $u_j\le u_{j-1}+C_3+p\log(u_{j-1}+\log A)$. The file proves, as a separate
  lemma about real sequences, that such sequences grow at most like
  $(j+1)\log(j+2)$.
- `Connectivity.lean`: `criticalPoint_norm_ge` (at critical points of
  $\log|s_k|^2$, $|s_k|\ge\eta$ for large $k$),
  `hessian_add_hessian_J_neg`, `morseIndex_ge` and the milestone
  `isNConnected_zeroSet_inclusion` ($Z_k\hookrightarrow M$ is
  $(n-1)$-connected, for nonempty $Z_k$ and large $k$).
- `Hypersurface.lean`: the milestone `exists_symplecticHypersurface`: for
  closed connected $M$ of dimension $2n$ with $n\ge2$ and a fixed integral
  lift $a$, for large $k$ there are a closed connected manifold $Z$ and a
  symplectic embedding $i:Z\to M$ of codimension two
  (`ω.IsSymplecticSubmanifoldEmbedding i`) whose image of the fundamental
  class is $(k\,a)\frown[M]$ and whose inclusion is $(n-1)$-connected
  (`ContinuousMap.IsNConnected _ (n - 1)`). The lift is fixed before $k$, as
  the page's notes say. The file also has `zeroSet_nonempty` by the
  argument above.

## Issues

Each issue is a few hundred lines, in an order where each comes after the
ones it waits for. An issue that adds an existing name of Tau Ceti or
Mathlib uses it instead; each prerequisite issue first searches both for its
statement.

1. **The de Rham theorem** (`SmoothSingular/DeRhamTheorem.lean`). Waits for
   nothing. Its agent may split it in two: the Mayer–Vietoris square of
   `deRhamHom` with its connecting maps, then the induction.
2. **Homotopy groups of $\mathbb CP^N$ in low degrees**
   (`ComplexProjectiveSpace/HomotopyGroups.lean`). Waits for nothing.
3. **Classifying maps for $H^2$** (`ProjectiveSpaceClassifying.lean`).
   Waits for 2.
4. **Hermitian line bundles with prescribed $c_1$** (`Realization.lean`).
   Waits for 3.
5. **Chern–Weil in degree two** (`Hermitian/ChernWeil.lean`). Waits for 4.
6. **The prequantum line bundle** (`LineBundle.lean`). Waits for 1, 4 and 5.
7. **Powers of a Hermitian line bundle** (`Power.lean`). Waits for nothing.
8. **The connection on the powers** (`PowerConnection.lean`). Waits for 7.
9. **Real-linear forms with dominant complex-linear part**
   (`DominantLinearPart.lean`). Waits for nothing.
10. **Transverse symplectic zero sets** (`ZeroSet.lean`, without the
    class). Waits for 9.
11. **The class of the zero set** (`ZeroSet.lean`, the milestone). Waits for
    10 and for the issue of *Poincaré duals of submanifolds* for
    `ZeroSet/DualClass.lean`; until #3278 creates it, for #3278.
12. **Centred Darboux charts with uniform bounds** (`RescaledChart.lean`,
    first half). Waits for nothing.
13. **Rescaled unitary charts** (`RescaledChart.lean`, second half). Waits
    for 8 and 12.
14. **Jet norms and asymptotically holomorphic sequences**
    (`AsymptoticallyHolomorphic.lean`). Waits for 13.
15. **Holomorphic approximation on polydiscs**
    (`HolomorphicApproximation.lean`). Waits for nothing.
16. **Taylor truncation on polydiscs** (`TaylorTruncation.lean`). Waits for
    nothing.
17. **Polynomial images lie on hypersurfaces** (`ImageHypersurface.lean`).
    Waits for nothing.
18. **Volumes of tubes around algebraic hypersurfaces**
    (`AlgebraicTube.lean`). Waits for nothing.
19. **Auroux's avoidance estimate** (`Avoidance.lean`). Waits for 15–18.
20. **Local quantitative transversality** (`LocalTransversality.lean`).
    Waits for 19.
21. **Peak sections** (`PeakSection.lean`). Waits for 14.
22. **Greedy colourings and Gaussian sums over separated sets**
    (`GreedyColoring.lean`, `SeparatedSum.lean`). Waits for nothing.
23. **The local correction** (`GlobalTransversality.lean`, first half).
    Waits for 20 and 21.
24. **Global uniform transversality** (`GlobalTransversality.lean`, the
    milestone). Waits for 22 and 23.
25. **The index bound for $\log|s_k|^2$** (`Connectivity.lean`, first half).
    Waits for 14.
26. **Lefschetz connectivity** (`Connectivity.lean`, the milestone). Waits
    for 10 and 25.
27. **Donaldson's hypersurface theorem** (`Hypersurface.lean`). Waits for
    6, 11, 24 and 26.

Issues 1, 2, 7, 9, 12, 15, 16, 17, 18 and 22 can start at once.

## Uses

- *Poincaré duals of submanifolds*: `ZeroSet/DualClass.lean` and
  `Orientation/DualClass.lean`, only in issues 11 and 27.
- Merged files of *Principal connections*, *First Chern number* and
  *Minimal coupling*: `IsCircleConnectionForm`, `exists_isCircleConnectionForm`,
  `curvature_add_mpullback`, `realFirstChernClass`,
  `mk_sub_mk_eq_smul_realFirstChernClass_iff`,
  `chernNumber_eq_integral_curvature`, the circle bundle of a Hermitian line
  bundle (`Hermitian/CircleBundle.lean`, `Hermitian/UnitFrame.lean`).
- Merged files of *Chern classes*: `TauCeti.complexEulerClass_tensorProduct`,
  `Projectivization.complexEulerClass_twistCore_one`,
  `TopCat.uliftIntegralCohomologyIso`.
- Merged files of *Smooth families*: `hasFiniteGoodCover_of_compactSpace`.
- Tau Ceti: Darboux charts, compatible almost complex structures and their
  metrics, complex-linear and antilinear parts, covariant derivatives and
  metric compatibility, associated bundles and their sections, section
  linearizations and zero sets, symplectic submanifold embeddings, Morse
  and Morse–Bott CW models, `IsNConnected`, the polydisc Cauchy integral and
  the Cauchy transform, Gaussian bounds, covering numbers, Stokes' theorem,
  de Rham and smooth singular Mayer–Vietoris sequences.
- Mathlib: `CovariantDerivative`, `iteratedFDeriv`, `Metric.IsSeparated`,
  `MvPolynomial.restrictDegree`, Lebesgue measure on
  `EuclideanSpace`, `Manifold.riemannianEDist`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §7.4, Theorem 7.4.1 and Lemma 7.4.2.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000],
  Propositions 2 and 3.
* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  Proposition 2 and §5.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 18.14.
* A. Hatcher, *Algebraic Topology*, §§4.2–4.3.
