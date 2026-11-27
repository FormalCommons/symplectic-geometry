# Asymptotically holomorphic sections

This is the detailed design of part 64 of `DESIGN.md`, *Asymptotically
holomorphic sections*, for §7.4 of `atlas/constructing-symplectic-manifolds.md`
up to the hypersurface theorem. It settles what `DESIGN.md` leaves to this
file:

- how the estimates that depend on $k$ are written;
- how Auroux's avoidance estimate is split into issues;
- which prerequisite issues give a Hermitian line bundle $L$ with
  Chern–Weil class $a$ and a unitary connection of curvature $-2\pi i\omega$;
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
quantities need no chart. The jet norms depend on the chart family, but no
statement compares two families: every statement takes the family as a
parameter, and the proofs use one family from `exists_rescaledUnitaryCharts`
throughout. The hypersurface theorem mentions no chart. The
right-inverse form of transversality on the page is not built, since no
milestone states it.

### The class of the line bundle: the prerequisites

Three facts are missing from both libraries, and the part plans them as
prerequisite issues (issues 1–4 below):

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
2. **Integral classes of degree two are Euler classes.** For a compact
   manifold $M$ and $b\in H^2(M;\mathbb Z)$ there is a smooth Hermitian line
   bundle $L$ with `complexEulerClass L = b`. The route goes through
   classifying maps. $M$ has finite CW type (Tau Ceti's
   `TauCeti.FiniteCWType.of_isManifold`). The homotopy groups of
   $\mathbb CP^N$ in low degrees are Tau Ceti's, from the long exact
   sequence of the Hopf fibration (`Topology/ComplexProjectiveSpace/Hopf/Basic.lean`
   and `Hopf/Exact.lean`): `TauCeti.ComplexProjectiveSpace.mk_mem_serreFibrations`,
   `instSimplyConnectedSpace` ($\pi_1=0$), `pi2MulEquivInt`
   ($\pi_2\cong\mathbb Z$) and `subsingleton_homotopyGroup` ($\pi_j=0$ for
   $3\le j\le 2N$). They are carried to `ℙ ℂ (Fin (N + 1) → ℂ)`, the base
   of `twistCore`, by
   `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`. So for
   $2N\ge\dim M$ obstruction theory over the skeleta gives a map
   $f:M\to\mathbb CP^N$ with $f^*h=b$.
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
3. **Chern–Weil in degree two.** For this $L$, with unitary frame bundle
   $P$, `deRhamHom (realFirstChernClass P)` is **minus** the real image of
   `complexEulerClass L`. Two merged theorems fix the sign. On a closed
   surface with orientation `o`, `chernNumber_eq_integral_curvature` makes
   the Chern number for `o.toHomologicalOrientation` equal to
   $-(2\pi)^{-1}\int_oF_\alpha$, and
   `integralTopForm_eq_closedFormHomologyPeriod` pairs $\int_o$ with the
   fundamental class of `(-o).toHomologicalOrientation` (the sign $s=-1$
   of `design/pseudoholomorphic-energy.md`). So, for one and the same
   homological orientation, `deRhamHom (realFirstChernClass P)` pairs with
   the fundamental class to minus the Chern number. Both sides are natural
   under the smooth map $f$: the Euler class by
   `TauCeti.complexEulerClass_pullback`, the real class by
   `realFirstChernClass_map` (below) and `TauCeti.deRhamHom_map`. So it
   suffices to prove it for `twistCore 1` on $\mathbb CP^N$. There
   restriction to a line $\mathbb CP^1$ is injective on $H^2(-;\mathbb R)$,
   and on $\mathbb CP^1$ the two theorems above give it.

   `realFirstChernClass_map`, with `IsCircleConnectionForm.mpullback` and
   `IsCircleConnectionForm.curvature_mpullback` that it rests on, is planned
   by `design/compatible-symplectic-forms.md` (part 49) in the merged
   `FiberBundle/Principal/RealChernClass.lean`. The
   Chern–Weil issue proves the three there, under those names and with the
   statements that design gives, unless part 49 has built them by then.
   Part 49 then uses them, and neither part waits for the other.

`LineBundle.lean` then builds the bundle and corrects the curvature. Take
$L$ from 2 with $b=-a$, and any connection form
(`SymplecticGeometry.exists_isCircleConnectionForm`). By 3 its real class
maps to the image of $a$, which is `deRhamHom` of $[\omega]$, so by 1 the
real class is $[\omega]$. By
`IsCircleConnectionForm.mk_sub_mk_eq_smul_realFirstChernClass_iff` the
difference of the curvature from $-2\pi\omega$ is exact. Adding the
pull-back of a primitive (`IsCircleConnectionForm.add_mpullback`,
`curvature_add_mpullback`) makes the curvature exactly $-2\pi\omega$.

So the bundle of the page, with curvature $-2\pi i\omega$ and real Chern
class $[\omega]$, has `complexEulerClass L = -a`: under the merged signs,
Tau Ceti's Euler class of a Hermitian line bundle is minus the image of its
Chern–Weil class. The curvature stays as on the page, since the peak
sections need $L$ positive for $J$, which is a condition on the curvature.
The sign is carried to the class of the zero sets in `ZeroSet.lean` and
`Hypersurface.lean` below.

*Minimal coupling* (#2265) is still open, but this part uses only its merged
`RealChernClass.lean` and the merged `CircleConnection.lean` and
`Connection/Circle.lean`. So no issue here waits for #2265.

### Auroux's avoidance estimate, split

The local transversality milestone follows Auroux's Proposition 3
[Auroux2002], from the avoidance estimate of Proposition 2 [Auroux2000]. For
a $C^1$ map $G:B^+\subset\mathbb C^n\to\mathbb C^{n+1}$ with $|G|\le1$ and
$|\bar\partial G|\le\epsilon$ on $B^+$ (sup norms only), it gives a $w$ with
$|w|\le\delta$ at distance at least $c\,\delta(\log(1/\delta))^{-p_0}$ from
$G(B)$. Sup norms are enough, since the proof compares $G(B)$ only with the
image of a polynomial map that is uniformly close to $G$. Each step below
takes what the one before gives. The proof has four independent steps and
one assembly, each an issue (issues 14–18), except the tube volumes, which
take issues 17a–17f and 17:

- **Holomorphic approximation.** On a closed polydisc of radius $\rho$, a
  $C^1$ function $f$ with $|\bar\partial f|\le\epsilon$ is within
  $C_n\rho\,\epsilon$ in sup norm, on the polydisc of radius $\rho/2$, of
  its polydisc Cauchy integral $h$, which is holomorphic (Tau Ceti's
  `Analysis/Complex/CauchyIntegralPolydisc.lean`). The route applies the
  one-variable Cauchy–Pompeiu formula one coordinate at a time. With $C_j$
  the boundary Cauchy integral in $z_j$ and $T_j$ the Cauchy transform in
  $z_j$ (`Analysis/Complex/Pompeiu/Basic.lean`), and since $C_i$ commutes
  with $\partial/\partial\bar z_j$ for $i\ne j$,
  $f=C_n\cdots C_1f+\sum_jT_j\,C_{j-1}\cdots C_1\,\partial f/\partial\bar z_j$.
  Only first derivatives of $f$ enter, $T_j$ is bounded by $2\rho$ times
  the sup norm, and $C_i$ by $2$ on the half-radius. This avoids the
  several-variable $\bar\partial$-equation.
- **Polynomial truncation.** A holomorphic function bounded by $M$ on a
  polydisc of radius $\rho$ differs on the polydisc of radius $\rho/2$ from
  its Taylor polynomial of degree less than $d$ by at most $(1+d)M2^{-d}$,
  in sup norm. This is Tau Ceti's
  `HasFPowerSeriesOnBall.norm_sub_partialSum_le` on the sup-norm ball of
  `Fin n → ℂ`; the issue adds the power series of $h$ on the polydisc, if
  neither library has it, and writes the partial sum as a polynomial map
  of degree less than $d$.
- **Algebraic dependence.** The image of a polynomial map
  $\mathbb C^n\to\mathbb C^{n+1}$ of degree at most $d$ lies in the zero set
  of a nonzero polynomial of degree at most $C_nd^{\,n}$. This is a
  dimension count. For $D$ of that size, the polynomials of degree $\le D$
  in $n+1$ variables outnumber those of degree $\le Dd$ in $n$ variables,
  so the linear map $Q\mapsto Q\circ P$ has a nonzero kernel. It uses Mathlib's
  `MvPolynomial.restrictTotalDegree` and Tau Ceti's `finrank_restrictTotalDegree`.
- **Tube volumes.** In the unit ball of $\mathbb C^{m}$, the
  $t$-neighbourhood of the zero set of a nonzero polynomial of degree at
  most $D$ has volume at most $C_mD^4t^2$ for every $t>0$. Any fixed
  exponents would do, since $D$ grows only as a power of
  $\log(1/\delta)$. The form that issue 17 states, $C_mD^{2m}t$ for
  $0<t\le1$, follows: the volume is also at most that of the ball, and
  $\min(A,Bx^2)\le\sqrt{AB}\,x$ for $x=D^2t$. The next section gives the
  route. The bound that uses only the Lipschitz constant of the map is too weak. It
  gives $\epsilon$ of order $\delta^{n+1}$, and the iteration over colours
  needs $\epsilon$ nearly linear in $\delta$.
- **Assembly.** These give the avoidance estimate. $B$ is covered by
  finitely many polydiscs of a radius depending on $n$ whose doubles lie
  in $B^+$. On each, $G$ is within $C(\epsilon+(1+d)2^{-d})$ of a
  polynomial map of degree less than $d$, and the product of the
  polynomials from the algebraic dependence step vanishes on all their
  images. For $d$ of order $\log(1/\delta)$ the error is below the
  distance sought. The volume of the $\delta$-ball of parameters exceeds
  the volume of the thin neighbourhood of the zero set, after rescaling by
  $\delta$.

### The tube-volume bound, by averages over complex lines

The routes through the area of the zero set need Hausdorff measure of
analytic sets and the monotonicity of Lelong numbers. The real route after
Wongkew needs a Milnor–Thom bound on the components of a real algebraic
set. Neither library has any of these. The route here uses only
polynomials in one complex variable on circles, Lebesgue measure and
Fubini's theorem. As in Crofton's formula it counts zeros on complex
lines. But it compares two centres through averages of $\log|P|$ over
balls, and never through the area of the zero set.

Throughout, $E$ is `EuclideanSpace ℂ (Fin m)` with `volume`, `P :
MvPolynomial (Fin m) ℂ` is nonzero with `P.totalDegree ≤ D`, and
$Z=\{z\mid$ `MvPolynomial.eval z.ofLp P = 0` $\}$. For $D=0$ the set $Z$ is
empty, so let $D\ge1$. Write $u=\log|P|$ (Mathlib's `Real.log`, which is
$0$ at $0$; $Z$ is null, so the averages below do not see this),
$V(c,r)$ for the average of $u$ over `Metric.ball c r`, and $S(c,r)$ for
the logarithm of the maximum of $|P|$ on `Metric.closedBall c r`. For
$c,v\in E$ let $p_{c,v}(s)=P(c+sv)$, a polynomial in one complex variable.
Its coefficient of degree `P.totalDegree` is $P_{\rm top}(v)$, where
$P_{\rm top}$ is `MvPolynomial.homogeneousComponent P.totalDegree P`, which
is nonzero. The zero set of $P_{\rm top}$ is null, by Tau Ceti's
`MvPolynomial.volume_setOfPred_eval_eq_zero` on `Fin m → ℂ`, carried to
$E$ by the linear equivalence `WithLp.ofLp`, under which the two Haar
measures agree up to a constant. Off it, $p_{c,v}$ is nonzero of degree at
most $D$ for every $c$. Let $h(c,\rho)$ be the proportion of the $v$ in
`Metric.ball 0 1` for which $p_{c,v}$ has a root of norm less than
$\rho$, that is, for which the line through $c$ in the direction $v$
meets $Z$ within $\rho\|v\|\le\rho$ of $c$.

1. **One variable.** For a nonzero $p\in\mathbb C[s]$ and $r>0$, the
   circle average of $\log|p|$ at radius $r$ is
   $\log|\mathrm{lc}(p)|+\sum_a\log\max(r,|a|)$, the sum over the roots
   with multiplicity. This is Mathlib's
   `Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`
   for $p(rs)$. For $r_1\le r_2$ a root $a$ adds to the difference of the
   averages at $r_2$ and $r_1$ a number between $0$ and
   $\log(r_2/r_1)$: $0$ if $|a|\ge r_2$, and $\log(r_2/r_1)$ if $a=0$. So
   the difference lies between $\mathrm{ord}_0(p)\log(r_2/r_1)$ and
   $\deg p\cdot\log(r_2/r_1)$, and is $0$ if no root has norm less than
   $r_2$. If $p(0)\ne0$, the average is at least $\log|p(0)|$. Since
   $|s-a|\le(\lambda+1)\max(r,|a|)$ for $|s|\le\lambda r$, and the maximum
   of $\log|p|$ on the circle of radius $r$ is at least the average, the
   maximum of $|p|$ on the disc of radius $\lambda r$ is at most
   $(\lambda+1)^{\deg p}$ times its maximum on the circle of radius $r$.
2. **Balls as families of circles.** For a measurable $g\ge0$ on $E$, the
   integral of $g$ over `ball c ρ` is $\rho^{2m}$ times the integral over
   $v\in$ `ball 0 1` of the circle average of $s\mapsto g(c+sv)$ at radius
   $\rho$. Multiplication by $e^{i\theta}$ is a linear isometry of $E$, so
   it preserves `volume` (`LinearIsometryEquiv.measurePreserving`) and
   `ball 0 1`. Average over $\theta$ and exchange the integrals by Tonelli.
   The statement is about lower Lebesgue integrals, so it needs no
   integrability.
3. **Averages of $\log|P|$.** Step 2 for $g=S-u$, with step 1 for each
   $p_{c,v}$, gives:
   - (a) if $P(c)\ne0$, then $V(c,r)\ge u(c)$ for every $r>0$;
   - (b) $S(y,R)-V(y,R)\le4^mD\log4$ for every $y$ and $R>0$. Let $|P|$
     reach its maximum on `closedBall y R` at $z_0$. The ball
     `ball z₀ (2 * R)` contains `ball y R` and lies in `ball y (3 * R)`,
     on which $u\le S(y,3R)$ almost everywhere. By (a) at $z_0$, the
     average of $S(y,3R)-u$ over `ball z₀ (2 * R)` is at most
     $S(y,3R)-S(y,R)$, which step 1 on the complex lines through $y$
     bounds by $D\log4$. Comparing the integrals of the nonnegative
     $S(y,3R)-u$ over `ball y R` and `ball z₀ (2 * R)` gives the bound.
     In particular $u$ is integrable on every ball;
   - (c) $0\le V(c,r_2)-V(c,r_1)\le D\log(r_2/r_1)\,h(c,r_2)$ for
     $0<r_1\le r_2$;
   - (d) if $P(y)=0$, then $V(y,r_2)-V(y,r_1)\ge\log(r_2/r_1)$ for
     $0<r_1\le r_2$, since every line through $y$ meets $Z$ at $y$.
4. **Change of centre.** There is a $K\ge2$, depending on $m$ only, such
   that for $\|c-y\|<a$ with $P(y)=0$, $\rho_1=KDa$ and $\rho_2=4\rho_1$:
   $V(c,\rho_2)-V(c,\rho_1)\ge\frac12\log4$, and so, by 3(c),
   $h(c,\rho_2)\ge1/(2D)$. Let $w=S(y,\rho_2+a)-u$, which is nonnegative
   almost everywhere on `ball y (ρ₂ + a)`, and let $W=S(y,\rho_2+a)-V$ be
   its averages. Since `ball y (ρ₁ - a)` lies in `ball c ρ₁` and
   `ball c ρ₂` in `ball y (ρ₂ + a)`,
   $W(c,\rho_1)\ge\alpha\,W(y,\rho_1-a)$ and
   $W(c,\rho_2)\le\beta\,W(y,\rho_2+a)$, with
   $\alpha=(1-1/(KD))^{2m}$ and $\beta=(1+1/(4KD))^{2m}$. By 3(d) and
   3(b),
   $V(c,\rho_2)-V(c,\rho_1)=W(c,\rho_1)-W(c,\rho_2)\ge\alpha\log4-(\beta-\alpha)\,4^mD\log4$.
   As $\beta-\alpha\le C_m/(KD)$, the factor $D$ cancels, and a large $K$
   gives $\frac12\log4$. Step 3(b), that the average of $\log|P|$ over a
   ball stays within $O(D)$ of its maximum, is what replaces the
   monotonicity of Lelong numbers here: it bounds what is lost when the
   centre moves from $y$ to $c$.
5. **Slices.** Let $v\ne0$, and let a closed $A\subseteq E$ meet each complex line
   $c+\mathbb Cv$ in at most $N$ points. Then the set of $c\in$ `ball 0 1`
   with $c+sv\in A$ for some $\|s\|<\rho$ has volume at most
   $C_mN\rho^2\|v\|^2$. Tonelli's theorem along $E=K^\perp\oplus K$, for
   the complex line $K=\mathbb Cv$, integrates over the lines, on
   each of which the set lies in $N$ discs of radius $\rho\|v\|$. For
   $A=Z$ and $P_{\rm top}(v)\ne0$, $N=D$.
6. **Assembly.** For $c$ in the $t$-thickening of $Z$, step 4 with $a=t$
   gives $h(c,4KDt)\ge1/(2D)$. Integrate over $c\in$ `ball 0 1` and
   exchange with the integral over $v$ (Tonelli; the set of pairs $(c,v)$
   is the projection of a $\sigma$-compact set, so it is measurable).
   Step 5 for almost every $v$ bounds the volume of the part of the
   thickening in `ball 0 1` by $2D\cdot C_mD(4KDt)^2=C_m'D^4t^2$.

So the exponents are $a=4$ and $b=2$, and issue 17 keeps the statement
of #3515. The steps are issues 17a–17f and 17 below. The design knows of
no published source that gives this proof as a whole. Step 1 is Jensen's
formula for polynomials, step 3(b) is a form of the Bernstein–Walsh
inequality, and the counting of zeros on lines through a point is the one
behind Lelong numbers and Crofton's formula.

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
zero section $s$ of `L k` gives the global unitary frame $s/|s|$ of `L k`.
In that frame $D_k$ is $d+i\beta$ for a real one-form $\beta$, and the
curvature of $D_k$ gives $d\beta=-2\pi k\,\omega$. So $\omega$ is exact, and
so is $\omega^n$.
Its integral over the closed manifold $M$ then vanishes (Tau Ceti's Stokes
theorem), against `TauCeti.SmoothTwoForm.IsSymplectic` and the positivity of
the Liouville volume.

## Files

New files of the part, in `Geometry/Symplectic/AsymptoticallyHolomorphic/`,
and the prerequisites, placed by topic.

### Prerequisites

- `Geometry/Manifold/SmoothSingular/DeRham/MayerVietoris/Induction.lean`:
  `SymplecticGeometry.HasFiniteGoodCover.bijective_deRhamHom` (for manifolds
  that have a finite good cover), `TauCeti.bijective_deRhamHom` (for a
  second-countable one through `mayerVietoris_induction`),
  `TauCeti.injective_deRhamHom`. If Tau Ceti's `deRhamHom` lands in smooth
  singular cohomology, the file also compares it with continuous singular
  cohomology, unless `SmoothSingular/Smoothing.lean` already does.
- `AlgebraicTopology/Cohomology/ProjectiveSpaceClassifying.lean`: for a
  finite CW complex $X$ of dimension at most $2N$, every class of
  $H^2(X;\mathbb Z)$ is $f^*h$ for some $f:X\to\mathbb CP^N$
  (`exists_continuousMap_projectivization_pullback_eq`), from Tau Ceti's
  homotopy groups of $\mathbb CP^N$ named above.
- `Geometry/Manifold/VectorBundle/Hermitian/Realization.lean`: on a compact
  manifold every integral class of degree two is the Euler class of a smooth
  Hermitian line bundle pulled back from `twistCore 1` along a smooth map
  (`exists_hermitianLineBundle_complexEulerClass_eq`).
- `Geometry/Manifold/VectorBundle/Hermitian/ChernWeil.lean`: for line
  bundles pulled back from `twistCore 1` along smooth maps,
  `deRhamHom (realFirstChernClass IB P)` is minus the real image of the
  Euler class (`deRhamHom_realFirstChernClass_eq_neg`). The same issue adds
  `IsCircleConnectionForm.mpullback`, `IsCircleConnectionForm.curvature_mpullback`
  and `realFirstChernClass_map` to `FiberBundle/Principal/RealChernClass.lean`,
  as `design/compatible-symplectic-forms.md` states them.
- `LinearAlgebra/Complex/DominantLinearPart.lean`: for a real-linear
  $F=A+B:V\to\mathbb C$ on a Hermitian space $(V,\omega,J)$, with $A$
  complex linear, $B$ antilinear and $\|B\|<\|A\|$, $F$ is surjective, its
  kernel is a symplectic subspace, and the orientation of the kernel that
  $F$ induces (as for transverse zero sets) agrees with the symplectic one.
  Main results:
  `surjective_of_norm_lt`, `isSymplectic_ker_of_norm_lt`,
  `orientation_ker_eq_of_norm_lt`.
- `Combinatorics/SimpleGraph/GreedyColoring.lean`: a locally finite graph
  of maximal degree at most $\Delta$ is $(\Delta+1)$-colourable
  (`SimpleGraph.colorable_of_forall_degree_le`), from Tau Ceti's
  `SimpleGraph.colorable_succ_of_forall_exists_card_le`.
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
- The steps of the tube-volume bound, by topic:
  `Analysis/Polynomial/CircleAverageLog.lean` (step 1, in the namespace
  `Polynomial`: `circleAverage_log_norm_eval`, the formula;
  `circleAverage_log_norm_eval_sub_le` and
  `circleAverage_log_norm_eval_sub_eq_zero`, the bounds on the difference
  of two radii; `rootMultiplicity_mul_log_le_circleAverage_sub`; and
  `exists_norm_eval_le_add_one_pow_mul`, the growth from radius $r$ to
  $\lambda r$),
  `MeasureTheory/Integral/BallCircleAverage.lean` (step 2,
  `MeasureTheory.setLIntegral_ball_eq_mul_setLIntegral_setLAverage_circleMap`),
  `Analysis/Complex/MvPolynomial/LogAverage.lean` (step 3, in the namespace
  `MvPolynomial`: `ae_eval_ne_zero`,
  `log_norm_eval_le_setAverage_ball`,
  `log_sup_sub_setAverage_log_norm_eval_le`,
  `integrableOn_log_norm_eval_ball`,
  `setAverage_log_norm_eval_sub_le` and
  `log_div_le_setAverage_log_norm_eval_sub`),
  `MeasureTheory/Measure/Lebesgue/LineSlice.lean` (step 5,
  `volume_setOfPred_exists_add_smul_mem_le`), and in `AlgebraicTube.lean`, before
  `volume_thickening_zeroLocus_le`, step 4
  (`MvPolynomial.setAverage_log_norm_eval_sub_ge_of_dist_lt` and
  `MvPolynomial.volume_ball_le_mul_volume_setOfPred_exists_root`) and the bound
  `MvPolynomial.volume_thickening_zeroLocus_le_pow_four_mul_sq`
  ($C_mD^4t^2$), from which `volume_thickening_zeroLocus_le` follows.

### Files of the part

- `LineBundle.lean`: `exists_prequantumLineBundle`: for compact $M$ and an
  integral lift $a$ of $[\omega]$, there is a Hermitian line bundle $L$ with
  `complexEulerClass L = -a` and a connection form $\alpha$ on its unitary
  frame bundle with `hα.curvature = -(2 * π) • ω`; the sign of the Euler
  class is that of prerequisite 3.
- `Power/Basic.lean`: `L k`, the associated bundle for $g\cdot z=g^kz$; its
  Hermitian metric; `powerOneEquiv : L 1 ≃ L`, `powerAddEquiv` with Tau
  Ceti's tensor product; `complexEulerClass_power` (`k •` the class of
  `L`, so $-k\,a$ for the bundle of `LineBundle.lean`).
- `Power/Connection.lean`: the connection $D_k$ on `L k` as a Mathlib
  `CovariantDerivative`. It is complex linear and metric, has the local
  formula $d+ik\,\sigma^*\alpha$ in a unitary frame
  (`powerConnection_apply_frame`) and curvature $ik\,F_\alpha$. For a section
  $s$, $\partial s(x)$ and $\bar\partial s(x)$ are `J.oneZeroPart (D s x)` and
  Tau Ceti's `J.zeroOnePart (D s x)`, with `oneZeroPart_add_zeroOnePart`;
  `oneZeroPart` and that lemma are in
  `Geometry/Manifold/VectorBundle/CauchyRiemann/OneZeroPart.lean`.
- `ZeroSet.lean`: for any covariant derivative $D$ on a bundle of normed
  complex lines over a manifold with compatible $J$:
  `isTransverse_of_norm_dbar_lt` (surjective
  `TauCeti.sectionLinearization` at the zeros, so the zero set is a
  submanifold by Tau Ceti's `exists_isManifold_sectionZero_of_contMDiff`)
  and `isSymplecticSubmanifoldEmbedding_zeroSet_of_norm_dbar_lt`; for any
  Hermitian line bundle with a complex-linear metric connection $D$ on a
  closed manifold with compatible $J$, the milestone `dualClass_zeroSet_eq_complexEulerClass_of_norm_dbar_lt`:
  with the symplectic orientations of $M$ and of the zero set $Z$, $Z$ has
  dual class `complexEulerClass L`, so that, for the fundamental classes of
  `toHomologicalOrientation` of these orientations, which *Poincaré duals
  of submanifolds* pairs with dual classes, $i_*[Z]$ is
  `complexEulerClass L` capped with $[M]$: this is $\mathrm{PD}(c_1(L))$ with
  $c_1$ read as Tau Ceti's Euler class. The milestone states this with the
  two results before it.
  At a zero, $Ds$ is the intrinsic linearization for every $D$, so the
  statement holds for every $D$.
- `RescaledChart.lean`: the rescaled unitary charts. `CenteredDarbouxCharts`
  are charts centred at every point with derivative at the centre complex
  linear for $J$, with uniform $C^r$ bounds. They come from finitely many
  `IsSymplectic.exists_darbouxChart_stdForm`
  charts, composed with translations and unitary symplectic linear maps,
  by compactness. `RescaledUnitaryCharts k₀ ρ₀` adds the rescaling and the
  frames in which the connection form is the model, with `jStruct_sub_le`, `iteratedFDeriv_jStruct_le` and
  `connectionForm_eq_model`. The existence theorem is
  `exists_rescaledUnitaryCharts`, and
  `exists_forall_ofReal_mul_riemannianEDist_symm_mem_Icc` compares $d_k$ with
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
  $G=(f-\sum_jz_j\partial_jf,\partial_1f,\dots,\partial_nf)$. The $C^1$
  bound on $f$ bounds $|G|$ on $B^+$. Since $\bar\partial$ of
  $\partial_jf$ is $\partial_j$ of $\bar\partial f$ in these flat
  coordinates, $|\bar\partial G|$ is at most a constant times
  $\|\bar\partial f\|_{C^1}$, which the page's bound on
  $\|\bar\partial f\|_{C^2}$ controls. After division of $G$ by a
  constant depending on $n$, the avoidance step applies.
- `GlobalTransversality.lean`: the local correction on one ball, by division
  by `peakSection` (`exists_local_correction`), and the iteration over
  colours (`exists_isUniformlyTransverse`, the milestone). The logarithms
  $u_j=\log(1/b_j)$ of the lower bounds obey a recurrence
  $u_j\le u_{j-1}+C_3+p\log(u_{j-1}+\log A)$. The file proves, as a separate
  lemma about real sequences, that such sequences grow at most like
  $(j+1)\log(j+2)$.
- `Connectivity.lean`: `criticalPoint_norm_ge` (at critical points of
  $\log|s_k|^2$, $|s_k|\ge\eta$ for large $k$),
  `hessian_add_hessian_J_neg`, `morseIndex_ge`, and the milestone
  `exists_relCWComplex_homotopyEquiv_zeroSet`: for nonempty $Z_k$ and large
  $k$, $M$ has the homotopy type of a CW complex relative to $Z_k$ whose
  cells all have dimension $n$ or more. In the form of Tau Ceti's
  `IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`, there are a
  Hausdorff space `X`, a closed embedding `j : C(Z_k, X)`, a
  `RelCWComplex (univ : Set X) (range j)` with no cell of dimension less
  than $n$, and `h : X ≃ₕ M` with `h (j z) = z`. It is assembled from the
  Morse–Bott attachment near $Z_k$ and the Morse CW models away from it.
  Its corollary `isNConnected_zeroSet_inclusion` ($Z_k\hookrightarrow M$ is
  $(n-1)$-connected) follows through `TauCeti.isNConnected_inclusion_skeletonLT`
  and the homotopy equivalence.
- `Hypersurface.lean`: the milestone `exists_symplecticHypersurface`: for
  closed connected $M$ of dimension $2n$ with $n\ge2$ and a fixed integral
  lift $a$, for large $k$ there are a closed connected manifold $Z$ and a
  symplectic embedding $i:Z\to M$ of codimension two
  (`ω.IsSymplecticSubmanifoldEmbedding i`) and an inclusion that is
  $(n-1)$-connected (`ContinuousMap.IsNConnected _ (n - 1)`), such that,
  with the symplectic orientations of $Z$ and $M$ and the fundamental
  classes of their `toHomologicalOrientation`, $i_*[Z]$ is
  $(-k\,a)\frown[M]$. This is the page's $[Z]=\mathrm{PD}(k\,a)$ under the
  library's signs: $Z$ is the zero set of a section of `L k`, whose Euler
  class is $-k\,a$ while its Chern–Weil class is $k[\omega]$ (prerequisite
  3). The lift is fixed before $k$, as the page's notes say. The file also
  has `zeroSet_nonempty` by the argument above.

## Issues

Each issue is a few hundred lines, in an order where each comes after the
ones it waits for. An issue that adds an existing name of Tau Ceti or
Mathlib uses it instead; each prerequisite issue first searches both for its
statement.

1. **The de Rham theorem**
   (`SmoothSingular/DeRham/MayerVietoris/Induction.lean`). Waits for
   nothing. Its agent may split it in two: the Mayer–Vietoris square of
   `deRhamHom` with its connecting maps, then the induction.
2. **Classifying maps for $H^2$** (`ProjectiveSpaceClassifying.lean`).
   Waits for nothing.
3. **Hermitian line bundles with prescribed $c_1$** (`Realization.lean`).
   Waits for 2.
4. **Chern–Weil in degree two** (`Hermitian/ChernWeil.lean`, and the
   pull-back lemmas in `Principal/RealChernClass.lean`). Waits for 3.
5. **The prequantum line bundle** (`LineBundle.lean`). Waits for 1, 3 and 4.
6. **Powers of a Hermitian line bundle** (`Power/Basic.lean`). Waits for nothing.
7. **The connection on the powers** (`Power/Connection.lean`). Waits for 6.
8. **Real-linear forms with dominant complex-linear part**
   (`DominantLinearPart.lean`). Waits for nothing.
9. **Transverse symplectic zero sets** (`ZeroSet.lean`, without the
   class). Waits for 8.
10. **The class of the zero set** (`ZeroSet.lean`, the milestone). Waits for
    9 and for the issue of *Poincaré duals of submanifolds* for
    `ZeroSet/DualClass.lean`; until #3278 creates it, for #3278.
11. **Centred Darboux charts with uniform bounds** (`RescaledChart.lean`,
    first half). Waits for nothing.
12. **Rescaled unitary charts** (`RescaledChart.lean`, second half). Waits
    for 7 and 11.
13. **Jet norms and asymptotically holomorphic sequences**
    (`AsymptoticallyHolomorphic.lean`). Waits for 12.
14. **Holomorphic approximation on polydiscs**
    (`HolomorphicApproximation.lean`). Waits for nothing.
15. **Taylor truncation on polydiscs** (`TaylorTruncation.lean`). Waits for
    nothing.
16. **Polynomial images lie on hypersurfaces** (`ImageHypersurface.lean`).
    Waits for nothing.
17. **Volumes of tubes around algebraic hypersurfaces**
    (`AlgebraicTube.lean`, step 6 of the tube-volume bound). It comes after
    six issues for steps 1–5, in this order:
    - 17a. **Circle averages of $\log|p|$** (`CircleAverageLog.lean`,
      step 1). Waits for nothing.
    - 17b. **Balls as families of circles** (`BallCircleAverage.lean`,
      step 2). Waits for nothing.
    - 17c. **Averages of $\log|P|$ near their maximum**
      (`LogAverage.lean`, first half: the null set of $P_{\rm top}$, step
      3(a), 3(b) and integrability). Waits for 17a and 17b.
    - 17d. **Growth of the averages of $\log|P|$** (`LogAverage.lean`,
      second half: steps 3(c) and 3(d)). Waits for 17c.
    - 17e. **Change of centre** (`AlgebraicTube.lean`, first half: step 4).
      Waits for 17d.
    - 17f. **Slices along a direction** (`LineSlice.lean`, step 5). Waits
      for nothing.

    Issue 17 itself proves `volume_thickening_zeroLocus_le_pow_four_mul_sq`
    and `volume_thickening_zeroLocus_le`. Waits for 17e and 17f.
18. **Auroux's avoidance estimate** (`Avoidance.lean`). Waits for 14–17.
19. **Local quantitative transversality** (`LocalTransversality.lean`).
    Waits for 18.
20. **Peak sections** (`PeakSection.lean`). Waits for 13.
21. **Greedy colourings and Gaussian sums over separated sets**
    (`GreedyColoring.lean`, `SeparatedSum.lean`). Waits for nothing.
22. **The local correction** (`GlobalTransversality.lean`, first half).
    Waits for 19 and 20.
23. **Global uniform transversality** (`GlobalTransversality.lean`, the
    milestone). Waits for 21 and 22.
24. **The index bound for $\log|s_k|^2$** (`Connectivity.lean`, first half).
    Waits for 13.
25. **Lefschetz connectivity** (`Connectivity.lean`, the milestone: the
    relative CW model and its corollary). Waits for 9 and 24.
26. **Donaldson's hypersurface theorem** (`Hypersurface.lean`). Waits for
    5, 10, 23 and 25.

Issues 1, 2, 6, 8, 11, 14, 15, 16, 17a, 17b, 17f and 21 can start at once.

## Uses

- *Poincaré duals of submanifolds*: `ZeroSet/DualClass.lean` and
  `Orientation/DualClass.lean`, only in issues 10 and 26.
- *Compatible symplectic forms* (part 49, not built): the statements of
  `IsCircleConnectionForm.mpullback`, `IsCircleConnectionForm.curvature_mpullback`
  and `realFirstChernClass_map` that its design gives, which issue 4 proves
  unless part 49 has by then; no issue here waits for part 49.
- Merged files of *Principal connections*, *First Chern number* and
  *Minimal coupling*: `IsCircleConnectionForm`, `exists_isCircleConnectionForm`,
  `curvature_add_mpullback`, `realFirstChernClass`,
  `mk_sub_mk_eq_smul_realFirstChernClass_iff`,
  `chernNumber_eq_integral_curvature`,
  `integralTopForm_eq_closedFormHomologyPeriod`, the circle bundle of a
  Hermitian line bundle (`Hermitian/CircleBundle.lean`,
  `Hermitian/UnitFrame.lean`).
- Merged files of *Chern classes*: `TauCeti.complexEulerClass_tensorProduct`,
  `Projectivization.complexEulerClass_twistCore_one`,
  `TopCat.uliftIntegralCohomologyIso`.
- Merged files of *Smooth families*: `hasFiniteGoodCover_of_compactSpace`.
- Tau Ceti: Darboux charts, compatible almost complex structures and their
  metrics, complex-linear and antilinear parts, covariant derivatives and
  metric compatibility, associated bundles and their sections, section
  linearizations and zero sets, symplectic submanifold embeddings, Morse
  and Morse–Bott CW models, `IsNConnected`, the polydisc Cauchy integral and
  the Cauchy transform, Taylor remainders, Gaussian bounds, covering
  numbers, Stokes' theorem, de Rham and smooth singular Mayer–Vietoris
  sequences, the Hopf fibration, the homotopy groups of $\mathbb CP^N$ and
  the null zero sets of nonzero polynomials
  (`MvPolynomial.volume_setOfPred_eval_eq_zero`).
- Mathlib: `CovariantDerivative`, `iteratedFDeriv`, `Metric.IsSeparated`,
  `MvPolynomial.restrictTotalDegree`, Lebesgue measure on
  `EuclideanSpace`, `Manifold.riemannianEDist`,
  `Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`,
  `MvPolynomial.homogeneousComponent`, `LinearIsometryEquiv.measurePreserving`.

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
