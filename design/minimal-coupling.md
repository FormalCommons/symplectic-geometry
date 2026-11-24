# Minimal coupling

This is the detailed design of part 39 of `DESIGN.md`, *Minimal coupling*.
It covers the milestone *Minimal coupling* of
`atlas/symplectic-group-actions.md`, which follows McDuff–Salamon
[McDuffSalamon2017], Proposition 5.1.9, with the page's Hamiltonian sign,
with the bundle $P$ kept fixed in the uniqueness statement, and with the
boundary of the converse read as the page's notes read it.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. All statements about Mathlib, Tau Ceti and the library were
checked against the versions pinned when this file was written (Tau Ceti
`c9d170eed5a8`).

## Setting and notation

- **The base and the bundle.** `IB : ModelWithCorners ℝ EB HB` with
  `[FiniteDimensional ℝ EB]`, `[IB.Boundaryless]`, `[IsManifold IB ∞ B]`,
  `[T2Space B]`, `[SigmaCompactSpace B]` (compactness where a statement needs
  it). $P$ is a smooth principal `Circle`-bundle in Tau Ceti's form, the
  instances of the merged
  `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`:
  `P : B → Type*` with `[FiberBundle Circle P]`, `[∀ b, MulAction Circleᵐᵒᵖ (P b)]`,
  `[PrincipalBundle Circle P]` and `[ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]`.
  Its charted total space is `ManifoldTotalSpace Circle P`, modelled on
  `IB.prod (𝓡 1)`, with projection $\pi$; the circle acts on it by
  `fun x ↦ op z • x`.
- **The interval.** $I=[a,b]$ is `Set.Icc a b` with `[Fact (a < b)]`, with
  Mathlib's manifold-with-boundary structure modelled on `𝓡∂ 1`. The
  coupling space is the product
  `ManifoldTotalSpace Circle P × Set.Icc a b`, modelled on
  `(IB.prod (𝓡 1)).prod (𝓡∂ 1)`. The coordinate $\lambda$ is
  `fun x ↦ (x.2 : ℝ)`, and $d\lambda$ is its differential as a smooth
  one-form. Tau Ceti's pull-back of forms and its naturality
  (`TauCeti.SmoothForm.mextDerivₗ_mpullback`) need no boundaryless model, so
  forms on this product are used as they are.
- **Families.** A family $\tau_\lambda$ of two-forms on $B$ is a map
  `τ : Set.Icc a b → SmoothTwoForm IB B` with `IsSmoothFamily (𝓡∂ 1) τ`, the
  predicate of *Smooth families*, which allows any parameter manifold. Where
  a merged result of *Smooth families* is stated only over `unitInterval`
  (`exists_isSmoothFamily_mextDerivₗ_eq`, the time extension), the family
  is reparametrized by Mathlib's affine homeomorphism
  `iccHomeoI a b : Set.Icc a b ≃ₜ unitInterval`, which is smooth both ways,
  with `IsSmoothFamily.comp`. If Mathlib has no smoothness lemma for
  `iccHomeoI` and its inverse, issue 4 adds both, in
  `Geometry/Manifold/Instances/Icc.lean`.
- **The generator and the sign.** The page's circle has period one, so its
  generator is $\xi_1=2\pi\cdot$`circleLieGenerator`, as *Group actions,
  moment maps and periods* in `DESIGN.md` says, and its fundamental vector
  field on the total space is
  $X=2\pi\cdot$`rightFundamentalVectorField (IB.prod (𝓡 1)) circleLieGenerator`;
  on the product it is $(X,0)$. A merged connection form `α` has
  `α(X_gen) = 1` for the field $X_{\mathrm{gen}}$ of `circleLieGenerator`,
  so the page's connection forms, with value $1$ on $X$, are
  $(2\pi)^{-1}$ times the library's, as part 39 of `DESIGN.md` notes. The
  page's Hamiltonian sign is $\iota_X\omega=-d\lambda$, written out as it
  is, with no Tau Ceti predicate (Tau Ceti's moment maps are for left
  actions, and this one is the right action of a principal bundle). The
  converse, on a manifold with a left action, uses Tau Ceti's
  `IsMomentMap` with $-\mu$, as `DESIGN.md` prescribes.

## Decisions

`DESIGN.md` leaves three questions to this file, and the work raised a
fourth.

- **The product $P\times[a,b]$.** It is the Lean product with `Set.Icc a b`
  above, not `unitInterval`, so that the Hamiltonian is the coordinate
  $\lambda$ itself, as on the page. The forms of the milestone live on this
  manifold with boundary. No flow is run on it: see the next point.
- **The flows.** No flow on a manifold with boundary is needed, and neither
  library has one.
  - *Uniqueness.* The Moser fields have no $\partial_\lambda$ component, so
    they are families over $\lambda$ of fields on the closed manifold $P$.
    The Moser problem is moved to the boundaryless `P × ℝ`. A closed form
    $\omega$ on $P\times[a,b]$ is $\mathrm{pr}^*\iota_a^*\omega+d(K\omega)$,
    where $K$ is the library's homotopy operator
    (`TauCeti.SmoothForm.homotopyOperator`, which allows a source with
    boundary) composed with the pull-back by the contraction
    $((p,\lambda),s)\mapsto(p,a+s(\lambda-a))$. The one-form $K\omega$ has
    no $d\lambda$ component, so it is determined by its slices, and the
    time extension of slices of *Smooth families*
    (`TauCeti.SmoothForm.timeExtend`, after reparametrization) extends it
    to `P × ℝ`. The extended forms are closed, invariant, and agree with
    the given ones on $P\times[a,b]$. The flow of the cut-off Moser field on
    `P × ℝ` then keeps every slice $P\times\{\lambda\}$ near $[a,b]$, so it
    restricts to a diffeomorphism of $P\times[a,b]$ that maps each boundary
    level to itself.
  - *Converse.* The region is a band in a boundaryless manifold (next
    point), and the flow that identifies its levels is a flow on that
    manifold.
- **The compact manifold with boundary of the converse.** The page's notes
  on Proposition 5.1.9(ii) read the compact manifold as the region
  $H^{-1}([a,b])$, bounded by the two end levels. The library states the
  converse that way: $(M,\omega)$ is a boundaryless symplectic manifold
  with a symplectic circle action and the page's Hamiltonian $H$, and the
  band $K=H^{-1}([a,b])$ is compact, the action is free on
  $K$ and $H(K)=[a,b]$. Freeness makes $X$ nonzero on $K$, so every value
  in $[a,b]$ is regular, and Tau Ceti's band atlas
  (`TauCeti.scalarRegularBandChartedSpace`,
  `Geometry/Manifold/RegularValue/Scalar/Boundary.lean`) makes $K$ a
  compact manifold whose boundary is $H^{-1}(a)\sqcup H^{-1}(b)$, as on the
  page. The conclusion is an equivariant, injective, smooth map
  $\psi:P\times[a,b]\to M$ onto $K$ with $H\circ\psi=\lambda$ that pulls
  $\omega$ back to a coupling form. A map whose pull-back of a symplectic
  form is nondegenerate is an immersion, so $\psi$ is a bijective immersion
  onto the band. Stating it on Tau Ceti's band atlas instead would need
  the smooth structure at the corners of $P\times[a,b]$, which Tau Ceti's
  own product theorem for bands (`TauCeti.exists_bandHomeomorph_diffeomorph`,
  `Geometry/Manifold/Morse/Deformation/Band.lean`) leaves out.
- **The Chern class.** The page's $c_1(P)_{\mathbb R}$ is the class of
  Chern–Weil theory in de Rham cohomology:
  `realFirstChernClass IB P : TauCeti.deRhamCohomology IB B 2` is
  $-(2\pi)^{-1}[F_\alpha]$ for the curvature `hα.curvature` of any
  connection form. It has the normalization of *First Chern number*:
  `chernNumber_eq_integral_curvature` says that on a closed surface the
  integral of $-(2\pi)^{-1}F_\alpha$ is the Chern number of the unit
  circle bundle. With it the page's condition
  $[\tau_\lambda]-[\tau_\nu]=-(\lambda-\nu)c_1(P)_{\mathbb R}$ says that
  $\tau_\lambda-\tau_\nu-(\lambda-\nu)(2\pi)^{-1}F_\alpha$ is exact, which
  is the curvature condition the construction needs. Comparing this class
  with the image of the integral class of `Topology/VectorBundle/Complex/`
  over a general base needs de Rham's theorem with products; no milestone
  needs it, and this part does not do it.

## Departures from `DESIGN.md`

This file corrects part 39 of `DESIGN.md` in the same pull request:

- The existence of a coupling form moves from `Coupling/Basic.lean` to a
  file of its own, `Coupling/Existence.lean`, so that the predicate and its
  properties come first and two issues do not write one file.
- Two files are added: `Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean`
  (the Chern class above) and `Geometry/Manifold/GroupAction/PrincipalBundle.lean`
  (the principal bundle of a free action of a compact Lie group, which the
  converse needs to produce $P$; Tau Ceti has the quotient manifold, and
  local trivializations only topologically).
- The converse is stated for a compact band of a boundaryless manifold, as
  above.
- The part does not use `GroupAction/InvariantPrimitive.lean` of *Lie group
  actions*: the one primitive the part needs, in the uniqueness proof, is
  invariant by construction, being the homotopy operator applied to an
  invariant form along an equivariant contraction. The Moser part of
  `Moser/Equivariant.lean` takes invariant primitives as hypotheses, as
  `DESIGN.md` says. The part still uses `GroupAction/Circle.lean` (the
  generator $\xi_1$ in the converse).

## Files

| File | Contents |
|---|---|
| `Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean` | `realFirstChernClass` and its API |
| `Geometry/Symplectic/Coupling/Basic.lean` | the predicate `IsCouplingForm`, nondegeneracy, the connection family of a coupling form, the cohomological condition |
| `Geometry/Symplectic/Coupling/Existence.lean` | the construction; the existence half of the milestone |
| `Geometry/Symplectic/Moser/Equivariant.lean` | the cut-off Moser flow of invariant data commutes with the symmetries |
| `Geometry/Symplectic/Coupling/Uniqueness.lean` | the uniqueness half of the milestone |
| `Geometry/Manifold/GroupAction/PrincipalBundle.lean` | the principal bundle of a free action of a compact Lie group |
| `Geometry/Symplectic/Coupling/Converse.lean` | the converse half of the milestone |

### `Geometry/Manifold/FiberBundle/Principal/RealChernClass.lean`

Over a base as in *Setting*, with the bundle's instances.

- `realFirstChernClass (IB) (P) : TauCeti.deRhamCohomology IB B 2`,
  defined as $-(2\pi)^{-1}$ times the class of the curvature of the
  connection form that `exists_isCircleConnectionForm` chooses. The
  curvature is closed (`IsCircleConnectionForm.isClosed_curvature`).
- `IsCircleConnectionForm.realFirstChernClass_eq (hα)`: for every
  connection form, `realFirstChernClass IB P = -(2 * π)⁻¹ •
  TauCeti.deRhamCohomology.mk IB 2 ⟨hα.curvature, hα.curvature_mem_closedForms⟩`.
  Proof: two connection forms differ by `π^* a`
  (`existsUnique_eq_add_mpullback`), and their curvatures by `d a`
  (`curvature_add_mpullback`).
- `realFirstChernClass_def`, stating the definition.

About 120 lines. It uses only merged files.

### `Geometry/Symplectic/Coupling/Basic.lean`

For `ω : SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Set.Icc a b)`
and `τ : Set.Icc a b → SmoothTwoForm IB B`:

- `IsCouplingForm ω τ : Prop`, a structure with four fields: `isClosed`
  (`ω.IsClosed`); `mpullback_smul` (invariance under
  `fun x ↦ (op z • x.1, x.2)` for every `z : Circle`); `interior_eq`
  ($\iota_{(X,0)}\omega=-d\lambda$, the page's sign, with $X$ the period-one
  field above); `mpullback_slice` (the slice at $\lambda$, the pull-back
  along `fun p ↦ (p, λ)`, is `π^* (τ λ)`). This last field is the
  page's identification of the reduced spaces $H^{-1}(\lambda)/S^1$ with
  $B$. The page's form is an `IsCouplingForm` by definition; there is no
  separate name for the form $\pi^*\tau_\lambda+d\lambda\wedge\alpha_\lambda$
  beyond the construction of `Existence.lean`.
- `IsCouplingForm.isNondegenerate (h) (hτ : ∀ λ, (τ λ).IsNondegenerate)`
  and `IsCouplingForm.isSymplectic`: every coupling form over a family of
  nondegenerate forms is symplectic. The pointwise step is linear algebra:
  a two-form on $V$ whose restriction to a hyperplane $W$ has radical
  spanned by a vector $x\in W$, with $\omega(x,e)\ne0$ for some $e\notin W$,
  is nondegenerate. Here $W=\ker d\lambda$, the radical of $\pi^*\tau_\lambda$
  is the vertical line, spanned by $X$
  (`exists_eq_smul_rightFundamentalVectorField_of_mfderiv_proj_eq_zero`),
  and $\omega(X,\partial_\lambda)=-1$. The issue searches Tau Ceti's linear
  symplectic reduction for this step before stating it, publicly, in a
  linear-algebra file.
- `IsCouplingForm.sub_eq_realFirstChernClass (h)`: the page's condition,
  `mk (τ λ) - mk (τ ν) = -((λ : ℝ) - ν) • realFirstChernClass IB P` for all
  $\lambda,\nu$. Proof: along the segment $s\mapsto(p,\nu+s(\lambda-\nu))$
  the homotopy formula of `DifferentialForm/HomotopyOperator.lean` writes
  $\pi^*(\tau_\lambda-\tau_\nu)$, the difference of the two slices, as
  $d\beta$ for an invariant one-form $\beta$ on $P$ with
  $\beta(X)=\lambda-\nu$. By the affine structure of connection forms
  (`existsUnique_eq_add_mpullback`),
  $\beta=(\lambda-\nu)(2\pi)^{-1}\alpha^0+\pi^*\gamma$ for a fixed
  connection form $\alpha^0$. Since pull-back along $\pi$ is injective on
  forms (`curvature_eq_iff`),
  $\tau_\lambda-\tau_\nu=(\lambda-\nu)(2\pi)^{-1}F_{\alpha^0}+d\gamma$, and
  `realFirstChernClass_eq` gives the class.

The page writes a coupling form as
$\pi^*\tau_\lambda+d\lambda\wedge\alpha_\lambda$ for a family of connection
forms with $d\alpha_\lambda=\pi^*\dot\tau_\lambda$. No statement of the part
needs that formula, so the file does not state it: the four fields carry
all that the milestone uses, and no derivative of a family over a closed
interval is taken.

The `@[ext]`-style API is the four fields. A coupling form is affine in
its data: `IsCouplingForm.lineMap (h₀ h₁) (s : ℝ)`, that
`ω₀ + s • (ω₁ - ω₀)` is a coupling form for the same `τ`, used by
`Uniqueness.lean`. About 450 lines.

### `Geometry/Symplectic/Coupling/Existence.lean`

- `exists_isCouplingForm [CompactSpace B] (hτ : IsSmoothFamily (𝓡∂ 1) τ)
  (hτs : ∀ λ, (τ λ).IsSymplectic) (hcoh : ∀ λ ν, mk (τ λ) - mk (τ ν) =
  -((λ : ℝ) - ν) • realFirstChernClass IB P) : ∃ ω, IsCouplingForm ω τ ∧
  ω.IsSymplectic`, the existence half of the milestone. The page asks for a
  closed connected $B$; connectedness is not used and the statement drops
  it. Together with `IsCouplingForm.sub_eq_realFirstChernClass` this is the
  "exactly under the cohomological condition" of `DESIGN.md`.

Proof, with no derivative of a family. Fix a connection form $\alpha^0$
(`exists_isCircleConnectionForm`) with curvature $F$. By `hcoh` and
`realFirstChernClass_eq`, the forms
$\tau_\lambda-\tau_a-(\lambda-a)(2\pi)^{-1}F$ are exact and a smooth family,
so they have a smooth family of primitives $\beta_\lambda$
(`exists_isSmoothFamily_mextDerivₗ_eq`, through `iccHomeoI`, on a compact
manifold, which has a finite good cover). Let $A$ be the one-form
$(2\pi)^{-1}(\lambda-a)\,\mathrm{pr}^*\alpha^0+\mathrm{pr}^*\pi^*\beta_\lambda$
on the product, the second term being the vertical form of the family
(Tau Ceti's `TauCeti.verticalForm`). Then
$\omega=\mathrm{pr}^*\pi^*\tau_a+dA$ is closed. Its slices are
$\pi^*\tau_\lambda$ by naturality. It is invariant because $\alpha^0$ and
pull-backs from $B$ are. By Cartan's formula and invariance,
$\iota_X\omega=-d(\iota_XA)=-d(\lambda-a)$. It is symplectic by
`IsCouplingForm.isSymplectic`. Unfolded, $\omega$ is the page's
$\pi^*\tau_\lambda+d\lambda\wedge\alpha_\lambda$ with
$\alpha_\lambda=(2\pi)^{-1}\alpha^0+\pi^*\dot\beta_\lambda$; the proof does
not need that formula. Milestone line: *Minimal coupling*. About 300
lines, with the smoothness lemmas of `iccHomeoI` if Mathlib lacks them.

### `Geometry/Symplectic/Moser/Equivariant.lean`

- `mfderiv_moserField`: if a diffeomorphism $g$ of $M$ preserves the slices of
  the two-form $\sigma$ and of the one-form $\beta$ on `N × M` and the
  cutoff $\rho$, then `moserField σ β ρ` is $g$-related to itself.
- `timeDependentFlowOf_moserField_comp`: its time-dependent flow then
  commutes with $g$. The time-dependent flow is the flow of the suspended
  field on `ℝ × M`, which is $(\mathrm{id}\times g)$-related to itself, so
  Tau Ceti's naturality of flows under related maps
  (`Geometry/Manifold/Flow/Related.lean`, `apply_flowOf`) applies.
- For a group: an action by such diffeomorphisms gives an equivariant
  Moser isotopy.

It needs nothing of this part, and uses only the merged `Moser/Field.lean`
and the library's `Geometry/Manifold/Flow/TimeDependent.lean`. About 200
lines.

### `Geometry/Symplectic/Coupling/Uniqueness.lean`

- `IsCouplingForm.exists_diffeomorph [CompactSpace B] (h₀ : IsCouplingForm ω₀ τ)
  (h₁ : IsCouplingForm ω₁ τ) (hτ : ∀ λ, (τ λ).IsNondegenerate)`: there is
  `Ψ : (ManifoldTotalSpace Circle P × Set.Icc a b) ≃ₘ⟮_, _⟯ _` with
  `(Ψ x).2 = x.2` (it preserves $H$), `Ψ (op z • x.1, x.2) = (op z • (Ψ x).1, x.2)`
  (it is equivariant) and `SmoothForm.mpullback Ψ Ψ.contMDiff ω₁ = ω₀`.
  As the page notes, $\Psi$ need not cover the identity of $B$, and the
  statement does not claim it. Milestone line: *Minimal coupling*.

Proof:
1. $\delta=\omega_1-\omega_0$ is closed, invariant, has zero slices and
   $\iota_X\delta=0$. With the contraction $c$ above,
   $\sigma=K\delta$ (the homotopy operator of $c^*\delta$) has
   $d\sigma=\delta$ (`mextDerivₗ_homotopyOperator`, as the slice at $a$
   vanishes), is invariant because $c$ is equivariant, has no
   $d\lambda$ component, and $\sigma(X)=0$.
2. $\omega_s=\omega_0+s\delta$ is a coupling form for every $s$
   (`IsCouplingForm.lineMap`), hence symplectic.
3. The Moser field $Y_s$ with $\iota_{Y_s}\omega_s=-\sigma$ has
   $d\lambda(Y_s)=0$, because
   $-d\lambda(Y_s)=\omega_s(X,Y_s)=\sigma(X)=0$.
4. Move to `P × ℝ` as *Decisions* says: extend $\omega_0$ and $\sigma$, take
   a cutoff that depends only on $(s,\lambda)$, equal to $1$ near
   $[0,1]\times[a,b]$ and supported where the extended forms are
   nondegenerate (an open condition, by compactness of $P$). The cut-off
   Moser field (`moserField`) is smooth, compactly supported, invariant, and
   tangent to the slices near $[a,b]$. Tangency: $\iota_XK\omega_0$ is the
   function $\lambda-a$, so by Cartan's formula and invariance the extension
   has $\iota_X\tilde\omega_0=-e'(\lambda)\,d\lambda$ for the extension $e$
   of $\lambda-a$, with $e'=1$ on $[a,b]$, and the argument of step 3
   applies wherever $e'\ne0$. Its flow is jointly smooth
   (`TauCeti.contMDiff_timeDependentFlowOf_param`), equivariant
   (`Moser/Equivariant.lean`), and satisfies Moser's equation where the
   cutoff is $1$.
5. The time-one map preserves each $P\times\{\lambda\}$ for
   $\lambda\in[a,b]$, so it restricts to a diffeomorphism of
   $P\times[a,b]$ whose inverse is the restriction of the inverse flow.

About 600 lines. If it grows past that, steps 1–3 go first, in one issue,
and steps 4–5 in a second.

### `Geometry/Manifold/GroupAction/PrincipalBundle.lean`

For a compact Lie group `G` (`[LieGroup IG ∞ G]`, boundaryless and
finite-dimensional) acting smoothly and freely on the right
(`[MulAction Gᵐᵒᵖ X]`, as Tau Ceti's principal bundles act) on a
boundaryless, Hausdorff, finite-dimensional manifold $X$:

- the fibres `fun q : X ⧸ Gᵐᵒᵖ ↦ {x : X // ⟦x⟧ = q}` over Tau Ceti's
  quotient manifold (`Geometry/Manifold/GroupAction/Quotient.lean`, with
  its charted space `ProperSMul.orbitRelQuotientChartedSpace` as a local
  instance) form a `FiberBundle G`, a `PrincipalBundle G` and a
  `ContMDiffFiberBundle ∞`. The trivializations are Tau Ceti's
  trivializations from equivariant maps
  (`Topology/Algebra/GroupAction/OrbitTrivialization.lean`) with the
  equivariant maps given by the smooth local sections of the slice charts;
- `orbitBundleDiffeomorph : ManifoldTotalSpace G (orbitFiber X) ≃ₘ X`, an
  equivariant diffeomorphism over the quotient map.

A compact group acts properly. For `Circle` the converse feeds it the
right action `op z • x = z • x` of the commutative circle. The file is
general, and the parts of `atlas/symplectic-fibrations.md` and *Hamiltonian
reduction* may use it. About 600 lines; if the smooth-bundle instance runs
long, it goes in a second issue after the topological bundle.

### `Geometry/Symplectic/Coupling/Converse.lean`

- `exists_isCouplingForm_comp_eq`: let $(M,\omega)$ be boundaryless and
  symplectic, with a smooth circle action preserving $\omega$, moment map
  $\mu$ in the page's sign (`ω.IsMomentMap a (fun x ↦ -μ x)`) and
  $H=\langle\mu,\xi_1\rangle$, the generator $\xi_1$ of
  `GroupAction/Circle.lean`. Let $K=H^{-1}([a,b])$ be compact (the page
  also asks for connectedness, which the proof does not use), with
  $H(K)=[a,b]$ and the action free on $K$. Then, with $P_0=H^{-1}(a)$
  (a closed manifold, through Tau Ceti's `regularLevelChartedSpace`),
  $B=P_0/S^1$ and $P$ the bundle of `PrincipalBundle.lean`, there are a smooth
  family of symplectic forms $\tau$ on $B$, a coupling form $\omega'$ for
  $\tau$ and a smooth equivariant injective map
  $\psi:P\times[a,b]\to M$ with range $K$, $H\circ\psi=\lambda$ and
  $\psi^*\omega=\omega'$. The family $\tau$ satisfies the page's condition,
  by `IsCouplingForm.sub_eq_realFirstChernClass`. Milestone line:
  *Minimal coupling*.

Proof:
1. Tau Ceti's invariant compatible almost complex structures
   (`IsNondegenerate.exists_compatible_mfderiv_smul_apply_of_compactSpace`)
   give an invariant $J$. On the open set where $X\ne0$, which contains
   $K$, the field $Y=-JX/\omega(X,JX)$ is invariant and $dH(Y)=1$. An
   invariant cutoff equal to $1$ near $K$ with compact support in that set
   (a cutoff averaged over the circle) makes it complete.
2. Its flow $\Phi$ commutes with the action (`Flow/Related.lean`) and
   $H(\Phi_t(x))=H(x)+t$ while the trajectory stays near $K$. The map
   $\psi(p,\lambda)=\Phi_{\lambda-a}(p)$, read on the total space through
   `orbitBundleDiffeomorph`, is smooth, injective (by $H$ and the flow
   property), onto $K$ (flowing back to $P_0$), equivariant, and has
   $H\circ\psi=\lambda$.
3. $\psi^*\omega$ is closed and invariant, and $\iota_X\psi^*\omega=-d\lambda$
   because $\psi$ relates the fundamental fields and $H\circ\psi=\lambda$.
   Each slice is then basic and descends along the submersion $\pi$ to a
   unique form $\tau_\lambda$ (the library's `BasicForm.lean` or Tau Ceti's
   `existsUnique_isSymplectic_mpullback_eq`), symplectic by Tau Ceti's
   descent of nondegeneracy (`isNondegenerate_descendedForm_iff`). Smoothness
   of $\lambda\mapsto\tau_\lambda$ is local, read through local sections of
   $P$ (`isSmoothFamily_iff_contMDiff`).

About 600 lines; if it grows, steps 1–2 (the equivariant product
structure of the band, which has nothing symplectic in it beyond $J$) come
first in their own issue.

## Issues

Each issue is a few hundred lines, in an order where each comes after the
ones it waits for.

1. **The real first Chern class of a circle bundle** (`RealChernClass.lean`).
   Waits for nothing.
2. **The equivariant Moser flow** (`Moser/Equivariant.lean`). Waits for
   nothing.
3. **Coupling forms** (`Coupling/Basic.lean`). Waits for 1.
4. **Existence of coupling forms** (`Coupling/Existence.lean`, and
   `Instances/Icc.lean` if Mathlib lacks the smoothness of `iccHomeoI`).
   Waits for 3.
5. **Uniqueness of coupling forms** (`Coupling/Uniqueness.lean`). Waits for
   2 and 3.
6. **The principal bundle of a free compact group action**
   (`GroupAction/PrincipalBundle.lean`). Waits for nothing.
7. **The converse** (`Coupling/Converse.lean`). Waits for 3, 6 and
   *Lie group actions*' `GroupAction/Circle.lean` (#2256).

Issues 1, 2 and 6 can start at once.

## Uses

- *Lie group actions*: `GroupAction/Circle.lean` (#2256), only in issue 7.
- Merged files of *First Chern number*:
  `Geometry/Manifold/FiberBundle/Principal/CircleConnection.lean`,
  `BasicForm.lean`, and `chernNumber_eq_integral_curvature` for the
  normalization.
- Merged files of *Smooth families*: `IsSmoothFamily`,
  `exists_isSmoothFamily_mextDerivₗ_eq`, the time extensions, and
  `DifferentialForm/HomotopyOperator.lean`.
- Merged files of *Moser isotopy* and *Isotopy extension*: `moserField`
  (`Moser/Field.lean`), `contMDiff_timeDependentFlowOf_param`
  (`Geometry/Manifold/Flow/TimeDependent.lean`).
- Tau Ceti: principal bundles, the quotient manifold theorem, regular
  levels and bands, naturality of flows, invariant compatible almost
  complex structures, averaging of functions over a compact group, descent
  of basic forms, de Rham cohomology.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §2.7 (connection forms and curvature) and Proposition 5.1.9.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*,
  Vol. I, Chapter II (connections on principal bundles).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 21.10 (the
  quotient manifold theorem).
