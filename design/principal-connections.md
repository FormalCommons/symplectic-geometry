# Principal connections

This is the detailed design of part 50 of `DESIGN.md`, *Principal
connections*. It covers the milestone *Weinstein's universal construction
for associated symplectic fibrations* of `atlas/symplectic-fibrations.md`,
which follows McDuff–Salamon [McDuffSalamon2017], §6.3, Theorem 6.3.3 and
equations (6.3.1)–(6.3.3), by the page's direct route and in the page's
signs (*Fibrations, connections and diffeomorphism groups* in `DESIGN.md`).
The general theory of connection forms follows Kobayashi–Nomizu, Vol. I,
Chapter II.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`. All
statements about Mathlib, Tau Ceti and the library were checked against the
versions pinned when this file was written (Tau Ceti `c9d170eed5a8`).

## Setting and notation

- **The base.** `IB : ModelWithCorners ℝ EB HB`, `[IsManifold IB ∞ B]`; a
  boundaryless model `[IB.Boundaryless]` wherever Cartan's formula or
  descent is used, and `[FiniteDimensional ℝ EB]`, `[T2Space B]`,
  `[SigmaCompactSpace B]` for existence, as in the merged
  `exists_isCircleConnectionForm`.
- **The group.** `IG : ModelWithCorners ℝ EG HG` with
  `[FiniteDimensional ℝ EG]`, `[IG.Boundaryless]` and `[LieGroup IG ∞ G]`.
  Its Lie algebra is Mathlib's `𝔤 := GroupLieAlgebra IG G`, with Mathlib's
  bracket (that of left-invariant fields), and the adjoint action is Tau
  Ceti's `TauCeti.Lie.adjointContinuousLinearMap g : 𝔤 →L[ℝ] 𝔤`.
- **The bundle.** $P$ is a smooth principal `G`-bundle in Tau Ceti's form,
  with the instances of the merged
  `Geometry/Manifold/FiberBundle/Principal/BasicForm.lean`:
  `P : B → Type*`, `[FiberBundle G P]`, `[∀ b, MulAction Gᵐᵒᵖ (P b)]`,
  `[PrincipalBundle G P]`, `[ContMDiffFiberBundle ∞ G P IB IG]`. Its
  charted total space `ManifoldTotalSpace G P` is modelled on `IB.prod IG`,
  its projection is $\pi$, the right action is `fun x ↦ op g • x`, and the
  fundamental field of $\xi$ is
  `rightFundamentalVectorField (IB.prod IG) ξ` (the page's $p\xi$).
- **The fibre.** `IF : ModelWithCorners ℝ EF HF`, `[IsManifold IF ∞ F]`,
  `[IF.Boundaryless]`, with a smooth left action `[MulAction G F]`,
  `[ContMDiffSMul IG IF ∞ G F]`. Its fundamental fields are Tau Ceti's
  `fundamentalVectorField IF ξ` (the page's $X_\xi$), and
  `InfinitesimalAction.fundamental IG G IF F` is the infinitesimal action
  of Tau Ceti's moment maps.
- **The associated bundle.** $M=P\times_GF$ is
  `ManifoldTotalSpace F (AssociatedBundle G P F)`, modelled on
  `IB.prod IF`. Its smooth structure is the theorem
  `TauCeti.AssociatedBundle.contMDiffFiberBundle IG`, installed as a local
  instance where needed, as Tau Ceti's own files do. The quotient map is
  $q(x,v)=[x,v]$, the map of
  `TauCeti.AssociatedBundle.contMDiff_totalSpaceMk_mk`, and $G$ acts on
  `ManifoldTotalSpace G P × F` diagonally by
  $(x,v)\cdot g=(x\cdot g,\ g^{-1}v)$, so that $q$ is invariant (Tau
  Ceti's quotient identifies $(p\cdot g,v)$ with $(p,g\cdot v)$).
- **Moment maps and the sign.** $\mu : F\to\mathfrak g^*$ is
  `μ : F → Module.Dual ℝ 𝔤`, in the page's sign. Tau Ceti's moment maps
  have the opposite sign, so the hypothesis is
  `σ.IsEquivariantMomentMap (fun x ↦ -μ x)`, as `DESIGN.md` prescribes;
  with it, Tau Ceti's `IsEquivariantMomentMap.momentCocycle_eq_zero` gives
  the page's identity $\langle\mu,[\xi,\eta]\rangle=-\sigma(X_\xi,X_\eta)$,
  and its moment map condition gives
  $\langle d\mu(x)\hat x,\xi\rangle=-\sigma(X_\xi(x),\hat x)$.

## Decisions

`DESIGN.md` leaves three questions to this file; the review of #2280 added
two more.

- **Forms with values in $\mathfrak g$.** They are Tau Ceti's
  vector-valued forms, `SmoothForm I M 𝔤 k`, with no basis of
  $\mathfrak g$. Tau Ceti's forms take any normed space of values, and
  every operation the part needs exists for them: the pull-back
  `SmoothForm.mpullback`, the exterior derivative `mextDerivₗ`, a change
  of values along a continuous linear map `SmoothForm.mapCoeff`
  (`DifferentialForm/MapCoeff.lean`), the paired wedge
  `SmoothForm.wedgeWith` along a continuous bilinear map, with its Leibniz
  rule `mextDeriv_wedgeWith` (`DifferentialForm/Wedge/`), and the
  invariant formula for $d$ of a one-form, `SmoothForm.mextDeriv_apply_one`
  (`DifferentialForm/VectorField.lean`). The equivariance of a connection
  form is then the equation of forms
  `mpullback (op g • ·) A = mapCoeff (adjointContinuousLinearMap g⁻¹) A`.
- **The bracket $[A\wedge A]$.** It is
  `SmoothForm.wedgeWith (TauCeti.lieL ℝ 𝔤 𝔤) A A`, where Tau Ceti's
  `TauCeti.lieL 𝕜 L M : L →L[𝕜] M →L[𝕜] M`
  (`Topology/Algebra/Lie/Bracket.lean`, with `@[simp] lieL_apply`) is the
  action of a finite-dimensional Lie algebra on a Lie module as a
  continuous bilinear map, so `TauCeti.lieL ℝ 𝔤 𝔤` is the bracket of
  $\mathfrak g$. With Tau Ceti's
  normalization of the wedge, `wedgeWith_apply_one_one`, one has
  $[A\wedge A](v,w)=2[A v,A w]$, so the curvature
  $F_A=dA+\tfrac12[A\wedge A]$ has
  $F_A(v,w)=dA(v,w)+[Av,Aw]$, the page's pointwise formula. Tau Ceti's
  $d$ of a one-form is $V(A W)-W(A V)-A[V,W]$, so on horizontal fields
  $F_A(X,Y)=-A([X,Y])$ with `mlieBracket`, as the page says.
- **Descent along $P\times F\to P\times_GF$.** Tau Ceti's
  `RoughForm.isBasic_of_mpullback_eq`, with the diagonal action, and
  the smooth descent `SmoothForm.descendedForm` give it once the
  kernel of $dq$ is known; that kernel is found with the pull-back principal
  bundle $Q=\pi_M^*P$ over $M$, where $\pi_M:M\to B$ is the projection. Tau Ceti
  makes it a smooth principal `G`-bundle (`TauCeti.PrincipalBundle.pullback`
  and `TauCeti.ContMDiffFiberBundle.pullback`), and the map
  $\Phi(x,v)=\big([x,v],x\big)$ is a $G$-equivariant diffeomorphism from
  `ManifoldTotalSpace G P × F` onto its charted total space, with
  $\pi_Q\circ\Phi=q$. It carries the fundamental field of $\xi$ for the
  diagonal action, $(x\xi,-X_\xi)$, to that of $Q$. So a form on $P\times F$
  that is invariant under the diagonal action and vanishes on the vectors
  $(x\xi,-X_\xi(v))$ is the pull-back along $q$ of a unique form on $M$.
  The same diffeomorphism shows that $q$ is a surjective submersion. This
  needs no quotient manifold theorem and no compactness of $G$.
- **Values in $\Omega^1(B,\mathrm{ad}P)$.** The affine structure is stated
  over *tensorial* one-forms on $P$ of type $\mathrm{Ad}$ (Kobayashi–Nomizu,
  Chapter II, §5): $\mathfrak g$-valued forms that are equivariant as
  connection forms are and vanish on vertical vectors. These are the forms
  on $B$ with values in $P\times_G\mathfrak g$, but no vector bundle
  structure on the adjoint bundle is needed, and none is built. For a
  commutative $G$ the adjoint action is trivial
  (`TauCeti.Lie.adjointContinuousLinearMap_eq_id`), and tensorial forms are
  the basic ones, the pull-backs from $B$ of the merged circle case.
- **`IsCircleConnectionForm` is kept, and derived from `IsConnectionForm`
  by a theorem.** The real-valued circle connection forms are used by
  merged files of *First Chern number* (`CircleConnection.lean`,
  `CurvatureIntegral.lean`) and by the issues of *Minimal coupling*, whose
  normalizations (the period, $2\pi$, the Chern number) are stated for real
  forms. Rewriting them as $\mathfrak g$-valued forms would make every use
  go through the identification of $\mathfrak g$ with $\mathbb R$, for
  nothing. Instead `isConnectionForm_mapCoeff_iff` says that $\alpha$ is a
  circle connection form exactly when $\alpha\,\xi_0$ is a connection form,
  for $\xi_0=$ `circleLieGenerator`, and the curvatures agree. The circle
  connection forms are normalized on `circleLieGenerator`, not on the
  period-one generator, so this comparison does not use
  `circlePeriodOneGenerator`; no other statement of this part needs a
  period-one circle.

## Departures from `DESIGN.md`

This file corrects part 50 of `DESIGN.md` in the same pull request:

- `Principal/Connection.lean` becomes the folder `Principal/Connection/`,
  with `Basic.lean` (connection forms, horizontal spaces, the affine
  structure), `Existence.lean` and `Curvature.lean`,
  so that three issues do not write one file. The comparison of curvatures
  with the circle case is in `Curvature.lean`.
- The curvature is `connectionCurvature A`, defined for every
  $\mathfrak g$-valued one-form, rather than a declaration named
  `curvature`: it needs no proof that $A$ is a connection form, and a bare
  `curvature` in the namespace `SymplecticGeometry` would say too little.
  The table of shared definitions is corrected.

Two files are added that `DESIGN.md` does not name:
`Geometry/Lie/MaurerCartan.lean` (the Maurer–Cartan form, from which local
connection forms are built) and
`Geometry/Manifold/FiberBundle/Associated/PullbackPrincipal.lean` (the
diffeomorphism $\Phi$ above).

## Files

| File | Contents |
|---|---|
| `Geometry/Lie/MaurerCartan.lean` | the left Maurer–Cartan form of a Lie group as a smooth $\mathfrak g$-valued one-form |
| `Geometry/Manifold/FiberBundle/Principal/Connection/Basic.lean` | `IsConnectionForm`, `IsTensorialForm`, horizontal spaces, the affine structure |
| `Geometry/Manifold/FiberBundle/Principal/Connection/Existence.lean` | existence over a paracompact base |
| `Geometry/Manifold/FiberBundle/Principal/Connection/Curvature.lean` | `connectionCurvature` and its properties |
| `Geometry/Manifold/FiberBundle/Associated/PullbackPrincipal.lean` | $P\times F$ as the pull-back of $P$ to $P\times_GF$; descent along $q$ |
| `Geometry/Manifold/FiberBundle/Associated/Connection.lean` | the connection induced on $P\times_GF$ |
| `Geometry/Symplectic/Fibration/Associated.lean` | Weinstein's form and the milestone |

### `Geometry/Lie/MaurerCartan.lean`

Tau Ceti has the Maurer–Cartan form evaluated on a vector field
(`TauCeti.leftMaurerCartanEval`, `Geometry/Lie/InvariantVectorField/Basic.lean`).
This file names it as a form.

- `leftMaurerCartanForm IG G : SmoothForm IG G (GroupLieAlgebra IG G) 1`,
  whose value at $g$ on $v$ is
  `mfderiv IG IG (fun h ↦ g⁻¹ * h) g v` (`leftMaurerCartanForm_apply`).
  It is Tau Ceti's left-invariant extension `TauCeti.leftInvariantSmoothForm`
  of the identity of $\mathfrak g$, which gives its smoothness.
- `leftMaurerCartanForm_apply_mulInvariantVectorField`: the value on the
  left-invariant field of $\xi$ is $\xi$.
- `mpullback_mul_right_leftMaurerCartanForm`: the pull-back by right
  multiplication by $h$ is `mapCoeff (adjointContinuousLinearMap h⁻¹)` of
  the form.
- The Maurer–Cartan equation is not needed by this part and is not part
  of this file's issue.

### `Geometry/Manifold/FiberBundle/Principal/Connection/Basic.lean`

`A : SmoothForm (IB.prod IG) (ManifoldTotalSpace G P) 𝔤 1`.

- `structure IsConnectionForm (A) : Prop` with fields
  `mpullback_op_smul (g : G) : SmoothForm.mpullback (fun x ↦ op g • x) _ A =
  SmoothForm.mapCoeff (Lie.adjointContinuousLinearMap g⁻¹) A` and
  `apply_rightFundamentalVectorField (x) (ξ) :
  A.val x ![rightFundamentalVectorField (IB.prod IG) ξ x] = ξ`; the page's
  $A_p(p\xi)=\xi$ and $A_{pg}(vg)=\mathrm{Ad}(g^{-1})A_p(v)$.
- `structure IsTensorialForm (a) : Prop`, for a `k`-form `a`: the same
  equivariance, and `a.val x v = 0` whenever some `v j` is vertical (in the
  kernel of the derivative of the projection).
- `horizontal A x : Submodule ℝ (TangentSpace _ x)`, the kernel of $A_x$,
  for any one-form `A`, with `mem_horizontal_iff`;
  `IsConnectionForm.isCompl_horizontal`: it is a complement of the
  vertical space, through Tau Ceti's `verticalLinearEquiv`;
  `IsConnectionForm.mfderiv_op_smul_mem_horizontal`: the action preserves
  it.
- The affine structure: `IsConnectionForm.add_isTensorialForm`,
  `IsConnectionForm.isTensorialForm_sub`, and
  `IsConnectionForm.existsUnique_eq_add`
  (`∃! a, IsTensorialForm a ∧ A' = A + a`).
- `isTensorialForm_iff_isBasic` for commutative $G$: a tensorial form is a
  basic form, with the merged `isBasic_of_mpullback_op_smul`.
- The circle comparison, for `G = Circle`, in
  `Principal/Connection/Circle.lean`:
  `isConnectionForm_mapCoeff_iff : IsConnectionForm
  (SmoothForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ
  circleLieGenerator) α) ↔ IsCircleConnectionForm α`, and every
  $\mathfrak g$-valued connection form is of this form for a unique
  $\alpha$, a circle connection form
  (`IsConnectionForm.existsUnique_eq_mapCoeff`).

### `Geometry/Manifold/FiberBundle/Principal/Connection/Existence.lean`

- For an equivariant trivialization `e` of $P$ (Tau Ceti's
  `Trivialization.IsEquivariant`), with fibre coordinate
  $\theta_e(x)=(e\,x)_2\in G$, the form $\theta_e^*\theta_{MC}$, the
  Maurer–Cartan form pulled back on the preimage of `e.baseSet`, satisfies
  both conditions of `IsConnectionForm` at the points over `e.baseSet`
  (`mpullback_op_smul_mpullback_trivialization_snd_maurerCartan`,
  `mpullback_trivialization_snd_maurerCartan_apply_rightFundamentalVectorField`),
  the $\mathfrak g$-valued analogues of the merged
  `mpullback_op_smul_mpullback_trivialization_snd` and
  `mpullback_trivialization_snd_apply_rightFundamentalVectorField`. Both
  conditions are affine, so a partition of unity of the base glues these
  local forms.
- `exists_isConnectionForm [FiniteDimensional ℝ EB] [T2Space B]
  [SigmaCompactSpace B] : ∃ A, IsConnectionForm A`, glued with a smooth
  partition of unity of the base, as the merged
  `exists_isCircleConnectionForm`, whose proof it adapts and credits.

### `Geometry/Manifold/FiberBundle/Principal/Connection/Curvature.lean`

- `connectionCurvature A := mextDerivₗ _ 1 A + (1/2 : ℝ) •
  SmoothForm.wedgeWith (TauCeti.lieL ℝ 𝔤 𝔤) A A`, with
  `connectionCurvature_def` and
  `connectionCurvature_apply : (connectionCurvature A).val x ![v, w] =
  mextDeriv A x ![v, w] + ⁅A.val x ![v], A.val x ![w]⁆`.
- `IsConnectionForm.mpullback_op_smul_connectionCurvature`: the curvature is
  equivariant, by naturality of $d$ and of the wedge.
- `IsConnectionForm.connectionCurvature_apply_eq_zero_of_vertical`: it
  vanishes when one argument is vertical. With $\xi^\sharp$ the fundamental
  field, differentiating the equivariance gives
  $L_{\xi^\sharp}A=-[\xi,A]$ (the $\mathfrak g$-valued version of the
  merged `mlieDerivForm_rightFundamentalVectorField_eq_zero`, proved the
  same way along the flow $x\mapsto x\cdot\exp(t\xi)$), and Cartan's
  formula with $A(\xi^\sharp)=\xi$ constant gives
  $\iota_{\xi^\sharp}dA=-[\xi,A]$, which the bracket term cancels.
  Together with equivariance, `IsConnectionForm.isTensorial_connectionCurvature`.
- `connectionCurvature_apply_horizontal`: for vector
  fields $X,Y$ horizontal near $x$,
  $F_A(X,Y)(x)=-A_x([X,Y](x))$ with `VectorField.mlieBracket`, from
  `SmoothForm.mextDeriv_apply_one`.
- `connectionCurvature_add`: for any one-form $a$, the curvature of $A+a$
  is $F_A+d a+[A\wedge a]+\tfrac12[a\wedge a]$, written with `wedgeWith`.
- The circle case: `IsCircleConnectionForm.connectionCurvature_mapCoeff`:
  the curvature of the $\mathfrak g$-valued form of $\alpha$ is
  `mapCoeff` of the pull-back of `hα.curvature`; the bracket vanishes
  since $\mathfrak g$ is spanned by `circleLieGenerator`.

### `Geometry/Manifold/FiberBundle/Associated/PullbackPrincipal.lean`

All in the namespace `TauCeti.AssociatedBundle`, about Tau Ceti's types.
Here `M := ManifoldTotalSpace F (AssociatedBundle G P F)`, `πM` its
projection as a smooth map, and `Q := πM *ᵖ P`.

- `pullbackProjDiffeomorph n IB IG IF : (ManifoldTotalSpace G P × F) ≃ₘ^n⟮(IB.prod IG).prod IF,
  (IB.prod IF).prod IG⟯ ManifoldTotalSpace G Q`,
  $(x,v)\mapsto([x,v],x)$, with `pullbackProjDiffeomorph_apply`,
  `proj_pullbackProjDiffeomorph` ($\pi_Q\circ\Phi=q$) and
  `pullbackProjDiffeomorph_smul` (equivariance for the diagonal action). Its
  forward map is smooth by Tau Ceti's
  `ManifoldTotalSpace.contMDiff_pullback_iff`; its inverse
  $([x,v],y)\mapsto(y,\ \text{the } w \text{ with } [y,w]=[x,v])$ has as
  second coordinate Tau Ceti's `sectionFunction` of the tautological section
  `pullbackProjSection` of $Q\times_GF$ over $M$, smooth by Tau Ceti's
  `contMDiff_sectionFunction`; in a trivialization $e$ of $P$,
  $w=(e\,y)_2^{-1}(e\,x)_2\,v$ by `sectionFunction_eq_inv_smul`.
- `mfderiv_pullbackProjDiffeomorph_fundamental`: $\Phi$ carries
  $(x\xi,-X_\xi(v))$ to the fundamental field of $\xi$ on $Q$.
- `isSubmersion_totalSpaceMk_mk` and `surjective_totalSpaceMk_mk`: $q$ is
  a surjective submersion.
- `existsUnique_mpullback_totalSpaceMk_mk_eq`: a smooth form on $P\times F$
  invariant under the diagonal action and vanishing when one argument is
  $(x\xi,-X_\xi(v))$ is `mpullback q` of a form on $M$, unique by Tau
  Ceti's `SmoothForm.eq_descendedForm_iff`. It is Tau Ceti's
  `RoughForm.isBasic_of_mpullback_eq` for $q$ and the diagonal action,
  with the kernel of $dq$ found through $\Phi$.

### `Geometry/Manifold/FiberBundle/Associated/Connection.lean`

The connection induced by a connection form on $P\times_GF$
([McDuffSalamon2017], Exercise 6.3.2).

- `IsConnectionForm.associatedHorizontal hA y`: at $y=[x,v]$, the image
  under $dq_{(x,v)}$ of $\ker A_x\times 0$; it does not depend on the
  representative, by equivariance of $A$ and invariance of $q$.
- `IsConnectionForm.isEhresmannConnection_associatedHorizontal`: Tau
  Ceti's `IsEhresmannConnection` for $\pi_M$. Complementarity with the
  vertical space follows from that of `horizontal` on $P$ and from
  $\Phi$; smoothness of the distribution is checked in a local section
  of $P$, where it is the image of a smooth frame.
- `IsConnectionForm.mfderiv_totalSpaceMk_mk_horizontalLift`: the horizontal
  lift at $[x,v]$ of $w$ is $dq$ of the horizontal lift of $w$ at $x$.

This file is not used by the milestone; it is the connection that the
page's notes on the milestone compare with $\tau_A$, which later parts
(*Coupling forms*) may use.

### `Geometry/Symplectic/Fibration/Associated.lean`

Here `σ : SmoothTwoForm IF F` with `σ.IsClosed` (Tau Ceti's closedness of
forms; nondegeneracy is not needed for the construction and is not
assumed), `μ : F → Module.Dual ℝ 𝔤`, `hμ : σ.IsEquivariantMomentMap
(fun x ↦ -μ x)`, `hσG : ∀ g : G, SmoothForm.mpullback (fun x ↦ g • x) _ σ = σ`
(the action is symplectic, which the page's Hamiltonian action includes and
Tau Ceti's `IsEquivariantMomentMap` does not), and `hA : IsConnectionForm A`. Forms on $P$ and $F$ are
pulled back to `ManifoldTotalSpace G P × F` along `Prod.fst` and
`Prod.snd`.

- `momentPairing μ hμs A : SmoothForm _ (ManifoldTotalSpace G P × F) ℝ 1`,
  the one-form $\langle\mu,A\rangle$, for
  `hμs : ∀ ξ, ContMDiff IF 𝓘(ℝ) ∞ (fun x ↦ μ x ξ)`: the paired wedge,
  along evaluation `(𝔤 →L[ℝ] ℝ) →L[ℝ] 𝔤 →L[ℝ] ℝ`, of the zero-form
  `SmoothForm.ofFunction` of $\mu$ (made continuous linear in finite
  dimension) and the pull-back of $A$. With `momentPairing_apply`.
- `weinsteinForm σ μ hμs A := mpullback Prod.snd σ +
  mextDerivₗ (momentPairing μ hμs A)`, the page's
  $\sigma+d\langle\mu,A\rangle$, with `weinsteinForm_def`.
- `weinsteinForm_apply`: the page's second expression,
  $\sigma(\hat x_1+X_{A v_1},\hat x_2+X_{A v_2})+\langle\mu,F_A(v_1,v_2)\rangle$,
  with `fundamentalVectorField` and `connectionCurvature`. The proof is
  the Leibniz rule `mextDeriv_wedgeWith`, the moment map condition for
  $d\mu$, and `momentCocycle_eq_zero` for the bracket term.
- `isClosed_weinsteinForm`, from the first expression.
- `mpullback_smul_weinsteinForm`: invariance under the diagonal action,
  from the first expression, the equivariance of $A$ and of $\mu$
  (`apply_smul`), and the invariance of $\sigma$, the hypothesis `hσG`.
- `weinsteinForm_apply_eq_zero_of_fundamental`: horizontality, from the
  second expression, since $\hat x+X_{A v}$ vanishes on $(x\xi,-X_\xi)$ and
  $F_A$ vanishes on vertical vectors.
- `associatedForm σ hμ hσG hA : SmoothForm (IB.prod IF) M ℝ 2`, the descended
  form of `existsUnique_mpullback_totalSpaceMk_mk_eq`, with
  `mpullback_totalSpaceMk_mk_associatedForm` (its pull-back along $q$ is
  `weinsteinForm`), `isClosed_associatedForm`, and
  `mpullback_associatedForm_fiber`: for every point $x$ of the total space
  of $P$, its pull-back along the fibre inclusion $v\mapsto[x,v]$ is $\sigma$.
- The milestone,
  `exists_isClosed_mpullback_eq_weinsteinForm`: there is a closed
  two-form $\tau$ on $M$ whose pull-back along $q$ is
  `weinsteinForm σ μ _ A` and whose pull-back along each fibre inclusion is
  $\sigma$; its docstring ends with "Milestone: *Weinstein's universal
  construction for associated symplectic fibrations*." $F$ need not be
  compact, nor $G$.

## Issues

Each issue is a few hundred lines, in an order where each comes after the
ones it waits for.

1. **The Maurer–Cartan form** (`Geometry/Lie/MaurerCartan.lean`). Waits
   for nothing.
2. **Connection forms on principal bundles**
   (`Principal/Connection/Basic.lean`). Waits for nothing.
3. **Existence of connection forms** (`Principal/Connection/Existence.lean`).
   Waits for 1 and 2.
4. **The curvature of a connection form**
   (`Principal/Connection/Curvature.lean`). Waits for 2.
5. **$P\times F$ as a principal bundle over $P\times_GF$**
   (`Associated/PullbackPrincipal.lean`). Waits for nothing.
6. **Weinstein's construction** (`Fibration/Associated.lean`). Waits for
   4 and 5.
7. **The induced connection on an associated bundle**
   (`Associated/Connection.lean`). Waits for 2 and 5.

Issues 1, 2 and 5 can start at once.

## Uses

- Merged files of *First Chern number*:
  `Geometry/Manifold/FiberBundle/Principal/BasicForm.lean` (descent of
  basic forms, invariant forms along fundamental fields) and
  `CircleConnection.lean` (the circle comparison, and the pattern of the
  existence proof); `Geometry/Lie/Exponential/Circle.lean`
  (`circleLieGenerator`).
- No file of *Lie group actions* or *Moment maps*: the moment map
  predicate is Tau Ceti's.
- Tau Ceti: principal, pull-back and associated bundles and their smooth
  structures (`Geometry/Manifold/FiberBundle/`), fundamental fields and
  the vertical isomorphism
  (`Geometry/Manifold/FiberBundle/Principal/FundamentalVectorField.lean`),
  the adjoint and coadjoint actions (`Geometry/Lie/Adjoint/`), forms with
  values in a normed space, their pull-back, exterior derivative, wedge
  and descent (`Geometry/Manifold/DifferentialForm/`), Ehresmann
  connections (`Geometry/Manifold/Submersion/EhresmannConnection.lean`),
  equivariant moment maps
  (`Geometry/Symplectic/Hamiltonian/EquivariantMomentMap/Basic.lean`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §6.3 (connection forms on principal bundles, Exercise 6.3.2, Theorem 6.3.3).
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and
  Multiplicity Diagrams*][GuilleminLermanSternberg1996], Chapter 1.
* [A. Weinstein, *A universal phase space for particles in Yang–Mills
  fields*][Weinstein1978].
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*,
  Vol. I, Interscience, 1963, Chapter II (connections on principal
  bundles, tensorial forms, curvature and the structure equation).
