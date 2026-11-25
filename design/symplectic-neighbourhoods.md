# Symplectic neighbourhoods

This is the detailed design of part 19 of `DESIGN.md`, *Symplectic
neighbourhoods*. It covers six milestones of `atlas/symplectic-manifolds.md`:
*Characteristic foliations and local symplectic quotients*, *Symplectic
neighbourhood theorem*, *Lagrangian neighbourhood theorem*, *Isotropic
neighbourhood theorem*, *Coisotropic neighbourhood theorem* and *Darboux
charts adapted to submanifolds*. They follow McDuff–Salamon
[McDuffSalamon2017], §3.4 (Exercise 3.4.9, Theorems 3.4.10 and 3.4.13,
Exercises 3.4.18 and 3.4.19, and the remarks on non-compact submanifolds on
p. 124). The isotropic and coisotropic theorems are also in Cieliebak's notes
[Cieliebak2010], Theorem 6.10 and Corollaries 6.13 and 6.14. The coisotropic
theorem is Gotay's, and [OhPark2005], §3, gives its explicit model.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`;
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. Manifolds, forms, embeddings and neighbourhood germs follow
*Manifolds, families and signs* of `DESIGN.md`. Every manifold here is
boundaryless, finite-dimensional, Hausdorff and second countable, as Tau
Ceti's tubular neighbourhoods and Moser theorems need it to be.

## What exists, and what the part adds

Tau Ceti has the pointwise and local ingredients. It has none of the
theorems about a neighbourhood of a whole submanifold.

- **Kernel foliations.** `TauCeti.SmoothForm.isInvolutiveDistribution_ker_bilinFormAt`
  (`Geometry/Manifold/TwoForm/Kernel.lean`) says that the kernel of a closed
  two-form is involutive. If the rank is constant, which Tau Ceti states as
  `hk : ∀ x, finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k`,
  `TauCeti.SmoothForm.characteristicFoliation` is the foliation of the
  kernel. For a coisotropic immersion, `IsCoisotropicMap.characteristicFoliation`
  and `map_characteristicFoliation_distribution`
  (`Geometry/Symplectic/Lagrangian/Presymplectic.lean`) identify the kernel
  with $(TQ)^\omega$. Frobenius is
  `TauCeti.IsInvolutiveDistribution.exists_flatChart` and
  `exists_flatChart_extend` (`Geometry/Manifold/Distribution/FlatChart.lean`).
  These give a chart that carries the distribution to a constant subspace
  `W`. They say nothing about the shape of the chart's image or about
  connected plaques.
- **Descent.** `TauCeti.SmoothForm.descendedForm` and
  `TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`
  (`Geometry/Manifold/DifferentialForm/Pullback/Submersion.lean`,
  `Geometry/Symplectic/Manifold/Descent.lean`) descend a form along a
  surjective submersion (Mathlib's `Manifold.IsSubmersion`), given
  `RoughForm.IsBasic`. Tau Ceti's only criterion for `IsBasic`,
  `isBasic_of_mpullback_eq`, needs fibre-preserving self-maps that act
  transitively on the fibres. It has no criterion from connected fibres.
- **Normal bundles.** `TauCeti.SmoothEmbedding.NormalSpace` with its bundle
  structure `normalSpaceFiberBundle`; the symplectic normal form
  `TauCeti.SmoothEmbedding.symplecticNormalForm` with
  `symplecticNormalRepresentative` and `contMDiff_symplecticNormalRepresentative`
  (`Geometry/Symplectic/Lagrangian/Embedding/Symplectic/Normal.lean`); and the
  splitting `HasSymplecticTangentImages.isCompl` (`.../SymplecticTangent.lean`).
- **Tubular neighbourhoods.** `TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`
  (`Geometry/Manifold/TubularNeighborhood/Existence.lean`) controls nothing
  about the derivative along the zero section. The Riemannian normal
  exponential `normalExp` (`.../TubularNeighborhood/Riemannian/`) has the
  derivative `mfderiv_normalExp_zeroSection_apply`, $(u,v)\mapsto
  df(u)+\operatorname{rep}(v)$, and is a partial diffeomorphism near the zero
  section (`exists_partialDiffeomorph_normalExp_subset`). For any map near a
  section, Tau Ceti has `exists_partialDiffeomorph_near_section`
  (`Geometry/Manifold/LocalDiffeomorph/Section.lean`). For the exponential map
  of a metric it has `contMDiffOn_prodMk_proj_riemannianExp` and
  `mfderiv_prodMk_proj_riemannianExp_zeroSection_apply`
  (`Geometry/Manifold/Riemannian/Geodesic/Exponential/VariableBase.lean`).
- **Moser.** Tau Ceti's relative Moser theorem
  `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`
  (`Geometry/Symplectic/Manifold/RelativeMoser.lean`) gives a diffeomorphism
  of neighbourhoods with derivative the identity along the submanifold, but
  only for `[CompactSpace Q]`. The non-compact theorem is the milestone
  *Relative Moser theorem with prescribed first derivative* of *Moser
  isotopy* (`Geometry/Symplectic/Moser/Relative.lean`).
- **Local results.** The pointwise relative Darboux theorem
  `TauCeti.SmoothTwoForm.exists_partialDiffeomorph_fix_immersion_mpullback_eq`
  (`Geometry/Symplectic/Manifold/RelativeDarboux.lean`), and the Darboux
  charts `TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`
  (`Geometry/Symplectic/Manifold/Darboux.lean`), whose charts are
  `PartialDiffeomorph I 𝓘(ℝ, X) M X ∞` and pull a constant form back through
  `mvfderiv`.
- **Linear algebra.** Witt's extension theorem
  `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`
  (`Geometry/Symplectic/WittExtension.lean`), the linear reduction
  `TauCeti.SymplecticForm.ReducedSpace` and `reduction`
  (`Geometry/Symplectic/LinearReduction.lean`, with the library's
  `LinearAlgebra/Symplectic/Reduction.lean`), and the coisotropic model
  `LinearMap.BilinForm.IsAlt.coisotropicModel`. Each of them only says that
  something exists at one point. A neighbourhood theorem needs a smooth
  family of linear symplectomorphisms along the submanifold, so it needs a
  construction, and a choice made point by point is not enough.
- **Cotangent bundles.** `TauCeti.CotangentBundle.symplecticForm`, which is
  $-d\lambda_{\mathrm{can}}$, and `isLagrangianMap_zeroSection`
  (`Geometry/Symplectic/Cotangent/Bundle/Graph.lean`). Tau Ceti has no
  bundled `SmoothEmbedding` for a zero section.

The part adds four things. The first is the descent of a closed form of
constant rank along any submersion with connected fibres onto a ball, with
the charts. The second is a smooth construction of the linear
symplectomorphism along the submanifold. The third is a diffeomorphism of
neighbourhoods with a prescribed derivative along the submanifold. The last
is one comparison theorem for submanifolds whose restricted form has
constant rank, of which the four neighbourhood milestones are corollaries.

## Decisions

`DESIGN.md` leaves one question to this file: which open issues of
*Symplectic vector bundles* the part waits for. The answer comes from the
following choices.

- **One theorem behind the four neighbourhood theorems.** Each of the four
  types has a restricted form $\sigma=f^*\omega$ of constant rank: rank
  $\dim Q$ for a symplectic submanifold, $0$ for an isotropic or Lagrangian
  one, and corank the codimension for a coisotropic one. Write
  $W_q=df_q(T_qQ)$ and $K_q=W_q\cap W_q^\omega=df_q(\ker\sigma_q)$. The
  comparison theorem of `Neighborhood/Basic.lean` takes two embeddings
  `f₀ : Q → M₀` and `f₁ : Q → M₁` of the same manifold, with equal
  restricted forms of constant rank and equal ambient dimensions, and a
  smooth family of linear maps $L_q:T_{f_0q}M_0\to T_{f_1q}M_1$ that carries
  $W_0^\omega$ into $W_1^\omega$ and preserves $\omega$ there. Such an $L$
  induces a symplectic isomorphism of the reduced normal spaces
  $W^\omega/K$; this is shown below. The theorem gives a symplectomorphism
  $\psi$ of neighbourhoods with $\psi\circ f_0=f_1$, $d\psi\circ
  df_0=df_1$, and $d\psi(v)-L(v)\in W_1$ for $v\in W_0^\omega$, that is,
  $d\psi$ induces the same map as $L$ on the reduced normal spaces. A
  diffeomorphism $\varphi:Q_0\to Q_1$ of the milestones enters as
  `f₁ := f₁' ∘ φ`. For the Lagrangian and coisotropic theorems $W^\omega=K$
  and $L=0$. For the symplectic theorem $L$ is $\Phi$ read through the
  symplectic normal representatives. For the isotropic theorem $L$ is the
  datum itself (next point).
- **Reduced normal bundles are given by smooth lifts.** Tau Ceti has a
  smooth bundle structure on the normal bundle $TM|_Q/TQ$, but not on
  $(TQ)^\omega/TQ$. The isotropic theorem takes its isomorphism $\Phi$ of
  symplectic normal bundles as the map that a smooth family
  $L_q:T_{f_0q}M_0\to T_{f_1(\varphi q)}M_1$ induces on the fibres
  `(hω.symplecticFormAt (f q)).ReducedSpace ((hω.symplecticFormAt (f q)).orthogonal W_q)`:
  $L$ maps $W_0^\omega$ into $W_1^\omega$ and preserves $\omega$ on it.
  Every smooth bundle isomorphism of these quotient bundles is of this form,
  because smooth complements lift it. So the statement is equivalent to the
  milestone's and builds no bundle. A later page that needs the quotient
  bundle itself can build it and its comparison with this form. The
  symplectic theorem is stated with Tau Ceti's normal bundle, as `DESIGN.md`
  says: $\Phi$ is a family
  `∀ q, f₀.NormalSpace q hn ≃L[ℝ] f₁.NormalSpace (φ q) hn`, smooth on total
  spaces, that preserves `symplecticNormalForm`.
- **The linear extension comes from compatible complex structures.**
  Smoothly in $q$, the comparison theorem needs a linear symplectomorphism
  $A_q:T_{f_0q}M_0\to T_{f_1q}M_1$ with $A_q\circ df_0=df_1$ and inducing
  $L$ on reduced normal spaces. A compatible $J$ gives the metric
  $g=\omega(\cdot,J\cdot)$, and with it the $\omega$-orthogonal splitting
  $V=H\oplus(K\oplus JK)\oplus E$ with $H=W\cap K^{\perp_g}$ and
  $E=(H\oplus K\oplus JK)^\omega$ (*`LinearAlgebra/Symplectic/Extension.lean`*
  below). On it, $A$ is given by an explicit formula. A
  `TauCeti.SmoothAlmostComplexStructure` on each $M_j$ compatible with
  $\omega_j$ comes from Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`, under the
  standing `[T2Space M]` and `[SigmaCompactSpace M]`, and
  `TauCeti.SmoothTwoForm.Compatible.compatibleAt` reads it at each point.
  That existence is used in `Neighborhood/Basic.lean` only:
  `Neighborhood/Extension.lean` takes the complex structures as
  arguments. So the part waits for no open issue of *Symplectic vector
  bundles*: neither #254, nor #266, nor #269.
- **Pull-backs and local Darboux frames are not needed.** $L$ and $A$ are
  stated as sections over $Q$ of the bundle of linear maps between the
  pull-backs `f₀ *ᵖ TangentSpace I₀` and `f₁ *ᵖ TangentSpace I₁`. These are
  Mathlib's pull-back bundles; Tau Ceti's
  `Bundle.Pullback.contMDiff_hom_section_iff` reads their smoothness. That
  uses nothing of #269. #269 is merged anyway, so taking it would add no
  blocker. The adapted Darboux charts come from Tau Ceti's pointwise
  relative Darboux theorem (below), not from frames, so the part does not
  wait for #266.
- **The adapted charts are local.** The milestone *Darboux charts adapted
  to submanifolds* needs neither the neighbourhood theorems nor `Tubular.lean`.
  Near $q_0$, a chart of $Q$ suited to its type, extended in the normal
  directions, gives a local diffeomorphism $g$ from a ball of
  `StdSpace (Fin n)` into $M$. It carries the linear subspace $S$ of the
  milestone's equations into $Q$, and $g^*\omega$ restricts on $S$ to the
  restriction of `stdForm`. Tau Ceti's flat theorem
  `exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`
  then corrects $g$
  to a symplectic one fixing $S$ near $0$. So `AdaptedDarboux.lean` waits
  only for `CharacteristicFoliation.lean`, which gives the coisotropic chart
  of $Q$. This follows the note of the review of #420.
- **Models.** The adapted charts are on `StdSpace (Fin n)` with `stdForm`,
  where $\omega_0=\sum_j dx_j\wedge dy_j$ (`stdForm_apply`). So the book's
  $q_j$ is `z.x j` and $p_j$ is `z.y j`, indices running over `Fin n` from
  `0`. The ball of `CharacteristicFoliation.lean` is the open unit ball of
  `StdSpace (Fin r)`, as an open subset (`TopologicalSpace.Opens`), and its
  leaf directions are the unit ball of `EuclideanSpace ℝ (Fin k)`.
- **Hypotheses on the submanifold.** A submanifold is
  `f : TauCeti.SmoothEmbedding J I ∞ Q M` with Tau Ceti's predicate on maps
  (`hω.HasSymplecticTangentImages J f`, `IsIsotropicMap`, `IsLagrangianMap`,
  `IsCoisotropicMap`). Tau Ceti's `...Embedding` structures are equivalent
  for a smooth embedding (`is…Embedding_iff_of_isSmoothEmbedding`).
  *Properly embedded* is `IsClosed (Set.range f)`. `Tubular.lean` does not
  need it, since the relative Moser theorem of *Moser isotopy* assumes no
  closed image; the theorems never assume it of $f_1$, and the symplectic and
  Lagrangian theorems not of $f_0$ either.
- **The relative Moser theorem that the part uses.** `Tubular.lean` needs
  the milestone *Relative Moser theorem with prescribed first derivative*
  in the form of Tau Ceti's `exists_diffeomorph_opens_of_eq_along`, without
  `[CompactSpace Q]`. Its Lean name and
  exact form are for `design/moser-isotopy.md` to fix; issue 6 below uses
  whatever that file gives.

## Departures from `DESIGN.md`

`DESIGN.md` is updated with this file, in its part 19, its dependency row
and two rows of its milestone table.

- These files are added. Each neighbourhood theorem would otherwise repeat
  the linear extension and its smoothness. The list has one file to a line,
  in the order of the paths as written here, and a new file goes in at its
  place in that order: pull requests that each add a file then change
  different lines.
  - `Geometry/Manifold/Diffeomorph/Basic.lean`: the diffeomorphism between
    empty manifolds on two models, which `MFDeriv.lean`, the neighbourhood
    theorems and *Moser isotopy*'s `Moser/Relative.lean` use.
  - `Geometry/Manifold/Distribution/FlatChart.lean`: the step of
    `CharacteristicFoliation.lean` that uses nothing symplectic.
  - `Geometry/Manifold/IsManifold/Basic.lean`: three instances for smooth
    steps, here and in other parts: `C^(m + 1)` structures from `C^∞` ones,
    `IsNormableSpace` on tangent spaces, which `Adjoint.lean` needs when
    its fibres are tangent spaces, and `Nontrivial` on tangent spaces, which
    `Energy/Density.lean` of *Pseudoholomorphic energy* uses.
  - `Geometry/Manifold/SmoothEmbedding/Diffeomorph.lean`: reparametrising a
    smooth embedding by a diffeomorphism from a manifold on another model, which
    `Symplectic.lean`, `Isotropic.lean` and `Coisotropic.lean` use.
  - `Geometry/Manifold/TubularNeighborhood/MFDeriv.lean`: the step of
    `Tubular.lean` that uses nothing symplectic.
  - `Geometry/Manifold/VectorBundle/Adjoint.lean`: a step of
    `Neighborhood/Extension.lean` that uses nothing symplectic.
  - `Geometry/Manifold/VectorBundle/Orthogonal.lean`: a step of
    `Neighborhood/Extension.lean` that uses nothing symplectic.
  - `Geometry/Manifold/VectorBundle/Subbundle.lean`: a step of
    `Neighborhood/Extension.lean` that uses nothing symplectic.
  - `Geometry/Manifold/VectorBundle/ZeroSection.lean`.
  - `LinearAlgebra/BilinearForm/Orthogonal.lean`: the linear-algebra lemma
    of `VectorBundle/Orthogonal.lean`.
  - `LinearAlgebra/Symplectic/Extension.lean`.
  - `Neighborhood/Basic.lean`.
  - `Neighborhood/Extension.lean`.
  - `Neighborhood/Frames.lean`: the smooth frames of the pieces of the
    splitting along `Q`, a step of `Neighborhood/Extension.lean`.
  - `Topology/Sets/Opens/Basic.lean`: the `IsEmpty` instance of
    `⊥ : Opens X`, beside Tau Ceti's `Topology/Sets/Opens.lean`.
- `Lagrangian.lean` no longer uses *Cotangent bundles* or
  `normalBundleDiffeomorphOfIsLagrangianMap`, since the comparison theorem
  needs only that the zero section is Lagrangian. The part therefore no
  longer builds on *Cotangent bundles*. No open issue has a blocker that
  this changes: #476 is blocked only by its design issue.
- `Analysis/Calculus/DifferentialForm/LieDeriv.lean` is added, in
  `SymplecticGeometry`, for the flat lemmas that `CharacteristicFoliation.lean` uses:
  they use nothing of symplectic geometry. *Contact geometry* later adds to
  it, in `TauCeti`, the linearity of the flat Lie derivative in the field.
- `AdaptedDarboux.lean` uses Tau Ceti's pointwise relative Darboux theorem
  instead of the neighbourhood theorems, so it can start at once. Its general
  steps are in five files of their own, listed in building issue 10.
- The part no longer builds on *Symplectic vector bundles*, neither on
  `Symplectic/Basic.lean` nor on any of its open issues: the compatible
  complex structures come from Tau Ceti, and the symplectic normal bundle
  is read through Tau Ceti's `symplecticNormalForm`. Its imports from
  that part are the merged `Geometry/Manifold/IsManifold/InteriorBoundary.lean`,
  in `CharacteristicFoliation.lean` and `FlatChart.lean`, for the open
  targets of maximal-atlas charts on a manifold without boundary, and the
  merged `Geometry/Manifold/VectorBundle/Pullback.lean`, in `Adjoint.lean`.

## Files and their contents

### `Geometry/Symplectic/Manifold/CharacteristicFoliation.lean`

The local quotients of a closed two-form of constant rank. Namespace
`TauCeti.SmoothForm`, beside Tau Ceti's `characteristicFoliation`, since
dot notation on `σ` finds it. For `σ : SmoothForm I M ℝ 2` with
`[BoundarylessManifold I M]` (`[I.Boundaryless]` for the descent and the
charts, as Tau Ceti's descent theorem and
`ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv` ask), and a manifold `B` over a model `IB`, which is an
explicit argument, `IsCharacteristicSubmersion IB σ p`, since `p` does not
determine it:

```lean
structure IsCharacteristicSubmersion (IB) (σ : SmoothForm I M ℝ 2) (p : M → B) : Prop where
  isSubmersion : Manifold.IsSubmersion I IB ∞ p
  surjective : Function.Surjective p
  isPreconnected_preimage_singleton : ∀ b, IsPreconnected (p ⁻¹' {b})
  ker_mfderiv : ∀ x, (mfderiv I IB p x).ker = LinearMap.ker (σ.bilinFormAt x)
```

This is the book's foliation-compatible chart, read on the whole of `M`.
On an open `U`, it is applied to `U` and the restriction
`SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ`.

- `IsCharacteristicSubmersion.isBasic (hp) (hσ : σ.IsClosed) :
  RoughForm.IsBasic IB p σ.val`. Route: for `x` in the fibre over `b`,
  write $\tau_x$ for the form on $T_bB$ with $\tau_x(dp\,u,dp\,v)=\sigma_x(u,v)$.
  It is well defined because `ker_mfderiv` holds and `σ` vanishes on its
  kernel (`IsCharacteristicSubmersion.apply_eq_of_mfderiv_eq`).
  $x\mapsto\tau_x$ is locally constant on the fibre. Near `x`, the chart
  of the submersion `p` at `x` (Mathlib's `IsSubmersionAt.domChart`), in
  which `p` is a linear projection, carries `σ` to a closed form
  (Tau Ceti's `SmoothForm.contDiffOn_mpullback`,
  `SmoothForm.IsClosed.extDeriv_mpullback_eq_zero`) whose
  kernel contains the constant subspace `W` of vertical vectors. By
  Cartan's formula for a constant vector field
  (`fderiv_apply_eq_zero_of_extDeriv_eq_zero` and
  `apply_add_eq_of_extDeriv_eq_zero`, in
  `Analysis/Calculus/DifferentialForm/LieDeriv.lean`),
  its coefficients do not change along `W`. On a ball in the chart, the
  part of the fibre through `x` is a slice parallel to `W`, so $\tau$ is
  constant there. A locally constant map on a preconnected fibre is
  constant.
- `IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq (hp)
  (hσ : σ.IsClosed) : ∃! τ : SmoothTwoForm IB B, τ.IsSymplectic ∧
  SmoothForm.mpullback p hp.isSubmersion.contMDiff τ = σ`, from Tau Ceti's
  `existsUnique_isSymplectic_mpullback_eq` with `isBasic`. Uniqueness among
  all forms, symplectic or not, is Tau Ceti's
  `SmoothForm.mpullback_injective_of_surjective` and needs no new lemma.
- `exists_isCharacteristicSubmersion (σ) (hσ : σ.IsClosed) (hk : ∀ x,
  finrank ℝ (LinearMap.ker (σ.bilinFormAt x)) = k) (hr : finrank ℝ E = k +
  2 * r) (x : M)`: there are an open `U ∋ x` and a diffeomorphism `Ψ` from
  `U` onto the product of the unit balls of `EuclideanSpace ℝ (Fin k)` and
  `StdSpace (Fin r)` (an open subset of the product) whose second component
  `p` is an `IsCharacteristicSubmersion` of the restriction of `σ` onto the
  ball of `StdSpace (Fin r)`. The first component gives the leaf
  coordinates that `AdaptedDarboux.lean` needs; `Ψ` sends `x` to `0`.
  Route: `exists_flatPartialDiffeomorph` (`FlatChart.lean`) for the
  kernel distribution gives a partial diffeomorphism `Φ` into the product,
  with `Φ x = 0` and the unit ball in its target, whose derivative sends
  the kernels to the vectors with second component `0`. Restrict `Φ` to
  the preimage of the unit ball. The fibres of `p` are the preimages of
  slices `ball × {b}`, so they are convex in the chart, hence connected. `p` is a submersion by
  Tau Ceti's `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv`
  (`Geometry/Manifold/Submersion/Split.lean`). The kernel of `dp` is the
  flat directions, so it is the kernel of `σ`.
- The milestone, as one theorem:
  `exists_isCharacteristicSubmersion_and_existsUnique_isSymplectic_mpullback_eq`. It
  states the involutivity of the kernel (Tau Ceti's), the charts of
  `exists_isCharacteristicSubmersion` around every point, and for every
  open `U`, every open `B ⊆ StdSpace (Fin r)` and every
  `IsCharacteristicSubmersion` from `U` onto `B`, the unique symplectic
  form downstairs. Milestone: *Characteristic foliations and local
  symplectic quotients*.
- The coisotropic case, in namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap`:
  `IsCoisotropicMap.exists_isCharacteristicSubmersion` applies the above to `σ = f^*ω` for a coisotropic immersion `f` of a closed
  `ω`, with `k` the codimension, explicit with `hk : finrank ℝ F + k =
  finrank ℝ E`, from Tau Ceti's
  `IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback`. Then
  `IsCoisotropicMap.isIsotropic_map_ker_bilinFormAt_mpullback` says that
  $df$ maps the kernel, the tangent spaces of the leaves, onto an isotropic
  subspace, which is $(TQ)^\omega$ by Tau Ceti's
  `map_characteristicFoliation_distribution`. Its docstring also ends with
  the milestone line, since the milestone has this second statement.
  `IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm`, with the
  same hypotheses and an identification `L` of the model of `N` with
  `EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)`, applies
  `exists_partialDiffeomorph_eval₂_eq_stdForm` to `f^*ω` in the same way:
  a chart of `N` in which `f^*ω` is the pull-back of `stdForm (Fin r)`
  along the second component of `L`. `AdaptedDarboux.lean` takes its
  coisotropic chart from it.

### `LinearAlgebra/Symplectic/Extension.lean`

Linear and pointwise. Namespace `TauCeti.SymplecticForm`. Let `ω` be a
symplectic form on a finite-dimensional `V`, `J` a compatible
`TauCeti.AlmostComplexStructure V` (`hJ : ω.Compatible J`), with
$g=\omega(\cdot,J\cdot)$ (Tau Ceti's `2⁻¹ •` `symmetrizedBilinForm`, per
the table of *Conventions*), and `W : Submodule ℝ V`.

- The pieces, as submodules defined from `ω`, `J` and `W`, each with its
  `_def` lemma: `W ⊓ ω.orthogonal W` (the radical $K$, a Tau Ceti
  expression, not a new definition); `ω.radicalComplement J W` ($H=W\cap
  K^{\perp_g}$); `ω.normalComplement J W` ($E=(H\oplus K\oplus JK)^\omega$,
  the $g$-orthogonal of $J(H\oplus K\oplus JK)$; it lies in $W^\omega$,
  but need not be $g$-orthogonal to $H$).
  Lemmas: `Disjoint` and `⊔` statements for $W=H\oplus K$ and
  $W^\omega=K\oplus E$ (`radicalComplement_sup_inf`,
  `inf_sup_normalComplement`);
  `IsSymplectic` for $H$ and $E$; $J K$ is isotropic and
  $V=H\oplus K\oplus JK\oplus E$, with $H$, $K\oplus JK$ and $E$ pairwise
  $\omega$-orthogonal; and `normalComplement` maps isomorphically and
  symplectically onto `ω.ReducedSpace (ω.orthogonal W)`.
- `hJ₀.extendAlong hJ₁ b hb L hL hLω hdim : V₀ ≃ₗ[ℝ] V₁`, for
  `b : W₀ ≃ₗ[ℝ] W₁` preserving the restricted forms (`hb`) and a linear
  `L : V₀ →ₗ[ℝ] V₁` with
  `hL : ∀ v ∈ ω₀.orthogonal W₀, L v ∈ ω₁.orthogonal W₁` and
  `hLω : ∀ v ∈ ω₀.orthogonal W₀, ∀ w ∈ ω₀.orthogonal W₀, ω₁ (L v) (L w) =
  ω₀ v w`, and with `hdim : finrank ℝ V₀ = finrank ℝ V₁`. It is `b` on $W_0$. On
  $E_0$ it is $L$ followed by the projection onto $E_1$ along $K_1$. On
  $J_0K_0$, $J_0k$ goes to the unique $u\in H_1\oplus J_1K_1$ with
  $\omega_1(b\,w,u)=\omega_0(w,J_0k)$ for all $w\in W_0$, corrected by the
  element $c(k)\in K_1$ with $\omega_1(c(k),u')=-\tfrac12\omega_1(u(k),u(k'))$
  for the $u'=u(k')$, so that the image of $J_0K_0$ is isotropic. API:
  `isSymplectomorphism_extendAlong`, `extendAlong_apply_coe` (on `W₀` it is
  `b`), `extendAlong_sub_mem` (`extendAlong v - L v ∈ W₁` for
  `v ∈ ω₀.orthogonal W₀`), and `extendAlong_def`. The lemma that `L`
  induces a form-preserving bijection of the reduced spaces, with the
  dimension count that makes $L(K_0)\subseteq K_1$ automatic, is
  `exists_isSymplectomorphism_reducedSpace_of_forall_apply_eq`, with
  `ker_restrict_le_comap_of_forall_apply_eq` for $L(K_0)\subseteq K_1$; they
  are in `LinearAlgebra/Symplectic/Reduction.lean`. That an isometry `b`
  preserves the dimension of the radical is Tau Ceti's
  `Submodule.finrank_inf_orthogonalBilin_eq_of_isometry`.
  Tau Ceti's Witt extension is the existence
  statement; this file gives a formula, so that the next file can prove it
  smooth.

### `LinearAlgebra/Range.lean`

The map `b` of the next file, for any two injective linear maps out of one
space. Namespace `LinearEquiv`.

- `LinearEquiv.ofInjectiveRange i j hi hj : range i ≃ₗ[R] range j`, sending
  `i x` to `j x`, with its inverse `ofInjectiveRange j i hj hi`. Also used
  by `LinearAlgebra/FiniteDimensional/Extension.lean`.

### `Geometry/Symplectic/Neighborhood/Extension.lean`

The construction above along a submanifold, smoothly. Namespace
`TauCeti.SmoothEmbedding`. For `f₀ : SmoothEmbedding J I₀ ∞ Q M₀`,
`f₁ : SmoothEmbedding J I₁ ∞ Q M₁`, two-forms `ω₀`, `ω₁` with compatible
`J₀ J₁ : TauCeti.SmoothAlmostComplexStructure` on `M₀` and `M₁`, with
`SmoothForm.mpullback f₁ _ ω₁ = SmoothForm.mpullback f₀ _ ω₀` of constant
rank, `finrank ℝ E₀ = finrank ℝ E₁`, and `L` a smooth section over `Q` of the
hom bundle of the pull-backs satisfying `hL` and `hLω` at every `q` (the
constant rank and the smoothness of `L` are hypotheses of
`contMDiff_smoothExtendAlong` only):

- `smoothExtendAlong … q : TangentSpace I₀ (f₀ q) ≃L[ℝ] TangentSpace I₁ (f₁ q)`,
  the map `extendAlong` of the previous file at `q`, with $W_j=df_j(T_qQ)$
  and `b` = $df_1\circ df_0^{-1}$ on $W_0$ (`mfderivRangeEquiv`);
  `smoothExtendAlong_def`.
- `contMDiff_smoothExtendAlong`: it is a smooth section of the hom bundle
  of the pull-backs. Route: the frames of the pieces along `f`, and the smooth
  projections along the splittings that `extendAlong_def` uses, are in
  `Neighborhood/Frames.lean` (namespace `TauCeti.SmoothEmbedding`), which
  imports `Geometry/Symplectic/Manifold/Flat.lean` of *Moser isotopy* for
  the flat maps of `σ` along `f`. Tau Ceti's `contMDiff_hom_bundle_iff`
  makes those projections smooth sections of the endomorphism bundles. On
  $W_0$ and $W_1$, `b` and $b^{-1}$ are $df_1\circ S_0$ and $df_0\circ S_1$
  for smooth left inverses $S_j$ of $df_j$
  (`exists_contMDiff_leftInverse_mfderiv`, from
  `Manifold.IsImmersion.exists_contMDiff_leftInverse_mfderiv` in
  `Geometry/Manifold/VectorBundle/Adjoint.lean`: the adjoint of $df$ for
  $\sigma(J\cdot,\cdot)$ and its pull-back to $TQ$).
- The adjoint step $(\omega_1^\flat)^{-1}\circ T^*\circ\omega_0^\flat$ of
  `extendAlong_def` is smooth by `ContMDiff.clm_bundle_bilinAdjoint`
  (`Geometry/Manifold/VectorBundle/Adjoint.lean`), for
  `ContinuousLinearMap.bilinAdjoint`, whose linear map is that formula
  (`ContinuousLinearMap.coe_bilinAdjoint`); both are in part 9's
  `Topology/Algebra/Module/BilinearForm.lean`.
- `smoothExtendAlong_comp_mfderiv` ($A\circ df_0=df_1$, applied:
  `smoothExtendAlong_apply_mfderiv`),
  `isSymplectomorphism_smoothExtendAlong` (at each `q`, for
  `hc₀.isNondegenerate.symplecticFormAt (f₀ q)` and the same for `f₁`), and
  `smoothExtendAlong_sub_mem`.

### `Geometry/Manifold/Distribution/FlatChart.lean`

The flat chart that `exists_isCharacteristicSubmersion` uses. It uses
nothing symplectic, so it sits with the manifold topic, beside Tau Ceti's
`Geometry/Manifold/Distribution/FlatChart.lean`. Namespace `TauCeti`.

- `IsInvolutiveDistribution.exists_flatPartialDiffeomorph (hinv) (hD :
  IsContMDiffDistribution I ∞ k D) (h₁ : finrank ℝ F₁ = k) (h₂ : finrank ℝ
  E = k + finrank ℝ F₂) (x : M)`, with `[BoundarylessManifold I M]`: a
  `PartialDiffeomorph` `Φ` into `F₁ × F₂` with `x` in its source,
  `Φ x = 0`, the unit ball in its target, and `(dΦ_y v).2 = 0 ↔ v ∈ D y`
  on its source. Route: Tau Ceti's `exists_flatChart`, a splitting of the
  model space along the flat subspace, and `Diffeomorph.smulAdd`.

### `Geometry/Manifold/TubularNeighborhood/MFDeriv.lean`

The first half of the common step of `DESIGN.md`. It uses nothing
symplectic, so it sits with the manifold topic, beside Tau Ceti's
`Geometry/Manifold/TubularNeighborhood/`. Namespace
`TauCeti.SmoothEmbedding`.

- `exists_diffeomorph_opens_mfderiv_eq (f₀ f₁) (A) (hA) (hAf)`: for a
  smooth section `A` over `Q` of the hom bundle of the pull-backs, each
  `A q` a linear equivalence with `A q (mfderiv J I₀ f₀ q v) = mfderiv J
  I₁ f₁ q v`, there are `U₀ : Opens M₀`, `U₁ : Opens M₁` and
  `ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁` with, for every `q`, `f₀ q ∈ U₀`,
  `(ψ ⟨f₀ q, _⟩ : M₁) = f₁ q` and `mfderiv I₀ I₁ ψ ⟨f₀ q, _⟩ = A q`. Route:
  Tau Ceti's `exists_partialDiffeomorph_mfderiv_eq`
  (`Geometry/Manifold/TubularNeighborhood/PrescribedDifferential.lean`),
  with `hA` read in tangent coordinates through
  `Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt`, and its
  partial diffeomorphism restricted to its source and target. It needs no
  compactness and no closed image.

### `Geometry/Manifold/Diffeomorph/Basic.lean`

The case of an empty `Q` in `MFDeriv.lean`. Namespace
`Diffeomorph`; the `IsEmpty` instance of `⊥ : Opens M`
(`TopologicalSpace.Opens.isEmpty_bot`) is in `Topology/Sets/Opens/Basic.lean`.
The neighbourhood theorems and `Moser/Relative.lean` of *Moser isotopy* use
both for an empty `Q`, with `Subsingleton.elim` for the restricted forms.

- `Diffeomorph.ofIsEmpty : M ≃ₘ^n⟮I, I'⟯ M'` for `[IsEmpty M] [IsEmpty M']`,
  Mathlib's `Diffeomorph.empty` with two models, and the `Unique` instance
  on such diffeomorphisms.

### `Geometry/Symplectic/Neighborhood/Tubular.lean`

The second half of the common step of `DESIGN.md`. Namespace
`TauCeti.SmoothEmbedding`. It imports `MFDeriv.lean`.

- `exists_symplectomorphism_opens_mfderiv_eq`: the same for symplectic
  `ω₀`, `ω₁`, and each `A q` a linear
  symplectomorphism, now with `ψ` also pulling the restriction of `ω₁` back
  to that of `ω₀` (in the form of `exists_diffeomorph_opens_of_eq_along`).
  Route: the first theorem gives `ψ'`, with `ψ'^*ω₁` and `ω₀` equal on
  $TM_0$ along `f₀`. The relative Moser theorem of *Moser isotopy*, applied
  on `U₀` along `f₀.codRestrict U₀` (Tau Ceti's `codRestrict`), gives `χ`
  with derivative the identity along `f₀`; then `ψ = ψ' ∘ χ`. This is the
  place where the errata's derivative conclusion
  [McDuffSalamon2019Errata] enters.

### `Geometry/Symplectic/Neighborhood/Basic.lean`

The comparison theorem. Namespace `TauCeti.SmoothEmbedding`.

- `exists_symplectomorphism_opens_of_mpullback_eq`. Hypotheses: `f₀`, `f₁`
  as above (no closed image is needed); symplectic `ω₀`, `ω₁`; equal
  restricted forms of constant rank `k`; `finrank ℝ E₀ = finrank ℝ E₁`; and
  `L` as in `Extension.lean`. Conclusion: `U₀`, `U₁` and a symplectomorphism
  `ψ : U₀ ≃ₘ⟮I₀, I₁⟯ U₁` with, for every `q`, `(ψ ⟨f₀ q, _⟩ : M₁) = f₁ q`,
  `mfderiv ψ` after `mfderiv f₀` equal to `mfderiv f₁` (applied to each `v`),
  and `mfderiv ψ v = L q v + mfderiv J I₁ f₁ q u` for some `u`, for
  `v ∈ ω₀`-orthogonal of the tangent range. Route: Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible` gives compatible
  `J₀`, `J₁`, read pointwise by `Compatible.compatibleAt`. Then `smoothExtendAlong` is an `A` for
  `exists_symplectomorphism_opens_mfderiv_eq`.

### `Geometry/Symplectic/Neighborhood/Symplectic.lean`

`TauCeti.SmoothTwoForm.IsNondegenerate.HasSymplecticTangentImages.exists_symplectomorphism_opens`,
the milestone. Two symplectic manifolds with symplectic submanifolds
`f₀ : SmoothEmbedding J₀ I₀ ∞ Q₀ M₀` and
`f₁ : SmoothEmbedding J₁ I₁ ∞ Q₁ M₁`, a diffeomorphism `φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁`
pulling `f₁^*ω₁` back to `f₀^*ω₀`, and `Φ : ∀ q, f₀.NormalSpace q hn ≃L[ℝ]
f₁.NormalSpace (φ q) hn`, smooth on total spaces under the bundle
structures `normalSpaceFiberBundle`, that preserves `symplecticNormalForm`.
Conclusion: `U₀`, `U₁` and a symplectomorphism `ψ` with
`ψ ⟨f₀ q, _⟩ = ⟨f₁ (φ q), _⟩` and
`mfderiv ψ (symplecticNormalRepresentative f₀ … q v) =
symplecticNormalRepresentative f₁ … (φ q) (Φ q v)`. Both sides are in
$(TQ)^\omega$, so this is the milestone's condition on
$d\psi|_{(TQ_0)^{\omega_0}}$ through `normalSpaceSymplecticComplementEquiv`.
Route: the comparison theorem for `f₀` and
`f₁.compDiffeomorphOfBoundaryless φ _`; `L` is $\mathrm{rep}_1\circ\Phi\circ$
`normalClass`, smooth by `contMDiff_symplecticNormalRepresentative`. Since
$K=0$, the comparison theorem's conclusion is the equality. Milestone:
*Symplectic neighbourhood theorem*.

### `Geometry/Manifold/VectorBundle/ZeroSection.lean`

At Tau Ceti's path, which has `zeroSectionTangentEquiv`. The embedding is the
library's own definition, so it is in `SymplecticGeometry.Bundle`:
`SymplecticGeometry.Bundle.zeroSectionEmbedding F V :
TauCeti.SmoothEmbedding IB (IB.prod 𝓘(ℝ, F)) ∞ B (TotalSpace F V)` for a
smooth vector bundle with finite-dimensional fibre over a boundaryless base.
It comes from Tau Ceti's `ContMDiff.isSmoothEmbedding_of_leftInverse` with
the projection. API: `coe_zeroSectionEmbedding` (it is `zeroSection F V`),
and `TauCeti.Bundle.isClosed_range_zeroSection`, about Mathlib's zero section.

### `Geometry/Symplectic/Neighborhood/Lagrangian.lean`

`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent`,
the milestone. For a Lagrangian `f : SmoothEmbedding J I ∞ L M`:
`U : Opens (CotangentBundle J L)`, `V : Opens M`, and
`ψ : U ≃ₘ V` with `ψ ⟨zeroSection _ _ q, _⟩ = ⟨f q, _⟩` and `ψ` pulling the
restriction of `ω` back to the restriction of
`TauCeti.CotangentBundle.symplecticForm J L`, which is
$-d\lambda_{\mathrm{can}}$, the page's sign. Route: the comparison theorem
for `f₀ = zeroSectionEmbedding` (Lagrangian by Tau Ceti's
`TauCeti.CotangentBundle.isLagrangianMap_zeroSection`) and `f₁ = f`, with `L = 0`. Both restricted
forms are `0`. The dimensions agree by Tau Ceti's
`IsLagrangianMap.two_mul_finrank`. Milestone:
*Lagrangian neighbourhood theorem*.

### `Geometry/Manifold/SmoothEmbedding/Diffeomorph.lean`

At Tau Ceti's path, in its namespace `TauCeti`, beside Tau Ceti's
`compDiffeomorph`, which needs one model. For boundaryless `M'` and `N`,
`N` on a finite-dimensional model, and `e : M' ≃ₘ^n⟮I', I⟯ M` with `1 ≤ n`:
`isImmersion_comp_diffeomorph_of_boundaryless`,
`isSmoothEmbedding_comp_diffeomorph_of_boundaryless`, and the bundled
`SmoothEmbedding.compDiffeomorphOfBoundaryless`, with its `_apply`, `coe_`
and `range_` lemmas, and `mfderiv_` and `range_mfderiv_` for its differential.

### `Geometry/Symplectic/Neighborhood/Isotropic.lean`

`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap.exists_symplectomorphism_opens_of_finrank_eq`.
Isotropic `f₀` and `f₁`, modelled on `J₀` and `J₁`, a diffeomorphism
`φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁`, and `L` over `Q₀` from `T_{f₀ q}M₀` to
`T_{f₁ (φ q)}M₁`, smooth as a section along
`f₁.compDiffeomorphOfBoundaryless φ _`,
mapping $W_0^\omega$ into $W_1^\omega$ and preserving $\omega$ there; the
dimensions of `M₀` and `M₁` are equal. Conclusion: `ψ` with
`ψ ∘ f₀ = f₁ ∘ φ`, and `mfderiv ψ v = L q v + mfderiv f₁ (φ q) u` for
some `u`, for $v\in W_0^\omega$,
which says that $d\psi$ and $L$ induce the same map of the reduced spaces
`ReducedSpace (orthogonal W)`. The restricted forms are `0`, so `φ` needs no
hypothesis.

`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap.exists_symplectomorphism_opens`,
the milestone, states it with Tau Ceti's `ReducedSpace` and `reduction`: a
family `Φ q` of linear symplectomorphisms of the reduced spaces, induced by
a smooth `L` as above (`Φ q [v] = [L q v]`), and the conclusion
`Φ q [v] = [mfderiv ψ v]`. It assumes neither a closed image nor equal
dimensions: `L` preserves $\omega$ because `Φ` does, and when `Q₀` is
nonempty the dimensions agree, since `Φ` matches reduced spaces of
dimension `dim M - 2 dim Q`. Milestone: *Isotropic neighbourhood theorem*.

### `Geometry/Symplectic/Neighborhood/Coisotropic.lean`

`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.exists_symplectomorphism_opens`,
the milestone. Coisotropic `f₀` and `f₁` (no closed image is needed),
modelled on `J₀` and `J₁`, a diffeomorphism `φ : Q₀ ≃ₘ⟮J₀, J₁⟯ Q₁`
pulling `f₁^*ω₁` back to `f₀^*ω₀`, and nothing else. Conclusion: `ψ`
with `ψ ∘ f₀ = f₁ ∘ φ` that pulls `ω₁` back to `ω₀`. Route: the comparison
theorem with `L = 0`, since $W^\omega=K$. The equal dimensions follow from
`φ` and Tau Ceti's `IsCoisotropicMap.finrank_ker_bilinFormAt_mpullback_add`
(the codimension is the rank of the kernel) when `Q₀` is nonempty.
Milestone: *Coisotropic neighbourhood theorem*.

### `Geometry/Symplectic/Neighborhood/AdaptedDarboux.lean`

For `(M, ω)` symplectic of dimension `2 * n` (`hn : finrank ℝ E = 2 * n`),
a smooth embedding `f : SmoothEmbedding J I ∞ Q M` (not necessarily with
closed image), and `q₀ : Q`, each theorem gives a chart
`e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞`
with `f q₀ ∈ e.source`, `e (f q₀) = 0`,
`ω.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)` on
the source (the form of Tau Ceti's Darboux charts), and
`e.source ∩ Set.range f = e.source ∩ e ⁻¹' S`. Here `S` is the following
set:

| Theorem (namespace `TauCeti.SmoothTwoForm.IsNondegenerate`) | Hypothesis | `S` |
|---|---|---|
| `HasSymplecticTangentImages.exists_darbouxChart_inter_range_eq` | `finrank ℝ E' = 2 * k` | `{z | ∀ j : Fin n, k ≤ (j : ℕ) → z.x j = 0 ∧ z.y j = 0}` |
| `IsIsotropicMap.exists_darbouxChart_inter_range_eq` | `finrank ℝ E' = k` | `{z | z.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → z.x j = 0}` |
| `IsLagrangianMap.exists_darbouxChart_inter_range_eq` | — | `{z | z.y = 0}` |
| `IsCoisotropicMap.exists_darbouxChart_inter_range_eq` | `finrank ℝ E' = 2 * n - k` | `{z | ∀ j : Fin n, (j : ℕ) < k → z.y j = 0}` |

The coisotropic theorem also states that at every `x = f q` in the source,
`mvfderiv I e x` maps $(T_xQ)^\omega$ onto
`{v | v.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → v.x j = 0}`, the span of the first
`k` vectors $\partial_{q_j}$. The four theorems share the milestone line.
Milestone: *Darboux charts adapted to submanifolds*.

Route, for all four. A chart `c` of `Q` at `q₀` onto an open set of the
linear space `S` is chosen so that `c` carries `f^*ω` to the restriction of
`stdForm` to `S`. For a symplectic `Q`, `c` is a Darboux chart of `f^*ω`
(Tau Ceti's). For an isotropic or Lagrangian `Q`, any chart will do, since
both restricted forms are `0`. For a coisotropic `Q`, `c` is a chart of `Q`
in which the closed form `f^*ω`, of constant rank, is the pull-back of
`stdForm (Fin r)` along a linear projection
(`IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm`).
The lemma `exists_localDiffeomorph_extend`,
public in `Geometry/Manifold/LocalDiffeomorph/Extend.lean` (with the centred charts
`exists_partialDiffeomorph_apply_eq_zero` that the isotropic case uses),
extends `f ∘ c⁻¹` in the directions
of a complement of `S`. It does so in a chart of `M`, by adding a fixed
linear map transverse to the image, as Tau Ceti's flat model in
`Geometry/Symplectic/Darboux/Immersion.lean` does; the linear map comes from
`LinearMap.exists_linearEquiv_comp_eq_of_injective`
(`LinearAlgebra/FiniteDimensional/Extension.lean`). That gives a local
diffeomorphism `g` near `0` with `g = f ∘ c⁻¹` on `S`. Since `g^*ω` is
defined only near `0`, Tau Ceti's flat theorem
`exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`
is applied on an open set of `StdSpace (Fin n)` around `0`,
with `σ₁ = g^*ω`, `σ₀ = stdForm` and the inclusion of `S`. Its
`htan` is the property of `c`. It gives `Φ` fixing `S` near `0` with
`Φ^*σ₁ = σ₀`. Then `e` is the inverse of `g ∘ Φ`, shrunk so that, `f`
being an embedding, the image of `Q` in the source is exactly the part of
`S` that `e` hits. The pull-back along the local inverse is
`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`, in the general
`Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean`, with
`Geometry/Manifold/LocalDiffeomorph/Basic.lean`; the
shrinking is `Topology.IsInducing.exists_isOpen_inter_range_eq`, in the
general `Topology/Maps/Embedding.lean`. These steps, for any chart `c` and injective linear
`ι : E' → StdSpace (Fin n)` with `range ι = S`, are the public
`exists_darbouxChart_inter_range_eq_of_chart` (same namespace), which the
four theorems share.

## What the part uses

- From *Moser isotopy*: `Relative.lean`, `Geometry/Manifold/DifferentialForm/Opens.lean` and
  `Geometry/Symplectic/Manifold/TwoForm.lean`, only in `Tubular.lean`, and `Opens.lean`
  also in `Symplectic.lean`.
- From *Liouville structures*: `Geometry/Manifold/MFDeriv/Opens.lean`
  (`mdifferentiable_subtypeVal`), in `CharacteristicFoliation.lean`.
- From *Symplectic vector bundles*:
  `Geometry/Manifold/VectorBundle/Pullback.lean` (merged), in
  `Geometry/Manifold/VectorBundle/Adjoint.lean`, for the derivative of an
  immersion as a section of the pull-back. The compatible complex
  structures of `Neighborhood/Basic.lean` come from Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`.
- From *Symplectic vector spaces*: `LinearAlgebra/Symplectic/Reduction.lean`
  (merged), in `Extension.lean`, and
  `LinearAlgebra/Symplectic/Subspace.lean` (merged), in `Extension.lean`,
  `CharacteristicFoliation.lean` and `Coisotropic.lean`.
- From *Compatible complex structures*:
  `LinearAlgebra/Symplectic/Compatible.lean` (merged), in `Extension.lean`, and
  `Topology/Algebra/Module/BilinearForm.lean` (merged), in
  `Geometry/Manifold/VectorBundle/Adjoint.lean`.
- From *Standard model*: `StdSpace`, `stdForm`, `stdForm_apply`, and the
  inclusions `StdSpace.stdInl`, `StdSpace.stdInr` and `StdSpace.ofX` that this part adds to
  `LinearAlgebra/Symplectic/Standard/Basic.lean`, in `AdaptedDarboux.lean`;
  `StdSpace` also in `CharacteristicFoliation.lean`.
- *Cotangent bundles* is not used: `Lagrangian.lean` needs only Tau Ceti's
  `symplecticForm` and `isLagrangianMap_zeroSection`, because the comparison
  theorem replaces the zero-section splitting.
- Tau Ceti and Mathlib, as listed in *What exists, and what the part adds*.

## Building issues

Sizes are estimates. A blocker given by number alone is an issue of this
list. Issues 1, 3, 5 and 10 can start at once.

1. **Descent along characteristic submersions.** `CharacteristicFoliation.lean`:
   `IsCharacteristicSubmersion`, `isBasic`,
   `existsUnique_isSymplectic_mpullback_eq`, with an example (the
   projection of a product $B\times F$ with a form pulled back from $B$).
   About 350 lines. Blockers: none.
2. **Characteristic charts and the milestone.** `CharacteristicFoliation.lean`:
   `exists_isCharacteristicSubmersion` (with `exists_flatPartialDiffeomorph`
   in `Geometry/Manifold/Distribution/FlatChart.lean`), the milestone
   theorem, and the coisotropic statements. About 350 lines. Blockers: 1.
3. **The linear extension.** `LinearAlgebra/Symplectic/Extension.lean`: the
   pieces and their lemmas, `extendAlong` and its API, and the lemma on the
   reduced spaces. About 400 lines. Blockers: none.
4. **The extension along a submanifold.** `Neighborhood/Extension.lean`.
   About 400 lines. Blockers: 3.
5. **Diffeomorphisms of neighbourhoods with a prescribed derivative.**
   `Geometry/Manifold/TubularNeighborhood/MFDeriv.lean`:
   `exists_diffeomorph_opens_mfderiv_eq`.
   Blockers: none.
6. **Symplectic correction.** `Tubular.lean`:
   `exists_symplectomorphism_opens_mfderiv_eq`. About 200 lines. Blockers:
   5, and the issue of *Moser isotopy* that builds `Relative.lean`, which
   `design/moser-isotopy.md` (#471) lists.
7. **The comparison theorem.** `Neighborhood/Basic.lean`. About 200 lines.
   Blockers: 4 and 6.
8. **Symplectic and Lagrangian neighbourhoods.** `Symplectic.lean`,
   `Geometry/Manifold/VectorBundle/ZeroSection.lean`, `Lagrangian.lean`.
   About 350 lines. Blockers: 7.
9. **Isotropic and coisotropic neighbourhoods.** `Isotropic.lean` and
   `Coisotropic.lean`. About 300 lines. Blockers: 7.
10. **Adapted Darboux charts.** `AdaptedDarboux.lean`: the local extension
    step and the symplectic, isotropic and Lagrangian theorems, with the
    general files `Geometry/Manifold/LocalDiffeomorph/Extend.lean`,
    `LinearAlgebra/FiniteDimensional/Extension.lean`,
    `Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean`,
    `Geometry/Manifold/LocalDiffeomorph/Basic.lean` and
    `Topology/Maps/Embedding.lean`. About 400
    lines. Blockers: none.
11. **Adapted Darboux charts of coisotropic submanifolds.**
    `AdaptedDarboux.lean`: the coisotropic theorem. About 200 lines.
    Blockers: 2, 10.

*Contact geometry*'s `LegendrianNeighborhood.lean` waits for issue 8.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §3.4.
* [D. McDuff and D. Salamon, errata to the third edition][McDuffSalamon2019Errata],
  p. 109 (the derivative along the submanifold in the relative Moser
  theorem).
* [K. Cieliebak, *Symplectic Geometry*, lecture notes][Cieliebak2010],
  Theorem 6.10, Corollaries 6.13 and 6.14.
* [Y.-G. Oh and J.-S. Park, *Deformations of coisotropic submanifolds and
  strong homotopy Lie algebroids*][OhPark2005], §3.
