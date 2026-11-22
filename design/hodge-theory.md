# Hodge theory

This is the detailed design of part 29 of `DESIGN.md`, *Hodge theory*. It
covers the milestone *Hodge decomposition on closed Kähler manifolds* of
`atlas/almost-complex-structures.md`. McDuff–Salamon [McDuffSalamon2017],
p. 171, quote the decomposition (4.3.8) without proof. The proof route here
follows Griffiths–Harris [GriffithsHarris1978], Chapter 0, §6 (the Hodge
theorem on a compact Riemannian manifold, through weak solutions, Rellich's
lemma and elliptic regularity) and §7 (the Kähler identities in osculating
holomorphic coordinates, and the decomposition). It also follows Demailly
[Demailly2012], Chapter VI, which the page names as the open-access proof,
and Warner's Chapter 6 (F. W. Warner, *Foundations of Differentiable
Manifolds and Lie Groups*, GTM 94, Springer, 1983), which Tau Ceti's
`Geometry/Manifold/DeRham/Harmonic.lean` cites for the half it proves.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. A *closed oriented Riemannian manifold* is, as in Tau Ceti's
`Harmonic.lean`: `I : ModelWithCorners ℝ E H` with `[FiniteDimensional ℝ E]`,
`[IsManifold I ∞ M]`, `[BoundarylessManifold I M]`, `[T2Space M]`,
`[CompactSpace M]`, the metric given by the instances
`[RiemannianBundle (fun x : M ↦ TangentSpace I x)]` and
`[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]`, and
an orientation `o : Manifold.Orientation I M (Fin m)`. Degrees are written
`k + l = m` with `hkl`, as Tau Ceti writes them. Each statement drops the
instances it does not use. $\Delta=dd^*+d^*d$ is Tau Ceti's
`TauCeti.SmoothForm.hodgeLaplacian o hkl`, $d^*$ its `codifferential`,
$\star$ its `hodgeStar`, and $\mathcal H^k$ its `harmonicForms o hkl`.

## What exists, and what the part adds

Tau Ceti has, at the pinned version:

- **Real Hodge theory without the analysis.** In
  `Geometry/Manifold/Riemannian/HodgeStar.lean` and `Codifferential.lean`:
  the Hodge star and codifferential of real smooth forms, the Hodge
  Laplacian, Green's formulas, `hodgeStar_codifferential`,
  `hodgeStar_hodgeLaplacian`, and the Leibniz rule
  `coe_codifferential_funSMulₗ`. In `Geometry/Manifold/DeRham/Harmonic.lean`:
  `harmonicForms`, `coexactForms`, the orthogonality half of the Hodge
  decomposition (`disjoint_closedForms_coexactForms`,
  `disjoint_harmonicForms_sup_exactForms_coexactForms`,
  `closedForms_inf_sup_coexactForms`),
  `harmonicForms.toDeRhamCohomology_injective`, and the Hodge theorem in
  degrees zero and top. The module docstring says what is missing: that
  $\mathcal H\oplus B\oplus B^*$ is every smooth form.
- **Euclidean elliptic theory.** In `Analysis/Pseudodifferential/`:
  interior regularity of scalar differential operators on distributions,
  `Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`
  (`DistributionalRegularity.lean`), with the mapping property
  `IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`. For systems
  there is only the symbol-level `Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`:
  the identification of a quantized symbol with the differential operator
  on $H^r$ is proved only for scalar coefficients. Also: smoothness from
  local $H^s$ regularity for every $s$
  (`Distribution.singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`,
  `Analysis/Distribution/WaveFrontSet/Sobolev/Smoothness.lean`), and
  Rellich's theorem with a cutoff,
  `BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`
  (`Analysis/Sobolev/BesselPotential/Rellich.lean`).
- **Abstract Hilbert-space tools.** In
  `Analysis/InnerProductSpace/Variational/Compatibility.lean`, for a bounded
  bilinear form $B$ on a real Hilbert space $V$ and a compact
  $J:V\to H$ with Gårding's inequality: the Fredholm alternative
  `IsCompactOperator.exists_forall_apply_eq_iff_of_garding` and
  `IsCompactOperator.finiteDimensional_ker_of_garding`.
- **Complex forms and types.** `SmoothForm.complexificationEquiv`, the
  complex de Rham cohomology `complexDeRhamCohomology` with `mk`,
  `mk_eq_zero_iff` and `complexDeRhamCohomology.complexificationEquiv`
  (`Geometry/Manifold/DeRham/ComplexCoefficients.lean`). The type
  decomposition (`Geometry/Manifold/DifferentialForm/AlmostComplexType.lean`):
  `SmoothForm.IsOfType`, `SmoothAlmostComplexStructure.typeForms`,
  `typeProjection` (a polynomial in the derivation
  `ContMDiffSection.alternatingDerivation` of $J$), `sum_typeProjection`,
  `mapCoeff_typeProjection_of_map_smul_conj`, and the real derivation
  `ContMDiffSection.realAlternatingDerivation`. Pointwise, the type law of
  the complexified Hodge star, from `Orientation.hodgeStar_lieMap`
  (`Analysis/InnerProductSpace/HodgeStar/Complex.lean`, `Isometry.lean`).
- **Hodge structures.** `TauCeti.Hodge.IsHodgeDecomposition`,
  `HodgeStructureOn.ofDecomposition`, `hodgeNumber`, `hodgeNumber_symm` and
  `finsum_hodgeNumber_eq_finrank` (`Geometry/Hodge/`), and the conjugation
  structure `TauCeti.Hodge.Conjugation`.
- **Kähler pairs and charts.** `TauCeti.SmoothTwoForm.IsKahler`, the
  symplectic orientation `TauCeti.SmoothTwoForm.IsNondegenerate.orientation`,
  `chartPushforward`, the chart expression `RoughForm.inChartAt`
  (`Geometry/Manifold/DifferentialForm/ExtDeriv.lean`) with
  `inChartAt_mextDeriv` (`Chart.lean`), and the pullback `mpullback` with
  its API (`DifferentialForm/Pullback/`, `DifferentialForm/Naturality.lean`).

Tau Ceti has no Sobolev or $L^2$ space of forms on a manifold, no elliptic
regularity on manifolds, no Hodge star or Laplacian of complex-valued
forms, no Lefschetz operator, and no Kähler identities. Mathlib has only
the linear `exteriorPower.hodgeStar`. This part adds the analytic half of
the Hodge theorem for real forms, its complexification, the Kähler
identities, the decomposition by type, and the milestone.

## Decisions

`DESIGN.md` leaves two questions to this file: how the part is split, and
whether the analytic half is proved on the whole manifold or through a
parametrix glued from charts.

- **The whole manifold, with local regularity.** The analytic half is
  proved on the whole manifold, through a Hilbert space of $L^2$ forms and
  the Fredholm alternative of Tau Ceti's `Compatibility.lean`, as
  Griffiths–Harris and Warner do. Charts enter only in two local steps,
  regularity and compactness, which use Tau Ceti's Euclidean theorems.
  No parametrix is built. A parametrix glued from charts would need
  pseudodifferential operators on a manifold and Sobolev spaces of real
  order on a manifold, neither of which Tau Ceti has. The route here needs
  neither: the Euclidean statements it needs exist, and the abstract
  Fredholm theory exists.
- **The Hilbert spaces.** `L2Form o k` is the completion of the smooth
  `k`-forms for the inner product $\int_M\langle\alpha,\beta\rangle\,
  \mathrm{vol}$. `H1Form o hkl` is the completion for
  $\langle\alpha,\beta\rangle+\langle\Delta\alpha,\beta\rangle$, which is an
  inner product by Tau Ceti's Green's formulas. Both are
  `UniformSpace.Completion`s of type synonyms of `SmoothForm I M ℝ k`
  carrying `InnerProductSpace.ofCore`. The Dirichlet form
  $\langle\Delta\alpha,\beta\rangle$ extends to a bounded bilinear form on
  `H1Form`, and the inclusion `H1Form.toL2` is the map $J$. Gårding's
  inequality then holds with constants $1$ and $1$, by the definition of
  the norm. Tau Ceti's `SobolevSection` is not used: it needs the model
  `𝓘(ℝ, E)`, its norm is the maximum of chart norms, which is not a Hilbert
  norm, and it is not tied to the Riemannian volume.
- **Regularity of systems through a scalar principal part.** In a chart
  the Hodge Laplacian is a system whose principal part is the scalar
  operator $g^{ij}\partial_i\partial_j$ times the identity. This follows
  from $d^*=\pm\star d\star$, with $d$ constant-coefficient and $\star$ a
  smooth matrix function in the chart, and from the pointwise identity
  $\varepsilon_\xi\iota_\xi+\iota_\xi\varepsilon_\xi=\lvert\xi\rvert^2$
  (Tau Ceti's `Contraction.lean`). Only the first-order terms couple the
  components. So regularity is proved componentwise, by Tau Ceti's scalar
  theorem and a bootstrap. If the components are $H^r$ near a point, the
  coupling terms are $H^{r-1}$, so the components are $H^{\min(s,r-1)+2}$.
  Every distribution has finite local order, so a start always exists. The
  matrix-coefficient quantization that Tau Ceti lacks is not needed.
- **Compactness by the closed graph theorem.** No Gårding or Gaffney
  inequality is proved by hand. Regularity with a right-hand side in
  $H^{-1}$ shows that every element of `H1Form` is $H^1$ in each chart of a
  finite atlas. The localization map from `H1Form` to $H^1$ of the chart is
  therefore everywhere defined. Its graph is closed, since both spaces map
  continuously into distributions, so it is bounded. Composed with Tau
  Ceti's Rellich theorem with a cutoff, and summed over a partition of
  unity, this makes `H1Form.toL2` compact.
- **The Kähler identities in osculating holomorphic charts, not through
  $\nabla J=0$.** The part proves, for real forms, the first-order identity
  $[L,d^*]=-[\mathcal J,d]$. Here $L=\omega\wedge\cdot$ and $\mathcal J$ is
  the derivation of $J$ on forms (Tau Ceti's `realAlternatingDerivation`,
  $(\mathcal J\alpha)(v_1,\dots,v_k)=\sum_i\alpha(\dots,Jv_i,\dots)$); the
  sign is fixed by functions on flat $\mathbb C^n$, where $d^*\omega=0$ and
  Tau Ceti's Leibniz rule for $d^*(f\omega)$ gives
  $[L,d^*]f=\iota_{\operatorname{grad}f}\omega=-df\circ J$. The identity is proved at
  each point $x_0$ in a chart in which $J$ is constant, which integrability
  provides, and in which the metric has vanishing first derivative at
  $x_0$. The chart is a holomorphic quadratic change of coordinates, which
  exists because $d\omega=0$. There the coefficients of $\star$ and $L$ have
  vanishing derivative at $x_0$, so both sides of the identity are their
  constant-coefficient versions at $x_0$, and the identity is linear
  algebra. This reuses the chart expressions of $\star$ and $d^*$ that the
  analytic half needs anyway. The alternative through $\nabla J=0$
  (*Almost Kähler geometry*) would need a connection on forms of every
  degree, $d=\sum e^i\wedge\nabla_{e_i}$ and
  $d^*=-\sum\iota_{e_i}\nabla_{e_i}$, none of which Tau Ceti has. So the
  part does not build on *Almost Kähler geometry*.
- **$[\Delta,\mathcal J]=0$ algebraically.** From $[L,d]=0$ ($d\omega=0$),
  the identity above, $\star\mathcal J=\mathcal J\star$ and
  $d^*=\pm\star d\star$, the commutator $[\mathcal J,\Delta]$ expands into
  terms that cancel because $d^2=0$ and $(d^*)^2=0$. Hence $\Delta$ commutes
  with $\mathcal J$ on real forms, its complexification commutes with the
  complex derivation, and so with every type projection, which is a
  polynomial in that derivation. The part needs no complex Hodge star with
  its Hermitian conventions, no $\partial^*$, $\bar\partial^*$ or
  $\Lambda$, and no $\Delta=2\Delta_{\bar\partial}$.
- **Complex forms by complexification.** Tau Ceti's star and codifferential
  are real. The complex Laplacian, star and harmonic forms are defined
  from the real ones through `SmoothForm.mapCoeff` on real and imaginary
  parts, and the complex Hodge theorem follows from the real one and
  `complexDeRhamCohomology.complexificationEquiv`.
- **$H^{p,q}$ in de Rham cohomology.** As on the page, $H^{p,q}(M)$ is the
  subspace of `complexDeRhamCohomology I M k` of classes of closed forms
  of type $(p,q)$, the image under `mk` of the closed forms in
  `J.typeForms p q`. It is not Tau Ceti's `dolbeaultCohomology`, which is
  defined only on manifolds modelled on `𝓘(ℂ, E)` and which the milestone
  does not mention. A closed $(p,q)$-form $\alpha$ is cohomologous to the
  $(p,q)$-component of its harmonic part. Write $\alpha=h+\Delta\gamma$
  with $h$ harmonic, by the analytic half. Apply the type projection,
  which commutes with $\Delta$. Then $\alpha-\Pi^{p,q}h=\Delta\Pi^{p,q}\gamma$
  is closed. A closed form $\Delta\beta$ is exact: $d^*d\beta$ is then closed
  and coexact, hence zero by `disjoint_closedForms_coexactForms`. So the
  harmonic $(p,q)$-forms map onto $H^{p,q}$, and the decomposition of
  harmonic forms by type gives the direct sum.
- **The milestone's hypotheses.** A closed Kähler manifold in the page's
  sense is a compact Hausdorff boundaryless manifold with
  `ω.IsKahler J` and `J.IsIntegrable` (*Nijenhuis tensor*'s
  `Integrable.lean`), with `finrank ℝ E = 2 * n`, as `DESIGN.md` says.
  The metric $g_J$ is installed inside the proof, as a local instance,
  from *Almost complex manifolds*' `TauCeti.SmoothTwoForm.Compatible.metric`
  with `metric_inner`. The orientation is the symplectic one,
  `IsNondegenerate.orientation`. Harmonic forms do not depend on the
  orientation (`harmonicForms_neg_orientation`), and the Kähler identities
  hold for both orientations. The results of the Kähler half that come
  before the milestone take any metric instance with
  `hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = ω.eval₂ x v (J x w)`, the
  convention of `DESIGN.md`, so that they do not depend on how the metric
  was built.
- **Models.** Every statement is for a general boundaryless model `I`. The
  local steps use charts that are `PartialDiffeomorph I 𝓘(ℝ, E) M E ∞`.
  These are the atlas charts of a boundaryless manifold, and the
  integrable charts of `IsIntegrable`. The Euclidean theorems on
  `CoordinateSpace n` are reached through a linear equivalence
  `E ≃L[ℝ] CoordinateSpace n`.

## Files and declarations

### `Analysis/Distribution/EllipticSystem.lean`

Interior regularity for a system of distributions on an open
`Ω : Opens (CoordinateSpace n)` whose principal part is one scalar
operator. `T : ι → 𝓓'(Ω, ℂ)` with `[Fintype ι]`. The scalar operator is
$P=\sum_{i\in t}c_i g_i\partial^{m_i}$ of order $M$, as in Tau Ceti's
`DistributionalRegularity.lean`, elliptic at `x`. The coupling is
$Q_{ab}=\sum_{j\in t'}c'_{abj}h_{abj}\partial^{m'_j}$ of order at most
$M-1$, with smooth real coefficients.

- `Distribution.IsLocallySobolevAt.of_ellipticSystem`: if every
  $PT_a+\sum_bQ_{ab}T_b$ is `IsLocallySobolevAt s x`, then every $T_a$ is
  `IsLocallySobolevAt (s + M) x`. The proof is the bootstrap above, from
  `exists_memSobolev_cutoffTempered` (finite order),
  `IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp` (the
  coupling loses at most $M-1$ derivatives) and
  `IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`.
- `Distribution.singularSupport_eq_empty_of_ellipticSystem`: if the right
  sides are smooth on `Ω` and $P$ is elliptic at every point of `Ω`, every
  $T_a$ is smooth. This uses the previous result for every $s$ and
  `singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`.

The coefficients are real smooth functions on the whole of
`CoordinateSpace n`, as Tau Ceti's theorem asks. Callers extend chart
coefficients by cutoffs.

### `Geometry/Manifold/DifferentialForm/PartialDiffeomorph.lean`

The coordinate expression of a form along a chart `ψ` that is a partial
diffeomorphism onto an open subset of `E` is Tau Ceti's pullback
`mpullback 𝓘(ℝ, E) I ψ.symm φ : E → E [⋀^Fin k]→L[ℝ] F`. Tau Ceti already
gives its linearity (`mpullback_add`, `mpullback_smul`), smoothness on
`ψ.target` (`SmoothForm.contDiffOn_mpullback`), recovery of the form on
`ψ.source` (`OpenPartialHomeomorph.mpullback_mpullback_symm_apply`),
compatibility with $d$ (`mpullback_mextDeriv_on`) and with the wedge product
(`mpullback_wedge`). This file adds, in Tau Ceti's namespace:

- `mpullback_symm_eq_inChartAt`: for the atlas chart
  `extChartPartialDiffeomorph I n x`, the expression agrees with `inChartAt`
  on its target.
- `mpullback_symm_realAlternatingDerivation`: the expression of
  $\mathcal J\varphi$ is the derivation of `chartPushforward` of $J$.
- `SmoothForm.extendByZeroAlong`: the smooth form on $M$, zero outside
  `ψ.source`, whose expression is a given smooth function with compact
  support in `ψ.target`, with `mpullback_symm_extendByZeroAlong`. It is
  `RoughForm.extendByZeroAlong`, defined piecewise from
  `mpullback I 𝓘(ℝ, E) ψ` on `ψ.source`, not through Tau Ceti's
  `RoughForm.extendByZero` between `Opens`. The regularity issue glues
  local smooth representatives with it.
- `SmoothForm.localize ψ χ α`: the expression of a smooth form along `ψ`,
  scaled by `χ ∘ ψ.symm` on `ψ.target` and `0` elsewhere, with its value on
  `ψ.target`, its support in `ψ '' tsupport χ` and its continuity.
  `L2.lean` bounds it in `L²`.

### `Geometry/Manifold/LocalDiffeomorph/ChartCover.lean`

- `exists_finite_partialDiffeomorph_cover`: on a compact boundaryless
  manifold, finitely many charts `extChartPartialDiffeomorph I ∞ x` with a
  subordinate smooth partition of unity.

### `Analysis/Calculus/ContDiff/Matrix.lean`

- `ContDiffOn.matrix_inv_apply`: a matrix-valued map with `C^n` entries on a
  set, whose determinant does not vanish there, has an inverse with `C^n`
  entries there.

### `Geometry/Manifold/DeRham/Hodge/Chart.lean`

`Chart.lean` imports `Analysis/Calculus/ContDiff/Matrix.lean`.

The coordinate expressions of the metric, the Hodge star and the
codifferential in a chart `ψ`:

- `gramInChart ψ : E → E →L[ℝ] E →L[ℝ] ℝ`, the inner product at
  `ψ.symm y` read through `mfderiv` of `ψ.symm`, smooth on `ψ.target`.
- `hodgeStarInChart o ψ hkl : E → (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
  (E [⋀^Fin l]→L[ℝ] ℝ)`, with `mpullback_symm_hodgeStar`. It is smooth on
  `ψ.target`, and is the star of `E` for the inner product `gramInChart ψ y`.
  By `Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum` it is a
  smooth function of the Gram matrix in a fixed basis. Hence
  `fderiv_hodgeStarInChart_eq_zero`: where `fderiv ℝ (gramInChart ψ)`
  vanishes, so does `fderiv ℝ (hodgeStarInChart o ψ hkl)`.
- `mpullback_symm_codifferential`: the expression of $d^*\beta$ is
  $\pm S\,d(S\,b)$, with $S$ the star in the chart, $b$ the expression of
  $\beta$, and the sign of Tau Ceti's definition of `codifferential`.

### `LinearAlgebra/BilinearForm/Gram.lean`

- `LinearMap.BilinForm.apply_sum_inv_toMatrix_smul`: if the Gram matrix
  $G$ of a bilinear form `B` in a basis `b` has a unit determinant, then
  `B` sends $\sum_{ij}(G^{-1})_{ij}\,\xi(b_i)\,b_j$ to the linear form $\xi$.

### `Geometry/Manifold/DeRham/Hodge/LocalLaplacian.lean`

`LocalLaplacian.lean` imports `LinearAlgebra/BilinearForm/Gram.lean`,
`Geometry/Manifold/DifferentialForm/PartialDiffeomorph.lean` and
`Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`.

- `exists_mpullback_symm_hodgeLaplacian_eq`: for a chart `ψ` and a basis `b` of
  `E`, there are smooth `B : Fin m → E → Λ →L[ℝ] Λ` and `C : E → Λ →L[ℝ] Λ`,
  with `Λ = E [⋀^Fin k]→L[ℝ] ℝ`, such that for every smooth `k`-form
  $\alpha$ with expression $a$ and every `y ∈ ψ.target`,
  $(\Delta\alpha)_\psi(y)=-\sum_{ij}G^{ij}(y)\,\partial_{b_i}\partial_{b_j}a(y)
  +\sum_iB_i(y)\,\partial_{b_i}a(y)+C(y)\,a(y)$,
  where $G^{ij}$ is the inverse Gram matrix of `gramInChart ψ y` in `b`.
  The second-order coefficient is computed from
  `exists_mpullback_symm_codifferential_eq` and `mpullback_symm_mextDerivₗ`,
  and identified with $G^{ij}$ times the identity
  by Tau Ceti's `alternatizeUncurryFin_curryLeft_comp_add_curryLeft`.
- `exists_mpullback_symm_hodgeLaplacian_transpose_eq`: the same shape for the
  formal transpose for Lebesgue measure of the operator conjugated by the
  fibre metric and the volume density. This is the operator that the weak
  equation gives in the chart. Its principal part is again
  $-G^{ij}\partial_i\partial_j$ times the identity.

### `Geometry/Manifold/Riemannian/Basic.lean`

- `ContMDiffOn.exists_norm_mfderiv_le_mul_norm` and
  `ContMDiffOn.exists_pos_mul_norm_le_norm_mfderiv`: upper and lower bounds
  on a compact set for the differential of a `C¹` map into `M`.

### `Geometry/Manifold/Riemannian/VolumeDensity/ChangeOfVariables.lean`

- `TauCeti.riemannianJacobian_pos`: Tau Ceti's `riemannianJacobian` is
  positive where the differential is injective.

### `Geometry/Manifold/Riemannian/PartialDiffeomorph.lean`

Estimates for a chart `ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n`, `n ≠ 0`, on
a compact `K ⊆ ψ.target`, used to show that `L2Form.localize` is bounded:

- `PartialDiffeomorph.exists_mul_norm_le_norm_mfderiv_symm_le`: the
  differential of `ψ.symm` is bounded above and below on `K` for the
  Riemannian norm, and `PartialDiffeomorph.exists_norm_mvfderiv_le_mul_norm`
  bounds the differential of `ψ` on `ψ.symm '' K`.
- `PartialDiffeomorph.riemannianJacobian_symm_pos` and
  `PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`: Tau Ceti's
  `riemannianJacobian` of `ψ.symm` is positive on `ψ.target`, and bounded
  above and away from zero on `K`.

### `Geometry/Manifold/DeRham/Hodge/L2.lean`

- `TauCeti.SmoothForm.l2Inner o (α β : SmoothForm I M ℝ k) : ℝ`, the integral of
  `alternatingFormInner` against `riemannianVolumeForm o`, written inline
  in Tau Ceti's `Codifferential.lean`, with `l2Inner_def`, symmetry,
  bilinearity and `l2Inner_self_eq_zero_iff` (through
  `l2Inner_eq_integral`, the integral against `riemannianVolume I M`,
  so in every dimension).
- `L2Form o k`, the Hilbert space completion described above, with
  `L2Form.ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] L2Form o k`,
  `inner_ofSmooth`, `ofSmooth_injective` and `denseRange_ofSmooth`.
- `L2Form.localize ψ χ hχ : L2Form o k →L[ℝ] Lp Λ 2 volume`, with
  `Λ = E [⋀^Fin k]→L[ℝ] ℝ` and `volume` an additive Haar measure on `E`, for
  a chart `ψ` and a smooth cutoff `χ` with `hχ : tsupport χ ⊆ ψ.source`. It
  extends `TauCeti.SmoothForm.localize ψ χ`,
  $\alpha\mapsto(\chi\circ\psi^{-1})\,\alpha_\psi$ on `ψ.target` and `0`
  elsewhere (`localize_ofSmooth`). It is bounded
  (`exists_norm_localizeLp_le`), since the differential of `ψ.symm` is
  bounded above and its Jacobian below on `ψ '' tsupport χ`.
- `L2Form.eq_ofSmooth_of_localize`: for finitely many charts `ψ i` and a
  smooth partition of unity `ρ` subordinate to their sources, taken as the
  cutoffs, if every `localize (ψ i) (ρ i) _ u` is a.e. a smooth `f i` with
  compact support in `(ψ i).target`, then
  `u = ofSmooth (∑ i, SmoothForm.extendByZeroAlong (ψ i) (f i) …)`.

### `Geometry/Manifold/DeRham/Hodge/Regularity.lean`

- `L2Form.IsWeakSolution o hkl u f`: for every smooth `k`-form $\varphi$,
  `⟪u, ofSmooth (Δ φ)⟫ = ⟪f, ofSmooth φ⟫`. It is a predicate on
  `L2Form`, used by the two theorems below and by `Basic.lean`.
- `L2Form.exists_eq_ofSmooth_of_isWeakSolution`: if `IsWeakSolution u
  (ofSmooth f)` with $f$ smooth, then `u = ofSmooth α` with $\alpha$ smooth
  and $\Delta\alpha=f$. In each chart, the weak equation says that the
  localization of `u`, multiplied by the fibre metric and the volume
  density, solves the transposed system of `LocalLaplacian.lean`. Then
  `singularSupport_eq_empty_of_ellipticSystem` applies, and
  `eq_ofSmooth_of_localize` glues.
- `L2Form.isLocallySobolev_one_of_forall_inner`: the $H^{-1}$ case. If
  $\langle u,\Delta\varphi\rangle$ is bounded by a constant times the norm
  of $\varphi$ in the Hodge $H^1$ norm, every localization of `u` is $H^1$
  near every point.

### `Geometry/Manifold/DeRham/Hodge/Sobolev.lean`

- `H1Form o hkl`, the completion for
  $\langle\alpha,\beta\rangle+\langle\Delta\alpha,\beta\rangle$, with
  `H1Form.ofSmooth`, `denseRange_ofSmooth`, `H1Form.toL2 : H1Form o hkl
  →L[ℝ] L2Form o k` extending the identity of smooth forms, and
  `H1Form.dirichlet : H1Form o hkl →L[ℝ] H1Form o hkl →L[ℝ] ℝ` extending
  $\langle\Delta\alpha,\beta\rangle$. Then
  `dirichlet_ofSmooth_right`: `dirichlet u (ofSmooth φ) = ⟪toL2 u,
  ofSmooth (Δ φ)⟫`, and `norm_sq_eq_dirichlet_add`:
  `‖u‖ ^ 2 = dirichlet u u + ‖toL2 u‖ ^ 2`, which is Gårding's inequality.
- `H1Form.isCompactOperator_toL2`, by the closed graph argument above, from
  `isLocallySobolev_one_of_forall_inner` and Rellich's theorem with a
  cutoff.

### `Geometry/Manifold/DeRham/Hodge/Basic.lean`

The Hodge theorem on a closed oriented Riemannian manifold, in Tau
Ceti's namespace, beside its `Harmonic.lean`:

- `TauCeti.finiteDimensional_harmonicForms` (an instance): from
  `finiteDimensional_ker_of_garding`, since the kernel of `dirichlet`
  consists of the images of harmonic forms, by
  `exists_eq_ofSmooth_of_isWeakSolution`.
- `TauCeti.exists_mem_harmonicForms_add_hodgeLaplacian`: every smooth form
  is $h+\Delta\gamma$ with $h$ harmonic and $\gamma$ smooth. Subtract the
  $L^2$-orthogonal projection onto the finite-dimensional harmonic forms.
  The rest is orthogonal to the kernel, so
  `exists_forall_apply_eq_iff_of_garding` gives a weak solution, which
  regularity makes smooth.
- `TauCeti.harmonicForms_sup_exactForms_sup_coexactForms`:
  `harmonicForms o hkl ⊔ exactForms I M k ⊔ coexactForms o hkl = ⊤`.
- `TauCeti.mem_exactForms_of_hodgeLaplacian_mem_closedForms`: if
  $\Delta\beta$ is closed, it is exact.
- `TauCeti.harmonicForms.toDeRhamCohomology_bijective`, in every degree
  (Tau Ceti has degree zero and top), and the equivalence
  `TauCeti.harmonicForms.deRhamCohomologyEquiv`.
- `TauCeti.finiteDimensional_deRhamCohomology`.

### `Geometry/Manifold/DeRham/Hodge/Complex.lean`

Complex-valued forms on a closed oriented Riemannian manifold, by
complexification:

- `TauCeti.SmoothForm.complexHodgeLaplacian o hkl` and
  `TauCeti.SmoothForm.complexHodgeStar o hkl`, ℂ-linear maps of
  `SmoothForm I M ℂ k`, acting on real and imaginary parts
  (`mapCoeff_reCLM_complexHodgeLaplacian`, `mapCoeff_imCLM_…`, and the same
  for the star).
- `TauCeti.complexHarmonicForms o hkl : Submodule ℂ (SmoothForm I M ℂ k)`,
  the forms whose real and imaginary parts are harmonic, with
  `mem_complexHarmonicForms_iff` (the kernel of `complexHodgeLaplacian`),
  `complexHarmonicForms_le_complexClosedForms`, and
  `complexHodgeStar_mem_complexHarmonicForms_iff`.
- `TauCeti.complexHarmonicForms.toComplexDeRhamCohomology_bijective`, from
  the real theorem and `complexDeRhamCohomology.complexificationEquiv`, and
  `TauCeti.exists_mem_complexHarmonicForms_add_complexHodgeLaplacian`.
- `TauCeti.finrank_complexDeRhamCohomology`: its complex dimension is the
  real dimension of `deRhamCohomology I M k`.

### `Analysis/Normed/Module/Alternating/Derivation.lean`

- Facts about Mathlib's `ContinuousAlternatingMap.fderivCompContinuousLinearMap`
  at the identity in the direction `A`, which is the derivation of an
  endomorphism `A` on forms:
  `fderivCompContinuousLinearMap_id_apply`,
  `fderivCompContinuousLinearMap_ofSubsingleton`,
  `fderivCompContinuousLinearMap_apply_comp_equiv` and the Leibniz rule
  `fderivCompContinuousLinearMap_wedge` for real-valued forms.

### `Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`

- `ContinuousAlternatingMap.alternatizeUncurryFin_eq_sum_coord_smulRight`:
  for a basis `b`, `alternatizeUncurryFin f` is the sum of the
  alternatizations of `b.coord i • f (b i)`.
- `ContinuousAlternatingMap.curryLeft_alternatizeUncurryFin_smulRight_add`
  and `curryLeft_alternatizeUncurryFin_smulRight_zero`: for a covector
  $\xi$, $\iota_v\varepsilon_\xi+\varepsilon_\xi\iota_v=\xi(v)$ in positive
  degree, and $\iota_v\varepsilon_\xi=\xi(v)$ in degree $0$.

### `Analysis/InnerProductSpace/HodgeStar/AlternatingForm.lean`

- `TauCeti.alternatingFormEquiv_lieMap`: for a skew-adjoint `A`, `lieMap A`
  on $\Lambda^k V$ is minus the derivation of `A` on forms.
- `TauCeti.alternatingFormEquiv_wedgeLeft`: the form of `u ∧ x` is
  `alternatizeUncurryFin` of `(innerSL ℝ u).smulRight`.
- `Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar`: the
  symbol of $d^*$ with Tau Ceti's sign,
  $\delta_u=\pm\star\varepsilon_u\star=-\iota_u$.

### `Analysis/InnerProductSpace/HodgeStar/Kahler/Lefschetz.lean`

Linear algebra for `V` a real inner product space of finite dimension, with
`J` an orthogonal almost complex structure on it, $\omega(v,w)=\langle Jv,w\rangle$,
on the fibres `V [⋀^Fin k]→L[ℝ] ℝ` of the form bundle, beside Tau Ceti's
`Kahler/Basic.lean`:

- `TauCeti.AlmostComplexStructure.lefschetz J : (V [⋀^Fin k]→L[ℝ] ℝ)
  →L[ℝ] (V [⋀^Fin (k + 2)]→L[ℝ] ℝ)`, wedge with $\omega$, with
  `lefschetz_apply`. Its use is the theorem below; the smooth version is in
  `Kahler/Identities.lean`.
- `Orientation.formHodgeStar_fderivCompContinuousLinearMap`: the star commutes
  with the derivation of a skew-adjoint `A`, such as `J`, from
  Tau Ceti's `Orientation.hodgeStar_lieMap` through `alternatingFormEquiv`.
- `TauCeti.AlmostComplexStructure.lefschetz_curryLeft_sub`: for every
  vector $u$, with $\varepsilon_u$ the wedge with $\langle u,\cdot\rangle$
  (`alternatizeUncurryFin` of `(innerSL ℝ u).smulRight`) and $\iota_u$ the
  interior product `curryLeft`,
  $L\iota_u-\iota_u L=\mathcal J\varepsilon_u-\varepsilon_u\mathcal J$.
  The symbol of $d^*$ with Tau Ceti's sign is
  $\delta_u=\pm\star\varepsilon_u\star=-\iota_u$
  (`Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar` of
  `HodgeStar/AlternatingForm.lean`), so
  this is
  $L\delta_u-\delta_u L=-(\mathcal J\varepsilon_u-\varepsilon_u\mathcal J)$,
  the constant-coefficient Kähler identity. It is proved from the Leibniz
  rules of $\iota_u$ and $\mathcal J$, without a unitary basis.

### `Geometry/Manifold/Complex/KahlerCoordinates.lean`

Beside *Nijenhuis tensor*'s `Integrable.lean`:

- `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.exists_partialDiffeomorph_fderiv_gramInChart_eq_zero`:
  let `J.IsIntegrable` with linear structure $J_0$, let `ω.IsClosed` (all
  of `ω.IsKahler J` that the proof uses), and let the metric instance
  satisfy `hg`. Then every $x_0$ lies in the source
  of a chart `ψ` with `chartPushforward` of $J$ equal to $J_0$ on
  `ψ.target`, and with `fderiv ℝ (gramInChart ψ) (ψ x₀) = 0`, the form
  that `fderiv_hodgeStarInChart_eq_zero` takes.
  Start from an integrable chart and compose it with
  $z\mapsto z+Q(z,z)$, where $Q$ is $J_0$-bilinear and symmetric and is
  chosen so that the first derivative of the metric vanishes. Such a $Q$
  exists because the derivative of the metric is $J_0$-invariant and, by
  $d\omega=0$, symmetric in the right pair of slots
  ([GriffithsHarris1978], Chapter 0, §7). The derivative of the composite
  is $J_0$-linear at every point, so $J$ stays constant. The local inverse
  comes from Tau Ceti's `ContDiffOn.exists_openPartialHomeomorph`. The
  file imports `SymmetricBilinear.lean` below for $Q$, and uses
  `mfderiv_trans_apply_eq_of_fderiv_apply_eq`, which this part adds to
  `Integrable.lean`, for the constancy of $J$. It also imports *Nijenhuis
  tensor*'s `AlmostComplex/Chart.lean`, for
  `forall_chartPushforward_apply_eq_iff` in its proofs.

### `LinearAlgebra/ComplexStructure/SymmetricBilinear.lean`

- `LinearMap.BilinForm.exists_symm_complexBilinear_apply_add_apply_eq`:
  the linear algebra behind $Q$ above, for a symmetric left-separating
  $j$-invariant form on a finite-dimensional space over a field of
  characteristic zero.
  It imports only Mathlib.

### `Geometry/Manifold/DifferentialForm/AlmostComplexType.lean`

- `ContMDiffSection.coe_realAlternatingDerivation`: at each point, Tau
  Ceti's `realAlternatingDerivation` of an endomorphism field `A` is
  `fderivCompContinuousLinearMap` at the identity in the direction `A x`,
  for `hodgeStar_realAlternatingDerivation` below. It imports
  `Analysis/Normed/Module/Alternating/Derivation.lean`.

### `Geometry/Manifold/DeRham/Kahler/Identities.lean`

On an oriented manifold with a metric instance satisfying `hg`,
`ω.IsKahler J` and `J.IsIntegrable`:

- `lefschetz ω : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 2)`,
  $\alpha\mapsto\alpha\wedge\omega$, with `lefschetz_apply`, and
  `mextDerivₗ_lefschetz`: $d(L\alpha)=L\,d\alpha$, from $d\omega=0$.
- `hodgeStar_realAlternatingDerivation`: $\star\mathcal A=\mathcal A\star$
  on smooth real forms for the derivation of any fibrewise skew-adjoint
  endomorphism field, pointwise from the linear file. This gives
  $\star\mathcal J=\mathcal J\star$, since `hg` makes $J$ orthogonal.
- `lefschetz_codifferential_sub`: the Kähler identity
  $L\,d^*\alpha-d^*L\alpha=-(\mathcal J\,d\alpha-d\,\mathcal J\alpha)$, at
  each point in the chart of `KahlerCoordinates.lean`, from
  `mpullback_symm_codifferential`, `fderiv_hodgeStarInChart_eq_zero`,
  `mpullback_mextDeriv_on`, `mpullback_symm_realAlternatingDerivation` and
  the linear identity.
- `hodgeLaplacian_realAlternatingDerivation`:
  $\Delta\mathcal J\alpha=\mathcal J\Delta\alpha$, by the algebra above.
  Also `realAlternatingDerivation_mem_harmonicForms`.

### `Geometry/Manifold/DeRham/ComplexCoefficients.lean`

Named like Tau Ceti's file:

- `TauCeti.complexDeRhamCohomology.conj k : TauCeti.Hodge.Conjugation
  (complexDeRhamCohomology I M k)`, induced by `mapCoeff` of complex
  conjugation, with `conj_mk`. Under
  `complexDeRhamCohomology.complexificationEquiv` it is Tau Ceti's
  `complexificationConjugation`.

### `Geometry/Manifold/DeRham/Kahler/Decomposition.lean`

On a closed Kähler manifold as above:

- `TauCeti.complexDeRhamCohomology.hodgePiece J k p q : Submodule ℂ
  (complexDeRhamCohomology I M k)`, the classes `mk φ` of closed forms with
  `φ.IsOfType J p q`, with `mem_hodgePiece_iff`. It is `⊥` unless
  `p + q = k`.
- `typeProjection_complexHodgeLaplacian`: the type projections commute with
  `complexHodgeLaplacian`. Then `typeProjection_mem_complexHarmonicForms`.
- `hodgePiece_eq_map_complexHarmonicForms`: $H^{p,q}$ is the image of the
  harmonic forms of type $(p,q)$, by the argument above.
- `isHodgeDecomposition_hodgePiece`:
  `IsHodgeDecomposition (conj k) k (fun p : ℤ ↦ hodgePiece J k p.toNat (k - p).toNat)`.
  The conjugation exchanges `hodgePiece J k p q` and `hodgePiece J k q p`
  by `mapCoeff_typeProjection_of_map_smul_conj`. The pieces form an
  internal direct sum because the harmonic forms of each type do, and
  harmonic forms map isomorphically to cohomology.
- `kahlerHodgeStructure`, Tau Ceti's `HodgeStructureOn.ofDecomposition`
  of it, whose `hodgeNumber p` is the dimension of `hodgePiece J k p (k - p)`.

### `Geometry/Manifold/DeRham/Kahler/HodgeNumbers.lean`

- `finrank_hodgePiece_symm`: $h^{p,q}=h^{q,p}$, from Tau Ceti's
  `hodgeNumber_symm`.
- `finrank_hodgePiece_serre`: for `p ≤ n` and `q ≤ n`,
  $h^{p,q}=h^{n-q,n-p}$. `complexHodgeStar` maps the harmonic forms of
  type $(p,q)$ isomorphically onto those of type $(n-q,n-p)$: it preserves
  harmonic forms, commutes with the complex derivation of $J$, and moves
  the degree from $p+q$ to $2n-p-q$ with the same eigenvalue $(p-q)i$.
- `finrank_deRhamCohomology_eq_sum`:
  $b_k=\sum_{p+q=k}h^{p,q}$, from `finsum_hodgeNumber_eq_finrank` and
  `finrank_complexDeRhamCohomology`.
- `even_finrank_deRhamCohomology_of_odd`.
- The milestone, `TauCeti.SmoothTwoForm.IsKahler.hodge_decomposition`
  (below), which installs $g_J$ and the symplectic orientation and
  collects these results.

## Milestone

```lean
theorem TauCeti.SmoothTwoForm.IsKahler.hodge_decomposition
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M]
    {ω : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
    (hK : ω.IsKahler J) (hJ : J.IsIntegrable) {n : ℕ} (hn : finrank ℝ E = 2 * n)
    (k : ℕ) :
    IsHodgeDecomposition (complexDeRhamCohomology.conj k) k
        (fun p : ℤ ↦ complexDeRhamCohomology.hodgePiece J k p.toNat (k - p).toNat) ∧
      FiniteDimensional ℝ (deRhamCohomology I M k) ∧
      (∀ p q, p + q = k →
        finrank ℂ (complexDeRhamCohomology.hodgePiece J k p q) =
          finrank ℂ (complexDeRhamCohomology.hodgePiece J k q p)) ∧
      (∀ p q, p + q = k → p ≤ n → q ≤ n →
        finrank ℂ (complexDeRhamCohomology.hodgePiece J k p q) =
          finrank ℂ (complexDeRhamCohomology.hodgePiece J (2 * n - k) (n - q) (n - p))) ∧
      finrank ℝ (deRhamCohomology I M k) =
        ∑ p ∈ Finset.range (k + 1), finrank ℂ (complexDeRhamCohomology.hodgePiece J k p (k - p)) ∧
      (Odd k → Even (finrank ℝ (deRhamCohomology I M k)))
```

This has the page's hypotheses, with Betti numbers the dimensions of de
Rham cohomology (see *Departures* in `DESIGN.md`). The direct sum is
`IsHodgeDecomposition.isInternal`. The bound `p ≤ n`, `q ≤ n` in the second
symmetry is needed. Outside it the page's $h^{n-q,n-p}$ has a negative
index, so the page's statement leaves that case out. In `ℕ` the
subtraction truncates, and the truncated right side need not vanish there:
for $p=n$, $q=n+1$, $k=2n+1$ the left side is `⊥`, while the right side is
`hodgePiece J 0 0 0`, all of $H^0(M;\mathbb C)$. The finer results
(`isHodgeDecomposition_hodgePiece`, `finrank_hodgePiece_symm`, …) are
stated separately, and the milestone collects them. No error of the page
was found, so `ERRATA.md` needs no entry.

## What the part uses

- *Nijenhuis tensor*, `Geometry/Manifold/Complex/Integrable.lean` (#862):
  `TauCeti.SmoothAlmostComplexStructure.IsIntegrable`, for
  `KahlerCoordinates.lean` and the milestone, and
  `mfderiv_trans_apply_eq_of_fderiv_apply_eq`, which this part adds there.
- *Almost complex manifolds*, `Geometry/Symplectic/Manifold/AlmostComplex/Metric.lean`
  (#860): `TauCeti.SmoothTwoForm.Compatible.metric` and `metric_inner`, in
  the proof of the milestone, and `val_eq_alternatingFormEquiv_kahlerForm`,
  which this part adds there, in `Kahler/Identities.lean`. This dependency
  is new; `DESIGN.md` records it.
- *Moser isotopy*, `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean`
  (merged): `PartialDiffeomorph.mfderivSymmEquiv`, which this part adds
  there, only in the proofs of `DeRham/Hodge/Chart.lean` and
  `DeRham/Hodge/LocalLaplacian.lean`.
- *Symplectic neighbourhoods*,
  `Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean`
  (merged): `PartialDiffeomorph.mpullback_symm_mpullback_apply`, only in
  the proof of `mpullback_symm_extendByZeroAlong`.
- *Nijenhuis tensor*, `Geometry/Symplectic/Manifold/AlmostComplex/Chart.lean`
  (#1295): `TauCeti.SmoothAlmostComplexStructure.mfderiv_symm_apply_chartPushforward_apply`,
  only in the proof of `mpullback_symm_realAlternatingDerivation`, and
  `TauCeti.SmoothAlmostComplexStructure.forall_chartPushforward_apply_eq_iff`,
  only in the proofs of `KahlerCoordinates.lean`.
- Tau Ceti: the declarations listed under *What exists*, and
  `SmoothForm.mapCoeff`, `exactForms`, `closedForms`,
  `deRhamCohomology.mk`, `riemannianVolumeForm`, `integralTopForm`,
  `alternatingFormInner`, `Orientation.formHodgeStar`,
  `TauCeti.exists_contMDiff_ae_eq_of_locally` (if the gluing is done on
  representatives), `TestFunction` cutoffs, `BesselPotentialSpace` and
  `ContDiffOn.exists_openPartialHomeomorph`.
- Mathlib: `UniformSpace.Completion` with its inner product space instance,
  `InnerProductSpace.ofCore`, the closed graph theorem
  `LinearMap.continuous_of_isClosed_graph`, `IsCompactOperator`,
  `PartialDiffeomorph`, and `MeasureTheory.Lp`.

The part does not use *Almost Kähler geometry*. Mathlib and Tau Ceti were
searched, at the pinned versions, for each definition and main result
above: for Hodge decompositions, harmonic forms, Sobolev and $L^2$ spaces
of sections, elliptic regularity of systems, Gårding inequalities,
Lefschetz operators and Kähler identities. What exists is listed under
*What exists*. The issues search again for their lemmas.

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #874, *Build the part Hodge theory*. Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Interior regularity of elliptic systems with a scalar principal part | `Analysis/Distribution/EllipticSystem.lean` | — | 300 |
| 2 | Forms along partial diffeomorphisms: agreement with `inChartAt`, $\mathcal J$, extension by zero, finite covers | `Geometry/Manifold/DifferentialForm/PartialDiffeomorph.lean`, `Geometry/Manifold/LocalDiffeomorph/ChartCover.lean` | — | 250 |
| 3 | The metric, the Hodge star and the codifferential in a chart | `DeRham/Hodge/Chart.lean` | 2 | 350 |
| 4 | The Hodge Laplacian in a chart has a scalar principal part | `DeRham/Hodge/LocalLaplacian.lean` | 3 | 350 |
| 5 | The Hilbert space of $L^2$ forms and its localizations | `DeRham/Hodge/L2.lean` | 2 | 400 |
| 6 | Regularity of weak solutions of $\Delta u=f$ | `DeRham/Hodge/Regularity.lean` | 1, 4, 5 | 450 |
| 7 | The Hodge $H^1$ space and compactness of its inclusion in $L^2$ | `DeRham/Hodge/Sobolev.lean` | 6 | 400 |
| 8 | The Hodge theorem on a closed oriented Riemannian manifold | `DeRham/Hodge/Basic.lean` | 7 | 300 |
| 9 | Complex harmonic forms | `DeRham/Hodge/Complex.lean` | 8 | 300 |
| 10 | The Lefschetz operator and the linear Kähler identity | `Analysis/InnerProductSpace/HodgeStar/Kahler/Lefschetz.lean`, `Analysis/InnerProductSpace/HodgeStar/AlternatingForm.lean`, `Analysis/Normed/Module/Alternating/Derivation.lean`, `Analysis/Normed/Module/Alternating/Uncurry/Fin.lean` | — | 350 |
| 11 | Osculating holomorphic charts of a Kähler manifold | `Geometry/Manifold/Complex/KahlerCoordinates.lean`, `LinearAlgebra/ComplexStructure/SymmetricBilinear.lean` | 3; #862 | 400 |
| 12 | The Kähler identity and $[\Delta,\mathcal J]=0$ | `DeRham/Kahler/Identities.lean`, `Geometry/Manifold/DifferentialForm/AlmostComplexType.lean` | 3, 10, 11 | 400 |
| 13 | Conjugation on complex de Rham cohomology, and the Hodge decomposition | `Geometry/Manifold/DeRham/ComplexCoefficients.lean`, `DeRham/Kahler/Decomposition.lean` | 9, 12 | 400 |
| 14 | Hodge numbers, Betti numbers, and the milestone | `DeRham/Kahler/HodgeNumbers.lean` | 13; #860 | 300 |

`DeRham/` stands for `Geometry/Manifold/DeRham/`. Issues 1, 2 and 10 can
start at once. Issue 11 also waits for #862, and issue 14 for #860. The
milestone is proved in issue 14. Issues 1–8 prove the Hodge theorem for
the Laplacian, which `DESIGN.md` notes can start at once. They need no
other part, and other parts may use them.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  p. 171, (4.3.8).
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (the Hodge theorem) and §7 (Kähler manifolds, the Kähler
  identities and the Hodge decomposition).
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012],
  Chapter VI, Theorem (8.5).
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*,
  Graduate Texts in Mathematics 94, Springer, 1983, Chapter 6. The plan's
  bibliography has no key for it.
