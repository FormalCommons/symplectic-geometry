# Smooth families

The detailed design of part 14 of `DESIGN.md`, *Smooth families*. It fixes
the files of the part, its definitions and their API, the Lean names and
statements of its main results, what it takes from Tau Ceti, Mathlib and the
other parts, and the building issues in the order they can be done. It
answers each question that `DESIGN.md` leaves to it (see *Decisions*).

The part has two halves. The first proves the milestone *Smooth families of
primitives* of `auxiliary/smooth-primitives.md`, and the stronger statement
(★) that its proof needs, by the Mayer–Vietoris induction over a finite good
cover that McDuff–Salamon [McDuffSalamon2017, proof of Theorem 3.2.4, p. 111]
sketch after Bott–Tu [BottTu1982], with Weil's good covers [Weil1952]. The
second passes between families over $[0,1]$ and over `ℝ`, as *Manifolds,
families and signs* in `DESIGN.md` asks: Seeley's extension in the time
variable (Seeley 1964, cited in full under *References*), the restriction of isotopies over `ℝ` to Tau Ceti's
`TauCeti.Diffeotopy`, the reading of a `Diffeotopy` over `ℝ` through
`Real.smoothTransition`, and the constructor of a `Diffeotopy` from a jointly
smooth family of diffeomorphisms. Paths of Tau Ceti files are relative to
`.lake/packages/TauCeti/TauCeti/`; every Tau Ceti and Mathlib name below was
checked at the pinned versions.

No statement of this part is one that the authors' errata
[McDuffSalamon2019Errata] correct, so the part does not cite them.

## What exists, and what the part adds

- **Forms and their slices.** Smooth forms `TauCeti.SmoothForm I M F k`
  (`Geometry/Manifold/DifferentialForm/Smooth.lean`), pullback as a linear map
  `TauCeti.SmoothForm.mpullback f hf`, the exterior derivative
  `TauCeti.mextDerivₗ` with `TauCeti.SmoothForm.mextDerivₗ_mpullback`, and
  multiplication by a function `TauCeti.SmoothForm.funSMulₗ`. A family is read
  through the slices `SmoothForm.mpullback (Prod.mk t)
  (contMDiff_const.prodMk contMDiff_id)`, as Tau Ceti's Moser theorem reads it.
  `TauCeti.SmoothForm.contMDiff_mpullback_prodMk`
  (`Geometry/Manifold/DifferentialForm/Pullback/Family.lean`) says that the
  slices of a form on `N × M` form a smooth section along the projection to
  `M`. Tau Ceti has no converse, no name for a smooth family, and no notion of
  a linear map that takes smooth families to smooth families; the part adds
  them.
- **Open subsets.** Restriction along `Opens.inclusion`, extension by zero
  `TauCeti.RoughForm.extendByZero` with `IsSmoothForm.extendByZero_smul`, and
  locality of smoothness `IsSmoothForm.of_mpullback_inclusion_sup`
  (`Geometry/Manifold/DifferentialForm/Opens.lean`).
- **De Rham cohomology.** `TauCeti.closedForms`, `TauCeti.exactForms`,
  `TauCeti.deRhamCohomology` with `deRhamCohomology.mk`, `mk_surjective`,
  `mk_eq_zero_iff`, `ker_mk` (`Geometry/Manifold/DeRham/Basic.lean`), the
  closed 0-forms as locally constant functions
  (`mem_closedForms_zero_iff`, `DeRham/DegreeZero.lean`), pullback of closed
  forms `TauCeti.closedForms.mpullback` (`DeRham/Map.lean`), homotopy
  invariance (`DeRham/HomotopyInvariance.lean`), and the Mayer–Vietoris
  sequence (`DeRham/MayerVietoris.lean`): `SmoothForm.injective_mayerVietoris`,
  `SmoothForm.exact_mayerVietoris`, `SmoothForm.surjective_mayerVietoris`,
  `exists_closedForms_mpullback_eq_mextDerivₗ`,
  `exists_closedForms_coe_eq_extendByZero_mextDeriv` and the connecting map.
  Tau Ceti has no finite-dimensionality of de Rham cohomology, not even on a
  compact manifold, and no good covers.
- **Homotopy operator.** `TauCeti.homotopyOperator` on the cylinder
  `M × Icc 0 1` (`Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`),
  on rough forms, with `IsSmoothForm.homotopyOperator`,
  `mextDeriv_homotopyOperator` (for closed forms, `d (h φ) = ι₁^* φ - ι₀^* φ`)
  and `homotopyOperator_mpullback_prodMap_id_of_isSmoothForm` (naturality
  along `g × id` for any differentiable `g`, slice inclusions included). All
  hold on manifolds with boundary or corners, which the cylinder over
  `unitInterval × W` is. Tau Ceti has no linear map on smooth forms for it.
- **Extension across a boundary.** `TauCeti.HalfSpaceExtension`
  (`Analysis/Sobolev/Trace/Reflection/HalfSpace.lean`) has Hestenes' reflection
  with `K` terms, `exists_contDiff_extension_halfSpace`, which is `C^n` only
  for `n < K`, with `timeScale`, `map_timeScale_eq_sum_pow_card_smul` and the
  coefficients `higherReflectionCoeff`; and
  `HasFTaylorSeriesUpToOn.contDiff_piecewise`
  (`Analysis/Calculus/ContDiff/FTaylorSeries.lean`) glues two functions across
  a closed cover when their Taylor series agree on the overlap. No finite
  reflection is smooth of every order: a sum $\sum_{j<K}c_jf(-\lambda_jt,x)$
  with distinct $\lambda_j>0$ matches every derivative at $t=0$ only if
  $\sum_jc_j(-\lambda_j)^n=1$ for every $n$, that is
  $\sum_jc_j/(1+\lambda_jz)=1/(1-z)$ as rational functions, which the poles
  forbid. So the $C^\infty$ extension is Seeley's series, new here. It reuses `timeScale`, `map_timeScale_eq_sum_pow_card_smul` for the
  derivatives of the dilated terms, and glues at $t=0$ as
  `HasFTaylorSeriesUpToOn.union_of_isClosed` does, by `HasFTaylorSeriesUpToOn.union`
  for sets closed only in their union, but not the reflection itself. Mathlib has neither.
- **Isotopies.** `TauCeti.Diffeotopy J n M`
  (`Geometry/Diffeomorphism/Diffeotopy/Basic.lean`), a level-preserving
  diffeomorphism of `unitInterval × M`, with `timeSlice`, `final`,
  `cylinderMap` on `M × unitInterval` and `mfderiv_cylinderMap_prodMk_snd`;
  `TauCeti.timeDependentFlowDiffeotopy` (`Diffeotopy/Flow.lean`);
  `TauCeti.eulerianField` with `eulerianField_apply_apply` and
  `hasMFDerivAt_eulerianField` (`Geometry/Manifold/Flow/Eulerian.lean`);
  `TauCeti.timeDependentFlowDiffeomorph`; `ContMDiff.smoothTransition`
  (`Geometry/Manifold/Instances/Icc.lean`); the inverse function theorem
  `TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq` and
  `TauCeti.isLocalDiffeomorph_of_mfderiv_eq`
  (`Geometry/Manifold/LocalDiffeomorph/Basic.lean`); Mathlib's
  `IsLocalDiffeomorph.diffeomorphOfBijective`, `Diffeomorph.prodComm`, and the
  unit tangent vector `1 : TangentSpace (𝓡∂ 1) t` of the interval with
  `mfderiv_subtypeVal_Icc_one` (`Geometry/Manifold/Instances/Icc.lean`), which
  points in the direction of increasing time at both ends. Tau Ceti has no
  passage from an isotopy over `ℝ` to a `Diffeotopy`, no velocity field of a
  `Diffeotopy`, and no constructor of a `Diffeotopy` from a family of
  diffeomorphisms.
- **Time reparametrization.** Tau Ceti's
  `Analysis/SpecialFunctions/SmoothTransition.lean` has the derivative of
  `Real.smoothTransition` outside $[0,1]$ (`deriv_of_neg`, `deriv_of_one_lt`)
  and its integral, but not that it is positive on $(0,1)$; the part adds it.
  Neither library has a smooth map from `ℝ` into a slightly larger open
  interval that is the identity on a closed interval. *Moser isotopy* and
  *Contact geometry* compose with such a map in time, and the part adds it.
  Tau Ceti's `TauCeti.exists_contDiff_odd_truncation` is the identity on
  `[-r, r]` but does not bound its values between `r` and `R`, so the part
  builds the map from Mathlib's `ContDiffBump` instead, as Tau Ceti's
  `TauCeti.exists_contDiff_eventuallyEq_id_forall_mem_ball` and
  `TauCeti.exists_contDiff_cutoff_id` do. Both need `0 < r`; the first is
  the identity only on some neighbourhood of `0`, and the second is the
  identity on `[-r, r]` but states no bound on its values.
- **Embeddings.** Mathlib's `exists_embedding_euclidean_of_compact`
  (`Geometry/Manifold/WhitneyEmbedding.lean`): a compact Hausdorff manifold
  has a smooth closed embedding into some `EuclideanSpace ℝ (Fin N)` with
  injective derivatives. It is the input of Weil's construction.

## Decisions

- **(★) for forms on `unitInterval × M`.** A smooth family over $[0,1]$ is a
  map `α : unitInterval → SmoothForm I M F k` that is the family of slices of
  a smooth form on `unitInterval × M` (`IsSmoothFamily`, below). This is the
  model of *Manifolds, families and signs*, given a name; no third model is
  added. A linear map `T` defined on a submodule of forms takes smooth
  families to smooth families when `t ↦ T (α t)` is a smooth family for every
  smooth family `α` with values in the submodule (`PreservesSmoothFamilies`).
  (★) is the structure `SmoothCohomologySplitting I M`, which holds the
  spaces $S^k$, the maps $p$ and $h$ of every degree at once, since the
  induction uses all degrees together. The milestone is stated for a manifold
  with a finite good cover; existence of such covers on compact boundaryless
  manifolds is a separate theorem, as is finite-dimensionality of de Rham
  cohomology there.
- **The time extension.** It is built in three layers: Seeley's extension of
  functions on `ℝ` from $[0,1]$, with parameters in an open set of a normed
  space (`Analysis/Calculus/ContDiff/Seeley/`); its manifold form for maps
  `unitInterval × M → F` into a normed space
  (`Geometry/Manifold/ContMDiff/TimeExtension.lean`); and its form for forms
  (`Geometry/Manifold/DifferentialForm/TimeExtension.lean`). A form is not
  extended through its components in a chart. Since a family is read through
  its slices, the extension is applied to the slices: each value
  $\alpha_t(x)$ lies in the fibre over $x$, which does not depend on $t$, and
  Seeley's operator, linear and acting at each $x$ separately, applies to
  $t\mapsto\alpha_t(x)$ there. The result is the form on `ℝ × M` with these
  slices, built by `SmoothForm.ofSlices`. Smoothness is checked on a tangent
  trivialization of $M$, which does not involve $t$, so it reduces to the
  manifold form for the functions $(t,y)\mapsto\alpha_t(y)(e_y v)$. The
  extension of a smooth form keeps all its slices, not its $dt$ components,
  which no statement of the parts reads.
- **Contractions of a good cover.** `IsSmoothlyContractible I N`: there are
  `c : N` and a smooth `F : N × unitInterval → N` with `F (x, 0) = c` and
  `F (x, 1) = x`. This is the form in which Weil states the Poincaré lemma
  [Weil1952, §2, p. 124], with Tau Ceti's orientation of the homotopy
  operator, so that `mextDeriv_homotopyOperator` gives
  $d\,h(F^*z)=z-F_0^*z=z$ for a closed form $z$ of positive degree. A good
  cover is a finite family of opens covering $M$ whose nonempty
  intersections of nonempty subfamilies are smoothly contractible. Nothing
  here asks for a diffeomorphism onto a star-shaped or convex set; Weil's
  convex charts give the contractions by straight lines.
- **The induction.** A direct strong induction on the number of members of
  the cover's set of intersections, not Tau Ceti's
  `TauCeti.mayerVietoris_induction`. That principle concerns all opens of a
  second-countable space, needs a basis closed under intersections, and asks
  the property to pass to countable disjoint unions; (★) does not, since it
  fails when cohomology is infinite-dimensional (the auxiliary page's example
  of the plane minus the points $(j,0)$, $j\in\mathbb{Z}$). The induction is on
  a finset `s` of index sets: the property holds for
  `⋃ a ∈ s, ⋂ i ∈ a, U i`, by `Finset.strongInduction` on `s.card`, since the
  intersection with the last member is a union of `s.card - 1` members.
- **Order of the cylinder.** Families and diffeotopies live on
  `unitInterval × M` and `ℝ × M`, time first, as `TauCeti.Diffeotopy`, Tau
  Ceti's Moser theorem and the overview do. `M × unitInterval` occurs only
  where Tau Ceti puts it: `TauCeti.homotopyOperator`, whose interval is the
  contraction parameter and never the time of a family, and
  `Diffeotopy.cylinderMap` with `Diffeotopy.HasHamiltonian`. One lemma passes
  between the two orders for forms (`mpullback_prodMk_mpullback_prodComm`,
  through Mathlib's `Diffeomorph.prodComm`). The time derivative of a
  diffeotopy is taken through `Diffeotopy.cylinderMap`, as
  `HasHamiltonian` takes it, so it needs no such lemma.
- **The constructor.** `TauCeti.Diffeotopy.ofContMDiff` takes a family
  `ψ : unitInterval → M ≃ₘ⟮I, I⟯ M`, jointly smooth, with `ψ 0` the identity:
  the input that the milestones of *Hamiltonian flows* describe. Its inverse
  is jointly smooth by an argument local in charts, the same at every time
  $t_0\in[0,1]$. Near $(t_0,x_0)$, the map is written as $G(s,u)$ in a chart
  of $M$ at $x_0$ and one at $\psi_{t_0}(x_0)$, for $s$ in an interval
  $[a,b]$ that is a neighbourhood of $t_0$ in $[0,1]$, and extended to all
  $s\in\mathbb R$ by Seeley's operator, giving $\tilde G$. Its partial
  derivative in $u$ at $(t_0,u_0)$ is invertible, so the implicit function
  theorem with a moving level solves $\tilde G(s,u)=v$ by a smooth
  $u=\varphi(s,v)$, and $\varphi(s,v)=\psi_s^{-1}v$ in charts for
  $s\in[a,b]$, because $\tilde G=G$ there. The slices being bijective, no
  injectivity of the extension and no compactness are needed. A version taking a
  `TauCeti.SmoothIsotopy` from the identity with surjective slices would need
  the same argument to see that the slices are diffeomorphisms, so it is not
  planned; a part that needs it adds it as a corollary.
  `TauCeti.SmoothIsotopy.exists_diffeotopy_apply_eq` gives a `Diffeotopy` on
  a compact set, but reparametrized by `Real.smoothTransition`, so it does
  not give $\Phi_t=\psi_t$ and cannot serve here; it remains the shortcut for
  statements about the time-one map.
- **The files of the bridge.** The bridge is two files, named after their
  content: `Geometry/Diffeomorphism/Diffeotopy/Real.lean` (isotopies over
  `ℝ` and diffeotopies: restriction, Eulerian fields, flows, the reading over
  `ℝ`) and `Geometry/Diffeomorphism/Diffeotopy/OfContMDiff.lean` (the
  constructor). Their declarations are in `TauCeti.Diffeotopy`, as they are
  about Tau Ceti's notion.
- **The velocity of a diffeotopy** is not defined here. *Hamiltonian flows*
  defines it, as `TauCeti.Diffeotopy.velocity` in
  `Diffeotopy/Velocity.lean`, and that part builds on this one. So the
  bridge states its Eulerian fields pointwise along the motion, with the
  time derivative of `Φ` written as the derivative of `Φ.cylinderMap` at
  `(x, t)` on `∂ₜ = ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))`, the vector
  that `HasHamiltonian` and `velocity_apply_apply` use. With Mathlib's
  `oneTangentSpaceIcc`, the interval's unit vector points towards
  increasing time also at $t=1$, where the chart of the interval reverses
  orientation.

## Files

### `Analysis/SpecialFunctions/SmoothTransition.lean`

Named like Tau Ceti's file; in Mathlib's namespace `Real.smoothTransition`,
except for the reparametrization, which is in `SymplecticGeometry`, and the
lemmas about Tau Ceti's `TauCeti.collaredSmoothTransition`, which are in `TauCeti`.

- `Real.smoothTransition.deriv_pos {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) :
  0 < deriv Real.smoothTransition x`, from the quotient
  $f(x)/(f(x)+f(1-x))$ and the positive derivative of
  `expNegInvGlue` on $(0,\infty)$ (Tau Ceti's `expNegInvGlue.hasDerivAt`).
- `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo {a b ε : ℝ}
  (hab : a ≤ b) (hε : 0 < ε) : ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧
  Set.EqOn c id (Set.Icc a b) ∧ (∀ t, c t ∈ Set.Ioo (a - ε) (b + ε)) ∧
  ∀ t ∉ Set.Ioo (a - ε) (b + ε), c t = (a + b) / 2`. Proof:
  let $m=(a+b)/2$, let $f$ be a `ContDiffBump m` with radii
  $(b-a)/2+\varepsilon/2$ and $(b-a)/2+\varepsilon$, and set
  $c(t)=m+f(t)(t-m)$. Then $f=1$ on $[a,b]$
  (`ContDiffBump.one_of_mem_closedBall`). Since $0\le f\le1$ and $f$
  vanishes off the open ball (`ContDiffBump.support_eq`),
  $|c(t)-m|<(b-a)/2+\varepsilon$, and $c=m$ off that ball. The case $a=b$
  is included. The statement
  does not mention `Real.smoothTransition`. It sits in this file because Tau
  Ceti keeps its truncations in its file of the same name.

### `Analysis/Calculus/ContDiff/FTaylorSeries.lean`

Named like Tau Ceti's file. `HasFTaylorSeriesUpToOn.union`, for sets each
closed relative to their union.

### `Analysis/Calculus/ContDiff/Concat.lean`

`SymplecticGeometry.curveTrans Z₁ Z₂`, for `Z₁ Z₂ : ℝ → E`, equal to
`Z₁ (2 * s)` for `s ≤ 1 / 2` and `Z₂ (2 * s - 1)` after, the parametrization
of `Path.trans`, with `ContDiff.curveTrans` (`C^n` when `Z₁` is constant
near `1`, `Z₂` near `0`, and `Z₁ 1 = Z₂ 0`). Tau Ceti's
`TauCeti.curveConcat` uses `3 * s` and `3 * s - 2` instead. *Maslov index*
uses it in `Maslov/Path/Regular.lean`.

### `Analysis/Normed/Group/FunctionSeries.lean`

Named like Mathlib's file. `tendstoUniformlyOn_finsetSum_of_hasSum`, the
form of `tendstoUniformlyOn_tsum` that assumes the pointwise sums exist
instead of completeness.

### `Analysis/Sobolev/Trace/Reflection/HalfSpace.lean`

Named like Tau Ceti's file; in its namespace `TauCeti.HalfSpaceExtension`.
`norm_timeScale_le` and `timeScale_of_fst_eq_zero`.

### `LinearAlgebra/Lagrange.lean`

Evaluation of Mathlib's Lagrange basis, in Mathlib's namespace `Lagrange`,
for `Seeley/Coefficients.lean`.

- `Lagrange.eval_basis (s : Finset ι) (v : ι → F) (i : ι) (x : F) :
  (basis s v i).eval x = ∏ j ∈ s.erase i, (x - v j) / (v i - v j)`.
- `Lagrange.sum_eval_basis_mul_eval (hvs : Set.InjOn v s) (hP : P.degree < #s)
  (x : F) : ∑ i ∈ s, (basis s v i).eval x * P.eval (v i) = P.eval x`.
- `Lagrange.sum_eval_basis_mul_pow (hvs : Set.InjOn v s) (hn : n < #s) (x : F) :
  ∑ i ∈ s, (basis s v i).eval x * v i ^ n = x ^ n`.

### `Analysis/Calculus/ContDiff/Seeley/Coefficients.lean`

Seeley's coefficients: a real sequence $a_k$ with
$\sum_ka_k(-2^k)^n=1$ for every $n\ge0$ and $\sum_k|a_k|2^{kn}<\infty$ for every
$n$. Seeley takes the limit of the Lagrange weights at the nodes $-2^k$,
$a_k=\prod_{j\ne k}(1+2^j)/(2^j-2^k)$, and bounds it.

- `SymplecticGeometry.seeleyCoeff : ℕ → ℝ`, with `seeleyCoeff_def` and
  `hasProd_seeleyCoeff (k : ℕ) : HasProd (fun j : ({k}ᶜ : Set ℕ) ↦
  (1 + 2 ^ (j : ℕ)) / (2 ^ (j : ℕ) - 2 ^ k)) (seeleyCoeff k)`.
- `summable_seeleyCoeff_mul_pow (n : ℕ) :
  Summable fun k ↦ |seeleyCoeff k| * 2 ^ (k * n)`.
- `tsum_seeleyCoeff_mul_neg_two_pow (n : ℕ) :
  ∑' k, seeleyCoeff k * (-2 ^ k) ^ n = 1`.

### `Analysis/Calculus/ContDiff/Seeley/Extension.lean`

Seeley's extension from $[0,1]$ to `ℝ`, for functions with values in a normed
space `F`. For $t<0$,
$E f(t)=\sum_ka_k\,\chi(2^kt)\,f(-2^kt)$, with a fixed smooth cutoff $\chi$
that is $1$ on $[-\tfrac12,0]$ and $0$ on $(-\infty,-1]$ (built from
`Real.smoothTransition`), so that only values of $f$ on $[0,1]$ enter and,
for each $t<0$, the sum is finite. At $t=1$ the same is done after the
reflection $t\mapsto1-t$.

- `SymplecticGeometry.seeleyExtend (f : ℝ → F) : ℝ → F` (from $[0,\infty)$,
  using values on $[0,1]$) and
  `SymplecticGeometry.seeleyIccExtend (f : ℝ → F) : ℝ → F` (from $[0,1]$,
  both ends), with `_def` lemmas.
- `seeleyIccExtend_of_mem (h : t ∈ Icc 0 1) : seeleyIccExtend f t = f t`;
  `seeleyIccExtend_congr (h : EqOn f g (Icc 0 1)) : seeleyIccExtend f =
  seeleyIccExtend g`; `seeleyIccExtend_zero`, `seeleyIccExtend_add`,
  `seeleyIccExtend_smul`, bundled as the `ℝ`-linear map
  `seeleyIccExtendLinearMap F : (ℝ → F) →ₗ[ℝ] (ℝ → F)` with
  `coe_seeleyIccExtendLinearMap`; and
  `LinearMap.map_seeleyIccExtend (L : F →ₗ[ℝ] G) : L (seeleyIccExtend f t) =
  seeleyIccExtend (L ∘ f) t`, the last because the sum is finite at each $t$.
  The same lemmas, and `seeleyExtendLinearMap`, for `seeleyExtend`.
- `contDiffOn_seeleyIccExtend {f : ℝ × E → F} {U : Set E} (hU : IsOpen U)
  (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ U)) : ContDiffOn ℝ ∞
  (fun p : ℝ × E ↦ seeleyIccExtend (fun s ↦ f (s, p.2)) p.1) (univ ×ˢ U)`,
  with the analogue `contDiffOn_seeleyExtend` from `Ici 0 ×ˢ U`. The proof
  bounds the derivatives of the terms by `summable_seeleyCoeff_mul_pow`
  (`map_timeScale_eq_sum_pow_card_smul` for the dilated terms), so the series
  of derivatives converges locally uniformly on $t<0$; its Taylor series at
  $t=0$ is that of $f$ by `tsum_seeleyCoeff_mul_neg_two_pow`; and
  `HasFTaylorSeriesUpToOn.union` glues the two sides on `univ ×ˢ U`, where
  they are closed only relative to their union.
- `exists_contDiff_eqOn_of_contDiffOn_halfSpace [HasContDiffBump E]`:
  a function smooth on `U ∩ {z | 0 ≤ z.1}`, for an open `U` of `ℝ × E`
  containing `(0, x₀)`, agrees on the part of some open `V ∋ (0, x₀)`
  where `0 ≤ z.1` with a function smooth on `ℝ × E`; added by issue 5 of
  *Liouville structures*.

The module docstring cites R. T. Seeley, *Extension of $C^\infty$ functions
defined in a half space*, Proc. Amer. Math. Soc. 15 (1964), 625–626, which
the plan's `references.bib` does not list, in full, and credits Tau Ceti's
`TauCeti.HalfSpaceExtension.contDiff_halfSpaceReflection`, whose proof this
one follows with an infinite sum in place of a finite one.

### `Geometry/Manifold/ContMDiff/TimeExtension.lean`

Maps `unitInterval × M → F` into a normed space, for a boundaryless `M`.

- `SymplecticGeometry.timeExtend (f : unitInterval × M → F) : ℝ × M → F`,
  `(t, x) ↦ seeleyIccExtend (fun s ↦ f (projIcc 0 1 _ s, x)) t`, with
  `timeExtend_def`.
- `timeExtend_apply_coe (t : unitInterval) (x : M) : timeExtend f (t, x) =
  f (t, x)`; `timeExtend_add`, `timeExtend_smul`;
  `timeExtendLinearMap M F : (unitInterval × M → F) →ₗ[ℝ] (ℝ × M → F)` with
  `coe_timeExtendLinearMap`; `LinearMap.map_timeExtend`.
- `timeExtend_eq_zero (h : ∀ s, f (s, x) = 0) (t : ℝ) : timeExtend f (t, x) =
  0`: Seeley's sum at `(t, x)` combines values of `f` at the same point `x`.
  *Hamiltonian flows* uses it to keep a Hamiltonian zero off a compact set
  after the extension.
- `ContMDiffOn.timeExtend {U : Set M} (hU : IsOpen U)
  (hf : ContMDiffOn ((𝓡∂ 1).prod I) 𝓘(ℝ, F) ∞ f (univ ×ˢ U)) :
  ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ (timeExtend f) (univ ×ˢ U)`, and
  `ContMDiff.timeExtend`, from `contDiffOn_seeleyIccExtend` in charts of $M$
  (the time coordinate needs no chart beyond `Subtype.val`).

### `Geometry/Manifold/DifferentialForm/SmoothFamily/Basic.lean`

Smooth families of forms over a parameter manifold `N` (model
`J : ModelWithCorners ℝ EN HN`; in the uses, `unitInterval` or `ℝ`).

- `SymplecticGeometry.IsSmoothFamily J (α : N → SmoothForm I M F k)
  : Prop := ∃ Ω : SmoothForm (J.prod I) (N × M) F k, ∀ t,
  SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω =
  α t`, with `isSmoothFamily_def`.
- `TauCeti.SmoothForm.ofSlices` (in Tau Ceti's namespace, as it is about
  Tau Ceti's `SmoothForm`): from a family whose slice section
  `p ↦ TotalSpace.mk' _ p.2 ((α p.1).val p.2)` is smooth along the projection,
  the form on `N × M` that vanishes on the parameter directions and has the
  slices `α t` (`mpullback_prodMk_ofSlices`). Hence
  `isSmoothFamily_iff_contMDiff`, the converse direction being Tau Ceti's
  `contMDiff_mpullback_prodMk`. The closure lemmas `.fun_smul`, `.funSMul`,
  `.extendByZero_smul` and the one on `U ⊔ V` are proved through this
  characterization, which makes smoothness of a family local in `M`; the
  others are built from `Ω` directly.
- Consequences: `IsSmoothFamily.contMDiff_apply` (for fixed `x` and `v`,
  `t ↦ (α t).val x v` is smooth); `isSmoothFamily_const`; `.add`, `.neg`,
  `.sub`, `.smul`, `.fun_smul` (by a smooth function of `t`), `.sum`;
  `.mpullback` (along a smooth map of `M`), `.mextDeriv`, `.funSMul` and
  `.extendByZero_smul` (multiplication by a fixed function with support in an
  open set, then extension by zero, as in `IsSmoothForm.extendByZero_smul`);
  `.comp` (reparametrization by a smooth map of parameter manifolds);
  `isSmoothFamily_iff_mpullback_inclusion_sup` (a family on `U ⊔ V` is
  smooth exactly when its restrictions to `U` and `V` are).
- The other order of the cylinder:
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodComm`, that the slice
  at `t` of the pullback of `Ω : SmoothForm (I.prod J) (M × N) F k` along
  `Diffeomorph.prodComm` is the pullback of `Ω` along `(·, t)`.
- `SymplecticGeometry.isSmoothFamily_interiorₗ`: for a two-form `σ` and a
  family `X_t` of vector fields that is jointly smooth on `N × M`, the
  family `t ↦ σ.interiorₗ (X t)` is smooth. It was first in
  `Flux/Hamiltonian.lean` of *Hamiltonian flows*; it is here because it is
  about smooth families only, and `SymplecticIsotopy.lean` of that part uses
  it too. For it this file imports Tau Ceti's
  `Geometry/Symplectic/Manifold/Flat.lean`.

### `Geometry/Manifold/ContMDiff/Dual.lean`

- `contMDiff_dual_apply_of_span_eq_top`: for a family `x : N → X` and a set
  `s` of functionals spanning `Module.Dual 𝕜 X`, if `t ↦ g (x t)` is `C^n`
  for each `g ∈ s`, then so is `t ↦ f (x t)` for every functional `f`.
  `contMDiff_dual_apply_of_separating`: the same for a finite-dimensional
  `X`, with `∀ z ≠ 0, ∃ g ∈ s, g z ≠ 0` in place of the span. Imports only
  Mathlib; `SmoothFamily/Map.lean` imports it.

### `Geometry/Manifold/DifferentialForm/SmoothFamily/Map.lean`

- `SymplecticGeometry.PreservesSmoothFamilies
  {D : Submodule ℝ (SmoothForm I M F k)} (T : D →ₗ[ℝ] SmoothForm I' M' G l) :
  Prop := ∀ α : unitInterval → D, IsSmoothFamily (𝓡∂ 1)
  (fun t ↦ (α t : SmoothForm I M F k)) → IsSmoothFamily (𝓡∂ 1)
  (fun t ↦ T (α t))`, with `preservesSmoothFamilies_def`.
- `.add`, `.smul`, `.neg`, `.sub`, `preservesSmoothFamilies_zero`;
  `.comp` (with a map whose image lies in the next domain, as
  `LinearMap.codRestrict`); `.mextDerivₗ`, `.mpullback` and `.funSMul` (post-
  composition with these maps); `preservesSmoothFamilies_subtype` (the
  inclusion of a submodule); `.of_mpullback_inclusion_sup` (gluing, from
  `isSmoothFamily_iff_mpullback_inclusion_sup`).
- Finite-dimensional targets: for `S` finite-dimensional with basis `b`,
  `preservesSmoothFamilies_iff_contMDiff_repr` — a map into `S` takes smooth
  families to smooth families exactly when, for every smooth family `α`, every
  coordinate `t ↦ b.repr (T (α t)) i` is smooth on `unitInterval`. The
  forward direction picks finitely many evaluations `ω ↦ ω.val x v` that
  separate `S`, so that each coordinate is a fixed linear combination of
  them; the converse writes the family as `∑ i, c_i(t) • b i`. Consequences:
  maps into a finite-dimensional space whose coordinates are smooth on
  families, and finite linear combinations of fixed forms with such
  coefficients, take smooth families to smooth families.

### `Geometry/Manifold/LocalDiffeomorph/OpenSubset.lean`

Named like Tau Ceti's file; in `TauCeti`.

- `TauCeti.isLocalDiffeomorph_inclusion`: for open subsets `U ≤ W`, the
  inclusion `Opens.inclusion h : U → W` is a `C^n` local diffeomorphism, for
  restricting families and forms between open subsets.

### `Geometry/Manifold/DifferentialForm/Pullback/Smooth.lean`

Named like Tau Ceti's file; in `TauCeti`.

- `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth
  `(k + 1)`-form along a constant map is `0`, for the end of a contraction.

### `Geometry/Manifold/DeRham/DegreeZero.lean`

Named like Tau Ceti's file; in `TauCeti`.

- `TauCeti.finiteDimensional_closedForms_zero`: an instance, on a connected
  manifold, of `FiniteDimensional ℝ (closedForms I M 0)`, for the degree-zero
  space of the contractible splitting.

### `Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`

Named like Tau Ceti's file; in `TauCeti`.

- `TauCeti.SmoothForm.homotopyOperator : SmoothForm (I.prod (𝓡∂ 1))
  (M × Icc (0 : ℝ) 1) F (k + 1) →ₗ[ℝ] SmoothForm I M F k`,
  the operator `TauCeti.homotopyOperator` with `IsSmoothForm.homotopyOperator`
  and `homotopyOperator_add`, with `coe_homotopyOperator` and
  `mextDerivₗ_homotopyOperator` (for a closed form, and a complete `F`).

### `Geometry/Manifold/DifferentialForm/SmoothFamily/HomotopyOperator.lean`

- `SymplecticGeometry.IsSmoothFamily.homotopyOperator`: for a smooth family
  $\alpha_t$ of `(k + 1)`-forms on `M' × Icc 0 1` over any parameter manifold
  `N`, with a complete coefficient space, the family $t\mapsto h\alpha_t$ of
  `k`-forms on `M'` is smooth. A form $\Omega$ on `N × (M' × Icc 0 1)` with
  slices $\alpha_t$ is pulled back along $((t,x),s)\mapsto(t,(x,s))$ on
  $(N\times M')\times[0,1]$, and the homotopy operator of that cylinder has
  the slices $h\alpha_t$ by
  `homotopyOperator_mpullback_prodMap_id_of_isSmoothForm` applied to the
  slice inclusions.
- `SymplecticGeometry.preservesSmoothFamilies_homotopyOperator_mpullback`:
  for a smooth `F : M' × Icc 0 1 → M`, a complete coefficient space and a
  submodule `D` of the forms on `M`, the map
  $\omega\mapsto h(F^*\omega)$ on `D` takes smooth families to smooth
  families, as a corollary of `IsSmoothFamily.homotopyOperator` through
  `IsSmoothFamily.mpullback`. The
  file imports `SmoothFamily/Map.lean` and `DifferentialForm/HomotopyOperator.lean`.

### `Geometry/Manifold/DifferentialForm/SmoothFamily/Poincare.lean`

- `SymplecticGeometry.isSmoothFamily_homotopyOperator_mpullback_and_mextDerivₗ_eq`:
  for a smooth contraction `Φ : M × unitInterval → M` of `M` to `c` and a
  smooth family $\alpha_t$ of closed `(k + 1)`-forms with a complete
  coefficient space, over any parameter manifold, $t\mapsto h(\Phi^*\alpha_t)$
  is a smooth family and $d\,h(\Phi^*\alpha_t)=\alpha_t$, by
  `IsSmoothFamily.homotopyOperator` and
  `SmoothForm.mextDerivₗ_homotopyOperator_mpullback_of_contraction`; with the
  corollary `IsSmoothlyContractible.exists_isSmoothFamily_mextDerivₗ_eq`.
- `SymplecticGeometry.exists_isSmoothFamily_mextDerivₗ_eq_of_starConvex`, the
  parametric radial primitives, through `StarConvex.lineContraction` of
  `DeRham/GoodCover/Basic.lean`: they also vanish at each point where the
  form vanishes along the segment from the centre, and are `0` where the form
  is. *Isotopy extension* uses them for the ball extension. The file imports
  `SmoothFamily/HomotopyOperator.lean` and `DeRham/GoodCover/Basic.lean`.

### `Geometry/Manifold/DifferentialForm/TimeExtension.lean`

- `TauCeti.SmoothForm.timeExtend : SmoothForm ((𝓡∂ 1).prod I)
  (unitInterval × M) F k →ₗ[ℝ] SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k`
  (in Tau Ceti's namespace, as it is about Tau Ceti's `SmoothForm`),
  for a boundaryless `M`: the form `ofSlices` of the slices extended by
  `seeleyIccExtend` at each point (see *Decisions*), named
  `TauCeti.SmoothForm.timeExtendSlice Ω s`, with `timeExtend_def`.
- `mpullback_prodMk_timeExtend (t : unitInterval)`: the slice of
  `timeExtend Ω` at `(t : ℝ)` is the slice of `Ω` at `t`.
- `IsSmoothFamily.exists_extend`: every smooth family over `unitInterval` is
  the restriction of one over `ℝ`.

### `Geometry/Manifold/ContMDiff/LineMap.lean`

- `ContMDiff.lineMap`: for `C^n` maps `f₁ f₂ : M → V` into a normed space
  over a nontrivially normed field `𝕜` and a `C^n` map `g : M → 𝕜`,
  `x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)` is `C^n`; the manifold form
  of Mathlib's `ContDiff.lineMap`. `DeRham/GoodCover/Basic.lean` imports it
  for its straight-line contractions.

### `Geometry/Manifold/DeRham/GoodCover/Basic.lean`

- `SymplecticGeometry.IsSmoothlyContractible (I) (N) : Prop := ∃ (c : N)
  (F : N × unitInterval → N), ContMDiff (I.prod (𝓡∂ 1)) I ∞ F ∧
  (∀ x, F (x, 0) = c) ∧ ∀ x, F (x, 1) = x`; it implies `Nonempty N`.
  `IsSmoothlyContractible.of_diffeomorph` (transport), and
  `Convex.isSmoothlyContractible` for a nonempty open convex subset of a
  normed space, by straight lines, with its corollary for an open subset of
  `M` carried by a chart or a partial diffeomorphism onto such a set.
  `isSmoothlyContractible_def` states the body.
  Both come from `IsSmoothlyContractible.of_starConvex_image`, for a nonempty
  open `U` and a map `φ : M → E'` to any real normed space, smooth on `U`,
  with a left inverse on `U`
  smooth on the star-convex set `φ '' U`, which covers a partial
  diffeomorphism directly; its other cases are
  `StarConvex.isSmoothlyContractible` (an open set of the model with
  star-convex image under `I`) and
  `IsSmoothlyContractible.of_starConvex_image_extChartAt` (a chart).
- `SymplecticGeometry.IsFiniteGoodCover (I) {ι : Type*} [Finite ι]
  (U : ι → Opens M) : Prop := (⨆ i, U i) = ⊤ ∧ ∀ s : Finset ι, s.Nonempty →
  ((⨅ i ∈ s, U i : Opens M) : Set M).Nonempty →
  IsSmoothlyContractible I (⨅ i ∈ s, U i : Opens M)`, with
  `isFiniteGoodCover_def` and the eliminators `IsFiniteGoodCover.iSup_eq_top`
  and `IsFiniteGoodCover.isSmoothlyContractible`.
- `SymplecticGeometry.HasFiniteGoodCover (I) (M) : Prop := ∃ (n : ℕ)
  (U : Fin n → Opens M), IsFiniteGoodCover I U`, with `hasFiniteGoodCover_def`,
  and
  `IsFiniteGoodCover.hasFiniteGoodCover` for any finite index type, through
  `IsFiniteGoodCover.comp_equiv` (reindexing).
- `IsSmoothlyContractible.hasFiniteGoodCover` (one set is a good cover), as
  the example of the predicate.

### `Geometry/Manifold/LocalDiffeomorph/Basic.lean`

- `IsLocalDiffeomorphAt.exists_partialDiffeomorph`: a local diffeomorphism
  at `x` agrees with a partial diffeomorphism on a source containing `x`,
  since Mathlib does not expose the body of `IsLocalDiffeomorphAt`; used by
  `Immersion/TangentProjection.lean`.
- `IsLocalDiffeomorphAt.congr_of_eventuallyEq`: a map that agrees near `x`
  with a local diffeomorphism at `x` is one too; and
  `PartialDiffeomorph.isLocalDiffeomorphAt_symm_comp_comp_model`: a partial
  diffeomorphism `Θ` between the model vector spaces of `I` and `J` that, on
  its source, maps exactly the points of `range I` into `range J` gives the
  local diffeomorphism `J.symm ∘ Θ ∘ I` at each point that `I` sends into its
  source. Both are used by `Boundary/Collar/Flow/Local.lean` of *Liouville
  structures*.

### `Analysis/Calculus/TangentGraphChart.lean`

Named like Tau Ceti's file.

- `ContDiffOn.exists_uniform_inverse_starProjection`: the graph coordinates
  of a smooth map over its tangent spaces, chosen uniformly in the base point
  near a point `w₀` where its derivative is injective, with derivative bounds of every order; used by
  `Immersion/TangentProjection.lean`.

### `Geometry/Manifold/MFDeriv/Chart.lean`

Differentials of maps into normed spaces read in an extended chart not
centred at the point, used by `Immersion/TangentProjection.lean`: the
`mvfderiv` and off-centre forms of Tau Ceti's
`TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt` and
`TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`.

- `ContMDiff.contDiffOn_mpullbackWithin_extChartAt_symm`: a `C^m` vector
  field on a `C^n` manifold, `m + 1 ≤ n`, read in an extended chart, is
  `C^m` on the chart's target; and
  `VectorField.mfderivWithin_extChartAt_symm_mpullbackWithin`: the derivative
  of the inverse chart sends that expression back to the field. Both are used
  by `Boundary/Collar/Flow/Local.lean` of *Liouville structures*.

### `Geometry/Manifold/Immersion/TangentProjection.lean`

The local graph charts of a compact manifold in a Euclidean space [Weil1952,
§1, pp. 120–122]. For a boundaryless `M`, a smooth `e : M → F` into a real
inner product space (such as `EuclideanSpace ℝ (Fin N)`) with injective
derivatives, and $x\in M$, let $P_x$ be the orthogonal projection onto the
range of `mvfderiv I e x`.

- `SymplecticGeometry.tangentProjectionChart`: near each `x`, the map
  $z\mapsto P_x(e(z)-e(x))$, as a partial diffeomorphism from a neighbourhood
  of `x` onto an open subset of that range, by the inverse function theorem.
- `exists_uniform_tangentProjectionChart` for compact `M` and an injective
  `e`: one radius $r>0$ and one bound for each order such that, for every `x`,
  some partial diffeomorphism given by $z\mapsto P_x(e(z)-e(x))$ on its source
  is defined on $\{z:\|e(z)-e(x)\|<r\}$, reaches the ball of radius $r$ about
  $0$, and has an inverse whose composite with `e` has derivatives of every
  order bounded on its target. It is not `tangentProjectionChart`, whose
  source is a choice.

### `Analysis/Convex/Deriv.lean`

Strict convexity from second derivatives, used by `GoodCover/Compact.lean`:
`strictConvexOn_of_deriv2_add_smul_pos` (along segments, in a real topological
vector space) and `ContDiffOn.strictConvexOn_norm_sub_sq` (the squared distance
`u ↦ ‖ψ u - c‖ ^ 2` for a `C²` map `ψ`).

### `Geometry/Manifold/DeRham/GoodCover/Compact.lean`

- `strictConvexOn_dist_sq_tangentProjectionChart`: for `r` small enough, in
  the chart at `x`, each function $u\mapsto\|e(\varphi_x^{-1}u)-e(y)\|^2$, for
  $\|e(y)-e(x)\|<r$, is strictly convex on a convex neighbourhood of the
  image of the ball (its second derivative is $2\,\mathrm{id}$ up to a term
  bounded by $\|e(\varphi_x^{-1}u)-e(y)\|$ times the bound above on second
  derivatives).
- `hasFiniteGoodCover_of_compactSpace [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [FiniteDimensional ℝ E] [IsManifold I ∞ M] :
  HasFiniteGoodCover I M`: cover $M$ by finitely many sets
  $e^{-1}B(e(x_i),\rho)$ with $\rho$ small against $r$; a nonempty
  intersection of some of them lies in the chart at its first centre, where
  it is the intersection of sublevel sets of convex functions, so it is
  carried onto a convex open set and is smoothly contractible. The embedding
  is Mathlib's `exists_embedding_euclidean_of_compact`.

### `Geometry/Manifold/DeRham/Map.lean`

- `TauCeti.SmoothForm.mpullback_mem_closedForms (f : M → M') (hf : ContMDiff I I' ∞ f)
  (hφ : φ ∈ closedForms I' M' k) : SmoothForm.mpullback f hf φ ∈ closedForms I M k`,
  the membership form of Tau Ceti's `closedForms.mpullback`. `SmoothFamily/Basic.lean`,
  `SmoothFamily/MayerVietoris.lean`,
  *Hamiltonian flows*' `DeRham/FamilyPrimitive.lean` and *Isotopy extension*'s
  `Cohomological/Primitive.lean` import it.

### `Geometry/Manifold/DeRham/SmoothFamily/Basic.lean`

For `[IsManifold I ∞ M]`:

- `SymplecticGeometry.SmoothCohomologySplitting (I) (M)`, a structure with
  fields
  - `space (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k)`, with
    `space_le_closedForms` and `finiteDimensional_space`;
  - `proj (k : ℕ) : closedForms I M k →ₗ[ℝ] SmoothForm I M ℝ k`, with
    `proj_mem : proj k z ∈ space k` and `proj_zero : (proj 0 z) = z` (in
    degree zero $S^0=Z^0$ and $p=\mathrm{id}$);
  - `primitive (k : ℕ) : closedForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k`,
    with `mextDerivₗ_primitive : mextDerivₗ I k (primitive k z) = z -
    proj (k + 1) z` (the identity $z=p(z)+d\,h(z)$, degree by degree, so that
    $\Omega^{-1}$ never occurs);
  - `eq_zero_of_mem_exactForms : s ∈ space k → s ∈ exactForms I M k → s = 0`;
  - `preservesSmoothFamilies_proj` and `preservesSmoothFamilies_primitive`.
- From a splitting `σ`: `σ.mk_proj` (`proj` keeps the class), `σ.spaceEquiv
  k : σ.space k ≃ₗ[ℝ] deRhamCohomology I M k` (the class map is bijective),
  `σ.proj_eq_zero_iff` (`proj k z = 0` exactly when `z` is exact),
  `σ.finiteDimensional_deRhamCohomology`, `σ.exactPrimitive k :
  exactForms I M (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k` with
  `mextDerivₗ_exactPrimitive` and `preservesSmoothFamilies_exactPrimitive`,
  and `σ.contMDiff_repr_mk`: for a basis `b` of `deRhamCohomology I M k` and a
  smooth family `z` of closed forms, every `t ↦ b.repr (deRhamCohomology.mk I
  k (z t)) i` is smooth on `unitInterval`, through `spaceEquiv` and
  `preservesSmoothFamilies_iff_contMDiff_repr`.

### `Geometry/Manifold/DeRham/SmoothFamily/Contractible.lean`

- `nonempty_smoothCohomologySplitting_of_isSmoothlyContractible
  (h : IsSmoothlyContractible I N) : Nonempty (SmoothCohomologySplitting I N)`:
  in degree zero the closed forms are the constants (a closed 0-form is
  constant along the contraction, by `mem_closedForms_zero_iff`), a space of
  dimension one; in positive degree `space = ⊥`, `proj = 0` and `primitive`
  is $z\mapsto h(F^*z)$, which takes smooth families to smooth families by
  `preservesSmoothFamilies_homotopyOperator_mpullback`.

### `Geometry/Manifold/DeRham/MayerVietoris.lean`

The linear tools of `SmoothFamily/MayerVietoris.lean` that do not involve smooth families:
`TauCeti.SmoothForm.glueₗ` (linear maps into the forms on `U` and on `V` that agree on `U ⊓ V`
glue to one into the forms on `U ⊔ V`), the cut-off functions
`SymplecticGeometry.MayerVietorisCutoff I U V` with `MayerVietorisCutoff.nonempty`, the cut-off
extensions `extendLeft` and `extendRight`, and the connecting form `connecting`.

### `Geometry/Manifold/DeRham/SmoothFamily/Cutoff.lean`

`MayerVietorisCutoff.isSmoothFamily_extendLeft` and `isSmoothFamily_extendRight`: the cut-off
extensions take smooth families to smooth families. A file of its own keeps
`MayerVietoris.lean` within its limit.

### `Geometry/Manifold/DeRham/SmoothFamily/MayerVietoris.lean`

For `[FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]` (the
hypotheses of Tau Ceti's Mayer–Vietoris sequence) and `U V : Opens M`:

- `nonempty_smoothCohomologySplitting_sup`: splittings on `U`, `V` and
  `U ⊓ V` give one on `U ⊔ V`. The construction is the auxiliary page's
  inductive step: first a correction by finitely many fixed closed forms
  that makes the restrictions to `U` and `V` exact, then a correction by
  finitely many fixed pairs that makes the class of the discrepancy on
  `U ⊓ V` lie in a fixed complement, then gluing with smooth functions
  $\rho_U,\rho_V$ summing to one on `U ⊔ V`; and the proof that the new space maps
  isomorphically onto cohomology. Degree zero is the injection of
  `SmoothForm.injective_mayerVietoris`, which keeps `closedForms 0`
  finite-dimensional. Each map is built from restrictions, `funSMulₗ` with
  extension by zero, `mextDerivₗ`, gluing (`SmoothForm.exact_mayerVietoris`),
  the maps of the three splittings and finite linear combinations of fixed
  forms with coefficients read off finite-dimensional spaces, so the closure
  lemmas of `SmoothFamily/Map.lean` give `PreservesSmoothFamilies`.
  The steps are public lemmas named after what they construct, so that the
  file stays within its limit.

### `Geometry/Manifold/DeRham/SmoothFamily/GoodCover.lean`

For `[FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
[SigmaCompactSpace M]`:

- `IsFiniteGoodCover.nonempty_smoothCohomologySplitting (hU : IsFiniteGoodCover
  I U) : Nonempty (SmoothCohomologySplitting I M)`, and the same from
  `HasFiniteGoodCover I M`: (★), by the strong induction of *Decisions*, the
  base case from `Contractible.lean`, the empty union by the zero splitting
  (a lemma `nonempty_smoothCohomologySplitting_of_isEmpty`), and transport
  from the open `⊤` to `M`.
- The milestone: `exists_primitiveMap_of_hasFiniteGoodCover
  (hM : HasFiniteGoodCover I M) (k : ℕ) : ∃ P : exactForms I M (k + 1) →ₗ[ℝ]
  SmoothForm I M ℝ k, (∀ η, mextDerivₗ I k (P η) = η) ∧
  PreservesSmoothFamilies P`. Its docstring ends with "Milestone: *Smooth
  families of primitives*." The page's degree $k\ge1$ of the exact forms is
  `k + 1` here.
- Its reading for one family: `exists_isSmoothFamily_mextDerivₗ_eq
  (hM : HasFiniteGoodCover I M) {η : unitInterval → SmoothForm I M ℝ (k + 1)}
  (hη : IsSmoothFamily (𝓡∂ 1) η) (hex : ∀ t, η t ∈ exactForms I M (k + 1)) :
  ∃ α : unitInterval → SmoothForm I M ℝ k, IsSmoothFamily (𝓡∂ 1) α ∧
  ∀ t, mextDerivₗ I k (α t) = η t`.
- `finiteDimensional_deRhamCohomology_of_hasFiniteGoodCover`, the smooth
  cohomology coordinates `contMDiff_repr_mk_of_hasFiniteGoodCover`, and, on a
  compact boundaryless manifold, the instance `FiniteDimensional ℝ
  (deRhamCohomology I M k)`, through `hasFiniteGoodCover_of_compactSpace`.

### `Geometry/Diffeomorphism/Diffeotopy/Real.lean`

In `TauCeti.Diffeotopy`, for `[FiniteDimensional ℝ E] [IsManifold I ∞ M]`
and, where the inverse function theorem is used, `[BoundarylessManifold I M]`.

Below, `∂ₜ` at `(x, t)` is the tangent vector
`((0 : E), (1 : TangentSpace (𝓡∂ 1) t))` of `M × unitInterval`, as in
*Decisions*.

- Joint smoothness of inverses, over any finite-dimensional boundaryless
  parameter manifold `P` (model `J`) and for any `1 ≤ n`, in Mathlib's
  namespace `Diffeomorph`, as it is about Mathlib's notion, and in
  `Geometry/Manifold/Diffeomorph/Family.lean`, as it uses no diffeotopy:
  `Diffeomorph.contMDiff_symm_eval {ψ : P → M ≃ₘ^n⟮I, I⟯ M} (hn : 1 ≤ n)
  (hψ : ContMDiff (J.prod I) I n (fun p : P × M ↦ ψ p.1 p.2)) :
  ContMDiff (J.prod I) I n (fun p : P × M ↦ (ψ p.1).symm p.2)`, named like
  Tau Ceti's `TauCeti.continuous_equiv_symm_eval`, by
  `isLocalDiffeomorphAt_of_injective_mfderiv` and `diffeomorphOfBijective`
  applied to `(p, x) ↦ (p, ψ p x)`; this is the hypothesis `hφ'` of Tau Ceti's
  `forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`.
- Restriction: `ofReal (ψ : ℝ → M ≃ₘ⟮I, I⟯ M) (hψ : …) (h₀ : ∀ x, ψ 0 x = x) :
  Diffeotopy I ∞ M`, with `ofReal_apply`, `toDiffeomorph_symm_ofReal_apply`,
  `symm_ofReal_apply`, `timeSlice_ofReal`, `final_ofReal` and
  `mfderiv_cylinderMap_ofReal (x : M) (t : unitInterval) : mfderiv
  (I.prod (𝓡∂ 1)) I (ofReal ψ hψ h₀).cylinderMap (x, t) ∂ₜ =
  TauCeti.eulerianField I (fun u ↦ (ψ u).toEquiv) t (ψ t x)`.
- Flows: `timeDependentFlowDiffeotopy_eq_ofReal` (for `n = ∞`, the restriction
  of `fun t ↦ timeDependentFlowDiffeomorph hc le_top hX 0 t`, jointly smooth
  by `TauCeti.contMDiff_timeDependentFlowDiffeomorph`, in
  `Geometry/Manifold/Flow/TimeDependent.lean`). The velocity
  of the flow diffeotopy is `velocity_timeDependentFlowDiffeotopy` of
  *Hamiltonian flows*, and is not stated here.
- The reading over `ℝ`: writing `s u` for `Real.smoothTransitionUnit u :=
  ⟨Real.smoothTransition u, _, _⟩ : unitInterval`, with
  `Real.coe_smoothTransitionUnit`, `Real.smoothTransitionUnit_of_nonpos`,
  `Real.smoothTransitionUnit_of_one_le`, `Real.contMDiff_smoothTransitionUnit` and
  `Real.mfderiv_smoothTransitionUnit_one` (all in `Geometry/Manifold/SmoothTransition.lean`, which imports, of
  the library, only `Geometry/Manifold/Instances/Icc.lean` of *Hamiltonian flows*),
  `smoothTransitionFamily (Φ : Diffeotopy I ∞ M)
  (t : ℝ) : M ≃ₘ⟮I, I⟯ M := Φ.timeSlice (s t)`,
  with `smoothTransitionFamily_def`, `smoothTransitionFamily_apply`,
  `smoothTransitionFamily_of_nonpos`
  (the identity), `smoothTransitionFamily_of_one_le` (`Φ.final`),
  `contMDiff_smoothTransitionFamily` and
  `contMDiff_smoothTransitionFamily_symm` (both jointly smooth, by
  `Real.contMDiff_smoothTransitionUnit` and `Φ.symm`, with no inverse function
  theorem), and
  `eulerianField_smoothTransitionFamily_apply (u : ℝ) (x : M) :
  TauCeti.eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u
  (Φ.smoothTransitionFamily u x) = deriv Real.smoothTransition u •
  mfderiv (I.prod (𝓡∂ 1)) I Φ.cylinderMap (x, s u) ∂ₜ`, by
  `eulerianField_apply_apply` and the chain rule through
  `mfderiv_subtypeVal_Icc_one`, as Tau Ceti's
  `SmoothIsotopy/Velocity/Isotopy.lean` differentiates through
  `smoothTransition`. Its form as vector fields,
  `eulerianField_smoothTransitionFamily (u : ℝ) :
  TauCeti.eulerianField I (fun v ↦ (Φ.smoothTransitionFamily v).toEquiv) u =
  ⇑(deriv Real.smoothTransition u • Φ.velocity (s u))`, follows by
  `velocity_apply_apply`. With `Real.smoothTransition.deriv_pos` and
  `deriv_of_neg`, `deriv_of_one_lt`, the consumers (*Hamiltonian flows*)
  pass between conditions on the velocity for all real times and for all
  $t\in[0,1]$.

### `Geometry/Diffeomorphism/Diffeotopy/OfContMDiff.lean`

In `TauCeti.Diffeotopy`, for `[FiniteDimensional ℝ E] [IsManifold I ∞ M]
[BoundarylessManifold I M]`:

- `Diffeomorph.contMDiff_symm_eval_unitInterval {ψ : unitInterval →
  M ≃ₘ⟮I, I⟯ M} (hψ : ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p ↦ ψ p.1 p.2)) :
  ContMDiff ((𝓡∂ 1).prod I) I ∞ (fun p ↦ (ψ p.1).symm p.2)`, in Mathlib's
  namespace `Diffeomorph` as `Diffeomorph.contMDiff_symm_eval` is, by the
  local argument of *Decisions*, with Tau Ceti's
  `HasStrictFDerivAt.jointImplicitFunctionOfProdDomain` for the extended
  chart map and `contDiffOn_seeleyIccExtend`.
- `ofContMDiff (ψ : unitInterval → M ≃ₘ⟮I, I⟯ M) (hψ : …) (h₀ : ∀ x, ψ 0 x =
  x) : Diffeotopy I ∞ M`, with `ofContMDiff_apply` and `timeSlice_ofContMDiff
  : (ofContMDiff ψ hψ h₀).timeSlice t = ψ t`.

## What the part uses

- From Tau Ceti and Mathlib: everything listed under *What exists*.
- From other parts: `TauCeti.Diffeotopy.mfderiv_cylinderMap_time` and
  `TauCeti.Diffeotopy.velocity` of
  `Diffeotopy/Velocity.lean` of *Hamiltonian flows*, which `Diffeotopy/Real.lean`
  imports publicly for the time derivative and the velocity of a diffeotopy;
  that file is merged and imports no file of this part. The part is at level
  0 of `DESIGN.md`'s build order and stays there. Also `Geometry/Manifold/IsManifold/Basic.lean` of
  *Symplectic neighbourhoods*, whose instance giving `C^(m + 1)` structures
  from `C^∞` ones the merged `DifferentialForm/HomotopyOperator.lean` uses; it
  imports only Mathlib, so the level does not change. And
  `Geometry/Manifold/Instances/Icc.lean` of *Hamiltonian flows*, which
  `SmoothTransition.lean` and `Diffeotopy/Real.lean` import for
  `mdifferentiableAt_subtypeVal_Icc`; it imports only Mathlib, so the level
  does not change.
  And `Geometry/Manifold/VectorBundle/Tangent/Opens.lean` of *Contact geometry*,
  which `Flow/TimeDependent.lean` imports to restrict a time-dependent field to
  an open subset; it imports only Mathlib and Tau Ceti, so the level does not
  change.
- What later parts take: *Hamiltonian flows* uses `Diffeotopy/Real.lean` (for
  `SymplecticIsotopy.lean`) and `ContMDiff/TimeExtension.lean` with
  `timeExtend_eq_zero` (for `Flux/CompactSupport.lean`); *Moser isotopy* uses
  `exists_isSmoothFamily_mextDerivₗ_eq`, `hasFiniteGoodCover_of_compactSpace`,
  `DifferentialForm/TimeExtension.lean` (to pass its primitives to `ℝ × M`),
  `exists_contDiff_eqOn_id_Icc_mem_Ioo` and `ofReal`; *Isotopy extension* uses both `TimeExtension.lean` files and
  the `FiniteDimensional` instance of `SmoothFamily/GoodCover.lean`, and
  `exists_contDiff_eqOn_id_Icc_mem_Ioo` in `Extension.lean`; *Contact geometry* uses both
  `TimeExtension.lean` files and the bridge, in `Family.lean` and
  `Gray.lean`, and `exists_contDiff_eqOn_id_Icc_mem_Ioo` in `Family.lean`.

## Issues

Each is a few hundred lines. The issues on the analysis and on families
can start at once; each issue's blockers come before it.

1. **Seeley coefficients.** `Analysis/Calculus/ContDiff/Seeley/Coefficients.lean`.
2. **Seeley's extension.** `Analysis/Calculus/ContDiff/Seeley/Extension.lean`,
   with `Analysis/Calculus/ContDiff/FTaylorSeries.lean`,
   `Analysis/Normed/Group/FunctionSeries.lean` and
   `Analysis/Sobolev/Trace/Reflection/HalfSpace.lean`. Blocked by 1.
3. **Time extension of maps.** `Geometry/Manifold/ContMDiff/TimeExtension.lean`.
   Blocked by 2.
4. **Smooth families of forms.**
   `Geometry/Manifold/DifferentialForm/SmoothFamily/Basic.lean`.
5. **Linear maps preserving smooth families.**
   `Geometry/Manifold/DifferentialForm/SmoothFamily/Map.lean`. Blocked by 4.
6. **Time extension of forms.**
   `Geometry/Manifold/DifferentialForm/TimeExtension.lean`. Blocked by 3 and 4.
7. **Good covers.** `Geometry/Manifold/DeRham/GoodCover/Basic.lean`.
8. **Tangent projection charts.**
   `Geometry/Manifold/Immersion/TangentProjection.lean` and
   `Geometry/Manifold/MFDeriv/Chart.lean`.
9. **Good covers of compact manifolds.**
   `Geometry/Manifold/DeRham/GoodCover/Compact.lean` and
   `Analysis/Convex/Deriv.lean`. Blocked by 7 and 8.
10. **Splittings and their consequences.**
    `Geometry/Manifold/DeRham/SmoothFamily/Basic.lean`. Blocked by 5.
11. **The homotopy operator on families, and contractible manifolds.**
    `Geometry/Manifold/DifferentialForm/HomotopyOperator.lean`,
    `Geometry/Manifold/DifferentialForm/SmoothFamily/HomotopyOperator.lean`,
    `Geometry/Manifold/DifferentialForm/Pullback/Smooth.lean`,
    `Geometry/Manifold/DeRham/DegreeZero.lean` and
    `Geometry/Manifold/DeRham/SmoothFamily/Contractible.lean`. Blocked by 7
    and 10.
12. **The Mayer–Vietoris step.**
    `Geometry/Manifold/DeRham/SmoothFamily/MayerVietoris.lean`,
    `Geometry/Manifold/DeRham/SmoothFamily/Cutoff.lean` and
    `Geometry/Manifold/DeRham/MayerVietoris.lean`. Blocked by 10.
    It is the largest issue; if it exceeds the size limit, the proof that the
    new space maps isomorphically onto cohomology (step 4) becomes an issue
    of its own after the construction.
13. **(★) and the milestone.**
    `Geometry/Manifold/DeRham/SmoothFamily/GoodCover.lean`. Blocked by 9, 11
    and 12.
14. **Isotopies over `ℝ` and diffeotopies.**
    `Analysis/SpecialFunctions/SmoothTransition.lean`,
    `Geometry/Manifold/SmoothTransition.lean`,
    `Geometry/Manifold/Diffeomorph/Family.lean`,
    `Geometry/Manifold/Flow/TimeDependent.lean` and
    `Geometry/Diffeomorphism/Diffeotopy/Real.lean`.
15. **Diffeotopies from families of diffeomorphisms.**
    `Geometry/Diffeomorphism/Diffeotopy/OfContMDiff.lean`. Blocked by 2 and 14
    (for `ofReal`, which `ofContMDiff_eq_ofReal` uses).
16. **A reparametrization equal to the identity on an interval.**
    `exists_contDiff_eqOn_id_Icc_mem_Ioo` in
    `Analysis/SpecialFunctions/SmoothTransition.lean`. Blocked by 14, which
    creates the file. It is much smaller than the others.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Theorem 3.2.4, p. 111.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982],
  §§2–5 (Mayer–Vietoris arguments over good covers).
* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1, pp. 120–122 (convex
  covers), §2, p. 124 (the homotopy operator of a contraction).
* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626 (cited in full, as the plan's
  `references.bib` does not list it).
