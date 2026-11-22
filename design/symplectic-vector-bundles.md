# Design: Symplectic vector bundles

This is the detailed design of part 12 of `DESIGN.md`, *Symplectic vector
bundles*. It fixes the files of the part, its definitions with their
representation and API, the Lean names and statements of its main results,
what it takes from Tau Ceti, Mathlib and the other parts, and the issues that
build it, in an order in which they can be done. It settles the three
questions that `DESIGN.md` leaves to it: the details of
`ContMDiffComplexStructure` and of its subtypes, the form of the spaces of
sections and of the frame covers their topologies use, and the surface
topology that the last milestone needs. It also plans, on the types defined
here, the constructions that part 12 of `DESIGN.md` lists for *First Chern
number* (pull-backs, direct sums, the tangent bundle of a surface with an
area form, Hermitian bundles and their circle bundles), together with the
symplectic isomorphisms and frames in which they are stated.

The mathematics is McDuff–Salamon [McDuffSalamon2017], §2.6: Theorem 2.6.3
and Exercise 2.6.2 (first milestone), Proposition 2.6.4 (second milestone)
and Proposition 2.6.7 (third milestone). All Tau Ceti and Mathlib names below
were checked against the pinned versions (Tau Ceti `v4.37.0-rc1`). Tau Ceti
paths are relative to `.lake/packages/TauCeti/TauCeti/`, and the library's
paths to `SymplecticGeometry/`.

## Setting and conventions

Throughout, the base is a smooth manifold `M`, possibly with boundary or
corners, and `V` is a smooth real vector bundle over it:

```lean
variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace M] [ChartedSpace HB M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
```

- **Regularity.** The bundle and the base are smooth; the structures on the
  bundle have a regularity `n : ℕ∞`, as in Tau Ceti's
  `TauCeti.ContMDiffAlmostComplexStructure I n M`. Every result is stated for
  every `n`; the milestones' two cases are `n = 0` (continuous structures,
  compact-open $C^0$ topology) and `n = ⊤` (smooth structures, compact-open
  $C^\infty$ topology). A regularity `n : ℕ∞` enters section spaces through
  its cast to `WithTop ℕ∞`, and Mathlib's instance for
  `ENat.LEInfty` gives the `ContMDiffVectorBundle n` instances from the smooth
  ones.
- **Regularity of the bundle.** The section types and their transport
  (`ContMDiffComplexStructure`, `ContMDiffTwoForm`, both `pushforward`s,
  `Tames`, `Compatible`) and the constructions below ask of a bundle only
  `[ContMDiffVectorBundle n F V I]`, for the regularity `n` of the structures
  on it, not the `∞` of the display above. The reason is the pull-back:
  along `f : C^n⟮I', N; I, M⟯`, `f *ᵖ V` is a $C^n$ bundle and no more
  (Mathlib's instance `ContMDiffVectorBundle.pullback`), and the Tau Ceti
  lemmas used for transport (`contMDiff_hom_bundle_iff`,
  `ContMDiff.clm_bundle_inverse`, `ContMDiffSection.mapEquiv`,
  `ContMDiffSection.clmComp`) need no more. The topologies, the existence
  results and the milestones keep the smooth bundle of the display.
- **Finite dimension only where used.** Like Tau Ceti's
  `ContMDiffAlmostComplexStructure` and its `frameTopology`, the types of
  this part assume nothing about the dimension of `EB` or `F`, so that the
  comparison with Tau Ceti on $TM$ reaches all of Tau Ceti's type. One
  definition does need finite rank: `IsNondegenerate.polarComplexStructure`
  takes `[FiniteDimensional ℝ F]`, since Tau Ceti's linear
  `SymplecticForm.polarComplexStructure` does
  (`Geometry/Symplectic/PolarCompatible.lean`). Apart from it, a result adds
  `[FiniteDimensional ℝ EB]`, `[FiniteDimensional ℝ F]` or
  `[LocallyCompactSpace EB]` only when its proof needs it:
  - local compactness of `EB`: `frameTopology_eq_of_covers`,
    `continuous_toContMDiffMap` and `continuous_fiberwiseMap`;
  - local compactness of `F`: `continuous_fiberwiseMap`, for Tau Ceti's
    continuity of composition through the total space (see *Continuity of
    fibrewise maps*);
  - finite rank of the source bundle: each use of `contMDiff_bundle_symm`,
    `contMDiff_hom_bundle_iff` or this library's `contMDiff_hom_bundle_symm`
    (the `pushforward`s, the classification, the
    transition maps of symplectic frames and the direct sum of complex
    structures);
  - finite rank of `F`: `isOpen_setOf_nondegenerate`;
    `ContMDiffTwoForm.ofBilinearSection`, whose smoothness comes from Tau
    Ceti's `contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`, and
    `compatibleForm` and the direct sum of forms, both built with it; every
    result that
    uses `polarComplexStructure` (`compatible_polarComplexStructure`,
    `polarComplexStructure_tangentEquiv`, `IsNondegenerate.exists_compatible`,
    `exists_homotopyEquiv_polarComplexStructure`,
    `polarComplexStructure_homotopic` and both milestones);
    `isOpen_polarFormulaDomain`,
    `isOpen_polarEndDomain` (through `isOpen_polarFormulaDomain`),
    `polarFormulaAt` and `polarEndAt` with their lemmas,
    `contMDiffOn_polarFormulaAt` and `contMDiffOn_polarEndAt`, which go
    through an equivalence of `F` with a Euclidean space; each use of Tau
    Ceti's `Tames.isUnit_one_sub_mul` (`Geometry/Symplectic/Cayley/Basic.lean`),
    in the symplectic-to-complex direction of the classification; and
    `Compatible.mem_cayleyPathDomain`, which applies part 9's
    `Compatible.mem_cayleyDomain` in `F` (see *Contractibility and the
    homotopy equivalence*);
  - finite dimension of `EB` and `F`: the existence of bundle metrics, with
    everything that rests on it.
- **No rank hypothesis.** The book takes rank $2n$. No statement here needs
  it: a nondegenerate form or a complex structure forces even rank, and the
  statements are about a given form or structure, or are equivalences between
  spaces that are both empty in odd rank. Rank $0$ is allowed everywhere.
- **Base hypotheses.** Results that need a bundle metric (existence of
  compatible structures) add `[T2Space M]
  [SigmaCompactSpace M]`, the hypotheses of Tau Ceti's
  `nonempty_contMDiffRiemannianMetric`
  (`Geometry/Manifold/VectorBundle/Riemannian/Existence.lean`). Nothing else
  is assumed of `M`; in particular the boundary may be nonempty, as the first
  milestone allows.
- **Signs.** Tameness and compatibility are Tau Ceti's: $\omega(v,Jv)>0$ for
  $v\ne0$, and $J$-invariance. The form attached to a metric and a complex
  structure is $\omega_{g,J}(u,v)=\tfrac12(g(Ju,v)-g(u,Jv))$, which for the
  Euclidean metric and $J_0$ on `StdSpace ι` is `stdForm ι`; its docstring
  says so, and the first issue that defines it proves that case
  (`stdForm_apply_eq_inner_sub_inner`, next to `stdForm_apply_eq_inner`).

## Files

| File | Content | Issues |
|---|---|---|
| `Geometry/Manifold/VectorBundle/ComplexStructure.lean` | `Bundle.ContMDiffComplexStructure`, its API, transport and topology; the comparison with Tau Ceti on $TM$; pull-back, direct sum and multiplication by `Complex.I` | 1, 2, 20 |
| `Geometry/Manifold/VectorBundle/Symplectic/Basic.lean` | `Bundle.ContMDiffTwoForm`, nondegeneracy, transport along bundle isomorphisms, the comparison with `TauCeti.SmoothTwoForm`, the flat form `flat` in the bundle of bilinear forms; symplectic isomorphisms and frames; forms of rank two | 3, 19, 27 |
| `Geometry/Manifold/VectorBundle/Section/Topology.lean` | a section as a $C^n$ map into the total space; continuity of fibrewise maps on section spaces | 4 |
| `Geometry/Manifold/ContMDiffMap/Chart/CodRestrict.lean` | corestriction of $C^n$ maps to an open subset of the target, continuous for the weak Whitney topology | 4 |
| `Geometry/Manifold/ContMDiffMap/Chart/Restriction.lean` | ambient chart derivatives of a function that agrees on an open set `U` with a $C^n$ map on `U`, and their convergence as that map converges in the weak Whitney topology on `U` | 4 |
| `Geometry/Manifold/VectorBundle/Symplectic/ComplexStructure/Basic.lean` | tame and compatible pairs, $\omega_{g,J}$, the metric `Compatible.metric` of a compatible pair, the spaces of forms taming a fixed $J$; $J_{g,\omega}$ and existence; the five lemmas that tie `polarFormulaAt` and `polarEndAt` to these, and the two that tie `flatAt` and `alternatingMapOfBilin` to them | 5, 6, 8, 27 |
| `Geometry/Manifold/VectorBundle/Cayley.lean` | the Cayley path formula in the endomorphism bundle of a vector bundle: smoothness along a base map, and the set `cayleyPathDomain` of the points where the path from a reference endomorphism is defined for every coefficient in $[0,1]$ | 7 |
| `Geometry/Manifold/VectorBundle/Riemannian/PolarEnd.lean` | for a bundle metric `g`, $J_{g,\sigma}$ on the bundle of bilinear forms (`polarFormulaDomain`, `polarFormulaAt` and its smoothness) and $J_{g,\omega_{g,B}}$ on the endomorphism bundle (`compatibleBilinAt`, `polarEndDomain`, `polarEndAt` and its smoothness) | 6, 8 |
| `Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean` | contractibility of the space of bundle metrics | 7 |
| `Geometry/Manifold/VectorBundle/Symplectic/ComplexStructure/Contractible.lean` | contractibility for a fixed form or structure, continuity of $\omega\mapsto J_{g,\omega}$ and $J\mapsto\omega_{g,J}$, the homotopy equivalence, the second milestone | 7, 8, 27 |
| `Geometry/Manifold/VectorBundle/Symplectic/Trivialization.lean` | local Darboux frames and the reduction of the structure group | 9 |
| `Analysis/InnerProductSpace/GramSchmidtOrtho.lean` | Gram–Schmidt turns `u₀, J u₀, u₁, …` into `e₀, J e₀, e₁, …` for a skew-adjoint orthogonal `J` | 9 |
| `Topology/VectorBundle/LinearIndependent.lean` | `Bundle.Trivialization.eventually_linearIndependent`: sections continuous and linearly independent at a point stay independent near it | 9 |
| `Geometry/Manifold/VectorBundle/Symplectic/Classification.lean` | the first milestone | 11 |
| `Geometry/Manifold/VectorBundle/Hom.lean` | `contMDiff_hom_bundle_symm`: the fibrewise inverses of a $C^n$ isomorphism of bundles as a $C^n$ section of the hom bundle; `Bundle.Trivial.contMDiff_comp_mk_iff` (with its `At`, `WithinAt` and `On` forms): $C^n$ maps out of the total space of a trivial bundle read on $M \times W$; `Bundle.Trivial.contMDiff_totalSpaceMk_clm`: a fixed continuous linear map, applied in each fibre, as a $C^n$ map of total spaces of trivial bundles | 1, 3, 25 |
| `Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean` | `contMDiff_compContinuousLinearMap_totalSpace`: precomposition by a $C^n$ hom-bundle section is $C^n$ on total spaces of alternating bundles; `Bundle.flatAt` and `Bundle.alternatingMapOfBilin`, which carry a point of the bundle of alternating maps of two vectors to the bundle of bilinear maps and back, with their smoothness along a map (`contMDiffAt_sectionAlong_flatAt`, `contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear`) | 3, 27 |
| `Geometry/Manifold/VectorBundle/Pullback.lean` | smoothness of sections of the alternating bundle of a pull-back | 18 |
| `Geometry/Manifold/VectorBundle/Prod.lean` | `Bundle.Prod.contMDiff_prodMap` and `Bundle.Prod.contMDiff_swap`: smoothness on total spaces of the fibrewise product of two maps and of the swap, for fibres with only a zero; `Bundle.Prod.contMDiff_prodCongr` and `Bundle.Prod.contMDiff_prodComm`: the same for bundle isomorphisms | 22 |
| `Topology/VectorBundle/Pullback.lean` | coordinates of alternating maps on a pull-back bundle; `Bundle.Pullback.neg_fiber`, `add_fiber`, `sub_fiber`, `smul_fiber`, `neg_pullback`, `add_pullback`, `sub_pullback`, `smul_pullback`, `zero_fiber`, `eq_zero_fiber_iff`, `zero_fiber_eq_iff`, `eq_zero_pullback_iff` and `zero_pullback_eq_iff`: operations and zeros in a fibre of a pull-back bundle, for `simp` | 18, 20 |
| `Topology/VectorBundle/Coordinates.lean` | coordinates of continuous bilinear forms on a vector bundle | 6 |
| `Geometry/Manifold/VectorBundle/BilinearForm.lean` | `SymplecticGeometry.Bundle.mapBilinPairAt`: a map on pairs of continuous bilinear forms on a normed space, applied in each fibre through a family of fibre equivalences; for a map related to one on another model by the equivalences between the models, computation through any equivalence with that model (`mapBilinPairAt_eq_conj`) and, for one $C^n$ on an open set, smoothness along $C^n$ sections (`contMDiffAt_mapBilinPairAt`); `polarFormulaAt` and the fibrewise Moser flow of the classification are built on it | 6, 11 |
| `Data/Bundle.lean` | `Bundle.Pullback.eq_iff`, `eq_fiber_iff`, `neg_apply_fiber` and `neg_apply_pullback`: equations and negated functions in a fibre of a pull-back bundle, for `simp` | 20 |
| `Geometry/Manifold/VectorBundle/Symplectic/Pullback.lean` | pull-backs of forms, of tame and compatible pairs, of isomorphisms and of frames | 21 |
| `Geometry/Manifold/VectorBundle/Symplectic/Prod.lean` | direct sums of forms, of tame and compatible pairs and of isomorphisms; block frames | 22 |
| `Geometry/Symplectic/Manifold/Volume.lean` | the symplectic orientation of a negated two-form | 23 |
| `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean` | `Unitary.continuousLinearMapSelfEquiv`; its case `𝕜 = ℂ` as `Unitary.continuousLinearMapCircleEquiv : unitary (ℂ →L[ℂ] ℂ) ≃ₜ* Circle` | 24, 26 |
| `Analysis/Normed/Operator/SpanSingleton.lean` | `LinearIsometryEquiv.toSpanSingleton`: a unit vector of a line `E` as `𝕜 ≃ₗᵢ[𝕜] E` | 26 |
| `Geometry/Manifold/VectorBundle/Riemannian/Trivial.lean` | constant metrics on trivial bundles, among them `constComplexEuclidean` | 25 |
| `Geometry/Manifold/VectorBundle/Hermitian/Basic.lean` | the symplectic form of a Hermitian bundle | 25 |
| `Geometry/Manifold/VectorBundle/Hermitian/CircleBundle.lean` | the circle bundle of a Hermitian line bundle as a principal `Circle`-bundle, for fibres with their own complex inner products; the smooth side is *First Chern number*'s prerequisite 3 | 26 |
| `Topology/FiberBundle/Basic.lean` | `FiberBundle.isOpen_of_forall_mem_iff_snd_mem`: a set of the total space that each trivialization reads as an open condition on the model fibre is open | 3 |
| `Topology/FiberBundle/ChangeModelFiber.lean` | change of model fibre of a fibre bundle along a homeomorphism | 26 |
| `Topology/FiberBundle/Principal/ChangeGroup.lean` | change of structure group of a principal bundle along `G ≃ₜ* H` | 26 |
| `Geometry/Manifold/IsManifold/InteriorBoundary.lean` | the interior of a manifold with boundary as a boundaryless manifold | 12 |
| `Topology/Connected/Clopen.lean` | preconnectedness of a dense subset from local preconnectedness | 12 |
| `Geometry/Manifold/Boundary/Collar/Push.lean` | pushing a compact manifold with boundary into its interior | 13 |
| `Topology/VectorBundle/ZeroSet.lean` | closedness of the zero set of a continuous section along a map | 14 |
| `Geometry/Manifold/VectorBundle/Section/Generic.lean` | sections with closed discrete zero sets over boundaryless manifolds | 14 |
| `Geometry/Diffeomorphism/Diffeotopy/Discrete.lean` | a diffeotopy whose final map sends a compact set off a closed discrete set | 16 |
| `Geometry/Manifold/VectorBundle/Section/Nonvanishing.lean` | smoothing nowhere-zero sections; nowhere-zero sections over surfaces with boundary | 15, 16 |
| `Geometry/Manifold/VectorBundle/Hermitian/Frame.lean` | appending a normalized orthogonal section to a unitary frame; unitary frame trivializations over any model | 17 |
| `Geometry/Manifold/VectorBundle/Hermitian/Surface.lean` | the third milestone | 17 |

Issue 10 (parametric smoothness of the linear Moser flow) goes where part 10,
*Linear Moser*, puts it (`Analysis/ODE/DysonSeries.lean`, as `DESIGN.md`
says), except its lemma `moserGenerator_conj`, which goes in
`Geometry/Symplectic/LinearMoser.lean`. The files
`Analysis/ODE/DysonSeries.lean`, `Section/Topology.lean`, `Section/Generic.lean`,
`Riemannian/SectionTopology.lean`, `IsManifold/InteriorBoundary.lean`,
`Topology/Connected/Clopen.lean`, `Geometry/Manifold/VectorBundle/Pullback.lean`,
`Geometry/Manifold/VectorBundle/Prod.lean`,
`Topology/VectorBundle/Pullback.lean`,
`Geometry/Symplectic/Manifold/Volume.lean` and the folders `Boundary/Collar/`
and `Geometry/Diffeomorphism/Diffeotopy/` have the names of a Tau Ceti or Mathlib file or
folder at the same place, so that the two merge upstream.

**Departures from `DESIGN.md`.** Each has its reason, and the overview
lists each one: #59, #113, #212 and #218 brought it in line with the
earlier ones, and #276, which planned `CodRestrict.lean`, added that
file to it.

- The overview's `.../Symplectic/ComplexStructure.lean` becomes a folder of
  two files from the start, since its content is more than one file holds.
- The local trivializations move from `Symplectic/Basic.lean` to
  `Symplectic/Trivialization.lean`, a file of their own: the local Darboux
  frames and the reduction of the structure group are a topic apart from
  the definitions in `Basic.lean`.
- `ContMDiffMap/Chart/CodRestrict.lean` is new: it holds a general fact
  about Tau Ceti's weak Whitney topology that the proof of
  `continuous_fiberwiseMap` uses (see *Continuity of fibrewise maps*), and
  sits in the Tau Ceti folder of that topology so that it can merge there.
  `ContMDiffMap/Chart/Restriction.lean` is new for the same reason: it
  holds the chart lemmas that the proof of `continuous_toContMDiffMap`
  uses, and has the path of Tau Ceti's file of the same name, whose lemmas
  it generalizes, so that the two can merge. It came with the code of
  issue 4 (#334).
- Five files are new (`IsManifold/InteriorBoundary.lean`,
  `Topology/Connected/Clopen.lean`, `Boundary/Collar/Push.lean`, `Section/Generic.lean`,
  `Section/Nonvanishing.lean`): they hold the prerequisites of the route to
  the third milestone below, which replaces the book's cutting of the surface.
- `Geometry/Diffeomorphism/Diffeotopy/Discrete.lean` is new: the step of
  issue 16 that moves the zeros of a section off a compact set is a fact
  about diffeotopies of boundaryless manifolds, with no bundle in it. It
  sits in Tau Ceti's diffeotopy folder, in the `TauCeti` namespace of the
  lemma it builds on, so that it can merge there.
- `Topology/VectorBundle/ZeroSet.lean` is new too: the closedness of the
  zero set that `Section/Generic.lean` uses holds for any continuous section
  of a topological vector bundle and needs no smooth structure, so it sits
  with the topological bundles.
- `VectorBundle/Cayley.lean` stands apart from the symplectic files: the
  bundle Cayley lemma and the set `cayleyPathDomain` that the contractibility
  proofs use mention no symplectic notion of this part, only Mathlib's
  endomorphism bundle and Tau Ceti's and part 9's linear Cayley formula
  (and, for one membership lemma, Tau Ceti's linear forms on a fibre).
- The contractibility of bundle metrics sits with Tau Ceti's topology on
  metrics, not in a symplectic file, since it mentions only Mathlib and Tau
  Ceti types.
- `Riemannian/PolarEnd.lean` stands apart from the symplectic files for the
  same reason: $J_{g,\sigma}$ on the bundle of bilinear forms and
  $J_{g,\omega_{g,B}}$ on the endomorphism bundle mention only Mathlib's
  bundle metrics and part 9's linear formula.
- Lemma 2.6.6 of the book (unitary frames along curves), which the overview
  puts in `Hermitian/Surface.lean`, is not planned here: the route below does
  not use it. If *First Chern number* needs it, that part's design plans it.
- The surface of the third milestone is not assumed oriented: the route does
  not use an orientation, so the statement is more general.
- `Topology/VectorBundle/Pullback.lean` is new: the coordinate lemma for
  alternating maps on a pull-back bundle uses no charts, so it sits in a
  topological file, beside Tau Ceti's linear-map lemma in its file of the same
  path. #323 asks the overview to record it.
- `Analysis/Normed/Operator/SpanSingleton.lean` is new, and
  `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean` also holds
  `Unitary.continuousLinearMapCircleEquiv`: the circle bundle uses both, but
  neither mentions a bundle, so each sits with its topic, in Mathlib's
  namespace of its type. They came with the code of issue 26 (#328).
- `Topology/FiberBundle/Principal/ChangeGroup.lean` is new: the change of
  structure group behind the principal `Circle`-bundle of
  `Hermitian/CircleBundle.lean` uses nothing about circles or frames, so it is stated
  for any principal bundle and any `G ≃ₜ* H`, in the Tau Ceti folder of
  principal bundles, so that it can merge there. The step it rests on, reading
  a fibre bundle with another model fibre along a homeomorphism, involves no
  group, so it has its own file, `Topology/FiberBundle/ChangeModelFiber.lean`.
- `Topology/FiberBundle/Basic.lean` is new: the openness argument behind
  `isOpen_setOf_nondegenerate` and `isOpen_polarFormulaDomain` holds for any
  fibrewise condition on any fibre bundle, so it is stated there, in Mathlib's `FiberBundle` namespace, as
  `FiberBundle.isOpen_of_forall_mem_iff_snd_mem` (#456).
- `Analysis/InnerProductSpace/GramSchmidtOrtho.lean` is new, from
  issue 9: the result that Gram–Schmidt applied to `u₀, J u₀, u₁, J u₁, …` gives
  `e₀, J e₀, e₁, J e₁, …` needs only an inner product space and a skew-adjoint
  orthogonal `J`. It is in Mathlib's namespace `InnerProductSpace`, in a file
  with the name of Mathlib's file of `gramSchmidt`, so that it can merge there.
- `Topology/VectorBundle/LinearIndependent.lean` is new, from issue 9:
  the result that sections independent at a point stay independent near it
  holds for any sections of a topological vector bundle that are continuous there, so it is
  stated there, in Mathlib's namespace `Bundle.Trivialization`, as
  `Bundle.Trivialization.eventually_linearIndependent`.
- `ContMDiffTwoForm.Compatible.metric`, the bundle metric $\omega(\cdot,J\cdot)$
  of a compatible pair, is public, in `Symplectic/ComplexStructure/Basic.lean`
  next to `compatibleForm`, which goes the other way.
- The lemma of `Section/Topology.lean` asks for joint $C^n$ regularity in a
  manifold parameter instead of derivatives continuous in the parameter (see
  below), and issues 6, 7 and 8 wait for part 9: issue 6 for its building
  issues 4 and 5, issue 7 for its building issue 6, and issue 8 for its
  building issues 4, 5 and 6 (see *What the part uses*).

## Complex structures on a bundle

`ComplexStructure.lean`, namespace `SymplecticGeometry.Bundle`.

```lean
structure ContMDiffComplexStructure (I : ModelWithCorners ℝ EB HB) (n : ℕ∞) (F : Type*)
    (V : M → Type*) [...] where
  toEndomorphism : Cₛ^n⟮I; F →L[ℝ] F, fun x ↦ V x →L[ℝ] V x⟯
  square_neg : ∀ x, (toEndomorphism x).comp (toEndomorphism x) = -ContinuousLinearMap.id ℝ (V x)
```

The fields are those of `TauCeti.ContMDiffAlmostComplexStructure`
(`Geometry/Symplectic/Manifold/AlmostComplex/ContMDiff.lean`), with the
tangent bundle replaced by `V`. Its API copies Tau Ceti's for $TM$, name for
name, so that the $TM$ statements are special cases:

- `toEndomorphism_injective`; `CoeFun` to `∀ x, V x →L[ℝ] V x`; `@[ext] ext`
  (from `J x v = K x v`); `@[simp] apply_apply` ($J(Jv)=-v$); `injective`,
  `surjective`;
- `almostComplexStructureAt J x : TauCeti.AlmostComplexStructure (V x)` with
  `almostComplexStructureAt_toLinearMap` and
  `@[simp] almostComplexStructureAt_apply`;
- `toEndomorphism_ne_id` and `not_exists_toEndomorphism_eq_id` (for
  `[Nontrivial F]`, and `[Nonempty M]` for the second);
- `ofLE` (forget regularity) with `@[simp] ofLE_toEndomorphism_apply`,
  `ofLE_apply`, `ofLE_refl`, `ofLE_ofLE`, `ofLE_injective`; `Neg` with
  `neg_apply`, `neg_toEndomorphism`, `neg_neg`, `ofLE_neg`;
- **Example.** `const`: for a complex structure `J₀ : TauCeti.AlmostComplexStructure W`
  on a finite-dimensional normed space `W` (so that `J₀` is continuous), the
  constant structure on the trivial bundle `Bundle.Trivial M W`, with
  `@[simp] const_toEndomorphism_apply`; in particular the standard one on
  `Bundle.Trivial M (StdSpace ι)`;
- **Transport.** For a fibrewise equivalence `Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x`
  whose map of total spaces is $C^n$, `pushforward Φ hΦ J :
  ContMDiffComplexStructure I n F₂ V₂`, the structure $\Phi J\Phi^{-1}$, with
  `@[simp] pushforward_apply`, `pushforward_refl` and `pushforward_trans`.
  Its section is `Φₛ.clmComp (J.toEndomorphism.clmComp Φ⁻¹ₛ)`, by Tau
  Ceti's `ContMDiffSection.clmComp` with `@[simp] clmComp_apply`
  (`Geometry/Manifold/VectorBundle/Hom.lean`). Here `Φₛ` and `Φ⁻¹ₛ` are the
  $C^n$ sections of the hom bundles from `V₁` to `V₂` and back. Tau Ceti's
  `contMDiff_hom_bundle_iff` (same file) gives `Φₛ` from `hΦ`, and needs
  only `[FiniteDimensional ℝ F₁]`. Then `Φ⁻¹ₛ` is the fibrewise inverse of
  `Φₛ`, given by `contMDiff_hom_bundle_symm` (this library's
  `Geometry/Manifold/VectorBundle/Hom.lean`, root namespace, shared with the
  two-form `pushforward`); its proof applies Tau Ceti's
  `ContMDiff.clm_bundle_inverse` to `Φₛ` and rewrites with Mathlib's
  `ContinuousLinearMap.inverse_equiv`.
  So `F₂` may have any dimension, as for the two-form `pushforward`; nothing
  about sections is rebuilt;
- `toContinuousComplexStructure : ContMDiffComplexStructure I n F V →
  TauCeti.Bundle.ContinuousComplexStructure F V`
  (`Topology/VectorBundle/Complex/Structure.lean`) with
  `toContinuousComplexStructure_apply` and
  `toContinuousComplexStructure_almostComplexStructureAt`. Its `Fiber` is the
  complex vector bundle that the first milestone's title refers to. For
  `n = 0` it is an equivalence, `continuousEquiv : ContMDiffComplexStructure
  I 0 F V ≃ TauCeti.Bundle.ContinuousComplexStructure F V` (by
  `contMDiff_zero_iff`), so no parallel $C^0$ type arises.

**Topology.** As for `TauCeti.SmoothAlmostComplexStructure.frameTopology`
(`Geometry/Symplectic/Manifold/AlmostComplex/Topology.lean`), the topology is
explicit data, not an instance:

```lean
variable {ι : Type*}
  (e : ι → Trivialization (F →L[ℝ] F) (π (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

def frameTopology : TopologicalSpace (ContMDiffComplexStructure I n F V) :=
  .induced toEndomorphism (ContMDiffSection.frameTopology (I := I) (n := n) e U hU)
```

with `isEmbedding_toEndomorphism_frameTopology`,
`continuous_frameTopology_iff`, `tendsto_frameTopology_iff`,
`continuous_toEndomorphism_apply_frameTopology`,
`isClosedEmbedding_toEndomorphism_frameTopology`, `t2Space_frameTopology`
(the last three for a covering family, `hcover : ∀ x, ∃ i, x ∈ U i`),
`frameTopology_eq_of_covers` and `continuous_neg_frameTopology`, each proved
as Tau Ceti proves it for $TM$.

**The tangent bundle.** For `V = TangentSpace I` (so `F = EB`):

- `tangentEquiv : ContMDiffComplexStructure I n EB (TangentSpace I) ≃
  TauCeti.ContMDiffAlmostComplexStructure I n M`, the identity on the two
  fields, with `tangentEquiv_apply` and
  `toContinuousComplexStructure_tangentEquiv`: composing with Tau Ceti's
  `ContMDiffAlmostComplexStructure.toContinuousComplexStructure`
  (`.../AlmostComplex/ComplexTangentBundle.lean`) gives this file's
  `toContinuousComplexStructure`;
- `tangentHomeomorph`: for `n = ⊤`, `tangentEquiv` followed by
  `ContMDiffAlmostComplexStructure.smoothEquiv`, a homeomorphism from
  `frameTopology e U hU` to `SmoothAlmostComplexStructure.frameTopology e U hU`
  for the same frames.

## Two-forms on a bundle

`Symplectic/Basic.lean`, namespace `SymplecticGeometry.Bundle`.

```lean
abbrev ContMDiffTwoForm (I) (n : ℕ∞) (F) (V) :=
  Cₛ^n⟮I; F [⋀^Fin 2]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin 2]→L[ℝ] Bundle.Trivial M ℝ x⟯
```

a $C^n$ section of Mathlib's bundle of alternating maps
(`ContMDiffVectorBundle.continuousAlternatingMap`), for $E=TM$ the bundle in
which the sections `TauCeti.SmoothForm.toContMDiffSection` of Tau Ceti's
smooth two-forms take their values. Tau Ceti's `SmoothTwoForm I M` is not
such a section: it is `SmoothForm I M ℝ 2`, a subtype of a submodule of all
forms (`Geometry/Manifold/TwoForm/Basic.lean`,
`Geometry/Manifold/DifferentialForm/Smooth.lean`). Here the type is an
`abbrev` of the section type, so that the module structure and
`frameTopology` of `ContMDiffSection` apply to it unchanged. Symplectic forms are not a new type
but the predicate below, as in Tau Ceti for $TM$.

- `bilinFormAt ω x : LinearMap.BilinForm ℝ (V x)`, with `@[simp]
  bilinFormAt_apply : ω.bilinFormAt x v w = ω x ![v, w]`, `isAlt_bilinFormAt`,
  and the `map_add`/`map_smul` lemmas (`bilinFormAt_add`, `bilinFormAt_smul`).
- `flat ω x : V x →L[ℝ] V x →L[ℝ] ℝ`, the same form as a point of Mathlib's
  bundle of continuous bilinear forms, with `@[simp] flat_apply :
  ω.flat x v w = ω x ![v, w]` and `toBilinForm_flat :
  (ω.flat x).toBilinForm = ω.bilinFormAt x`, as Tau Ceti's
  `SmoothTwoForm.flat` (`Geometry/Symplectic/Manifold/Flat.lean`) on $TM$.
  The fibres carry no norm, so Tau Ceti's `ContinuousAlternatingMap.flatL`
  cannot be applied to `ω x` itself: `flat` is `flatL ℝ F ℝ` of `ω x` read
  through the fibre equivalence of `trivializationAt F V x`, carried back by
  the same equivalence (`ContinuousLinearEquiv.bilinearCongr`); `flat_apply`
  hides that choice. `contMDiff_flat`: the map
  `x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (ω.flat x)` is
  `ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n`, by the proof of Tau
  Ceti's `contMDiffAt_sectionAlong_flatL` with `TangentSpace I` replaced by
  `V` (`contMDiffAt_hom_bundle`, `contMDiffAt_continuousAlternatingMap_bundle`,
  `inCoordinates_apply_eq₂`). This is the input of the smoothness of
  $J_{g,\omega}$ below. Issue 27 moves that body to a point of the
  alternating bundle, `Bundle.flatAt F (ω x)` (see *Continuity of
  $\omega\mapsto J_{g,\omega}$ and $J\mapsto\omega_{g,J}$*), so that `flat`
  gets `flat_def : ω.flat x = Bundle.flatAt F (ω x)`, and `contMDiff_flat`
  becomes the case `b = id` of `contMDiffAt_sectionAlong_flatAt`; the statements of `flat`,
  `flat_apply` and `contMDiff_flat` do not change.
- `IsNondegenerate ω : Prop := ∀ x, (ω.bilinFormAt x).Nondegenerate`, with
  the unfolding lemmas of Tau Ceti's `Geometry/Symplectic/Manifold/TwoForm.lean`,
  `isNondegenerate_iff_separatingLeft` and
  `isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot`, `IsNondegenerate.neg`,
  `IsNondegenerate.nondegenerate_bilinFormAt`, and
  `IsNondegenerate.symplecticFormAt : TauCeti.SymplecticForm (V x)` with
  `@[simp] symplecticFormAt_apply`.
- `isOpen_setOf_nondegenerate`: the fibrewise nondegenerate forms are an open
  subset of the total space of the alternating bundle (used by issue 4's
  lemma; nondegeneracy is not an open condition on sections over a
  noncompact base). It follows from
  `FiberBundle.isOpen_of_forall_mem_iff_snd_mem`
  (`Topology/FiberBundle/Basic.lean`): a trivialization turns a form into
  its pull-back by a linear equivalence, which keeps nondegeneracy.
- **Example.** `const`: on the trivial bundle `Bundle.Trivial M W`, the
  constant section of a symplectic form on `W`, with `@[simp] const_apply`
  and `isNondegenerate_const`; in particular `stdForm ι` on
  `Bundle.Trivial M (StdSpace ι)`.
- **Transport.** For fibrewise equivalences `Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x` whose
  map of total spaces is $C^n$ (`[FiniteDimensional ℝ F₁]`),
  `pushforward Φ hΦ : ContMDiffTwoForm I n F₁ V₁ ≃ₗ[ℝ] ContMDiffTwoForm I n F₂ V₂`
  with `@[simp] pushforward_apply` ($\omega(\Phi^{-1}u,\Phi^{-1}v)$),
  `pushforward_refl`, `pushforward_trans` and `IsNondegenerate.pushforward`.
  It is Tau Ceti's `ContMDiffSection.mapEquiv`
  (`Geometry/Manifold/VectorBundle/Section/Map.lean`) for the fibrewise map
  $\omega_x\mapsto\omega_x\circ(\Phi_x^{-1}\times\Phi_x^{-1})$ of the
  alternating bundles. Both that map and its inverse are precompositions by
  a $C^n$ section of a hom bundle, so they are $C^n$ on total spaces by
  `contMDiff_compContinuousLinearMap_totalSpace` (this library's
  `Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean`, root
  namespace, any arity and coefficient bundle). For the map the section is
  $x\mapsto\Phi_x^{-1}$, given by `contMDiff_hom_bundle_symm` (this
  library's `Geometry/Manifold/VectorBundle/Hom.lean`, root namespace, shared
  with the transport of complex structures); for its inverse it is
  $x\mapsto\Phi_x$, given by Tau Ceti's `contMDiff_hom_bundle_iff`. Nothing
  about sections is rebuilt.
- **The tangent bundle.** `tangentEquiv : ContMDiffTwoForm I ⊤ EB
  (TangentSpace I) ≃ₗ[ℝ] TauCeti.SmoothTwoForm I M`, built from
  `TauCeti.SmoothForm.ofContMDiffSection` and `SmoothForm.toContMDiffSection`
  (`Geometry/Manifold/DifferentialForm/Smooth.lean`) and their inverse lemmas
  `ofContMDiffSection_toContMDiffSection` and
  `toContMDiffSection_ofContMDiffSection`, with `@[simp] tangentEquiv_apply`
  and `tangentEquiv_symm_apply` (both evaluate pointwise to the same
  alternating map) and `isNondegenerate_tangentEquiv_iff`.

## Tame and compatible pairs

`Symplectic/ComplexStructure/Basic.lean`, namespace `SymplecticGeometry.Bundle`.
The predicates follow `TauCeti.SmoothTwoForm.Tames`, `Invariant` and
`Compatible` (`Geometry/Symplectic/Manifold/TwoForm.lean`); the regularities of
the form and of the structure are independent.

- `ContMDiffTwoForm.Tames ω J := ∀ x v, v ≠ 0 → 0 < ω.bilinFormAt x v (J x v)`,
  `Invariant ω J`, `structure Compatible ω J : Prop` (`invariant`, `tames`),
  with the unfolding lemmas `tames_def`, `invariant_def`, `tames_iff`,
  `invariant_iff` and
  `Invariant.apply` ($\omega(Jv,Jw)=\omega(v,w)$), as in Tau Ceti's
  `TwoForm.lean`; `Tames.isNondegenerate`, `Compatible.isNondegenerate`,
  `IsNondegenerate.tames_iff`, `IsNondegenerate.invariant_iff`,
  `IsNondegenerate.compatible_iff` (the pointwise Tau Ceti predicates
  `TauCeti.SymplecticForm.Tames` and `Compatible` on `symplecticFormAt x`
  and `almostComplexStructureAt x`), `Compatible.compatibleAt`; and
  transport along bundle isomorphisms, which moves the form and the structure
  together: `Tames.pushforward`, `Invariant.pushforward` and
  `Compatible.pushforward`, from `ω.Tames J` to
  `(pushforward Φ hΦ ω).Tames (J.pushforward Φ hΦ')`, where `hΦ` and `hΦ'`
  are the smoothness of `Φ` at the regularities of `ω` and of `J`.
- On $TM$, `tames_tangentEquiv_iff`, `invariant_tangentEquiv_iff` and
  `compatible_tangentEquiv_iff`: the predicates agree with Tau Ceti's under
  the two `tangentEquiv`s (followed by `toSmooth` for the structure).
- `convex_setOf_tames J`, `convex_setOf_invariant J` and
  `convex_setOf_compatible J`: in the vector space `ContMDiffTwoForm I n F V`,
  the forms taming (invariant under, compatible with) a fixed `J` form a
  convex set.
- $\omega_{g,J}$: for `g : Bundle.ContMDiffRiemannianMetric I n F V`,
  `ContMDiffComplexStructure.compatibleForm g J : ContMDiffTwoForm I n F V`
  (`[FiniteDimensional ℝ F]`) with `compatibleForm_apply` (the formula above)
  and `compatible_compatibleForm`. It is `ContMDiffTwoForm.ofBilinearSection`
  of the bilinear section `x ↦ compatibleBilinAt g x (J x)`, which is $C^n$ by
  `Bundle.ContMDiffRiemannianMetric.contMDiff_compatibleBilinAt`
  (`Riemannian/PolarEnd.lean`). The constructor
  `ContMDiffTwoForm.ofBilinearSection β hβ` (`[FiniteDimensional ℝ F]`), in
  `Symplectic/Basic.lean` with `ofBilinearSection_apply` and
  `bilinFormAt_ofBilinearSection`, turns a $C^n$ bilinear section `β` with
  `β x v v = 0` into a two-form, by Tau Ceti's
  `contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`. The same issue
  adds `bilinFormAt_pushforward_apply` there, next to
  `bilinFormAt_pushforward`. Issue 27 replaces the private value
  `ofBilinearSectionAt` of `ofBilinearSection` by the public
  `Bundle.alternatingMapOfBilin F (β x) (hβ x)`, which needs only a point of
  the bundle of bilinear forms; `ofBilinearSection` and its lemmas keep their
  statements.
- The metric of a compatible pair: for `hc : ω.Compatible J`,
  `ContMDiffTwoForm.Compatible.metric hc : Bundle.ContMDiffRiemannianMetric I n F V`
  (`[FiniteDimensional ℝ F]`), with `Compatible.metric_inner`
  (`hc.metric.inner x u v = ω.bilinFormAt x u (J x v)`),
  `Compatible.compatibleForm_metric` (`compatibleForm hc.metric J = ω`) and
  `Compatible.symplecticFormAt_apply_apply_eq_metric_inner`, the same on each
  fibre for the linear pair, the hypothesis of Tau Ceti's lemmas on an inner
  product of the form `ω(·, J ·)` (`Geometry/Symplectic/CompatibleMetric.lean`).
- $J_{g,\sigma}$ on the bundle of bilinear forms. Two maps need the
  smoothness of the polar formula: $J_{g,\omega}$ along a nondegenerate
  two-form, and, for the homotopy equivalence below, $J_{g,\omega_{g,B}}$ as
  a function of a point $(x,B)$ of the endomorphism bundle, where `B` need
  not be a complex structure. Both come from one chart argument, made for a
  form `σ` that is a point of Mathlib's bundle
  `fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ` of continuous bilinear forms; each of the
  two maps is that result composed with a smooth map into this bundle. The
  declarations of this bullet and the next one mention only Mathlib's
  bundles, `Bundle.ContMDiffRiemannianMetric` and part 9's `TauCeti`
  operations, so they go in a file of their own,
  `Geometry/Manifold/VectorBundle/Riemannian/PolarEnd.lean`, which imports
  no file of this part but `Topology/VectorBundle/Coordinates.lean`,
  `Geometry/Manifold/VectorBundle/BilinearForm.lean` and
  `Topology/FiberBundle/Basic.lean`, in the namespace `Bundle.ContMDiffRiemannianMetric` (where `g.polarFormulaAt x σ`
  finds them), except `Bundle.polarFormulaDomain` and
  `Bundle.euclideanEquivAt`, which involve no metric. Only the lemmas named
  below as being in `SymplecticGeometry.Bundle` stay in this file. For a metric `g`:
  - `Bundle.polarFormulaDomain F V : Set (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
    fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ)`, the points $(x,\sigma)$ where the skew
    part of `σ` is nondegenerate, with `@[simp] mem_polarFormulaDomain_iff :
    q ∈ polarFormulaDomain F V ↔
    (q.snd.toBilinForm - q.snd.toBilinForm.flip).Nondegenerate`. It is open
    (`isOpen_polarFormulaDomain`, `[FiniteDimensional ℝ F]`), by
    `FiberBundle.isOpen_of_forall_mem_iff_snd_mem` with the open set
    `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm_sub_flip`
    of forms on `F`: over the base set of a trivialization, the reading of
    `q.snd` in it is `q.snd` carried along the fibre equivalence
    (`ContinuousLinearMap.inCoordinates_eq_bilinearCongr`, over any
    `NontriviallyNormedField` and topological base, in
    `Topology/VectorBundle/Coordinates.lean`), and carrying a form along a
    linear equivalence does not change whether its skew part is
    nondegenerate (`ContinuousLinearEquiv.nondegenerate_bilinearCongr_sub_flip_iff`,
    in part 9's `Topology/Algebra/Module/BilinearForm.lean`), so the chart
    of the total space reads the domain as that open set.
  - `polarFormulaAt g x (σ : V x →L[ℝ] V x →L[ℝ] ℝ) : V x →L[ℝ] V x`, part 9's
    `TauCeti.metricPolarFormula` on `W` of the pair (`g x`, `σ`) carried
    along `e x : V x ≃L[ℝ] W` (the trivialization at `x` followed by
    Mathlib's `ContinuousLinearEquiv.ofFinrankEq`, the definition
    `Bundle.euclideanEquivAt F V x` with `euclideanEquivAt_def`), conjugated
    back by `e x`; with `polarFormulaAt_def`. Since `g x` is positive, the
    carried pair lies in `polarDomain W` exactly when `⟨x, σ⟩ ∈ polarFormulaDomain F V`
    (`mem_polarDomain_bilinearCongr`, for any `e : V x ≃L[ℝ] W`).
    `polarFormulaAt_eq_conj`: for `σ` with
    `(σ.toBilinForm - σ.toBilinForm.flip).Nondegenerate`, the same holds for any
    `e' : V x ≃L[ℝ] W'` to an inner product space `W'` with
    `[FiniteDimensional ℝ W']`, which `metricPolarFormula` on `W'` needs, by
    `metricPolarFormula_conj` (applied to `e'` after the inverse of `e x`),
    so the choice of `e x` does not matter.
  - `contMDiffOn_polarFormulaAt`: the map
    `q ↦ TotalSpace.mk' (F →L[ℝ] F) q.proj (polarFormulaAt g q.proj q.snd)` of
    the bundle of bilinear forms to the endomorphism bundle is
    `ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n`
    on `polarFormulaDomain F V`, for `g` of order `n`. Proof: by
    `contMDiffAt_hom_bundle`, at a point over `x₀` it suffices to read the
    map in the trivialization at `x₀`. By `polarFormulaAt_eq_conj` with the
    fibre equivalence of that trivialization followed by `F ≃L[ℝ] W`, the
    reading is conjugation by a constant equivalence of `metricPolarFormula`
    at the readings of `g` and of `q.snd` in the trivialization, carried to
    `W` by a constant equivalence. That pair is $C^n$ in `q`: `g` is $C^n$
    in coordinates, and the reading of `q.snd` is the chart of the total
    space. It lies in `polarDomain W`, so `contDiffOn_metricPolarFormula`
    concludes. This is the argument of Tau Ceti's private
    `contMDiff_polarEnd` (`.../AlmostComplex/Polar.lean`), with the form a
    variable of the total space instead of a fixed section, and part 9's
    public lemma in place of Tau Ceti's private
    `contMDiffAt_metricChangeTransport_mul_mul_sqrt`. It is the only chart
    argument for the polar formula in this part.
  - `exists_continuousLinearEquiv_inner_eq`: for `[FiniteDimensional ℝ F]`,
    some `e : V x ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F))` has
    `⟪e u, e v⟫ = g.inner x u v`. The fibres carry no inner product, so the
    lemmas below that compare with Tau Ceti's linear construction for the
    inner product `g x` read the fibre through such an `e`.
  - In `SymplecticGeometry.Bundle`, two lemmas for
    `hω : ω.IsNondegenerate`. `IsNondegenerate.mk_flat_mem_polarFormulaDomain`:
    `⟨x, ω.flat x⟩ ∈ polarFormulaDomain F V`, by `mem_polarFormulaDomain_iff`
    and `LinearMap.IsAlt.sub_flip_eq_two_smul`: the skew part of the
    alternating form is twice the form.
    `IsNondegenerate.polarFormulaAt_flat g e he`:
    for `e : V x ≃L[ℝ] W` to a finite-dimensional inner product space with
    `he : ∀ u v, ⟪e u, e v⟫ = g.inner x u v`, `g.polarFormulaAt x (ω.flat x)`
    is the conjugate by `e` of the continuous endomorphism of Tau Ceti's
    linear `TauCeti.SymplecticForm.polarComplexStructure` of
    `(hω.symplecticFormAt x).transport e`, by `polarFormulaAt_eq_conj`,
    part 9's `metricPolarFormula_eq` and
    `metricPolarComplexStructure_innerSL`.
- $J_{g,\omega}$: `ContMDiffTwoForm.IsNondegenerate.polarComplexStructure g hω :
  ContMDiffComplexStructure I n F V`, whose value at `x` is Tau Ceti's linear
  `TauCeti.SymplecticForm.polarComplexStructure` of `hω.symplecticFormAt x` for
  the inner product `g x`: `polarComplexStructure_apply e he` and
  `almostComplexStructureAt_polarComplexStructure e he` state it through an
  `e` as in `polarFormulaAt_flat`, and
  `polarComplexStructure_eq_polarFormulaAt` says that it is
  `g.polarFormulaAt x (ω.flat x)`. With `compatible_polarComplexStructure g`,
  the orthogonality `apply_polarComplexStructure_apply` and the
  characterization `polarComplexStructure_eq_iff` by these two properties,
  which `polarComplexStructure_tangentEquiv` uses. Its smoothness is no new chart
  argument: by `polarFormulaAt_flat`, its section is
  `contMDiffOn_polarFormulaAt` composed with `contMDiff_flat ω`, whose
  values lie in `polarFormulaDomain F V` by `mk_flat_mem_polarFormulaDomain`. This generalizes Tau Ceti's $TM$ version
  (`Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`); on $TM$,
  `polarComplexStructure_tangentEquiv` says that it is Tau Ceti's
  `SmoothTwoForm.IsNondegenerate.polarComplexStructure`.
- $J_{g,\omega_{g,B}}$ for an endomorphism `B` of a fibre, in `PolarEnd.lean`
  as above. The bullet above gives smoothness only along a section, while
  the homotopy equivalence below needs it on the total space of the
  endomorphism bundle. For a metric `g`:
  - `compatibleBilinAt g x (B : V x →L[ℝ] V x) : V x →L[ℝ] V x →L[ℝ] ℝ`,
    the form $\tfrac12(g_x(Bu,v)-g_x(u,Bv))$ of the formula above, defined
    for every `B` from `(g x).comp B` and Mathlib's
    `ContinuousLinearMap.precomp` (no norm on the fibres is needed), with
    `@[simp] compatibleBilinAt_apply`, `isAlt_compatibleBilinAt` (its
    `toBilinForm` is alternating, as `isAlt_bilinFormAt` says for a
    two-form), and linearity in `B`: `compatibleBilinAt_add` and
    `compatibleBilinAt_smul`. In `SymplecticGeometry.Bundle`,
    `flat_compatibleForm`:
    `(compatibleForm g J).flat x = g.compatibleBilinAt x (J x)`.
  - `contMDiff_compatibleBilinAt`: the map
    `q ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) q.proj (compatibleBilinAt g q.proj q.snd)`
    of the endomorphism bundle to the bundle of bilinear forms is
    `ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n`
    for `g` of order `n`: by `contMDiffAt_hom_bundle` and
    `inCoordinates_apply_eq₂`, its reading in a trivialization is a fixed
    continuous bilinear expression in the readings of `g` and of `q.snd`.
  - `polarEndDomain g : Set (TotalSpace (F →L[ℝ] F) fun x ↦ V x →L[ℝ] V x)`,
    the preimage of `polarFormulaDomain F V` under that map, so the points
    $(x,B)$ where `compatibleBilinAt g x B` is nondegenerate, with
    `@[simp] mem_polarEndDomain_iff`. It is open (`isOpen_polarEndDomain`),
    by `isOpen_polarFormulaDomain` and `contMDiff_compatibleBilinAt`. It
    contains the values of every complex structure
    (`SymplecticGeometry.Bundle.ContMDiffComplexStructure.mk_mem_polarEndDomain`,
    so that `J.mk_mem_polarEndDomain g x : ⟨x, J x⟩ ∈ g.polarEndDomain`), by
    `flat_compatibleForm`, `compatible_compatibleForm`,
    `Compatible.isNondegenerate` and `mk_flat_mem_polarFormulaDomain`.
  - `polarEndAt g x B : V x →L[ℝ] V x :=
    g.polarFormulaAt x (g.compatibleBilinAt x B)`, with `polarEndAt_def`. In
    `SymplecticGeometry.Bundle`, `polarEndAt_eq_polarComplexStructure`: if
    `hω : ω.IsNondegenerate` and `ω.flat x = compatibleBilinAt g x B`, then
    `polarEndAt g x B = hω.polarComplexStructure g x`, by `polarEndAt_def`
    and `polarComplexStructure_eq_polarFormulaAt`. So at `B = J x`
    it is $J_{g,\omega_{g,J}}$ at `x`, with `ω` the form
    `compatibleForm g J`, nondegenerate by `compatible_compatibleForm`.
  - `contMDiffOn_polarEndAt`: the map
    `q ↦ TotalSpace.mk' (F →L[ℝ] F) q.proj (polarEndAt g q.proj q.snd)` of
    the endomorphism bundle to itself is
    `ContMDiffOn (I.prod 𝓘(ℝ, F →L[ℝ] F)) (I.prod 𝓘(ℝ, F →L[ℝ] F)) n` on
    `polarEndDomain g`, for `g` of order `n`: it is `contMDiffOn_polarFormulaAt`
    composed with `contMDiff_compatibleBilinAt`, and `polarEndDomain g` is
    the preimage of `polarFormulaDomain F V`.
- Existence, over a Hausdorff σ-compact base: `IsNondegenerate.exists_compatible`
  (`∃ J, ω.Compatible J`), and `ContMDiffComplexStructure.exists_compatible`
  (`∃ ω, ω.Compatible J`), from `nonempty_contMDiffRiemannianMetric`.

## Spaces of sections and their topology

The spaces in the second milestone are subtypes with the subspace topology of
a `frameTopology`:

| Space | Lean type | Topology |
|---|---|---|
| complex structures | `ContMDiffComplexStructure I n F V` | `ContMDiffComplexStructure.frameTopology e U hU` |
| $\omega$-tame, $\omega$-compatible structures | `{J // ω.Tames J}`, `{J // ω.Compatible J}` | subspace of the above |
| symplectic forms | `{ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate}` | subspace of `ContMDiffSection.frameTopology e' U' hU'` |
| forms taming, compatible with $J$ | `{ω // ω.Tames J}`, `{ω // ω.Compatible J}` | the same |
| bundle metrics | `Bundle.ContMDiffRiemannianMetric I n F V` | Tau Ceti's `Bundle.ContMDiffRiemannianMetric.frameTopology` |

**How statements quantify over covers.** A statement takes the frames of each
bundle it uses (`e U hU` for the endomorphism bundle, `e' U' hU'` for the
alternating bundle) as explicit variables, assumes that they cover
(`hcover : ∀ x, ∃ i, x ∈ U i`), and installs the topologies with `letI`, as
Tau Ceti's statements do. So every statement holds for every covering frame
system; by `frameTopology_eq_of_covers` (for a locally compact model `EB`, as every
finite-dimensional one is) the topology does not depend on it, and the atlas
cover `fun x : M ↦ trivializationAt _ _ x` with its base sets always exists,
so the statements are not vacuous. No canonical cover and no global instance
is introduced: Tau Ceti has none, and one here would clash with its later
choice.

## Continuity of fibrewise maps

`Section/Topology.lean`, namespace `ContMDiffSection`, over a nontrivially
normed field `𝕜` as in Tau Ceti's file. This is the lemma that `DESIGN.md`
describes, in the form the uses need: the parameter is a manifold, and the
fibre map is jointly $C^n$ in the parameter, the point and the fibre value,
on an open subset of the total space. Joint regularity implies the condition
of `DESIGN.md` (derivatives up to order $n$ continuous in the parameter) and
is what the uses provide, since the fibre maps are explicit formulas.

```lean
variable {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] {IP : ModelWithCorners 𝕜 EP HP}
  (Φ : P → ∀ x, V x → W x) {O : Set (TotalSpace F V)}
  (hΦ : ContMDiffOn (IP.prod (I.prod 𝓘(𝕜, F))) (I.prod 𝓘(𝕜, F')) n
    (fun q : P × TotalSpace F V ↦ TotalSpace.mk' F' q.2.proj (Φ q.1 q.2.proj q.2.snd))
    (univ ×ˢ O))

def fiberwiseMap (p : P) (s : {s : Cₛ^n⟮I; F, V⟯ // ∀ x, ⟨x, s x⟩ ∈ O}) : Cₛ^n⟮I; F', W⟯

theorem continuous_fiberwiseMap [IsManifold IP n P] [LocallyCompactSpace EB]
    [LocallyCompactSpace F] (hO : IsOpen O) (hcover) :
    letI := frameTopology e U hU; letI := frameTopology e' U' hU'
    Continuous fun q : P × {s // ∀ x, ⟨x, s x⟩ ∈ O} ↦ fiberwiseMap Φ hΦ q.1 q.2
```

with `fiberwiseMap_apply`. The definition does not use that `O` is open, so
`fiberwiseMap` does not take `hO`; only `continuous_fiberwiseMap` does.
Here `e U hU` is a covering frame system of `V` (`hcover`) and `e' U' hU'`
is any frame system of `W`. The target needs no cover, since
`continuous_frameTopology_iff_frameCoordinates` tests one frame of `W` at a
time; the uses supply covers of both bundles anyway.

**The route.** By `continuous_frameTopology_iff_frameCoordinates`, it is
enough to show, for each `j`, that the frame coordinates of
`fiberwiseMap Φ hΦ p s` in `e' j` on `U' j` are continuous in `(p, s)` in
`C^n⟮I, U' j; 𝓘(𝕜, F'), F'⟯`. Let `N j : Opens (TotalSpace F V)` be the
points of `O` over `(e' j).baseSet` (open, since `O` is and the projection is
continuous); it is a manifold with model `I.prod 𝓘(𝕜, F)`. The coordinates
are the composite `G p ∘ σ s` of

- `σ s : C^n⟮I, U' j; I.prod 𝓘(𝕜, F), N j⟯`, the map `x ↦ ⟨x, s x⟩`
  restricted to `U' j` and corestricted to `N j`, that is
  `((toContMDiffMap s).restrict (U' j)).codRestrict (N j) _`, with the two
  helpers below and Tau Ceti's `ContMDiffMap.restrict`; and
- `G p : C^n⟮I.prod 𝓘(𝕜, F), N j; 𝓘(𝕜, F'), F'⟯`, the map
  `v ↦ (e' j ⟨v.proj, Φ p v.proj v.snd⟩).2`, which is jointly $C^n$ on
  `P × N j` by `hΦ` and the smoothness of `e' j` over its base set.

Then `p ↦ G p` is continuous by Tau Ceti's
`ContMDiff.continuous_manifoldWeakWhitney`
(`Geometry/Manifold/ContMDiffMap/Chart/ManifoldFamily.lean`); `s ↦ σ s` by
`continuous_toContMDiffMap`, Tau Ceti's `ContMDiffMap.continuous_restrict`
(`.../ContMDiffMap/Chart/Restriction.lean`) and the family form
`Continuous.codRestrict_manifoldWeakWhitney`; and the
composite by Tau Ceti's `ContMDiffMap.continuous_comp_manifoldWeakWhitney`
(`.../ContMDiffMap/Chart/Comp.lean`). That last lemma assumes local
compactness of the models of the source (`EB`) and of the middle manifold
(`EB × F`), which is where `[LocallyCompactSpace F]` comes from. Every use
(issues 7 and 8) has a finite-dimensional `F`, the fibre of the endomorphism
or alternating bundle of a finite-rank bundle, so the hypothesis costs them
nothing. The statement should hold without it, but a proof would need
continuity of composition through a middle manifold whose model is not
locally compact, which neither Tau Ceti nor Mathlib provides; the docstring
says so.

**The two helpers.** They are general facts about sections and about
$C^n$ maps, so they are public and named.

- In `Section/Topology.lean`, namespace `ContMDiffSection`: a section as a
  $C^n$ map into the total space, and its continuity in the section.

  ```lean
  def toContMDiffMap (s : Cₛ^n⟮I; F, V⟯) : C^n⟮I, M; I.prod 𝓘(𝕜, F), TotalSpace F V⟯ :=
    ⟨fun x ↦ TotalSpace.mk' F x (s x), s.contMDiff⟩

  @[simp] theorem toContMDiffMap_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) :
      toContMDiffMap s x = TotalSpace.mk' F x (s x)

  theorem toContMDiffMap_injective :
      Function.Injective (toContMDiffMap : Cₛ^n⟮I; F, V⟯ → C^n⟮I, M; I.prod 𝓘(𝕜, F), _⟯)

  theorem continuous_toContMDiffMap [LocallyCompactSpace EB] (hcover : ∀ x, ∃ i, x ∈ U i) :
      letI := frameTopology e U hU
      Continuous (toContMDiffMap : Cₛ^n⟮I; F, V⟯ → C^n⟮I, M; I.prod 𝓘(𝕜, F), TotalSpace F V⟯)
  ```

  The proof checks the chart tests of `continuous_manifoldWeakWhitney_iff`.
  The chart of the total space at a point over `b` is built from
  `trivializationAt F V b`, so whether `toContMDiffMap s` sends a point into
  its source does not depend on `s`, and the coordinate representative is
  the pair of a function that does not depend on `s` and the frame
  coordinates of `s` in `trivializationAt F V b`. These coordinates are
  continuous in `s` by Tau Ceti's `continuous_frameCoordinates_of_cover`
  (`Section/FrameCover.lean`), which is where `hcover` and the local
  compactness of `EB` are used. The two facts about the chart of the total
  space are Tau Ceti's `Bundle.mem_extChartAt_source_iff` and
  `Bundle.extChartAt_apply_of_mem_baseSet`
  (`Geometry/Manifold/VectorBundle/Submersion.lean`), applied at the point
  `toContMDiffMap s p`; the library does not restate them.

  The frame coordinates are $C^n$ maps on the open base set only, while the
  chart test reads `p ↦ (trivializationAt F V b ⟨p, s p⟩).2` in an ambient
  chart of `M`; the two lemmas of `ContMDiffMap/Chart/Restriction.lean`
  below bridge the gap.
- In `Geometry/Manifold/ContMDiffMap/Chart/Restriction.lean`, namespace
  `ContMDiffMap`, at the path of Tau Ceti's file of the same name: the
  ambient chart derivatives of a function `f : M → F` that agrees on an open
  set `U` with a map `g : C^n⟮I, U; 𝓘(𝕜, F), F⟯`, with nothing assumed
  about `f` off `U`.

  ```lean
  theorem iteratedFDerivWithin_eq_taylorComp_of_eqOn_opens (U : Opens M)
      (g : C^n⟮I, U; 𝓘(𝕜, F), F⟯) (f : M → F) (hfg : ∀ y : U, f y = g y) (x : M) (y : U)
      {z : E} (hz : z ∈ (extChartAt I x).target) (hy : (extChartAt I x).symm z ∈ U)
      (hys : (extChartAt I x).symm z ∈ (extChartAt I (y : M)).source) (m : ℕ) (hm : m ≤ n) :
      iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm) (extChartAt I x).target z =
        (ftaylorSeriesWithin 𝕜 (g ∘ (extChartAt I y).symm)
          (extChartAt I y).target (extChartAt I (y : M) ((extChartAt I x).symm z))).taylorComp
          (ftaylorSeriesWithin 𝕜 (extChartAt I (y : M) ∘ (extChartAt I x).symm)
            (extChartAt I x).target z) m

  theorem tendsto_iteratedFDerivWithin_of_eqOn_opens [LocallyCompactSpace E] (U : Opens M)
      {P : Type*} {l : Filter P} {g : P → C^n⟮I, U; 𝓘(𝕜, F), F⟯}
      {g₀ : C^n⟮I, U; 𝓘(𝕜, F), F⟯} (hg : Tendsto g l (𝓝 g₀)) {f : P → M → F} {f₀ : M → F}
      (hfg : ∀ p (y : U), f p y = g p y) (hfg₀ : ∀ y : U, f₀ y = g₀ y) (x : M) {z : E}
      (hz : z ∈ (extChartAt I x).target) (hy : (extChartAt I x).symm z ∈ U)
      (m : ℕ) (hm : m ≤ n) :
      Tendsto (fun q : P × E ↦ iteratedFDerivWithin 𝕜 m (f q.1 ∘ (extChartAt I x).symm)
          (extChartAt I x).target q.2)
        (l ×ˢ 𝓝[(extChartAt I x).target] z)
        (𝓝 (iteratedFDerivWithin 𝕜 m (f₀ ∘ (extChartAt I x).symm) (extChartAt I x).target z))
  ```

  They generalize Tau Ceti's
  `ContMDiffMap.iteratedFDerivWithin_eq_restrict_taylorComp` and
  `ContMDiffMap.tendsto_iteratedFDerivWithin_of_restrict`, which are the case
  `g = f.restrict U` of a $C^n$ map `f` on all of `M`, by the same proofs.
- In `Geometry/Manifold/ContMDiffMap/Chart/CodRestrict.lean`, namespace
  `ContMDiffMap`, beside Tau Ceti's weak Whitney files: corestriction of a
  $C^n$ map to an open subset of the target that contains its range.

  ```lean
  def codRestrict (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) : C^n⟮I, M; J, W⟯

  @[simp] theorem coe_codRestrict_apply (f : C^n⟮I, M; J, N⟯) (W : Opens N)
      (h : ∀ x, f x ∈ W) (x : M) : (f.codRestrict W h x : N) = f x

  @[simp] theorem val_comp_codRestrict (f : C^n⟮I, M; J, N⟯) (W : Opens N)
      (h : ∀ x, f x ∈ W) : Subtype.val ∘ f.codRestrict W h = f

  theorem codRestrict_mem_chartJetSet_iff [IsManifold I n M] [IsManifold J n N]
      (f : C^n⟮I, M; J, N⟯) (W : Opens N) (h : ∀ x, f x ∈ W) (x : M) (y : W) (m : ℕ)
      (K : Set (extChartAt I x).target) (V : Set (E [×m]→L[𝕜] F)) :
      f.codRestrict W h ∈ chartJetSet x y m K V ↔ f ∈ chartJetSet x (y : N) m K V

  theorem continuous_codRestrict_manifoldWeakWhitney [IsManifold I n M] [IsManifold J n N]
      (W : Opens N) :
      Continuous fun f : {f : C^n⟮I, M; J, N⟯ // ∀ x, f x ∈ W} ↦ f.1.codRestrict W f.2

  theorem _root_.Continuous.codRestrict_manifoldWeakWhitney [IsManifold I n M]
      [IsManifold J n N] {P : Type*} [TopologicalSpace P] {g : P → C^n⟮I, M; J, N⟯}
      (hg : Continuous g) (W : Opens N) (h : ∀ p x, g p x ∈ W) :
      Continuous fun p ↦ (g p).codRestrict W (h p)
  ```

  Here `E` and `F` are the model spaces of `M` and `N`. The last lemma is the
  form for a continuous family of maps, which the proof of
  `continuous_fiberwiseMap` uses.

  Smoothness of the corestriction is Tau Ceti's
  `TauCeti.ContMDiff.subtypeVal_comp_iff`. Continuity needs no local
  compactness: a chart of `W` is the restriction of a chart of `N`
  (Mathlib's `OpenPartialHomeomorph.subtypeRestr`, with `subtypeRestr_coe`
  and `subtypeRestr_source`), so the preimage of a chart test of `W` is the
  trace on the subtype of a chart test of `N`.

**Remarks.** The docstring records the
example of `DESIGN.md` showing that continuity in the parameter alone does
not suffice for $n\ge1$. The uses take `P = Unit`, or `P = ℝ` with the time
entering the formula only through `smoothTransition`, which keeps every
coefficient in $[0,1]$ for every real time; the homotopies are then the
restrictions to `unitInterval`. A formula that is smooth only for times in
$[0,1]$ is never fed to the lemma with `P = ℝ` directly.

## Contractibility and the homotopy equivalence

`Symplectic/ComplexStructure/Contractible.lean`. All the maps are
`fiberwiseMap`s of explicit formulas, so their continuity is
`continuous_fiberwiseMap`.

- **The domain of the bundle Cayley path.** Both Cayley paths below need an
  open set of the endomorphism bundle on which the path from a reference
  endomorphism to the fibre value is defined for every coefficient in
  $[0,1]$. Only the reference differs between them, so the set and its
  arguments (independence from the trivialization, the units, openness and
  membership) are planned once, for an arbitrary reference, in
  `Geometry/Manifold/VectorBundle/Cayley.lean`, the file of the bundle
  Cayley lemma below. The set and its first four lemmas mention only
  Mathlib's bundles and the linear Cayley formula, so they go in Mathlib's
  namespace `Bundle`, as `Bundle.polarFormulaDomain` does; the membership
  lemma is about Tau Ceti's `SymplecticForm.Compatible`, so it goes in that
  namespace. Part 9's
  Cayley domain (`Geometry/Symplectic/Cayley/Domain.lean` of
  `design/compatible-complex-structures.md`) and its lemmas live in a
  complete normed algebra, and `Compatible.mem_cayleyDomain` moreover on a
  finite-dimensional normed space, while the fibres `V x` carry neither a
  norm nor a finite-dimensionality instance; so the set is read through
  trivializations, under `[CompleteSpace F]`. Write
  `E := TotalSpace (F →L[ℝ] F) fun x ↦ V x →L[ℝ] V x`, and for `q : E` let
  `φ q` be conjugation by the fibre equivalence `V q.proj ≃L[ℝ] F` of
  `trivializationAt F V q.proj` (Mathlib's
  `ContinuousLinearEquiv.conjContinuousAlgEquiv`, an algebra isomorphism
  `(V q.proj →L[ℝ] V q.proj) ≃A[ℝ] (F →L[ℝ] F)`).
  - `Bundle.cayleyPathDomain F V (A : ∀ q : E, V q.proj →L[ℝ] V q.proj) : Set E`,
    the points `q` with `(b, φ q (A q), φ q q.snd) ∈ cayleyDomain (F →L[ℝ] F)`
    for every $b\in[0,1]$, with `mem_cayleyPathDomain_iff`, which says so.
  - `mem_cayleyPathDomain_iff_of_mem_baseSet`: the same condition, with
    `φ q` replaced by conjugation by the fibre equivalence at `q.proj` of any
    linear trivialization (`[e.IsLinear ℝ]`) whose base set contains `q.proj`. Two such
    conjugations differ by an algebra automorphism of `F →L[ℝ] F`, which
    preserves units and, by Tau Ceti's `map_cayleyFormula`, the Cayley
    formula, so the set does not depend on the choice.
  - `mem_cayleyPathDomain_iff_forall_mem_cayleyDomain`: the same condition
    read in the fibre ring, `(b, A q, q.snd) ∈ cayleyDomain (V q.proj →L[ℝ] V q.proj)`
    for every $b\in[0,1]$; the two lemmas before and after it follow from it
    by part 9's `map_mem_cayleyDomain_iff`.
  - `isUnit_of_mem_cayleyPathDomain`: for `q` in the set and $b\in[0,1]$,
    `IsUnit (1 - A q * q.snd)` and
    `IsUnit (1 - b • cayleyFormula (A q) q.snd)` in the fibre ring
    `V q.proj →L[ℝ] V q.proj`. These are the two unit hypotheses that
    `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle` asks for at
    `q` with coefficient `b`, since Tau Ceti's proof states them in the
    fibre ring (`hu₁`, `hu₂` of `ContMDiffAt.cayleyPathFormula_hom_bundle`).
    Proof: from `mem_cayleyPathDomain_iff`, apply the algebra isomorphism
    `(φ q).symm`, which preserves units and, by `map_cayleyFormula`, the
    Cayley formula.
  - `isOpen_cayleyPathDomain`: if `U` is an open subset of `E` and
    `q ↦ TotalSpace.mk' (F →L[ℝ] F) q.proj (A q)` is continuous on `U`, then
    `U ∩ cayleyPathDomain F V A` is open. Over the base set of the
    trivialization at a point `x₀`, use its fibre equivalences, by
    `mem_cayleyPathDomain_iff_of_mem_baseSet`. There the trivialization of
    the endomorphism bundle reads `(x, B)` as `(x, φ B)`
    (`inCoordinates_eq_conjContinuousAlgEquiv`), so the set is, inside `U`,
    the preimage under the continuous reading of `q ↦ (A q, q.snd)` of the
    open set of part 9's `isOpen_setOf_forall_Icc_mem_cayleyDomain`.
  - `TauCeti.SymplecticForm.Compatible.mem_cayleyPathDomain`, under
    `[FiniteDimensional ℝ F]`, used as `h₀.mem_cayleyPathDomain h`:
    let `ω` be a Tau Ceti symplectic form on `V q.proj`, and `J₀`, `J`
    almost complex structures on it whose linear maps are those of `A q`
    and `q.snd`, with `ω.Compatible J₀` and `ω.Tames J`; then
    `q ∈ cayleyPathDomain F V A`. Transport `ω`, `J₀` and `J` to `F` along
    the fibre equivalence (Tau Ceti's `SymplecticForm.transport` and
    `AlmostComplexStructure.transport`). Compatibility and tameness survive
    (`Compatible.transport`, `Tames.transport`,
    `Geometry/Symplectic/SymplecticTransport.lean`), and the transported
    linear maps are those of `φ q (A q)` and `φ q q.snd`
    (`conjContinuousAlgEquiv_apply_apply`,
    `AlmostComplexStructure.transport_apply`). So part 9's
    `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain`, on the normed
    finite-dimensional space `F`, gives the triple for $|b|\le1$. This
    transport is the linear lemma
    `TauCeti.SymplecticForm.Compatible.mem_cayleyDomain_of_continuousLinearEquiv`
    (for a topological vector space with a continuous linear equivalence to a
    finite-dimensional normed space), in part 9's
    `Geometry/Symplectic/Cayley/Domain.lean` next to `Compatible.mem_cayleyDomain`,
    with `Compatible.exists_toLinearMap_eq_cayleyPathFormula`: there the Cayley path
    `cayleyPathFormula (smoothTransition t) A B` represents an `ω`-tame
    structure, `ω`-compatible when the endpoint is, transported from Tau
    Ceti's linear `Compatible.cayleyPath`. These statements need only
    `[FiniteDimensional ℝ F]`: completeness of `F` then comes from Mathlib's
    instance `FiniteDimensional.proper_real`.
- **Fixed form, tame and compatible structures.** Fix a compatible `J₀`
  (`IsNondegenerate.exists_compatible`). The contraction is
  $(t,J)\mapsto$ `TauCeti.cayleyPathFormula (smoothTransition (1 - t)) (J₀ x) (J x)`
  at each point, with `P = ℝ`, as Tau Ceti's `Compatible.cayleyPath` scales
  the Cayley coordinate by `smoothTransition`. The formula is Tau Ceti's linear
  one (`Geometry/Symplectic/Cayley/Smooth.lean`), natural under algebra
  isomorphisms (`map_cayleyPathFormula`) and jointly smooth in the
  coefficient and both structures wherever `1 - A * B` and
  `1 - b • cayleyFormula A B` are units (`contDiffAt_cayleyPathFormula`).
  Tau Ceti proves the second only for $|b|\le1$
  (`Compatible.isUnit_one_sub_smul_cayleyFormula`), and it fails for larger
  $|b|$ in general, which is why the coefficient goes through
  `smoothTransition`. The open set `O` of the lemma is
  `cayleyPathDomain F V (fun q ↦ J₀ q.proj)`, with the fixed structure as
  reference. It is open by `isOpen_cayleyPathDomain` with `U = univ`, since
  `J₀` is a continuous section of the endomorphism bundle. It contains
  `⟨x, J x⟩` for every `J` tame for `ω`, by
  `Compatible.mem_cayleyPathDomain` with `hω.symplecticFormAt x`,
  `almostComplexStructureAt J₀ x` and `almostComplexStructureAt J x`
  (`almostComplexStructureAt_apply`).

  The hypothesis `hΦ` of `continuous_fiberwiseMap`
  is checked in trivializations, and for $V = TM$ with $n = \infty$ Tau Ceti
  has done this step: `ContMDiffAt.cayleyPathFormula_hom_bundle`
  (`.../AlmostComplex/CayleyPath.lean`) shows that
  `cayleyPathFormula (b q) (A q) (B q)` is smooth at `q₀` as a map into the
  endomorphism bundle of $TM$ along a smooth base map `f : P → M`, given
  smooth `b`, `A`, `B` and the two units at `q₀` only. Its proof rewrites
  `inCoordinates` as conjugation by the fibre equivalence
  (`ContinuousLinearMap.inCoordinates_eq_conjContinuousAlgEquiv`,
  `Topology/VectorBundle/Coordinates.lean`, stated for any vector bundle),
  moves the formula through it with `map_cayleyPathFormula`, and ends with
  `contDiffAt_cayleyPathFormula`. None of these steps uses the smooth
  structure of the bundle or the order `∞`: Mathlib's `contMDiffAt_hom_bundle`
  needs only a topological vector bundle, and `contDiffAt_cayleyPathFormula`
  holds at every order. So the library states the lemma once, at every order
  `n : WithTop ℕ∞`, analytic order included, as for its two inputs (`f`, `b`,
  `A`, `B` of order `n`, conclusion of order `n`), for
  the endomorphism bundle of any topological vector bundle `V` with complete
  fibre `F` (`[FiberBundle F V] [VectorBundle ℝ F V]`, the fibres topological
  modules, `[CompleteSpace F]`; no `ContMDiffVectorBundle` and no
  `IsManifold`), as `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle`
  in the root namespace, by Tau Ceti's proof with `TangentSpace I` replaced by
  `V`; the chart computation is not redone in another way. Tau Ceti's lemma
  is its case `V = TangentSpace I`, `n = ∞`, so no comparison is needed. It
  mentions only Mathlib's endomorphism bundle and Tau Ceti's
  `cayleyPathFormula`, so it has a file of its own,
  `Geometry/Manifold/VectorBundle/Cayley.lean`, with `cayleyPathDomain`
  above. That file imports only Mathlib's
  `Geometry/Manifold/VectorBundle/Hom.lean`, Tau Ceti's
  `Geometry/Symplectic/Cayley/Smooth.lean`,
  `Topology/VectorBundle/Coordinates.lean`, and part 9's
  `Geometry/Symplectic/Cayley/Domain.lean`; `Contractible.lean` imports
  it. The suffix `_of_vectorBundle` is provisional, since the plain name
  is Tau Ceti's: if Tau Ceti generalizes its own lemma in this way, the
  library's lemma is removed in favour of it. Then `hΦ` holds at
  each point of `univ ×ˢ O`: apply the lemma with parameter space
  `ℝ × TotalSpace (F →L[ℝ] F) (fun x ↦ V x →L[ℝ] V x)`, base map the bundle
  projection, `b` the time through `smoothTransition (1 - ·)`, `A` the value
  of `J₀` and `B` the fibre value; its two unit hypotheses come from
  `isUnit_of_mem_cayleyPathDomain`, since `smoothTransition`
  takes values in $[0,1]$. The lemma is applied at the cast to
  `WithTop ℕ∞` of the design's regularity `n : ℕ∞`, never at the analytic
  order, since `smoothTransition` is smooth but not analytic. That the path
  stays tame, and compatible when `J` is, are Tau
  Ceti's linear lemmas behind `SmoothTwoForm.Compatible.tames_cayleyPath` and
  `compatible_cayleyPath` (`.../AlmostComplex/CayleyPath.lean`), which this
  generalizes. In `Contractible.lean` the smoothness on `univ ×ˢ O` is
  `ContMDiffComplexStructure.contMDiffOn_cayleyPathFormula` (with the time
  through `smoothTransition`), the membership of the values of a tame `J` is
  `ContMDiffTwoForm.Compatible.mem_cayleyPathDomain`, and the structures on
  the path are `ContMDiffTwoForm.Compatible.cayleyPath h₀ h t`, the bundle
  form of Tau Ceti's `SmoothTwoForm.Compatible.cayleyPath`, with
  `cayleyPath_apply`, `exists_almostComplexStructureAt_cayleyPath`,
  `tames_cayleyPath`, `compatible_cayleyPath`, `cayleyPath_of_nonpos`,
  `cayleyPath_of_one_le` and `continuous_cayleyPath` (joint continuity in the
  time and the tame structure, from `continuous_fiberwiseMap`); the
  contraction is the path at time `1 - t`. The endpoints use part 9's
  `cayleyPathFormula_zero` and `cayleyPathFormula_one`.
  Results: `ContMDiffTwoForm.IsNondegenerate.contractibleSpace_tames`
  and `contractibleSpace_compatible` (`ContractibleSpace {J // ω.Tames J}`,
  resp. `Compatible`, for every covering frame system).
- **Fixed structure, taming and compatible forms.** These sets are convex
  (`convex_setOf_tames`), nonempty (`ContMDiffComplexStructure.exists_compatible`),
  and `frameTopology` is a topological vector space
  (`isTopologicalAddGroup_frameTopology`, `continuousSMul_frameTopology`), so
  Mathlib's `Convex.contractibleSpace` applies: `ContMDiffComplexStructure.contractibleSpace_tames`
  and `contractibleSpace_compatible` for `{ω // ω.Tames J}` and
  `{ω // ω.Compatible J}`, for any frame system of the alternating bundle,
  covering or not, since the proof does not use a cover. Their docstrings
  note that a contractible space is nonempty, which is the existence half of
  the milestone.
- **Metrics.** `Bundle.ContMDiffRiemannianMetric.contractibleSpace_frameTopology`,
  from Tau Ceti's `continuous_convexCombination_frameTopology`, over a
  Hausdorff σ-compact base. It mentions only Mathlib and Tau Ceti types, so it
  goes in `Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`,
  the path of the Tau Ceti file that holds that lemma.
- **Continuity of $\omega\mapsto J_{g,\omega}$ and $J\mapsto\omega_{g,J}$.**
  The homotopy equivalence below needs both maps to be continuous for the
  frame topologies. Each is a `fiberwiseMap` with `P = Unit`, on the model
  `𝓘(ℝ, Unit)` (see *Remarks* above), so the hypothesis `hΦ` of
  `continuous_fiberwiseMap` asks for smoothness on a total space: for the
  first, of the flat map out of the bundle of alternating maps of two
  vectors; for the second, of the passage from an alternating bilinear form
  to an alternating map. The library and Tau Ceti have each only along a
  section over the base (`contMDiff_flat`, Tau Ceti's
  `contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`); Mathlib has
  neither. Issue 27 states both along a map `b : N → M` into the base, as
  Mathlib's `ContMDiffAt.clm_bundle_apply` is stated: a section is the case
  `b = id`, a total space the case `b = TotalSpace.proj` with the identity
  as the map into it.

  *The pointwise maps and their smoothness.* They mention only Mathlib's
  bundles and Tau Ceti's `flatL`, so they go in
  `Geometry/Manifold/VectorBundle/ContinuousAlternatingMap.lean`, beside
  `contMDiff_compContinuousLinearMap_totalSpace`, over the file's field `𝕜`,
  with values in a normed space `G` (the two-forms of this part are the case
  `𝕜 = G = ℝ`), `alternatingMapOfBilin` with values in the file's
  coefficient bundle `W` (it uses no trivialization), and a manifold `N`
  with model `IN`:

  ```lean
  def Bundle.flatAt (F) {x : M} (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x) :
      V x →L[𝕜] V x →L[𝕜] G

  @[simp] theorem Bundle.flatAt_apply (α : V x [⋀^Fin 2]→L[𝕜] Trivial M G x) (v w : V x) :
      flatAt F α v w = α ![v, w]

  theorem contMDiffAt_sectionAlong_flatAt {b : N → M} {α : ∀ y, V (b y) [⋀^Fin 2]→L[𝕜] Trivial M G (b y)}
      {y₀ : N}
      (hα : ContMDiffAt IN (I.prod 𝓘(𝕜, F [⋀^Fin 2]→L[𝕜] G)) n
        (fun y ↦ TotalSpace.mk' (F [⋀^Fin 2]→L[𝕜] G)
          (E := fun x ↦ V x [⋀^Fin 2]→L[𝕜] Trivial M G x) (b y) (α y)) y₀) :
      ContMDiffAt IN (I.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
        (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G)
          (E := fun x ↦ V x →L[𝕜] V x →L[𝕜] G) (b y) (flatAt F (α y))) y₀

  def Bundle.alternatingMapOfBilin (F) [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {x : M}
      (β : V x →L[𝕜] V x →L[𝕜] W x) (hβ : ∀ v, β v v = 0) : V x [⋀^Fin 2]→L[𝕜] W x

  @[simp] theorem Bundle.alternatingMapOfBilin_apply (β : V x →L[𝕜] V x →L[𝕜] W x)
      (hβ : ∀ v, β v v = 0) (v : Fin 2 → V x) :
      alternatingMapOfBilin F β hβ v = β (v 0) (v 1)

  theorem contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear [CompleteSpace 𝕜]
      [FiniteDimensional 𝕜 F₁] {b : N → B}
      {α : ∀ y, E₁ (b y) [⋀^Fin 2]→L[𝕜] E₂ (b y)}
      {β : ∀ y, E₁ (b y) →L[𝕜] E₁ (b y) →L[𝕜] E₂ (b y)} {y₀ : N}
      (hβ : ContMDiffAt IN (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁ →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁ →L[𝕜] F₂)
          (E := fun x ↦ E₁ x →L[𝕜] E₁ x →L[𝕜] E₂ x) (b y) (β y)) y₀)
      (hα : ∀ y v, α y v = β y (v 0) (v 1)) :
      ContMDiffAt IN (IB.prod 𝓘(𝕜, F₁ [⋀^Fin 2]→L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ [⋀^Fin 2]→L[𝕜] F₂)
          (E := fun x ↦ E₁ x [⋀^Fin 2]→L[𝕜] E₂ x) (b y) (α y)) y₀
  ```

  The two smoothness lemmas are named as Tau Ceti's
  `SmoothTwoForm.contMDiffAt_sectionAlong_flatL`, of which the first is the
  generalization from `TangentSpace I` to `V`. `flatAt F α` is
  the body of today's `ContMDiffTwoForm.flat` with `ω x` replaced by `α`:
  `flatL 𝕜 F G` of `α` read through the fibre equivalence of
  `trivializationAt F V x`, carried back by it. `contMDiffAt_sectionAlong_flatAt` is the
  proof of Tau Ceti's `contMDiffAt_sectionAlong_flatL` with `TangentSpace I`
  replaced by `V`, as `contMDiff_flat` already does at `b = id`: by
  `contMDiffAt_hom_bundle` and `contMDiffAt_continuousAlternatingMap_bundle`,
  both of which Mathlib states along a map into the total space, the
  reading at `y` near `y₀` in the trivialization at `b y₀` is the
  continuous linear map `flatL 𝕜 F G` applied to the reading of `α y`
  (`inCoordinates_apply_eq₂`). `alternatingMapOfBilin` is the private
  `ofBilinearSectionAt` of `Symplectic/Basic.lean` made a function of `β x`
  alone (Tau Ceti's `LinearMap.IsAlt.toAlternatingMap`, made continuous by
  Mathlib's `AlternatingMap.toContinuousAlternatingMap`, the fibre being
  finite-dimensional and Hausdorff by `VectorBundle.finiteDimensional` and
  `FiberBundle.t2Space`). `contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear`
  is the proof of Tau Ceti's
  `contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`, its case
  `b = id`, with the sections
  `y ↦ e.symm (b y) (v i)` along `b` (Tau Ceti's sections composed with `b`,
  which is $C^n$ at `y₀` as the projection of `hβ`) and Mathlib's
  `ContMDiffAt.clm_bundle_apply` along `b`; the module docstring credits that
  proof, and that of `contMDiffAt_sectionAlong_flatL`. As for
  `_of_vectorBundle` above, the library's lemma is removed if Tau Ceti
  generalizes its own. In `Symplectic/Basic.lean`, `flat` becomes
  `flatAt F (ω x)` (`flat_def`) and `contMDiff_flat` the case `b = id` of
  `contMDiffAt_sectionAlong_flatAt`, and `ofBilinearSection` takes its values from
  `alternatingMapOfBilin`, so that each chart argument is made once.

  *The bridges*, in `Symplectic/ComplexStructure/Basic.lean`:
  - `Bundle.mk_flatAt_mem_polarFormulaDomain` (namespace `Bundle`, as
    `polarFormulaDomain`): for `α : V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x` with
    `(MultilinearMap.toBilinMap α.toMultilinearMap).Nondegenerate`,
    `⟨x, flatAt F α⟩ ∈ polarFormulaDomain F V`, by the proof of
    `IsNondegenerate.mk_flat_mem_polarFormulaDomain` (the skew part of an
    alternating form is twice the form), which becomes its case `α = ω x`
    by `flat_def` and `bilinFormAt_def`. Its hypothesis is membership in the
    open set of `isOpen_setOf_nondegenerate`.
  - `ContMDiffComplexStructure.compatibleForm_eq_alternatingMapOfBilin`:
    `compatibleForm g J x = alternatingMapOfBilin F (g.compatibleBilinAt x (J x)) _`,
    the proof of vanishing on the diagonal coming from
    `isAlt_compatibleBilinAt`, by `ext` and the `_apply` lemmas of the
    three.

  *The continuity lemmas*, in `Contractible.lean`, with `e U hU` a frame
  system of the endomorphism bundle and `e' U' hU'` one of the bundle
  `fun x ↦ V x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x`, under the hypotheses of
  `Compatible.continuous_cayleyPath` (`[FiniteDimensional ℝ F]` gives the
  local compactness of both model fibres that `continuous_fiberwiseMap`
  asks for):

  ```lean
  theorem ContMDiffTwoForm.continuous_polarComplexStructure
      (g : ContMDiffRiemannianMetric I n F V) (hcover' : ∀ x, ∃ i, x ∈ U' i) :
      letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
      letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
      Continuous fun ω : {ω : ContMDiffTwoForm I n F V // ω.IsNondegenerate} ↦
        ω.2.polarComplexStructure g

  theorem ContMDiffComplexStructure.continuous_compatibleForm
      (g : ContMDiffRiemannianMetric I n F V) (hcover : ∀ x, ∃ i, x ∈ U i) :
      letI := ContMDiffComplexStructure.frameTopology (I := I) (n := n) e U hU
      letI := ContMDiffSection.frameTopology (I := I) (n := n) e' U' hU'
      Continuous (compatibleForm g : ContMDiffComplexStructure I n F V → ContMDiffTwoForm I n F V)
  ```

  Only the cover of the source bundle is assumed, as in
  `continuous_fiberwiseMap`. For the first, the open set `O` is the set
  of `isOpen_setOf_nondegenerate`, which contains `⟨x, ω x⟩` exactly when
  `ω` is nondegenerate at `x` (`bilinFormAt_def`), so the subtype of
  nondegenerate forms maps continuously into that of `fiberwiseMap`
  (`Continuous.subtype_mk`). The formula is
  `g.polarFormulaAt q.proj (flatAt F q.snd)`, and `hΦ` is
  `contMDiffOn_polarFormulaAt` composed with `contMDiffAt_sectionAlong_flatAt` (`b` the
  projection, `α` the fibre value), which maps `O` into
  `polarFormulaDomain F V` by `mk_flatAt_mem_polarFormulaDomain`. Its
  `fiberwiseMap` at `()` is $J_{g,\omega}$, by `ext`,
  `polarComplexStructure_eq_polarFormulaAt` and `flat_def`, and
  `continuous_frameTopology_iff` concludes. For the second, `O` is all of the
  endomorphism bundle, the formula is
  `alternatingMapOfBilin F (g.compatibleBilinAt q.proj q.snd) _`, and `hΦ` is
  `contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear` with `β` from
  `contMDiff_compatibleBilinAt` and `hα` from `alternatingMapOfBilin_apply`.
  Its `fiberwiseMap` at `()` is `compatibleForm g J`
  (`compatibleForm_eq_alternatingMapOfBilin`), and the source map is
  `isEmbedding_toEndomorphism_frameTopology`. The two `hΦ` are steps of these
  proofs only.

  *The straight line on forms.* In `Symplectic/ComplexStructure/Basic.lean`,
  `ContMDiffTwoForm.IsNondegenerate.tames_lineMap_compatibleForm`: for
  `hω : ω.IsNondegenerate`, a metric `g` and `t ∈ Icc 0 1`,
  `(AffineMap.lineMap ω (compatibleForm g (hω.polarComplexStructure g)) t).Tames
  (hω.polarComplexStructure g)`, by Mathlib's `Convex.lineMap_mem` for
  `convex_setOf_tames`, since both ends tame $J_{g,\omega}$
  (`compatible_polarComplexStructure`, `compatible_compatibleForm`,
  `Compatible.tames`). Its `Tames.isNondegenerate` is the nondegeneracy the
  homotopy needs.
- **The homotopy equivalence.** `exists_homotopyEquiv_polarComplexStructure`:
  for a metric `g`,
  `∃ e : {ω // ω.IsNondegenerate} ≃ₕ ContMDiffComplexStructure I n F V,
  (∀ ω, e.toFun ω = ω.2.polarComplexStructure g) ∧
  ∀ J, (e.invFun J).1 = compatibleForm g J`, a theorem for each pair of
  covering frame systems. The map is continuous by
  `continuous_polarComplexStructure`, and the inverse is
  $J\mapsto\omega_{g,J}$, continuous into the subtype by
  `continuous_compatibleForm`, `Continuous.subtype_mk` and
  `compatible_compatibleForm` with `Compatible.isNondegenerate`. On the
  forms, $\omega$ and $\omega_{g,J_{g,\omega}}$ both tame $J_{g,\omega}$, and
  the straight line `AffineMap.lineMap` between them, for $t$ in
  `unitInterval`, stays nondegenerate by `tames_lineMap_compatibleForm`.
  It is continuous in $(t,\omega)$ by Mathlib's
  `ContinuousMap.Homotopy.affine`: the second end is
  continuous in $\omega$ as the composite of the two continuity lemmas above,
  and the frame topology is a topological vector space
  (`isTopologicalAddGroup_frameTopology`, `continuousSMul_frameTopology`).
  At time $0$ it is $\omega$ (`AffineMap.lineMap_apply_zero`), at time $1$
  the composite (`AffineMap.lineMap_apply_one`). This is
  `ContMDiffTwoForm.homotopic_compatibleForm_polarComplexStructure`. On the
  structures the path is stated for two metrics `g₀` and `g₁`, so that
  `polarComplexStructure_homotopic` can use it too: $J$ and
  $J_{g_1,\omega_{g_0,J}}$ are both compatible with $\omega_{g_0,J}$, and the
  Cayley path between them, with $J_{g_1,\omega_{g_0,J}}$ as reference and
  coefficient `smoothTransition t`, is a fibrewise formula in $(t, J_x)$
  that is jointly smooth for every real $t$ on an open set `O` of the
  endomorphism bundle, defined below, that contains the values of every
  complex structure. The reference is not a fixed section: at a point `q` of
  the endomorphism bundle it is
  `A q = g₁.polarFormulaAt q.proj (g₀.compatibleBilinAt q.proj q.snd)`
  (`polarEndAt g q.proj q.snd` when `g₀ = g₁ = g`), which at
  `q = ⟨x, J x⟩` is $J_{g_1,\omega_{g_0,J}}$ at `x`
  (`ContMDiffComplexStructure.polarFormulaAt_compatibleBilinAt`, in
  `Basic.lean`). The hypothesis `hΦ` of
  `continuous_fiberwiseMap` comes from
  `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle` as above, with
  `b` the time through `smoothTransition` and this `A`, which depends on the
  point of the endomorphism bundle and not only on its base point; the lemma
  allows that, since `A` may be any function of the parameter `q`. Its
  hypothesis `hA`, smoothness of `A` at the point, is
  `contMDiffOn_polarFormulaAt_compatibleBilinAt` (in `PolarEnd.lean`, with
  `contMDiffOn_polarEndAt` its case `g₀ = g₁`) on the open set
  `polarEndDomain g₀`, which contains `O`; its two unit hypotheses at the
  point follow from the membership in `O` by `isUnit_of_mem_cayleyPathDomain`,
  at the time `b` of the point.

  The set `O` is `polarEndDomain g₀ ∩ cayleyPathDomain F V A`, for this `A`.
  It is open by `isOpen_cayleyPathDomain` with `U = polarEndDomain g₀`, which
  is open (`isOpen_polarEndDomain`) and on which `A` is continuous. It
  contains `⟨x, J x⟩` for every complex structure `J`: the point is in
  `polarEndDomain g₀` (`mk_mem_polarEndDomain`), and
  `Compatible.mem_cayleyPathDomain` applies with the linear symplectic form
  of $\omega_{g_0,J}$ at `x`, the linear structure $J_{g_1,\omega_{g_0,J}}$ at
  `x`, whose map is `A ⟨x, J x⟩`, and the one of `J x`; both are compatible
  with that form (`compatible_polarComplexStructure`,
  `compatible_compatibleForm`), and the second is therefore tame for it, by
  Tau Ceti's `Compatible.tames`. The structures on the path are
  `Compatible.cayleyPath` for $\omega_{g_0,J}$ and the reference
  $J_{g_1,\omega_{g_0,J}}$. In `Contractible.lean` the smoothness and the
  continuity for a reference `A` that is `Cⁿ` on an open set `W` are
  `contMDiffOn_cayleyPathFormula_of_contMDiffOn` and
  `continuous_fiberwiseMap_cayleyPathFormula`, which give, with `W = univ`,
  `contMDiffOn_cayleyPathFormula` and `Compatible.continuous_cayleyPath`
  too. Then come `mk_mem_polarEndDomain_inter_cayleyPathDomain`,
  `continuous_cayleyPath_polarComplexStructure` and the homotopy
  `homotopic_polarComplexStructure_compatibleForm` from
  $J\mapsto J_{g_1,\omega_{g_0,J}}$ to the identity.
  `polarComplexStructure_homotopic`: for two metrics the two maps
  $\omega\mapsto J_{g,\omega}$ are homotopic. Contracting the metrics would
  need continuity in the metric, which the library does not have; instead,
  $J_{g_0,\omega}$ is homotopic to $J_{g_1,\omega_{g_0,J_{g_0,\omega}}}$ by
  the path above with two metrics, and that is homotopic to $J_{g_1,\omega}$
  by the straight line on forms for `g₀`.
- **Milestone.** `SymplecticGeometry.Bundle.contractibleSpace_compatible_tames`:
  the conjunction of the three parts of the plan (for every nondegenerate
  `ω`, the two spaces of structures are contractible; for every `J`, the two
  spaces of forms are contractible; for every metric, the existential of
  `exists_homotopyEquiv_polarComplexStructure`), over a Hausdorff σ-compact base, for every `n` and
  every covering frame systems. Milestone: *Compatible and tame complex
  structures on symplectic vector bundles*. By the two `tangentEquiv`s and
  `tangentHomeomorph`, the case $E=TM$, `n = ⊤`, of its statements about
  spaces of structures for a fixed form is the corresponding statement for
  Tau Ceti's `SmoothAlmostComplexStructure`. The statements about spaces of
  forms do not transfer, since Tau Ceti puts no topology on `SmoothTwoForm`.
  This part states neither case, which belongs to the page
  `atlas/almost-complex-structures.md`.

## Local Darboux frames

`Symplectic/Trivialization.lean`.

- `ContMDiffTwoForm.IsNondegenerate.exists_isLocalFrameOn_isDarbouxBasis`:
  with no hypothesis on the base, every `x` has an open neighbourhood `W` and
  sections `s : Fin k × Fin 2 → ∀ y, V y` forming a $C^n$ local frame on `W`
  (Mathlib's `IsLocalFrameOn`) that is a Darboux basis of
  `hω.symplecticFormAt y` (Tau Ceti's `TauCeti.SymplecticForm.IsDarbouxBasis`,
  in the book's normalization) at every `y ∈ W`. Route: extend a Darboux
  basis of $V_x$ to local sections $a_i,b_i$, constant in a trivialization,
  and run a symplectic Gram–Schmidt on them: where $c=\omega(a_1,b_1)\ne0$,
  keep $a_1$ and $c^{-1}b_1$, and project the other sections by
  $v\mapsto v-\omega(v,c^{-1}b_1)a_1+\omega(v,a_1)c^{-1}b_1$, which fixes them
  at $x$. No metric, complex structure or ODE is needed.
- `IsNondegenerate.exists_trivialization_isSymplectomorphism`: for a symplectic
  form `σ` on the model fibre `F`, every point lies in the base set of a
  trivialization in the $C^n$ maximal atlas whose fibre maps carry
  `symplecticFormAt y` to `σ`, built from the frame by Tau Ceti's
  `IsLocalFrameOn.trivialization` (`Geometry/Manifold/VectorBundle/FrameTrivialization.lean`)
  with a Darboux basis of `σ`; and
  `IsNondegenerate.isSymplectomorphism_coordChangeL`: the coordinate changes of two such
  trivializations preserve `σ`, so the structure group reduces to
  $\mathrm{Sp}(F,\sigma)$. For `F = StdSpace (Fin k)` and `σ = stdForm`, the
  matrices of the coordinate changes lie in `Matrix.symplecticGroup` by
  *Standard model*'s `mem_symplecticGroup_iff_isSymplectomorphism`.
- `IsNondegenerate.exists_isSymplecticFrameOn`: the same in the language of
  the symplectic frames of *Constructions* below. For a symplectic form `σ`
  on a normed space `W` with `[FiniteDimensional ℝ W]` and
  `finrank ℝ W = finrank ℝ F`, every point has an
  open neighbourhood `U` and a frame `Φ` with `ω.IsSymplecticFrameOn σ U Φ`:
  choose a linear equivalence `e : W ≃L[ℝ] F`, apply the previous result to
  the form `σ` moved to `F` along `e`, and compose `e` with the inverses of
  the fibre maps of that trivialization. This is the form in which *First
  Chern number* takes frames over discs.

## Classification

`Symplectic/Classification.lean`. For two bundles `V₁`, `V₂` over `M`, with
$C^n$ forms and structures `h₁ : ω₁.Tames J₁`, `h₂ : ω₂.Tames J₂` (no
hypothesis on the base, since neither direction uses a bundle metric):

```lean
theorem exists_symplectic_bundleEquiv_iff_exists_complex_bundleEquiv :
    (∃ Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x, ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
        (fun v ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) ∧
      ∀ x v w, ω₂.bilinFormAt x (Φ x v) (Φ x w) = ω₁.bilinFormAt x v w) ↔
    (∃ Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x, ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
        (fun v ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)) ∧
      ∀ x v, Φ x (J₁ x v) = J₂ x (Φ x v))
```

Isomorphisms are not a new structure: a $C^n$ family of fibrewise
equivalences, whose inverse is then $C^n$ (Tau Ceti's `contMDiff_bundle_symm`,
`bundleDiffeomorph`), as in Tau Ceti's homotopy invariance. Its docstring and
that of the theorem of the previous section end with the line Milestone:
*Symplectic vector bundles are complex vector bundles*.

- **Symplectic to complex.** Transport $J_1$ by $\Phi$ to
  $J_1'$ (`ContMDiffComplexStructure.pushforward`), which tames $\omega_2$
  by `Tames.pushforward`, since $\Phi$ carries $\omega_1$ to $\omega_2$. For two structures taming the same form,
  $A=\tfrac12(1-J_2J_1')$ is invertible (Tau Ceti's linear
  `Tames.isUnit_one_sub_mul`) and $J_2A=AJ_1'$; it is a polynomial in the
  sections, hence $C^n$, and $A\circ\Phi$ is the complex isomorphism. No
  ODE is needed in this direction.
- **Complex to symplectic.** Transport $\omega_1$ to $\omega_1'$
  (`ContMDiffTwoForm.pushforward`), which tames $J_2$ by `Tames.pushforward`.
  Write $\beta$ for `smoothTransition` and set
  $\omega_t=(1-\beta(t))\omega_1'+\beta(t)\omega_2$. Since $\beta$ takes
  values in $[0,1]$, each $\omega_t$, for every real $t$, is a convex
  combination of two forms taming $J_2$, so it tames $J_2$ and is
  nondegenerate. Part 10's lemmas need exactly this: their hypothesis `hinv`
  asks for invertibility at every real time, which the straight path
  $(1-t)\omega_1'+t\omega_2$ does not give (for $\omega_2=2\omega_1'$ it is
  zero at $t=-1$). The path is smooth, with $\omega_0=\omega_1'$ and
  $\omega_1=\omega_2$, and the linear Moser construction of part 10
  (`SymplecticGeometry/Geometry/Symplectic/LinearMoser.lean`: the left Dyson
  series of `moserGenerator`), applied fibrewise, gives $\Psi_1$ with
  $\Psi_1^*\omega_2=\omega_1'$. The generator is a formula in the family of
  forms and its time derivative, with no metric. To see that $\Psi_1$ is $C^n$
  on the total space, read everything in a trivialization at a base point
  $x$ and take as parameter the pair $(a,b)=(\omega_1'(x),\omega_2(x))$ of
  trivialized forms there, not the chart coordinates of $x$. The pair ranges
  over the set of pairs all of whose convex combinations $(1-s)a+sb$,
  $s\in[0,1]$, are invertible; this set is open, since $[0,1]$ is compact,
  and it suffices for `hinv`, which only meets the values $\beta(t)\in[0,1]$.
  The path $t\mapsto(1-\beta(t))a+\beta(t)b$ is affine in $(a,b)$, so issue
  10's lemmas on an open parameter set give a propagator that is $C^n$ in
  $(a,b,t)$. Composing with the trivialized sections, which are $C^n$ within
  the chart range, a set that may meet the boundary, is then
  `ContDiffOn.comp`. Two trivializations differ by a linear isomorphism, and
  `moserGenerator_conj` carries the generator, hence $\Psi_1$, from one to
  the other.

## Constructions

These are the constructions that part 12 of `DESIGN.md` lists under
*Constructions*, which *First Chern number* uses. None of them is a new type
of bundle: each is a form, a complex structure, a predicate or a lemma on
the bundles of Mathlib and Tau Ceti (`f *ᵖ V`, `V₁ ×ᵇ V₂`,
`TangentSpace I`, complex bundles with a metric). Unless a name says
otherwise they are in the namespace `SymplecticGeometry.Bundle`; those on
forms are in `ContMDiffTwoForm`, so that dot notation finds them, and those
on complex structures are in `ContMDiffComplexStructure` and in
`ComplexStructure.lean`, since they use no form.

### Symplectic isomorphisms and frames

`Symplectic/Basic.lean`. Both are stated with what the file already has.

- **Isomorphisms.** A symplectic isomorphism from `(V₁, ω₁)` to `(V₂, ω₂)` is
  a family `Φ : ∀ x, V₁ x ≃L[ℝ] V₂ x` with `hΦ`, $C^n$ on total spaces, such
  that `pushforward Φ hΦ ω₁ = ω₂`. No structure is added: the classification
  states its isomorphisms in the same unbundled form, and *First Chern
  number* bundles them itself (`SymplecticSurfaceBundle.Iso`). The link
  between the two forms is `pushforward_eq_iff`:
  `pushforward Φ hΦ ω₁ = ω₂ ↔ ∀ x v w, ω₂.bilinFormAt x (Φ x v) (Φ x w) =
  ω₁.bilinFormAt x v w`. With `pushforward_refl` and `pushforward_trans`
  this gives identities, inverses and composites of isomorphisms.
- **Frames.** For a normed space `W` with a symplectic form
  `σ : TauCeti.SymplecticForm W` and a set `U ⊆ M`:

  ```lean
  structure ContMDiffTwoForm.IsSymplecticFrameOn (ω : ContMDiffTwoForm I n F V)
      (σ : TauCeti.SymplecticForm W) (U : Set M) (Φ : ∀ x, W ≃L[ℝ] V x) : Prop where
    contMDiffOn : ContMDiffOn (I.prod 𝓘(ℝ, W)) (I.prod 𝓘(ℝ, F)) n
      (fun p : M × W ↦ TotalSpace.mk' F p.1 (Φ p.1 p.2)) (U ×ˢ univ)
    map_bilinFormAt : ∀ x ∈ U, ∀ v w, ω.bilinFormAt x (Φ x v) (Φ x w) = σ v w
  ```

  A frame need not be defined off `U`; values there are ignored. API:
  `IsSymplecticFrameOn.mono` (to a smaller set);
  `IsSymplecticFrameOn.isSymplectomorphism` (at `x ∈ U`,
  `σ.IsSymplectomorphism (hω.symplecticFormAt x) (Φ x).toLinearEquiv`, Tau
  Ceti's predicate of `Geometry/Symplectic/SymplecticTransport.lean`, for
  `hω : ω.IsNondegenerate`);
  `IsSymplecticFrameOn.nondegenerate_bilinFormAt` (`(ω.bilinFormAt x).Nondegenerate`
  for `x ∈ U`, since `Φ x` carries it to `σ`);
  `IsSymplecticFrameOn.trans` (composing with a symplectic isomorphism `Ψ`
  from `ω` to `ω'` gives a frame `fun x ↦ (Φ x).trans (Ψ x)` of `ω'`);
  `IsSymplecticFrameOn.precomp` (for a linear symplectomorphism
  `e : W' ≃L[ℝ] W` from `σ'` to `σ`, `fun x ↦ e.trans (Φ x)` is a frame for
  `σ'`).
  **Example.** `isSymplecticFrameOn_const`: on `Bundle.Trivial M W'`
  with `const ω'`, a linear symplectomorphism `e : W ≃L[ℝ] W'` from `σ` to
  `ω'` is a frame `fun _ ↦ e` over `univ`. Existence over small open sets is
  `IsNondegenerate.exists_isSymplecticFrameOn` (*Local Darboux frames*).
- **Transition maps.** For two families `Φ Φ' : ∀ x, W ≃L[ℝ] V x`, the
  definition `frameTransition Φ Φ' x : W ≃L[ℝ] W` is
  `(Φ x).trans (Φ' x).symm`, with `frameTransition_def` (by `(rfl)`),
  `@[simp] frameTransition_apply` (`(Φ' x).symm (Φ x v)`),
  `@[simp] frameTransition_self` (the identity), `frameTransition_trans`
  (`(frameTransition Φ Φ' x).trans (frameTransition Φ' Φ'' x) =
  frameTransition Φ Φ'' x`) and `@[simp] frameTransition_symm`
  (`(frameTransition Φ Φ' x).symm = frameTransition Φ' Φ x`, the analogue of
  Mathlib's `Trivialization.symm_coordChangeL`). As a map it is
  `(Φ' x)⁻¹ ∘ Φ x`, in the order of Mathlib's `coordChangeL`, so the
  $\Phi_1^{-1}\Phi_2$ of *First Chern number* is `frameTransition Φ₂ Φ₁`. It uses no form, so it is in
  `SymplecticGeometry.Bundle`; *First Chern number*'s transition loops are
  its values along a loop. For frames `Φ`, `Φ'` of `ω` for `σ` over `U`:
  `IsSymplecticFrameOn.isSymplectomorphism_frameTransition`
  (`frameTransition Φ Φ' x` preserves `σ` at `x ∈ U`) and, for
  `[FiniteDimensional ℝ W]` and `IsOpen U`,
  `IsSymplecticFrameOn.contMDiffOn_frameTransition`
  (`fun x ↦ (frameTransition Φ Φ' x : W →L[ℝ] W)` is $C^n$ on `U`). The
  frames that *First Chern number* uses are over open sets, and openness
  makes the argument pointwise. At `x ∈ U`, the field `contMDiffOn` gives
  smoothness at every `(x, v)`, since `U ×ˢ univ` is open; read through
  the total space of `Bundle.Trivial M W` (with Tau Ceti's
  `Bundle.Trivial.diffeomorphProd` and `Bundle.Trivial.contMDiffAt_mk_iff`,
  `Geometry/Manifold/VectorBundle/Trivial.lean`), Tau Ceti's
  `TauCeti.contMDiffAt_hom_bundle_iff`
  (`Geometry/Manifold/VectorBundle/Hom.lean`) makes `Φ` and `Φ'` sections of the hom bundle from `Bundle.Trivial M W` to
  `V` that are $C^n$ at `x`. Then `ContMDiffAt.clm_bundle_inverse` and
  `ContMDiffAt.clm_bundle_comp` give the composite at `x`, a section of the
  endomorphisms of the trivial bundle, which is the map into `W →L[ℝ] W`.

### Pull-backs

For a map `f : C^n⟮I', N; I, M⟯` (the argument of Mathlib's instance
`ContMDiffVectorBundle.pullback`), with `N` a manifold over a model
`I' : ModelWithCorners ℝ EN HN`:

- `Geometry/Manifold/VectorBundle/Pullback.lean`, in the root namespace
  `Bundle.Pullback`, beside Tau Ceti's lemma of the same file name:
  `Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`, the
  analogue for alternating maps of Tau Ceti's
  `Bundle.Pullback.contMDiff_hom_section_iff`, in its generality: a map
  `f : K` with `[FunLike K N M] [ContinuousMapClass K N M]` and
  `hf : ContMDiff I' I n f`. The target is a trivial bundle over each base,
  since that is what `ContMDiffTwoForm` uses: `Bundle.Trivial N G` over `N`,
  not the pull-back `f *ᵖ Bundle.Trivial M G`, whose fibres are the same type
  but whose total-space topology and atlas are other instances. For a
  family `A : ∀ y, V (f y) [⋀^ι]→L[𝕜] G`, the section `y ↦ A y` of the
  alternating bundle of `f *ᵖ V` and `Bundle.Trivial N G` is $C^n$ if and
  only if `y ↦ ⟨f y, A y⟩` is $C^n$ into the alternating bundle of `V` and
  `Bundle.Trivial M G`. Its proof follows Tau Ceti's: near `y`, both are read
  in the trivializations at `f y` and at `y`, and the coordinate expressions
  agree on a neighbourhood. That they agree is
  `ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem`, which
  involves no charts and so lives in `Topology/VectorBundle/Pullback.lean`,
  beside Tau Ceti's `ContinuousLinearMap.inCoordinates_pullback_of_mem` in
  the file of the same name. No rank hypothesis, and any finite index type
  `ι`. The field is any nontrivially normed field: Mathlib's
  `contMDiffAt_continuousAlternatingMap_bundle`, on which the proof rests,
  needs no `[CharZero 𝕜]`. Only the smoothness instances of that bundle,
  such as `ContMDiffVectorBundle.continuousAlternatingMap`, do, so a caller
  adds `[CharZero 𝕜]` only where it needs the alternating bundle to be a
  $C^n$ vector bundle.
- `Symplectic/Pullback.lean`: `ContMDiffTwoForm.pullback ω f :
  ContMDiffTwoForm I' n F (f *ᵖ V)`, with value `ω (f y)` at `y`. The
  argument order is that of Tau Ceti's `ContMDiffSection.pullback ω f`
  (`Section/Module.lean`), of which `ContMDiffTwoForm` is an `abbrev`: that
  is a section of the pull-back of the alternating bundle, and the lemma
  above makes it a section of the alternating bundle of `f *ᵖ V`, since the
  two fibres at `y` are the same type. API: `@[simp] pullback_apply`;
  `bilinFormAt_pullback`, and `bilinFormAt_pullback_apply` for its
  value `ω (f y) ![v, w]` on `v w : V (f y)`, which `simp` proves with
  `pullback_apply` and `@[simp] bilinFormAt_apply_pullback`, the value
  `ω y ![v, w]` of any form `ω` on `f *ᵖ V` on `v w : V (f y)`; `pullback_zero`,
  `pullback_add`, `pullback_smul`, `@[simp] pullback_neg`,
  `@[simp] pullback_sub` and the linear map `pullbackLinearMap I F V n f`,
  as Tau Ceti has them for sections; `IsNondegenerate.pullback`;
  `IsNondegenerate.symplecticFormAt_pullback` (the symplectic form of the
  pull-back at `y` is that of `ω` at `f y`), through
  `IsNondegenerate.toBilinForm_symplecticFormAt` in `Symplectic/Basic.lean`,
  and `@[simp] IsNondegenerate.symplecticFormAt_pullback_apply`, its value
  on `v w : V (f y)`, for any proof that the pull-back is nondegenerate.
  `bilinFormAt_pullback` and `symplecticFormAt_pullback` are not `@[simp]`,
  for the reason given below for `pullback_toEndomorphism`.
- `ComplexStructure.lean`: `ContMDiffComplexStructure.pullback J f :
  ContMDiffComplexStructure I' n F (f *ᵖ V)`, the endomorphism section
  `y ↦ J (f y)`, which is $C^n$ by `Bundle.Pullback.contMDiff_hom_section_iff`
  itself. API: `pullback_toEndomorphism` (`J (f y)`),
  `almostComplexStructureAt_pullback`, `pullback_neg`, and `coe_pullback`
  (`⇑(J.pullback f y) = ⇑(J (f y))`). `simp` treats a vector by its type.
  On a vector of `V (f y)` it evaluates the pull-back by `@[simp]
  pullback_apply` (`J.pullback f y v = J (f y) v`). A vector of
  `(f *ᵖ V) y` stays in the pull-back bundle, where the lemmas about
  `J.pullback f` as a complex structure apply to it; there
  `@[simp] apply_eq_pullback_apply` (`J (f y) v = J.pullback f y v`) and
  `@[simp] pullback_neg_apply` (`(-J).pullback f y v = -J.pullback f y v`)
  bring `J (f y)` and `-J` to it. `@[simp]
  coe_almostComplexStructureAt_pullback` evaluates the almost complex
  structure of the pull-back. The root-namespace `@[simp]
  Bundle.Pullback.eq_iff` (`Data/Bundle.lean`) moves an equation stated in
  `(f *ᵖ V) y` between vectors of `V (f y)` to `V (f y)`, and `@[simp]
  Bundle.Pullback.eq_fiber_iff` moves one stated in `V (f y)` between
  vectors of `(f *ᵖ V) y` to `(f *ᵖ V) y`, and `@[simp] neg_apply_fiber`
  and `neg_apply_pullback` evaluate a negated function on a vector of the
  other type. In `Topology/VectorBundle/Pullback.lean`, which imports
  `Data/Bundle.lean`, `@[simp]
  Bundle.Pullback.neg_fiber`, `add_fiber`, `sub_fiber` and `smul_fiber`
  take an operation in `V (f y)` on vectors of `(f *ᵖ V) y` in
  `(f *ᵖ V) y`, and `@[simp] neg_pullback`, `add_pullback`, `sub_pullback`
  and `smul_pullback` take one in `(f *ᵖ V) y` on vectors of `V (f y)` in
  `V (f y)`. Each fires only where the two types differ. `zero_fiber` is
  not `@[simp]`: a zero alone has no argument whose type could decide
  between them. In an equation, `@[simp] eq_zero_fiber_iff`,
  `zero_fiber_eq_iff`, `eq_zero_pullback_iff` and `zero_pullback_eq_iff`
  replace a zero of the other type by the zero of the equation's type.
  `coe_pullback` and `pullback_neg` are not `@[simp]`: `coe_pullback` would
  undo `apply_eq_pullback_apply`, and `pullback_neg` would rewrite the
  left-hand side of `pullback_neg_apply`. Neither is `ContMDiffComplexStructure.neg_apply`,
  whose left-hand side `simp` rewrites with `neg_toEndomorphism`.
  `pullback_toEndomorphism` and `almostComplexStructureAt_pullback` are
  not `@[simp]`: they rewrite under the coercion of the pulled-back bundle,
  and the rewritten term no longer matches the lemmas about `V (f y)`.
- `Symplectic/Pullback.lean`, the pairs: `Tames.pullback`,
  `Invariant.pullback` and `Compatible.pullback`, for a form and a complex
  structure of the same regularity `n`, from `ω.Tames J` to
  `(ω.pullback f).Tames (J.pullback f)`, pointwise.
- Isomorphisms: `pullback_pushforward`, `(pushforward Φ hΦ ω).pullback f` is
  `pushforward (fun y ↦ Φ (f y)) _ (ω.pullback f)`,
  the smoothness coming from Tau Ceti's `Bundle.Pullback.contMDiff_fiberwise`
  (so a symplectic isomorphism pulls back to one);
  `pushforward_pullback_id`, the pull-back along `ContMDiffMap.id`, moved to
  `V` by the identity of each fibre (smooth by Tau Ceti's
  `Bundle.Pullback.idDiffeomorph`), is `ω`; `pushforward_pullback_comp`, for
  `g : C^n⟮I', N; I, M⟯` and `f : C^n⟮I'', P; I', N⟯`, the pull-back along
  `g.comp f`, moved to `f *ᵖ (g *ᵖ V)` by the identity of each fibre (smooth
  by `Bundle.Pullback.compDiffeomorph`), is `(ω.pullback g).pullback f`.
- Frames: `IsSymplecticFrameOn.pullback`, a frame `Φ` of `ω` over `U` gives
  the frame `fun y ↦ Φ (f y)` of `ω.pullback f` over `f ⁻¹' U`; the
  transition maps of pulled-back frames are
  `@[simp] frameTransition_pullback`: `frameTransition (fun y ↦ Φ (f y))
  (fun y ↦ Φ' (f y)) y = frameTransition Φ Φ' (f y)`, for any map
  `f : N → M`, by `frameTransition_apply`.
- Along the derivative: for `f : K` with `[FunLike K N M]
  [ContinuousMapClass K N M]` and `hf : ContMDiff I' I ∞ f`,
  `ContMDiffTwoForm.compMFDeriv f hf ω : ContMDiffTwoForm I' ⊤ EN
  (TangentSpace I')`, for `ω` a form on `f *ᵖ TangentSpace I`, is
  $\sigma(u,v)=\omega(df\,u,df\,v)$: `compContinuousLinearMap` along
  `mfderiv I' I f`, smooth by `Bundle.Pullback.contMDiff_mfderiv_hom`. API:
  `compMFDeriv_def`, `compMFDeriv_apply` (not `@[simp]`: `simp` evaluates
  on vectors with `@[simp] compMFDeriv_apply_apply`) and
  `bilinFormAt_compMFDeriv`.

### Direct sums

For `ω₁ : ContMDiffTwoForm I n F₁ V₁` and `ω₂ : ContMDiffTwoForm I n F₂ V₂`
over the same base, on Mathlib's direct sum `V₁ ×ᵇ V₂` (`Bundle.Prod`, with
`Bundle.Prod.contMDiffVectorBundle`), with `[FiniteDimensional ℝ F₁]
[FiniteDimensional ℝ F₂]`:

- `Symplectic/Prod.lean`: `ContMDiffTwoForm.prod ω₁ ω₂ :
  ContMDiffTwoForm I n (F₁ × F₂) (V₁ ×ᵇ V₂)`, with
  `@[simp] prod_apply`,
  $(\omega_1\oplus\omega_2)_x((v_1,v_2),(w_1,w_2))=\omega_{1,x}(v_1,w_1)+\omega_{2,x}(v_2,w_2)$.
  Its value at `x` is
  `(ω₁ x).compContinuousLinearMap fst + (ω₂ x).compContinuousLinearMap snd`
  (`prod_def`), $C^n$ by Tau Ceti's product criterion
  (`Geometry/Manifold/VectorBundle/Prod.lean`, with `contMDiff_fst` and
  `contMDiff_snd`) and `contMDiff_compContinuousLinearMap_totalSpace`.
  `IsNondegenerate.prod`, and
  `IsNondegenerate.symplecticFormAt_prod`: the symplectic form of the sum at
  `x` is Tau Ceti's `TauCeti.SymplecticForm.prod` of the two
  (`Geometry/Symplectic/Prod/Basic.lean`).
- `ComplexStructure.lean`: `ContMDiffComplexStructure.prod J₁ J₂ :
  ContMDiffComplexStructure I n (F₁ × F₂) (V₁ ×ᵇ V₂)`, with value
  `(J₁ x).prodMap (J₂ x)`, $C^n$ by `Bundle.Prod.contMDiff_prodMap`
  (`Geometry/Manifold/VectorBundle/Prod.lean`) and `contMDiff_hom_bundle_iff`.
  API: `@[simp] prod_apply`, `@[simp] almostComplexStructureAt_prod` (Tau Ceti's
  `TauCeti.AlmostComplexStructure.prod` of the two), and
  `prod_toEndomorphism`, which is not `@[simp]`, since it would rewrite the
  left side of `prod_apply` to a `Prod.map`.
- `Symplectic/Prod.lean`, the pairs: `Tames.prod` and `Compatible.prod`, from
  Tau Ceti's `SymplecticForm.prod_tames` and `SymplecticForm.prod_compatible`
  at each point, and `Invariant.prod`.
- Isomorphisms: `pushforward_prodCongr`, the sum of two symplectic
  isomorphisms, `fun x ↦ (Φ₁ x).prodCongr (Φ₂ x)` (Mathlib's
  `ContinuousLinearEquiv.prodCongr`), carries `ω₁.prod ω₂` to the sum of the
  images; `pushforward_prodComm`, the fibrewise swap
  `ContinuousLinearEquiv.prodComm` carries `ω₁.prod ω₂` to `ω₂.prod ω₁`.
  Smoothness of these maps of total spaces is the product criterion:
  `Bundle.Prod.contMDiff_prodCongr` and `Bundle.Prod.contMDiff_prodComm`,
  corollaries of `Bundle.Prod.contMDiff_prodMap` and `Bundle.Prod.contMDiff_swap`
  (fibrewise `Prod.map` and swap, for fibres with only a zero), in
  the library's `Geometry/Manifold/VectorBundle/Prod.lean` (root namespace,
  with the path of Tau Ceti's file of the criterion). So
  `pushforward_prodCongr` takes only the smoothness of `Φ₁` and `Φ₂`, and
  `pushforward_prodComm` no smoothness hypothesis.
- Block frames: `IsSymplecticFrameOn.prod`, frames `Φ₁` of `ω₁` for `σ₁`
  and `Φ₂` of `ω₂` for `σ₂` over `U` give the frame
  `fun x ↦ (Φ₁ x).prodCongr (Φ₂ x)` of `ω₁.prod ω₂` for `σ₁.prod σ₂` over
  `U`. For the standard models, `IsSymplecticFrameOn.stdSum`: for frames
  for `stdForm ι` and `stdForm κ`, the frame
  `fun x ↦ (StdSpace.sumEquiv ι κ).trans ((Φ₁ x).prodCongr (Φ₂ x))` for
  `stdForm (ι ⊕ κ)`; and `frameTransition_stdSum`: if the `frameTransition`s
  of two such pairs at `x` are `Matrix.toEuclideanLin A` and
  `Matrix.toEuclideanLin B`, that of the block frames is
  `Matrix.toEuclideanLin (Matrix.symplecticSum A B)`. So a transition loop of
  a sum is the image of the pair of loops under `TauCeti.GLSymplectic.sum`,
  the form of `TauCeti.GLSymplectic.maslovIndex_sum`.
- `StdSpace.sumEquiv ι κ : StdSpace (ι ⊕ κ) ≃L[ℝ] StdSpace ι × StdSpace κ`
  exists in *Standard model*'s files (merged, #232), and this part uses it:
  `LinearAlgebra/Symplectic/Standard/Basic.lean` has the equivalence, with
  `sumEquiv_def`, the `@[simp]` lemmas `x_sumEquiv_fst`, `y_sumEquiv_fst`,
  `x_sumEquiv_snd`, `y_sumEquiv_snd`, `x_sumEquiv_symm`, `y_sumEquiv_symm`,
  and `isSymplectomorphism_sumEquiv` (it carries `stdForm (ι ⊕ κ)` to
  `(stdForm ι).prod (stdForm κ)`); `.../Standard/Matrix.lean` has
  `StdSpace.sumEquiv_toEuclideanLin_symplecticSum`, which conjugates
  `Matrix.toEuclideanLin (Matrix.symplecticSum A B)` to the product of the
  maps of `A` and `B`. `IsSymplecticFrameOn.stdSum` and
  `frameTransition_stdSum` rest on these two lemmas.

Tau Ceti's topological Whitney sum `TauCeti.FiniteRankBundleCore.whitneySum`
is not used; `whitneySumTotalSpaceHomeomorph` compares the total spaces
where needed.

### Rank two and area forms

- `Symplectic/Basic.lean`:
  `ContMDiffTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`:
  for `finrank ℝ F = 2`, `ω.IsNondegenerate ↔ ∀ x, ω x ≠ 0`. The fibres have
  dimension two (they are linearly equivalent to `F` by a trivialization),
  and the proof is the pointwise step of Tau Ceti's
  `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`
  (`Geometry/Symplectic/Manifold/Surface.lean`), Tau Ceti's
  `LinearMap.BilinForm.IsAlt.nondegenerate_iff_ne_zero_of_finrank_eq_two`
  (`LinearAlgebra/BilinearForm/SymplecticBasis.lean`).
- The tangent bundle of a surface with an area form needs no definition: for
  `σ : TauCeti.SmoothTwoForm I S` that vanishes nowhere on a manifold whose
  model space has dimension two, the symplectic bundle is
  `TangentSpace I` with `tangentEquiv.symm σ`, nondegenerate by
  `isNondegenerate_tangentEquiv_iff` and Tau Ceti's lemma above. The
  orientation it induces is Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation` with `n = 1`; no
  second name is introduced.
- `Geometry/Symplectic/Manifold/Volume.lean`, in Tau Ceti's namespace
  because it is about Tau Ceti's notions only:
  `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg`: for odd `n`
  and `hn : finrank ℝ E = 2 * n`, `h.neg.volumeOrientation hn =
  -h.volumeOrientation hn`, with Tau Ceti's `IsNondegenerate.neg` and the
  negation of `Manifold.Orientation`. The volume form of `-σ = (-1) • σ` is
  $(-1)^n$ times that of `σ` by Tau Ceti's `TauCeti.SmoothTwoForm.volumeForm_smul`
  (same file) with `c = -1`, so no separate `volumeForm_neg` is added, and
  `Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff` turns
  the sign of the form into the sign of the orientation at each point.
  *First Chern number* plans `volumeOrientation_eq_ofTopForm` for the same
  file; the two issues do not depend on each other.

### Hermitian bundles

The one representation of a Hermitian bundle in this part, used by
`Hermitian/Basic.lean` and `Hermitian/Surface.lean`, and by the users of
`Hermitian/CircleBundle.lean` (whose results are stated more generally,
for fibres with their own complex inner products; see its section), is
Tau Ceti's of
`Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean` and
`Riemannian/Hermitian.lean`:

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousConstSMul ℂ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance : VectorBundle ℝ F V := VectorBundle.restrictScalars ℝ ℂ F V
local instance : FiniteDimensional ℝ F := Module.Finite.trans ℂ F

variable [ContMDiffVectorBundle n F V I]
  (g : Bundle.ContMDiffRiemannianMetric I n F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
```

A Hermitian line bundle is the case `finrank ℂ F = 1`. The metric is a real
one, invariant under `Complex.I`; its Hermitian product at `x` is Tau Ceti's
`g.complexInnerProductSpace hI x` (conjugate-linear in the first argument,
as in Mathlib). No structure bundles `g` and `hI`, as in Tau Ceti; Tau Ceti's
`exists_contMDiffRiemannianMetric_inner_smul_I` gives such a pair over a
Hausdorff σ-compact base.

- `ComplexStructure.lean`: `ContMDiffComplexStructure.ofComplexModule I n F V`,
  multiplication by `Complex.I` on any complex bundle (no metric), whose
  endomorphism section is Tau Ceti's `contMDiff_smulIEquiv_bundle`
  (`Geometry/Manifold/VectorBundle/Complexification.lean`). API:
  `@[simp] ofComplexModule_toEndomorphism`, `ofComplexModule_apply`
  (`Complex.I • v`, which `simp` proves) and
  `@[simp] almostComplexStructureAt_ofComplexModule` (Tau Ceti's
  `AlmostComplexStructure.ofComplexModule (V x)`), so that its
  `toContinuousComplexStructure` gives back the complex structure of `V`.
- `Hermitian/Basic.lean`, namespace
  `SymplecticGeometry.Bundle.ContMDiffComplexStructure`: the form of the
  Hermitian bundle is no new definition. It is
  `(ofComplexModule I n F V).compatibleForm g : ContMDiffTwoForm I n F V`,
  the form $\omega_{g,J}$ of *Tame and compatible pairs* for $J$ the
  multiplication by `Complex.I`. Its value
  $\tfrac12(g_x(iv,w)-g_x(v,iw))$ is $g_x(iv,w)$ once `hI` gives
  $g_x(v,iw)=-g_x(iv,w)$, which is the overview's form. Compatibility with
  `ofComplexModule`, and so nondegeneracy, are `compatible_compatibleForm`
  and `Compatible.isNondegenerate`, and its smoothness is that of
  `compatibleForm`: nothing is proved twice. API, all under `hI`:
  - `compatibleForm_ofComplexModule_apply`: $\omega_x(v,w)=g_x(iv,w)$, and
    `compatibleForm_ofComplexModule_apply_smul_I`, $\omega_x(v,iw)=g_x(v,w)$;
  - `im_inner_eq_compatibleForm_ofComplexModule`: the imaginary part of the
    Hermitian product of `v` and `w` is $\omega_x(v,w)$, from Tau Ceti's
    `Bundle.ContMDiffRiemannianMetric.complexInnerProductSpace_inner`;
  - the standard case, `compatibleForm_ofComplexModule_trivial`: on
    `Bundle.Trivial M (ι → ℂ)`, for any `[Fintype ι]` (the line bundle is
    `ι = Fin 1`; the proof is the same for every `ι`), and for any metric
    `g` with $g_x(u,v)=\langle c\,u,c\,v\rangle$ (hypothesis `hg`), for
    `c = TauCeti.complexToRealEuclidean ι`, such as the constant metric
    `g₀` below, the fibrewise map `c`
    is a symplectic isomorphism from `(ofComplexModule I n _ _).compatibleForm g`
    to `const (stdForm ι)` (`pushforward` of the one is the other). The
    smoothness of `c` on total spaces, which `pushforward` takes, is
    `Bundle.Trivial.contMDiff_totalSpaceMk_clm`, which the issue adds to
    `Geometry/Manifold/VectorBundle/Hom.lean` in the root namespace. The
    proof uses `stdComplexStructure_complexToRealEuclidean`
    (`J₀ (c v) = c (i • v)`), which the issue adds to
    `LinearAlgebra/Symplectic/Standard/Basic.lean`, next to
    `stdComplexStructure_complexEuclideanEquiv`. So
    the sign agrees with *Standard model*, where `stdForm ι z w =
    ⟪J₀ z, w⟫` and `J₀` is multiplication by `Complex.I` moved along
    `complexToRealEuclidean`. Neither Mathlib nor Tau Ceti has a constant
    `ContMDiffRiemannianMetric` on a trivial bundle (Mathlib's instance
    `IsContMDiffRiemannianBundle` for `Bundle.Trivial` is only a `Prop`),
    so the issue builds `g₀` in
    `Geometry/Manifold/VectorBundle/Riemannian/Trivial.lean`:
    `Bundle.ContMDiffRiemannianMetric.const b hb hpos`, in the root namespace
    since it is about Mathlib's type alone, for a symmetric positive
    definite `b : W →L[ℝ] W →L[ℝ] ℝ` on a finite-dimensional normed space
    `W`, on `Bundle.Trivial M W`, with `@[simp] const_inner`. It is the
    structure `{ inner := fun _ ↦ b, symm := fun _ ↦ hb, pos := fun _ ↦ hpos,
    isVonNBounded := fun _ ↦ b.isVonNBounded_setOf_lt_one_of_pos hpos,
    contMDiff := contMDiff_const_bundlePairing b }`: the last two fields are
    Tau Ceti's `ContinuousLinearMap.isVonNBounded_setOf_lt_one_of_pos`
    (`Topology/Algebra/Module/BilinearForm.lean`) and
    `TauCeti.contMDiff_const_bundlePairing`
    (`Geometry/Manifold/VectorBundle/Hom.lean`). Then `g₀` is the case
    `b = (innerSL ℝ).bilinearComp c c`, in the same file:
    `Bundle.ContMDiffRiemannianMetric.constComplexEuclidean ι`, with
    `@[simp] constComplexEuclidean_inner` ($g_0(u,v)=\langle c\,u,c\,v\rangle$),
    and the standard case for it is
    `compatibleForm_ofComplexModule_constComplexEuclidean`, where `hg` is
    `constComplexEuclidean_inner`. They are candidates for Mathlib.

### The circle bundle of a Hermitian line bundle

`Hermitian/CircleBundle.lean`, namespace `SymplecticGeometry.Bundle`,
except for the lemmas that dot notation on a Tau Ceti or Mathlib type finds,
which sit in that type's namespace (below).

**Hypotheses.** The file does not mention `g` or `hI`. Its fibres carry
their own norms and complex inner products, as in Tau Ceti's
`OrthonormalFrameBundle`:

```lean
variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℂ F E]
  [Fact (Module.finrank ℂ F = 1)]
```

and the principal `Circle`-bundle adds `[TauCeti.ContinuousFiberNorm F E]`,
which is what Tau Ceti's `OrthonormalFrameBundle.instPrincipalBundleFiber`
asks for. Each declaration takes only the instances it uses: the action of
`Circle` on unit vectors needs only normed fibres, and its freeness no
bundle structure at all. The dimension of a fibre comes from Mathlib's
`VectorBundle.finrank_eq`. Nothing smooth is assumed, and the base is
arbitrary, with or without boundary.

A Hermitian line bundle `(g, hI)` of *Hermitian bundles* above is a special
case. With the variables of that section and `[Fact (finrank ℂ F = 1)]`,
the results apply after three local instances, in this form (checked to
elaborate against the merged file):

```lean
letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
letI : IsContinuousRiemannianBundle F V :=
  instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
```

The third gives `ContinuousFiberNorm F V` through Tau Ceti's instance for
continuous Riemannian bundles; its type has to be written out, or instance
search does not find `ContinuousFiberNorm`. The smooth structure on the
circle bundle needs more: the hypotheses of Tau Ceti's
`sphereBundleChartedSpace` and `isManifold_sphereBundle`. Three of these come
with the variables of *Hermitian bundles*: `[IsManifold I n M]`, which
follows from `[IsManifold I ∞ M]`, `[ContMDiffVectorBundle n F V I]`, and
`[FiniteDimensional ℝ F]`, the local instance `Module.Finite.trans ℂ F`
(instance search does not find it alone, since Mathlib's
`FiniteDimensional.complexToReal` goes through `Module.complexToReal`). The
rest, `[I.Boundaryless]`, `[FiniteDimensional ℝ EB]`,
`[IsContMDiffRiemannianBundle I n F V]` (a local instance from the
smoothness of `g`) and `1 ≤ n`, are stated only where that atlas is used, in
*First Chern number*'s prerequisite 3.

**Contents.**

- The circle bundle is the subtype `{p : TotalSpace F E // ‖p.snd‖ = 1}`,
  on which Tau Ceti's `sphereBundleChartedSpace` and
  `isManifold_sphereBundle` (`Riemannian/Sphere.lean`, radius `1`) put the
  smooth structure. Tau Ceti's set `TauCeti.sphereBundle F E` has the same
  condition (`TauCeti.mem_sphereBundle`), so its lemmas are used through
  `Homeomorph.setCongr`; no second circle bundle type is introduced.
- The action of `Circle` on the subtype by scalar multiplication in the
  fibres: the instance `instMulActionCircleBundle`, with
  `@[simp] circleBundle_smul_apply`; freeness, the iff
  `@[simp] circleBundle_smul_eq_iff` (`z • p = w • p ↔ z = w`); the orbits
  are the fibres, `exists_circleBundle_smul_eq_iff`
  (`(∃ z, z • p = q) ↔ p.val.proj = q.val.proj`, in rank one); and
  continuity, the instance `instContinuousSMulCircleBundle`.
- The principal-bundle form is Tau Ceti's rank-one unitary frame bundle
  `OrthonormalFrameBundle.Fiber ℂ F E ℂ` (fibre `ℂ ≃ₗᵢ[ℂ] E x`), a principal
  bundle for `unitary (ℂ →L[ℂ] ℂ)` by `instPrincipalBundleFiber`.
  `circleBundleHomeomorph` is the homeomorphism from its total space to the
  subtype, `φ ↦ ⟨x, φ.frame 1⟩`, whose inverse sends a unit vector `v` to
  the frame `z ↦ z • v`, built with `LinearIsometryEquiv.toSpanSingleton`
  (below). API: `@[simp] circleBundleHomeomorph_apply`,
  `proj_circleBundleHomeomorph_symm` and
  `@[simp] circleBundleHomeomorph_symm_apply_frame`.
- **The intertwining is stated fibre by fibre**, in the form that
  `Bundle.Trivialization.IsEquivariant` uses, and not with the right action
  on the total space: with frame domain `ℂ`, instance search for Tau Ceti's
  total-space action `Bundle.TotalSpace.instSMul` times out.
  `circleBundleHomeomorph_smul (u : unitary (ℂ →L[ℂ] ℂ)) (φ : Fiber ℂ F E ℂ x)`
  says that `circleBundleHomeomorph ⟨x, op u • φ⟩` is
  `Unitary.continuousLinearMapCircleEquiv u • circleBundleHomeomorph ⟨x, φ⟩`.
- The right action of `Circle` on frames, the instance
  `instMulActionCircleFiber : MulAction Circleᵐᵒᵖ (Fiber ℂ F E ℂ x)`, is that
  of `unitary (ℂ →L[ℂ] ℂ)` along the inverse of
  `Unitary.continuousLinearMapCircleEquiv`. Its lemmas are in Tau Ceti's
  namespace `TauCeti.OrthonormalFrameBundle.Fiber`, next to
  `Fiber.frame_smul_apply`: `op_circle_smul_eq` (by `rfl`) and
  `@[simp] frame_op_circle_smul_apply` (`(op z • φ).frame v =
  φ.frame (z * v)`). The **equivariance** of the homeomorphism is
  `circleBundleHomeomorph_op_circle_smul (z : Circle) (φ : Fiber ℂ F E ℂ x)`:
  `circleBundleHomeomorph ⟨x, op z • φ⟩ = z • circleBundleHomeomorph ⟨x, φ⟩`.
- The principal `Circle`-bundle. Both instances on
  `TotalSpace Circle (Fiber ℂ F E ℂ)` come from the general change of model
  fibre and of structure group, applied to
  `Unitary.continuousLinearMapCircleEquiv`:
  `instFiberBundleCircleFiber : FiberBundle Circle (Fiber ℂ F E ℂ)` is
  `FiberBundle.changeModelFiber`
  (`Topology/FiberBundle/ChangeModelFiber.lean`), and
  `instPrincipalBundleCircleFiber : TauCeti.PrincipalBundle Circle
  (Fiber ℂ F E ℂ)` is `TauCeti.PrincipalBundle.changeGroup`
  (`Topology/FiberBundle/Principal/ChangeGroup.lean`). These constructions
  take as instance arguments the topology on the new total space and the
  action of `Circle` on frames, so the file supplies
  `instTopologicalSpaceTotalSpaceCircleFiber`, the topology induced along
  `Bundle.TotalSpace.modelFiberEquiv`, and `instMulActionCircleFiber`
  (above). Their hypotheses, that `Bundle.TotalSpace.modelFiberEquiv` is
  inducing and that the action of `Circle` is that of
  `unitary (ℂ →L[ℂ] ℂ)` through the isomorphism, then hold by `rfl`. The
  trivializations are those of `instPrincipalBundleFiber` read through the
  isomorphism by `Bundle.Trivialization.changeModelFiber`, and no
  trivialization or total-space equivalence specific to `Circle` is
  defined. *First Chern number* uses both instances.
- The smooth side (smoothness of the action and of the coordinate changes,
  the diffeomorphism onto the submanifold, and the submersion, which comes
  from Tau Ceti's `TauCeti.ManifoldTotalSpace.isSubmersion_proj`) belongs to
  *First Chern number*'s prerequisite 3, in this file.

**Placement.** Everything the file has now is topological, but the file
stays in `Geometry/Manifold/VectorBundle/Hermitian/` and does not move to
`Topology/VectorBundle/`. *First Chern number*'s prerequisite 3 adds the
smooth side of the same circle bundle (`circleBundleDiffeomorph` and the
smooth principal bundle) to this file, and that side needs manifolds; the
circle bundle stays one topic in one file, with the other Hermitian files.
The parts that involve no bundle at all have their own files, by topic:
`Unitary.continuousLinearMapCircleEquiv` and
`LinearIsometryEquiv.toSpanSingleton`, below.

- `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean`, in Mathlib's
  namespace `Unitary`, for `RCLike 𝕜`:
  `Unitary.continuousLinearMapSelfEquiv 𝕜 : unitary (𝕜 →L[𝕜] 𝕜) ≃ₜ* unitary 𝕜`,
  whose `MulEquiv` is by definition
  `((TauCeti.StrongUnitary.unitaryEquivStrongUnitary 𝕜).toMulEquiv.trans
  TauCeti.StrongUnitary.mulEquivUnitary).symm`
  (`Unitary.toMulEquiv_continuousLinearMapSelfEquiv`, by `rfl`), so that the
  library has one identification of the two groups. Tau Ceti's topology on
  `StrongUnitary` is the strong operator topology and the frame bundle's on
  `unitary (𝕜 →L[𝕜] 𝕜)` the norm topology, so the new content is continuity
  for the norm in both directions, by `continuous_eval_const 1` and
  `continuous_id.smul continuous_const` as in Tau Ceti's proof. API, both
  `@[simp]`: `Unitary.coe_continuousLinearMapSelfEquiv_apply`
  (`(u : 𝕜 →L[𝕜] 𝕜) 1`) and `Unitary.continuousLinearMapSelfEquiv_symm_apply`
  (`α` acts by `x ↦ α * x`).
  The case `𝕜 = ℂ` composed with Tau Ceti's
  `TauCeti.circleEquivUnitary : Circle ≃ₜ* unitary ℂ`
  (`Analysis/Complex/Circle.lean`) is the isomorphism of structure groups
  of the circle bundle, in the same file and namespace:
  `Unitary.continuousLinearMapCircleEquiv : unitary (ℂ →L[ℂ] ℂ) ≃ₜ* Circle`,
  by definition
  `(continuousLinearMapSelfEquiv ℂ).trans circleEquivUnitary.symm`
  (`continuousLinearMapCircleEquiv_def`, by `rfl`), so that the library has
  one identification of the two groups. API, both `@[simp]`:
  `Unitary.coe_continuousLinearMapCircleEquiv_apply` (`u 1`) and
  `Unitary.continuousLinearMapCircleEquiv_symm_apply` (`z` acts by
  `v ↦ z * v`).
- `Analysis/Normed/Operator/SpanSingleton.lean`, in Mathlib's namespace
  `LinearIsometryEquiv`: for a seminormed space `E` over a nontrivially
  normed field `𝕜` with `h : finrank 𝕜 E = 1` and a unit vector `v`
  (`hv : ‖v‖ = 1`), `LinearIsometryEquiv.toSpanSingleton 𝕜 E h hv :
  𝕜 ≃ₗᵢ[𝕜] E`, `a ↦ a • v`, the equivalence that Mathlib's
  `LinearIsometry.toSpanSingleton` becomes when `E` is a line. It is the
  inverse of `circleBundleHomeomorph` on each fibre. API:
  `@[simp] toSpanSingleton_apply`, `@[simp] toLinearIsometry_toSpanSingleton`
  and `toSpanSingleton_one`. Mathlib's `LinearIsometryEquiv.toSpanUnitSingleton`
  is different: its target is the submodule `𝕜 ∙ v`.

## Unitary frames over surfaces with boundary

`Hermitian/Surface.lean`. The surface is `S` with `[ChartedSpace
(EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S] [CompactSpace S]
[ConnectedSpace S] [T2Space S]` and `hS : ((𝓡∂ 2).boundary S).Nonempty`. The
Hermitian bundle is in the one representation of *Hermitian bundles* above,
over `S` with `I = 𝓡∂ 2` and `n = ∞`: `g : Bundle.ContMDiffRiemannianMetric
(𝓡∂ 2) ∞ F V` and `hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) =
g.inner x v w`. The theorem uses neither the form of a Hermitian bundle
nor the circle bundle, so this issue does not wait for theirs.

```lean
theorem Bundle.ContMDiffRiemannianMetric.exists_orthonormal_contMDiffSection_of_boundary_nonempty
    (g) (hI) {k : ℕ} (hk : finrank ℂ F = k) :
    ∃ s : Fin k → ∀ x, V x,
      (∀ i, ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod 𝓘(ℝ, F)) ∞ (fun x ↦ (⟨x, s i x⟩ : TotalSpace F V))) ∧
      letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
      letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
      ∀ x, Orthonormal ℂ fun i ↦ s i x
```

the form of Tau Ceti's `exists_orthonormal_contMDiffSection_of_finrank_lt`.
The plan states the milestone as a trivialization, so a corollary gives it in
that form: `Bundle.ContMDiffRiemannianMetric.exists_unitary_trivialization_of_boundary_nonempty`, for a
`ℂ`-basis `b : Basis (Fin k) ℂ F`, a trivialization in the smooth maximal
atlas with base set `univ` whose fibre map at each `x` sends the frame to
`b` and so is a `ℂ`-linear isometry from `(V x, g x)` to `F` with the
inner product that makes `b` orthonormal. It is Tau Ceti's
`IsLocalFrameOn.trivialization` and `trivialization_mem_maximalAtlas`
(`Geometry/Manifold/VectorBundle/FrameTrivialization.lean`) for the real
frame $(s_i, i\,s_i)_i$ and the real basis $(b_i, i\,b_i)_i$ of `F`, with
Mathlib's `basisOfOrthonormalOfCardEqFinrank` at each point. The docstring
of the corollary ends with the line Milestone: *Unitary trivializations over
surfaces with boundary*. It keeps the connectedness that
the plan adds to the book, and drops orientability, which the proof below
does not use; this is a generalization, not an error, so `ERRATA.md` gets no
entry.

The frame theorem is the case `n = 0`, `r = 0` of the public
`exists_orthonormal_contMDiffSection_of_boundary_nonempty_of_le`: `k`
orthonormal sections of a bundle of complex rank `k + r` over a compact
connected `M` modelled on `𝓡∂ (n + 2)`, with nonempty boundary and
`n + 2 ≤ 2 * (r + 1)`, the analogue of Tau Ceti's theorem. Two steps that
need no boundary are public in `Hermitian/Frame.lean`, for any model:
`contMDiff_and_orthonormal_vecCons_of_mem_orthogonalSpanFamily` (normalize a
nowhere-zero section of `g.orthogonalSpanFamily hI s` and put it in front of
`s`) and `exists_unitary_trivialization_of_orthonormal` (the frame
trivialization of `TauCeti.complexDoubledFrame s` over an open `U`).

**Route.** The book cuts the surface along curves, by induction on the genus
and the number of boundary components; that requires knowing how every
compact bordered surface is built from pieces. Neither library has this,
and the library does not prove it: the following route needs only results
that Tau Ceti has or nearly has.

1. *A nowhere-zero section.* Every smooth real bundle of rank at least $2$ over
   `S` has a smooth nowhere-zero section. Take a generic section on the
   interior $\mathring\Sigma$. For rank above $2$ it has no zero at all (Tau
   Ceti's `ContMDiffSection.mem_residual_setOf_affineFamily_ne_zero`); for
   rank $2$ its zero set is closed and discrete (issue 14), so finite on a
   compact $K\subset\mathring\Sigma$ that the collar push of issue 13 maps
   `S` into. $\mathring\Sigma$ minus the other zeros is connected (issue 12
   and Tau
   Ceti's `isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`), so a
   compactly supported diffeotopy (Tau Ceti's
   `exists_diffeotopy_final_comp_eq_of_isPreconnected`,
   `Geometry/Diffeomorphism/Diffeotopy/Configuration.lean`) moves these
   finitely many zeros out of $K$, into the collar. Composing the inverse of
   its final map with the collar push gives a map $h:\Sigma\to\Sigma$
   homotopic to the identity along which the section has no zero, so
   $h^*E\cong E$ (Tau Ceti's
   `ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`) has a
   continuous nowhere-zero section; it is smoothed by issue 15's lemma.
   Connectedness enters here: every component of the interior must reach the
   boundary.
2. *Induction.* As in the proof of Tau Ceti's
   `exists_orthonormal_contMDiffSection_of_finrank_lt`: the Hermitian
   orthogonal complement of the sections chosen so far is a smooth complex
   bundle of positive rank (`orthogonalSpanFamily`,
   `hasLocalContMDiffSubbundleFrames_orthogonalSpanFamily`,
   `Geometry/Manifold/VectorBundle/Riemannian/OrthogonalComplement.lean`,
   for any model with corners), so of real rank at least $2$; step 1 gives a
   nowhere-zero section, which is normalized and appended.

Lemma 2.6.6 of the book (unitary frames along a curve with given ends) is not
needed on this route and is not proved here; if *First Chern number* needs
it, its design adds it.

## What the part uses

- **Tau Ceti:** the $TM$ versions it generalizes (`ContMDiffAlmostComplexStructure`,
  `SmoothAlmostComplexStructure.frameTopology`, `SmoothTwoForm.Tames`,
  `Compatible`, `IsNondegenerate.polarComplexStructure`, `Compatible.cayleyPath`),
  `ContMDiffSection.frameTopology` with `frameTopology_eq_of_covers`,
  `ContMDiffRiemannianMetric.frameTopology`, `nonempty_contMDiffRiemannianMetric`,
  `exists_contMDiffRiemannianMetric_inner_smul_I`, the linear Cayley transform
  (`cayleyPathFormula` and its unit lemmas), `SymplecticForm.polarComplexStructure`,
  `ContinuousComplexStructure`, `bundleDiffeomorph`, `contMDiff_bundle_symm`,
  transport of sections (`ContMDiffSection.mapLinearMap`, `mapEquiv`),
  `SmoothForm.toContMDiffSection` and `ofContMDiffSection`, smooth Gram–Schmidt,
  frame trivializations, orthogonal complements in Hermitian bundles,
  generic sections (`Section/Generic.lean`, `Section/Parametric.lean`),
  diffeotopies of configurations, topological collars
  (`isCollared_subtypeVal_boundary_of_compactSpace`, `collarPart`,
  `IsCollar.collarCoord`), homotopy invariance of
  pullbacks, and vector-space charts for boundaryless manifolds
  (`Geometry/Manifold/ModelTransport/`); for the constructions, pull-backs of
  sections and their smoothness criteria (`ContMDiffSection.pullback`,
  `Bundle.Pullback.contMDiff_hom_section_iff`, `contMDiff_fiberwise`,
  `idDiffeomorph`, `compDiffeomorph`), the product criterion of
  `Geometry/Manifold/VectorBundle/Prod.lean`,
  `contMDiffAt_continuousAlternatingMap_bundle_of_bilinear`, the linear
  `SymplecticForm.prod` and `AlmostComplexStructure.prod` with their tame and
  compatible lemmas, `GLSymplectic.sum` and `maslovIndex_sum`,
  `contMDiff_smulIEquiv_bundle`,
  `complexInnerProductSpace`, the sphere bundle, the orthonormal frame bundle
  with its principal-bundle instance, `circleEquivUnitary`, the one-dimensional
  `StrongUnitary` isomorphisms, the symplectic orientation
  `IsNondegenerate.volumeOrientation` with `volumeForm_smul`, and
  `TauCeti.contMDiffAt_hom_bundle_iff`, `ContMDiffAt.clm_bundle_inverse` and
  `ContMDiffAt.clm_bundle_comp` for transition maps.
- **Mathlib:** smooth vector bundles, the bundles of linear and alternating
  maps, `ContMDiffSection`, `IsLocalFrameOn`, `Bundle.ContMDiffRiemannianMetric`,
  manifolds with boundary (`ModelWithCorners.interior`, `boundary`),
  `ContractibleSpace`, `ContinuousMap.HomotopyEquiv`, and smooth approximation
  (`exists_contMDiffMap_forall_mem_convex_of_local` and its section
  version `exists_contMDiffSection_forall_mem_convex_of_local`); for the
  constructions, `EuclideanSpace.sumEquivProd`,
  `LinearIsometryEquiv.piLpCongrLeft`.
- **Other parts.** *Linear Moser* (part 10) for the complex-to-symplectic
  direction of the classification, with the parametric smoothness of issue 10.
  *Standard model* for the corollary on `Matrix.symplecticGroup`, for
  `stdForm` and `complexToRealEuclidean` in the standard Hermitian case, and
  for `StdSpace.sumEquiv` with its two lemmas, which exist (#232).
  *Symplectic neighbourhoods* for the instance of
  `Geometry/Manifold/IsManifold/Basic.lean` giving `C^(m + 1)` structures
  from `C^∞` ones, in
  `Geometry/Manifold/VectorBundle/Pullback.lean`. *Liouville structures* for
  `Geometry/Manifold/ModelTransport/InteriorModel.lean` (the interior re-modelled
  over `E`, `SymplecticGeometry.InteriorModel`), in
  `Section/Nonvanishing.lean`. The
  part uses nothing from *Compatible complex structures* (part 9) beyond what
  Tau Ceti already has: the fibrewise constructions it needs (the Cayley path,
  $J_{g,\omega}$, $\omega_{g,J}$, the complex-linear part) are Tau Ceti's
  linear ones or explicit formulas. There are two exceptions. The first is
  the polar formula on the bundle of bilinear forms (`polarFormulaDomain`,
  `polarFormulaAt` and `contMDiffOn_polarFormulaAt`), from which both the
  smoothness of `polarComplexStructure` and `polarEndAt` with its
  smoothness are derived. It uses part 9's
  `Analysis/InnerProductSpace/Symplectic/PolarComplexStructure/Smooth.lean`
  (`TauCeti.polarDomain`, `isOpen_polarDomain`, `mem_polarDomain_iff`,
  `TauCeti.metricPolarFormula`, `contDiffOn_metricPolarFormula`,
  `metricPolarFormula_conj`, `metricPolarFormula_eq`) and
  `metricPolarComplexStructure_transport` and
  `metricPolarComplexStructure_innerSL` from its `Basic.lean`: part 9
  states the smoothness of the formula publicly, where Tau Ceti's is
  private, and building on it means that the chart argument is made once,
  in `contMDiffOn_polarFormulaAt`, instead of once along a section for
  $J_{g,\omega}$ and again on the endomorphism bundle for `polarEndAt`, and
  that Tau Ceti's private `contMDiffAt_metricChangeTransport_mul_mul_sqrt`
  is not copied. The cost is that issue 6 waits for part 9's building
  issues 4 and 5, which have no blocker outside part 9. The second is
  `cayleyPathDomain`, the one set from which the open set `O` of both
  Cayley paths, the fixed-form contraction and the homotopy equivalence, is
  taken, which uses part 9's
  `Geometry/Symplectic/Cayley/Domain.lean` (`cayleyDomain`,
  `isOpen_setOf_forall_Icc_mem_cayleyDomain`,
  `Compatible.mem_cayleyDomain`), so that the units, the compactness of
  $[0,1]$ and the two Tau Ceti unit lemmas are handled there once. It makes
  issue 7 wait for part 9's building issue 6, which has no blocker. So issues 6 and 7
  wait for part 9, and issue 8 through them. The straight line on forms of
  the homotopy equivalence needs nothing from part 9: its nondegeneracy
  comes from `convex_setOf_tames` (see `tames_lineMap_compatibleForm`), not
  from a fibrewise `TauCeti.SymplecticForm.Tames.lineMap`.

## Building issues

Each is a few hundred lines; a blocker given by number alone is an issue of
this list, and a blocker from another part is named with its part and its
design file (only issues 6, 7 and 8 have one). An issue may start once its
blockers are merged. Issues 1, 3, 4, 10, 12–15, 18, 23 and 24 can start at
once. Issues 1–17 and 27 build the milestones, and issues 18–26 the constructions
of *Constructions* for *First Chern number*.

1. **Complex structures on a bundle.** `ComplexStructure.lean`: the
   structure and its API up to `toContinuousComplexStructure` and
   `continuousEquiv`, `const`, `pushforward`, and `frameTopology` with the
   lemmas listed above. Blockers: none.
2. **Complex structures on the tangent bundle.** `tangentEquiv`,
   `toContinuousComplexStructure_tangentEquiv`, `tangentHomeomorph`, in the
   same file. Blockers: 1.
3. **Two-forms on a bundle.** `Symplectic/Basic.lean`: `ContMDiffTwoForm`,
   `bilinFormAt`, `IsNondegenerate` with its unfolding lemmas,
   `symplecticFormAt`, `isOpen_setOf_nondegenerate`, `flat` with
   `contMDiff_flat`, `const`, `pushforward`, `tangentEquiv` (first checking
   that `SmoothForm.ofContMDiffSection` accepts sections with values in
   `Bundle.Trivial M ℝ x`). Blockers: none.
4. **Continuity of fibrewise maps.** `Section/Topology.lean`:
   `toContMDiffMap` with `toContMDiffMap_apply` and
   `continuous_toContMDiffMap`, `fiberwiseMap`, `fiberwiseMap_apply`,
   `continuous_fiberwiseMap`; and, in `ContMDiffMap/Chart/CodRestrict.lean`,
   `ContMDiffMap.codRestrict` with `coe_codRestrict_apply` and
   `continuous_codRestrict_manifoldWeakWhitney`. Blockers: none. If the
   issue is long, the two helpers (`toContMDiffMap` with its lemmas, and
   `CodRestrict.lean`) become a first issue of their own.
5. **Tame and compatible pairs.** `Symplectic/ComplexStructure/Basic.lean`:
   `Tames`, `Invariant`, `Compatible` with their unfolding lemmas and
   pointwise characterizations, `Tames.pushforward` and
   `Compatible.pushforward`, the $TM$ comparisons, convexity, and
   `compatibleForm` with `compatible_compatibleForm`. Blockers: 1, 2, 3.
6. **The polar complex structure and existence.** In
   `Riemannian/PolarEnd.lean`, `polarFormulaDomain`, `polarFormulaAt` with their
   lemmas and `contMDiffOn_polarFormulaAt`; in the same file as issue 5,
   `IsNondegenerate.mk_flat_mem_polarFormulaDomain` and
   `IsNondegenerate.polarFormulaAt_flat`,
   `IsNondegenerate.polarComplexStructure` with its smoothness, the $TM$
   comparison `polarComplexStructure_tangentEquiv`, and the two
   `exists_compatible`. Blockers: 5, and part 9's building issues 4 and 5
   (`PolarComplexStructure/Basic.lean` and `Smooth.lean` of
   `design/compatible-complex-structures.md`).
7. **Contractibility of tame and compatible structures and forms.**
   `Symplectic/ComplexStructure/Contractible.lean`: the four
   `contractibleSpace_…` theorems; the bundle Cayley lemma
   `ContMDiffAt.cayleyPathFormula_hom_bundle_of_vectorBundle` and
   `cayleyPathDomain` with its lemmas in `VectorBundle/Cayley.lean`;
   and the contractibility of metrics in
   `Riemannian/SectionTopology.lean`. Blockers: 4, 6, and part 9's building
   issue 6 (`Geometry/Symplectic/Cayley/Domain.lean` of
   `design/compatible-complex-structures.md`), for `cayleyPathDomain`.
8. **The homotopy equivalence and the second milestone.**
   `Symplectic/ComplexStructure/Contractible.lean`:
   `exists_homotopyEquiv_polarComplexStructure`, `polarComplexStructure_homotopic`,
   `contractibleSpace_compatible_tames`; in `Riemannian/PolarEnd.lean`,
   `compatibleBilinAt` with `contMDiff_compatibleBilinAt`, `polarEndDomain`
   and `polarEndAt` with their lemmas and `contMDiffOn_polarEndAt`; and, in
   `Symplectic/ComplexStructure/Basic.lean`, `flat_compatibleForm`,
   `mk_mem_polarEndDomain` and `polarEndAt_eq_polarComplexStructure`.
   Blockers: 7, which brings 6 and part 9's building issues 4, 5 and 6
   (`PolarComplexStructure/Basic.lean`, `Smooth.lean` and
   `Geometry/Symplectic/Cayley/Domain.lean` of
   `design/compatible-complex-structures.md`), and 27. The `PolarEnd.lean`
   declarations of this issue and the three `Basic.lean` lemmas are an
   issue of their own (#638), done first, since issue 27 uses
   `compatibleBilinAt`.
9. **Local Darboux frames.** `Symplectic/Trivialization.lean`, as above. The
   frame form `IsNondegenerate.exists_isSymplecticFrameOn`
   comes last. Blockers: 6, 19.
10. **Parametric smoothness of the linear Moser flow.** The solution of the
    linear Moser equation, read in a trivialization, is $C^n$ jointly in the
    time and in a parameter ranging over an open subset $U$ of a normed
    space, for $C^n$ data; and the construction is natural under linear
    isomorphisms. The set must be open: on an arbitrary set, derivatives
    within it need not be unique, and the superposition lemma the proof
    uses (Tau Ceti's `ContinuousMap.contDiffAt_mkD_comp`) needs a
    neighbourhood. Boundary points of the base are handled in the
    *Classification* section, by taking the pair of forms as parameter.
    It is applied to the path $(1-\beta(t))\omega_1'+\beta(t)\omega_2$, with
    $\beta$ = `smoothTransition`, which is nondegenerate at every real time,
    as part 10's hypothesis `hinv` requires. Naturality comes from four
    new lemmas. Their hypotheses on the map follow Mathlib's
    `NormedSpace.map_exp`: a class of bundled morphisms
    (`{F} [FunLike F B C] [AlgHomClass F ℝ B C] (f : F)`) with
    `hf : Continuous f`, so that they apply to an `AlgHom`, an `AlgEquiv`,
    a `ContinuousAlgHom` or a `ContinuousAlgEquiv` without conversion. The
    algebras `B` and `C` are complete normed algebras (`[CompleteSpace B]`,
    `[CompleteSpace C]`), and `p : ℝ → B` is continuous.
    The first, `SymplecticGeometry.map_dysonTerm`, gives
    `f (dysonTerm p n t) = dysonTerm (f ∘ p) n t`, by induction on `n`,
    passing `f`, made a continuous linear map by `hf`, through each
    integral (`ContinuousLinearMap.intervalIntegral_comp_comm`). The second,
    `SymplecticGeometry.map_dysonSeries`, gives
    `f (dysonSeries p t) = dysonSeries (f ∘ p) t`, from the first and
    `ContinuousLinearMap.map_tsum` with `summable_dysonTerm`; Tau Ceti's
    uniqueness lemma `eq_mul_dysonSeries` may give a shorter proof.
    Completeness of `C` cannot be dropped: Mathlib's integral is zero in an
    incomplete space, so there the right side would be `1` for every `t`.
    The third, `SymplecticGeometry.map_dysonSeriesLeft`, is the same
    statement for `dysonSeriesLeft`. It follows from the second through
    `op_dysonSeriesLeft`, applied to Mathlib's
    `AlgHom.op (AlgHom.ofClass f) : Bᵐᵒᵖ →ₐ[ℝ] Cᵐᵒᵖ`, continuous by
    `continuous_op.comp (hf.comp continuous_unop)`. This is why the lemmas
    take a morphism class rather than `B →A[ℝ] C`: Mathlib has no opposite
    of a continuous algebra homomorphism. All three are about Tau Ceti's
    Dyson series alone, so they go in `Analysis/ODE/DysonSeries.lean`, in
    namespace `SymplecticGeometry`, as `DESIGN.md` prescribes for that file
    (dot notation does not reach these functions); all three are
    candidates for Tau Ceti.
    Conjugation by `e : V ≃L[ℝ] W` is the case
    `f = e.conjContinuousAlgEquiv` (Mathlib), where `W →L[ℝ] W` is complete
    since `W` is finite-dimensional. The fourth,
    `moserGenerator_conj`, stays in `LinearMoser.lean`: the generator of the
    forms moved along `e` is `e.conjContinuousAlgEquiv (moserGenerator ω t)`.
    Part 10 (`Geometry/Symplectic/LinearMoser.lean`) proves
    smoothness in time only (`contDiff_dysonSeriesLeft_moserGenerator`), so
    this extends it, after checking Tau Ceti's
    `ODE.exists_contDiffOn_picard_solution` and `contDiff_timeDependentFlow`.
    Blockers: none.
11. **Classification and the first milestone.** `Symplectic/Classification.lean`.
    Blockers: 5, 6, 9, 10.
12. **The interior of a manifold with boundary.**
    `IsManifold/InteriorBoundary.lean`, namespace `ModelWithCorners`:
    `I.interior M` is open (Mathlib's `ModelWithCorners.isOpen_interior`) and
    dense (`ModelWithCorners.dense_interior`); `I.interiorOpens M` is it as an
    `Opens M`, for `[IsManifold I 1 M]`, and the instance
    `ModelWithCorners.BoundarylessManifold.interior` makes it, as
    an open submanifold, boundaryless; this is a few lines from Mathlib's
    `isInteriorPoint_iff_isInteriorPoint_val`, as Mathlib's instance
    `BoundarylessManifold.open` shows. Tau Ceti's `BoundarylessModel` gives
    it charts in the model vector space. For a connected `M` it is connected
    (`ModelWithCorners.isConnected_interior`, and the instance
    `ModelWithCorners.connectedSpace_interiorOpens`), with no hypothesis on
    the dimension, since every point has a neighbourhood whose interior part
    is the image of a convex set in a chart; the topological step,
    `Dense.isPreconnected_of_forall_exists_mem_nhds`, goes in
    `Topology/Connected/Clopen.lean`. Blockers: none.
13. **Pushing into the interior.** `Boundary/Collar/Push.lean`, namespace
    `TauCeti.IsCollar`: for a compact Hausdorff manifold modelled on
    `𝓡∂ (k + 1)` with a collar `hc : IsCollar c` (from Tau Ceti's
    `isCollared_subtypeVal_boundary_of_compactSpace`),
    `IsCollar.exists_homotopy_push`: there are a compact $K\subseteq$
    `I.interior M`, an open subset of the interior disjoint from $K$ and
    nonempty when the boundary is (the image under `c` of the depths in
    $(0,1/2)$, inside `TauCeti.collarPart c (1 / 2)`), and a
    homotopy from the identity to a map with image in $K$. The map raises
    the depth coordinate of `IsCollar.collarCoord (1 / 2)` below $1/2$ to
    $1/2$ (`Boundary/Collar/Deformation.lean`). Blockers: none.
14. **Sections with discrete zeros.** `Section/Generic.lean`, namespace
    `ContMDiffSection`: `exists_mem_span_isClosed_isDiscrete_zero`, over a
    second-countable boundaryless manifold modelled on a finite-dimensional
    space, for a bundle of rank equal to the dimension with a finite spanning
    family of smooth sections (Tau Ceti's `exists_fin_spanning_contMDiffSection`,
    `Section/FiniteSpan.lean`, gives one), a smooth section in their span whose zero set
    is closed and discrete. Tau Ceti has the rest: for larger rank,
    `mem_residual_setOf_affineFamily_ne_zero` gives no zeros at all, and for
    equal rank `mem_residual_setOf_isRegular_affineFamily` with
    `exists_isManifold_sectionZero_of_contMDiff`
    (`Section/SmoothZero.lean`) gives a regular section whose zero set is a
    $0$-dimensional submanifold. The new work is the closed-and-discrete step,
    which the proof of Tau Ceti's `finite_sectionZero_of_contMDiff` contains
    for a compact base, without compactness. Its closedness half,
    `VectorBundle.isClosed_setOf_eq_zero` for a continuous section along a
    map, goes in `Topology/VectorBundle/ZeroSet.lean`. Blockers: none.
15. **Smoothing nowhere-zero sections.** `Section/Nonvanishing.lean`:
    `SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_continuous`,
    a continuous nowhere-zero section of a smooth bundle over a compact
    manifold (with boundary allowed) can be replaced by a smooth one, via
    `exists_contMDiffSection_forall_mem_convex_of_local` and a metric.
    Blockers: none.
16. **Nowhere-zero sections over surfaces with boundary.** Same file: step 1
    of the route above,
    `SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`
    for real bundles of rank at least $2$ over `S`, with its diffeotopy step
    `TauCeti.exists_diffeotopy_apply_one_notMem` in
    `Geometry/Diffeomorphism/Diffeotopy/Discrete.lean`. Blockers: 12, 13, 14, 15.
17. **Unitary frames and the third milestone.** `Hermitian/Surface.lean`:
    the frame theorem and its trivialization corollary, with the two
    general steps they use in `Hermitian/Frame.lean`. Blockers: 16.

18. **Sections of the alternating bundle of a pull-back.**
    `Geometry/Manifold/VectorBundle/Pullback.lean`:
    `Bundle.Pullback.contMDiff_continuousAlternatingMap_section_iff`; and
    `Topology/VectorBundle/Pullback.lean`:
    `ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem`.
    Blockers: none.
19. **Symplectic isomorphisms, frames and forms of rank two.**
    `Symplectic/Basic.lean`: `pushforward_eq_iff`, `IsSymplecticFrameOn` with
    its API and `isSymplecticFrameOn_const`, `frameTransition` with its API
    (`frameTransition_symm` among it),
    and `isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`. Blockers: 3.
20. **Pull-back, direct sum and multiplication by `Complex.I` for complex
    structures.** `ComplexStructure.lean`: `ContMDiffComplexStructure.pullback`,
    `prod` and `ofComplexModule` with their API, and `Bundle.Pullback.eq_iff`
    in `Data/Bundle.lean`, and `Bundle.Pullback.neg_fiber` in
    `Topology/VectorBundle/Pullback.lean`, which `ComplexStructure.lean`
    imports. Blockers: 1.
21. **Pull-backs of symplectic bundles.** `Symplectic/Pullback.lean`:
    `ContMDiffTwoForm.pullback` with its API, `Tames.pullback`,
    `Compatible.pullback`, `pullback_pushforward`, `pushforward_pullback_id`,
    `pushforward_pullback_comp`, `IsSymplecticFrameOn.pullback`,
    `frameTransition_pullback`. Blockers:
    5, 18, 19, 20.
22. **Direct sums of symplectic bundles.** `Symplectic/Prod.lean`, with
    `Bundle.Prod.contMDiff_prodMap`, `Bundle.Prod.contMDiff_swap` and their
    corollaries `Bundle.Prod.contMDiff_prodCongr` and `Bundle.Prod.contMDiff_prodComm`
    in `Geometry/Manifold/VectorBundle/Prod.lean`, using
    the existing `StdSpace.sumEquiv`: `ContMDiffTwoForm.prod` with its API,
    `Tames.prod`, `Compatible.prod`,
    `pushforward_prodCongr`, `pushforward_prodComm`,
    `IsSymplecticFrameOn.prod`, `IsSymplecticFrameOn.stdSum` and
    `frameTransition_stdSum`. Blockers: 5, 19, 20.
23. **The orientation of a negated two-form.**
    `Geometry/Symplectic/Manifold/Volume.lean`:
    `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg`. Blockers:
    none.
24. **Unitaries of `𝕜 →L[𝕜] 𝕜`.**
    `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean`:
    `Unitary.continuousLinearMapSelfEquiv` with its API. Blockers: none.
25. **The symplectic form of a Hermitian bundle.**
    `Riemannian/Trivial.lean`: `Bundle.ContMDiffRiemannianMetric.const` and
    `constComplexEuclidean`; `Bundle.Trivial.contMDiff_totalSpaceMk_clm` in
    `Hom.lean`;
    then `Hermitian/Basic.lean`: the lemmas on
    `(ofComplexModule I n F V).compatibleForm g` and the standard case.
    Blockers: 5, 20.
26. **The circle bundle of a Hermitian line bundle.**
    `Hermitian/CircleBundle.lean`: `circleBundleHomeomorph`, the action of
    `Circle` and the `TauCeti.PrincipalBundle Circle` instance, over any
    base: none of them needs the smooth hypotheses of the sphere-bundle
    atlas, which its section leaves to *First Chern number*. With it,
    `Unitary.continuousLinearMapCircleEquiv` in
    `Analysis/CStarAlgebra/Unitary/ContinuousLinearMap.lean` and
    `LinearIsometryEquiv.toSpanSingleton` in
    `Analysis/Normed/Operator/SpanSingleton.lean`. Blockers: 24.

27. **Continuity of $\omega\mapsto J_{g,\omega}$ and $J\mapsto\omega_{g,J}$.**
    As in *Contractibility and the homotopy equivalence*: in
    `ContinuousAlternatingMap.lean`, `Bundle.flatAt`, `contMDiffAt_sectionAlong_flatAt`,
    `Bundle.alternatingMapOfBilin` and
    `contMDiffAt_sectionAlong_continuousAlternatingMap_of_bilinear`, with the
    two `_apply` lemmas; in `Symplectic/Basic.lean`, `flat_def`,
    with `contMDiff_flat` and `ofBilinearSection` rebuilt on them; in
    `Symplectic/ComplexStructure/Basic.lean`,
    `Bundle.mk_flatAt_mem_polarFormulaDomain`,
    `compatibleForm_eq_alternatingMapOfBilin` and
    `IsNondegenerate.tames_lineMap_compatibleForm`; in `Contractible.lean`,
    `continuous_polarComplexStructure` and `continuous_compatibleForm`.
    Blockers: 4, 6, and the issue split from 8 for its `PolarEnd.lean`
    declarations (#638), for `compatibleBilinAt`.

The issues of *First Chern number* that its design says wait for "the issues
from #57" wait for these: its pull-backs and isomorphisms for 19 and 21, its
direct sums for 22, its area-form tangent bundles for 19 and 23, its
Hermitian line bundles for 25, and its circle bundle (its prerequisite 3)
for 26.

Before each issue, its agent searches Tau Ceti and Mathlib again for the
statements it is to prove, since both move.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.6.
* M. W. Hirsch, *Differential Topology*, GTM 33, Springer, Chapter 2 (the
  compact-open $C^k$ topologies) and Chapter 3 (transversality of generic
  sections).
* M. Brown, *Locally flat imbeddings of topological manifolds*, Ann. of Math.
  75 (1962) (collars).
