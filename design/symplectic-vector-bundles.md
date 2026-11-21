# Design: Symplectic vector bundles

This is the detailed design of part 12 of `DESIGN.md`, *Symplectic vector
bundles*. It fixes the files of the part, its definitions with their
representation and API, the Lean names and statements of its main results,
what it takes from Tau Ceti, Mathlib and the other parts, and the issues that
build it, in an order in which they can be done. It settles the three
questions that `DESIGN.md` leaves to it: the details of
`ContMDiffComplexStructure` and of its subtypes, the form of the spaces of
sections and of the frame covers their topologies use, and the surface
topology that the last milestone needs.

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
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
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
  - local compactness of `EB`: `frameTopology_eq_of_covers` and
    `continuous_fiberwiseMap`;
  - finite rank of the source bundle: each use of `contMDiff_bundle_symm` or
    `contMDiff_hom_bundle_iff` (the `pushforward`s and the classification);
  - finite rank of `F`: `isOpen_setOf_nondegenerate`; every result that
    uses `polarComplexStructure` (`compatible_polarComplexStructure`,
    `polarComplexStructure_tangentEquiv`, `IsNondegenerate.exists_compatible`,
    `exists_homotopyEquiv_polarComplexStructure`,
    `polarComplexStructure_homotopic`, both milestones, and the local
    Darboux frames of issue 9); and each use of Tau Ceti's
    `Tames.isUnit_one_sub_mul` (`Geometry/Symplectic/Cayley/Basic.lean`), in
    the symplectic-to-complex direction of the classification;
  - finite dimension of `EB` and `F`: the existence of bundle metrics, with
    everything that rests on it.
- **No rank hypothesis.** The book takes rank $2n$. No statement here needs
  it: a nondegenerate form or a complex structure forces even rank, and the
  statements are about a given form or structure, or are equivalences between
  spaces that are both empty in odd rank. Rank $0$ is allowed everywhere.
- **Base hypotheses.** Results that need a bundle metric (existence of
  compatible structures, the classification) add `[T2Space M]
  [SigmaCompactSpace M]`, the hypotheses of Tau Ceti's
  `nonempty_contMDiffRiemannianMetric`
  (`Geometry/Manifold/VectorBundle/Riemannian/Existence.lean`). Nothing else
  is assumed of `M`; in particular the boundary may be nonempty, as the first
  milestone allows.
- **Signs.** Tameness and compatibility are Tau Ceti's: $\omega(v,Jv)>0$ for
  $v\ne0$, and $J$-invariance. The form attached to a metric and a complex
  structure is $\omega_{g,J}(u,v)=\tfrac12(g(Ju,v)-g(u,Jv))$, which for the
  Euclidean metric and $J_0$ on `StdSpace ι` is `stdForm ι`; its docstring
  says so, and the first issue that defines it proves that case.

## Files

| File | Content | Issues |
|---|---|---|
| `Geometry/Manifold/VectorBundle/ComplexStructure.lean` | `Bundle.ContMDiffComplexStructure`, its API, transport and topology; the comparison with Tau Ceti on $TM$ | 1, 2 |
| `Geometry/Manifold/VectorBundle/Symplectic/Basic.lean` | `Bundle.ContMDiffTwoForm`, nondegeneracy, transport along bundle isomorphisms, the comparison with `TauCeti.SmoothTwoForm` | 3 |
| `Geometry/Manifold/VectorBundle/Section/Topology.lean` | continuity of fibrewise maps on section spaces | 4 |
| `Geometry/Manifold/VectorBundle/Symplectic/ComplexStructure/Basic.lean` | tame and compatible pairs, $\omega_{g,J}$, the spaces of forms taming a fixed $J$; $J_{g,\omega}$ and existence | 5, 6 |
| `Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean` | contractibility of the space of bundle metrics | 7 |
| `Geometry/Manifold/VectorBundle/Symplectic/ComplexStructure/Contractible.lean` | contractibility for a fixed form or structure, the homotopy equivalence, the second milestone | 7, 8 |
| `Geometry/Manifold/VectorBundle/Symplectic/Trivialization.lean` | local Darboux frames and the reduction of the structure group | 9 |
| `Geometry/Manifold/VectorBundle/Symplectic/Classification.lean` | the first milestone | 11 |
| `Geometry/Manifold/IsManifold/InteriorBoundary.lean` | the interior of a manifold with boundary as a boundaryless manifold | 12 |
| `Geometry/Manifold/Boundary/Collar/Push.lean` | pushing a compact manifold with boundary into its interior | 13 |
| `Geometry/Manifold/VectorBundle/Section/Generic.lean` | sections with closed discrete zero sets over boundaryless manifolds | 14 |
| `Geometry/Manifold/VectorBundle/Section/Nonvanishing.lean` | smoothing nowhere-zero sections; nowhere-zero sections over surfaces with boundary | 15, 16 |
| `Geometry/Manifold/VectorBundle/Hermitian/Surface.lean` | the third milestone | 17 |

Issue 10 (parametric smoothness of the linear Moser flow) goes where part 10,
*Linear Moser*, puts it (`Analysis/ODE/DysonSeries.lean`, as `DESIGN.md`
says), except its lemma `moserGenerator_conj`, which goes in
`Geometry/Symplectic/LinearMoser.lean`. The files
`Analysis/ODE/DysonSeries.lean`, `Section/Topology.lean`, `Section/Generic.lean`,
`Riemannian/SectionTopology.lean`, `IsManifold/InteriorBoundary.lean` and the
folder `Boundary/Collar/` have the names of a Tau Ceti or Mathlib file or
folder at the same place, so that the two merge upstream.

**Departures from `DESIGN.md`.** Each has its reason; #59 brings the overview
in line once this design is merged.

- The overview's `.../Symplectic/ComplexStructure.lean` becomes a folder of
  two files from the start, since its content is more than one file holds.
- The local trivializations move from `Symplectic/Basic.lean` to
  `Symplectic/Trivialization.lean`, since their proof uses $J_{g,\omega}$,
  which is defined after `Basic.lean`.
- Four files are new (`IsManifold/InteriorBoundary.lean`,
  `Boundary/Collar/Push.lean`, `Section/Generic.lean`,
  `Section/Nonvanishing.lean`): they hold the prerequisites of the route to
  the third milestone below, which replaces the book's cutting of the surface.
- The contractibility of bundle metrics sits with Tau Ceti's topology on
  metrics, not in a symplectic file, since it mentions only Mathlib and Tau
  Ceti types.
- Lemma 2.6.6 of the book (unitary frames along curves), which the overview
  puts in `Hermitian/Surface.lean`, is not planned here: the route below does
  not use it. If *First Chern number* needs it, that part's design plans it.
- The surface of the third milestone is not assumed oriented: the route does
  not use an orientation, so the statement is more general.
- The lemma of `Section/Topology.lean` asks for joint $C^n$ regularity in a
  manifold parameter instead of derivatives continuous in the parameter (see
  below), and no issue of this part waits for part 9 (see *What the part
  uses*).

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
  `@[simp] almostComplexStructureAt_toLinearMap` and
  `almostComplexStructureAt_apply`;
- `toEndomorphism_ne_id` and `not_exists_toEndomorphism_eq_id` (for
  `[Nontrivial F]`, and `[Nonempty M]` for the second);
- `ofLE` (forget regularity) with `@[simp] ofLE_toEndomorphism_apply`,
  `ofLE_apply`, `ofLE_refl`, `ofLE_ofLE`, `ofLE_injective`; `Neg` with
  `neg_apply`, `neg_toEndomorphism`, `neg_neg`, `ofLE_neg`;
- **Example.** `const`: for a complex structure `J₀ : TauCeti.AlmostComplexStructure W`
  on a normed space `W`, the constant structure on the trivial bundle
  `Bundle.Trivial M W`, with `@[simp] const_toEndomorphism_apply`; in
  particular the standard one on `Bundle.Trivial M (StdSpace ι)`;
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
  `Φₛ`, which is $C^n$ by Tau Ceti's `ContMDiff.clm_bundle_inverse` (same
  file, no hypothesis on the dimension), with Mathlib's
  `ContinuousLinearMap.isInvertible_equiv` and
  `ContinuousLinearMap.inverse_equiv`, following the proof of
  `contMDiff_bundle_symm`. So `F₂` may have any dimension, as for the
  two-form `pushforward`; nothing about sections is rebuilt;
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
  noncompact base).
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
  alternating bundles; that map and its inverse are $C^n$ on total spaces
  because $\Phi$ is and, by Tau Ceti's `contMDiff_bundle_symm`
  (`Geometry/Manifold/VectorBundle/Hom.lean`), so is $\Phi^{-1}$. Nothing
  about sections is rebuilt. The transport of complex structures,
  `ContMDiffComplexStructure.pushforward`, composes hom-bundle sections
  instead, as its entry above says.
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
  with the unfolding lemmas `tames_iff`, `invariant_iff` and
  `Invariant.apply` ($\omega(Jv,Jw)=\omega(v,w)$), as in Tau Ceti's
  `TwoForm.lean`; `Tames.isNondegenerate`, `Compatible.isNondegenerate`,
  `IsNondegenerate.tames_iff`, `IsNondegenerate.invariant_iff`,
  `IsNondegenerate.compatible_iff` (the pointwise Tau Ceti predicates
  `TauCeti.SymplecticForm.Tames` and `Compatible` on `symplecticFormAt x`
  and `almostComplexStructureAt x`), `Compatible.compatibleAt`; and
  transport along bundle isomorphisms, which moves the form and the structure
  together: `Tames.pushforward` and `Compatible.pushforward`, from
  `ω.Tames J` to `(pushforward Φ hΦ ω).Tames (J.pushforward Φ hΦ)`.
- On $TM$, `tames_tangentEquiv_iff` and `compatible_tangentEquiv_iff`: the
  predicates agree with Tau Ceti's under the two `tangentEquiv`s.
- `convex_setOf_tames J`, `convex_setOf_compatible J`: in the vector space
  `ContMDiffTwoForm I n F V`, the forms taming (compatible with) a fixed `J`
  form a convex set.
- $\omega_{g,J}$: for `g : Bundle.ContMDiffRiemannianMetric I n F V`,
  `ContMDiffComplexStructure.compatibleForm g J : ContMDiffTwoForm I n F V`
  with `compatibleForm_apply` (the formula above) and
  `compatible_compatibleForm`.
- $J_{g,\omega}$: `ContMDiffTwoForm.IsNondegenerate.polarComplexStructure g hω :
  ContMDiffComplexStructure I n F V`, whose value at `x` is Tau Ceti's linear
  `TauCeti.SymplecticForm.polarComplexStructure` of `hω.symplecticFormAt x` for
  the inner product `g x` (`polarComplexStructure_apply`), with
  `compatible_polarComplexStructure`. Its smoothness is proved as Tau Ceti
  proves it for $TM$ in `Geometry/Symplectic/Manifold/AlmostComplex/Polar.lean`,
  which this generalizes; on $TM$, `polarComplexStructure_tangentEquiv` says
  that it is Tau Ceti's `SmoothTwoForm.IsNondegenerate.polarComplexStructure`.
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
  (Φ : P → ∀ x, V x → W x) {O : Set (TotalSpace F V)} (hO : IsOpen O)
  (hΦ : ContMDiffOn (IP.prod (I.prod 𝓘(𝕜, F))) (I.prod 𝓘(𝕜, F')) n
    (fun q : P × TotalSpace F V ↦ TotalSpace.mk' F' q.2.proj (Φ q.1 q.2.proj q.2.snd))
    (univ ×ˢ O))

def fiberwiseMap (p : P) (s : {s : Cₛ^n⟮I; F, V⟯ // ∀ x, ⟨x, s x⟩ ∈ O}) : Cₛ^n⟮I; F', W⟯

theorem continuous_fiberwiseMap [LocallyCompactSpace EB] (hcover) (hcover') :
    letI := frameTopology e U hU; letI := frameTopology e' U' hU'
    Continuous fun q : P × {s // ∀ x, ⟨x, s x⟩ ∈ O} ↦ fiberwiseMap Φ hO hΦ q.1 q.2
```

with `fiberwiseMap_apply`. The proof goes through
`ContMDiffSection.continuous_frameTopology_iff`. The docstring records the
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
  `smoothTransition`. The open set `O` of the lemma is the set of points
  $(x,B)$ of the endomorphism bundle where `1 - J₀ x * B` is a unit and
  `1 - b • cayleyFormula (J₀ x) B` is a unit for every $b\in[0,1]$; it is
  open because units are open and $[0,1]$ is compact. Tau Ceti's
  `Tames.isUnit_one_sub_mul_of_toLinearMap` and
  `Compatible.isUnit_one_sub_smul_cayleyFormula` show that the values of
  every tame `J` lie in it. That the path stays tame, and compatible when `J` is, are Tau
  Ceti's linear lemmas behind `SmoothTwoForm.Compatible.tames_cayleyPath` and
  `compatible_cayleyPath` (`.../AlmostComplex/CayleyPath.lean`), which this
  generalizes. Results: `ContMDiffTwoForm.IsNondegenerate.contractibleSpace_tames`
  and `contractibleSpace_compatible` (`ContractibleSpace {J // ω.Tames J}`,
  resp. `Compatible`, for every covering frame system).
- **Fixed structure, taming and compatible forms.** These sets are convex
  (`convex_setOf_tames`), nonempty (`ContMDiffComplexStructure.exists_compatible`),
  and `frameTopology` is a topological vector space
  (`isTopologicalAddGroup_frameTopology`, `continuousSMul_frameTopology`), so
  Mathlib's `Convex.contractibleSpace` applies: `ContMDiffComplexStructure.contractibleSpace_tames`
  and `contractibleSpace_compatible` for `{ω // ω.Tames J}` and
  `{ω // ω.Compatible J}`. Their docstrings note that a contractible space is
  nonempty, which is the existence half of the milestone.
- **Metrics.** `Bundle.ContMDiffRiemannianMetric.contractibleSpace_frameTopology`,
  from Tau Ceti's `continuous_convexCombination_frameTopology`, over a
  Hausdorff σ-compact base. It mentions only Mathlib and Tau Ceti types, so it
  goes in `Geometry/Manifold/VectorBundle/Riemannian/SectionTopology.lean`,
  the path of the Tau Ceti file that holds that lemma.
- **The homotopy equivalence.** `exists_homotopyEquiv_polarComplexStructure`:
  for a metric `g`,
  `∃ e : {ω // ω.IsNondegenerate} ≃ₕ ContMDiffComplexStructure I n F V,
  ∀ ω, e.toFun ω = ω.2.polarComplexStructure g`, a theorem for each pair of
  covering frame systems. The inverse is $J\mapsto\omega_{g,J}$. On the
  forms, $\omega$ and $\omega_{g,J_{g,\omega}}$ both tame $J_{g,\omega}$, and
  the straight line between them stays nondegenerate. On the structures, $J$
  and $J_{g,\omega_{g,J}}$ are both compatible with $\omega_{g,J}$, and the
  Cayley path between them, with $J_{g,\omega_{g,J}}$ as reference and
  coefficient `smoothTransition t`, is a fibrewise formula in $(t, J_x)$
  that is jointly smooth for every real $t$ on an open set, defined as above
  with $b\in[0,1]$, that contains the values of every complex structure. `polarComplexStructure_homotopic`: for two metrics
  the two maps $\omega\mapsto J_{g,\omega}$ are homotopic, by contracting the
  metrics.
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
  every `x` has an open neighbourhood `W` and sections
  `s : Fin k × Fin 2 → ∀ y, V y` forming a $C^n$ local frame on `W`
  (Mathlib's `IsLocalFrameOn`) that is a Darboux basis of
  `hω.symplecticFormAt y` (Tau Ceti's `TauCeti.SymplecticForm.IsDarbouxBasis`,
  in the book's normalization) at every `y ∈ W`. Route: $J=J_{g,\omega}$ and
  the metric $\omega(\cdot,J\cdot)$; extend a $J_x$-complex basis
  $u_1,\dots,u_k$ of $V_x$ to local sections, and apply Tau Ceti's smooth
  Gram–Schmidt (`Geometry/Manifold/VectorBundle/GramSchmidt.lean`) to
  $u_1,Ju_1,u_2,Ju_2,\dots$; since the metric is $J$-invariant, the output is
  $e_1,Je_1,e_2,Je_2,\dots$, a Darboux frame. No ODE is needed.
- `IsNondegenerate.exists_trivialization_isSymplectomorphism`: for a symplectic
  form `σ` on the model fibre `F`, every point lies in the base set of a
  trivialization in the $C^n$ maximal atlas whose fibre maps carry
  `symplecticFormAt y` to `σ`, built from the frame by Tau Ceti's
  `IsLocalFrameOn.trivialization` (`Geometry/Manifold/VectorBundle/FrameTrivialization.lean`)
  with a Darboux basis of `σ`; and
  `isSymplectomorphism_coordChangeL`: the coordinate changes of two such
  trivializations preserve `σ`, so the structure group reduces to
  $\mathrm{Sp}(F,\sigma)$. For `F = StdSpace (Fin k)` and `σ = stdForm`, the
  matrices of the coordinate changes lie in `Matrix.symplecticGroup` by
  *Standard model*'s `mem_symplecticGroup_iff_isSymplectomorphism`.

## Classification

`Symplectic/Classification.lean`. For two bundles `V₁`, `V₂` over `M`, with
$C^n$ forms and structures `h₁ : ω₁.Tames J₁`, `h₂ : ω₂.Tames J₂`, over a
Hausdorff σ-compact base:

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
  forms and its time derivative, with no metric, so it commutes with the
  coordinate changes of trivializations; that $\Psi_1$ is $C^n$ on the total
  space is then issue 10's parametric smoothness, read in trivializations.

## Unitary frames over surfaces with boundary

`Hermitian/Surface.lean`. The surface is `S` with `[ChartedSpace
(EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S] [CompactSpace S]
[ConnectedSpace S] [T2Space S]` and `hS : ((𝓡∂ 2).boundary S).Nonempty`. A
Hermitian bundle is represented as Tau Ceti does in
`Geometry/Manifold/VectorBundle/Riemannian/LineSplitting.lean`: a complex
vector bundle `[VectorBundle ℂ F V]`, smooth as a real bundle through
`VectorBundle.restrictScalars`, with a metric
`g : Bundle.ContMDiffRiemannianMetric (𝓡∂ 2) ∞ F V` and
`hI : ∀ x v w, g.inner x (I • v) (I • w) = g.inner x v w`.

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
  (`Geometry/Manifold/ModelTransport/`).
- **Mathlib:** smooth vector bundles, the bundles of linear and alternating
  maps, `ContMDiffSection`, `IsLocalFrameOn`, `Bundle.ContMDiffRiemannianMetric`,
  manifolds with boundary (`ModelWithCorners.interior`, `boundary`),
  `ContractibleSpace`, `ContinuousMap.HomotopyEquiv`, and smooth approximation
  (`exists_contMDiffMap_forall_mem_convex_of_local` and its section
  version `exists_contMDiffSection_forall_mem_convex_of_local`).
- **Other parts.** *Linear Moser* (part 10) for the complex-to-symplectic
  direction of the classification, with the parametric smoothness of issue 10.
  *Standard model* only for the corollary on `Matrix.symplecticGroup`. The
  part uses nothing from *Compatible complex structures* (part 9) beyond what
  Tau Ceti already has: the fibrewise constructions it needs (the Cayley path,
  $J_{g,\omega}$, $\omega_{g,J}$, the complex-linear part) are Tau Ceti's
  linear ones or explicit formulas. So none of its issues waits for part 9,
  although `DESIGN.md` lists that part among its prerequisites.

## Building issues

Each is a few hundred lines; the blockers are issues of this list, and an
issue may start once its blockers are merged. Issues 1, 3, 4, 10, 12–15 can start
at once.

1. **Complex structures on a bundle.** `ComplexStructure.lean`: the
   structure and its API up to `toContinuousComplexStructure` and
   `continuousEquiv`, `const`, `pushforward`, and `frameTopology` with the
   lemmas listed above. Blockers: none.
2. **Complex structures on the tangent bundle.** `tangentEquiv`,
   `toContinuousComplexStructure_tangentEquiv`, `tangentHomeomorph`, in the
   same file. Blockers: 1.
3. **Two-forms on a bundle.** `Symplectic/Basic.lean`: `ContMDiffTwoForm`,
   `bilinFormAt`, `IsNondegenerate` with its unfolding lemmas,
   `symplecticFormAt`, `isOpen_setOf_nondegenerate`, `const`, `pushforward`,
   `tangentEquiv` (first checking that `SmoothForm.ofContMDiffSection` accepts
   sections with values in `Bundle.Trivial M ℝ x`). Blockers: none.
4. **Continuity of fibrewise maps.** `Section/Topology.lean`:
   `fiberwiseMap`, `fiberwiseMap_apply`, `continuous_fiberwiseMap`. Blockers:
   none. If the proof is long, split off the chart estimate as a first issue.
5. **Tame and compatible pairs.** `Symplectic/ComplexStructure/Basic.lean`:
   `Tames`, `Invariant`, `Compatible` with their unfolding lemmas and
   pointwise characterizations, `Tames.pushforward` and
   `Compatible.pushforward`, the $TM$ comparisons, convexity, and
   `compatibleForm` with `compatible_compatibleForm`. Blockers: 1, 2, 3.
6. **The polar complex structure and existence.** Same file:
   `IsNondegenerate.polarComplexStructure` with its smoothness, the $TM$
   comparison `polarComplexStructure_tangentEquiv`, and the two
   `exists_compatible`. Blockers: 5.
7. **Contractibility of tame and compatible structures and forms.**
   `Symplectic/ComplexStructure/Contractible.lean`: the four
   `contractibleSpace_…` theorems; and the contractibility of metrics in
   `Riemannian/SectionTopology.lean`. Blockers: 4, 6.
8. **The homotopy equivalence and the second milestone.**
   `Symplectic/ComplexStructure/Contractible.lean`:
   `exists_homotopyEquiv_polarComplexStructure`, `polarComplexStructure_homotopic`,
   `contractibleSpace_compatible_tames`. Blockers: 7.
9. **Local Darboux frames.** `Symplectic/Trivialization.lean`, as above. The
   smooth Gram–Schmidt of Mathlib and Tau Ceti needs a linearly ordered
   index, so the frame is built on `Fin (2 * k)` and reindexed to
   `Fin k × Fin 2`. Blockers: 6.
10. **Parametric smoothness of the linear Moser flow.** The solution of the
    linear Moser equation, read in a trivialization, is $C^n$ jointly in the
    time and in a parameter ranging over a subset of a normed space (the
    chart coordinates of the base point, which may lie on the boundary), for
    $C^n$ data; and the construction is natural under linear isomorphisms.
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
    `I.interior M` is open (Mathlib's `ModelWithCorners.isOpen_interior`), and
    the instance `ModelWithCorners.BoundarylessManifold.interior` makes it, as
    an open submanifold, boundaryless; this is a few lines from Mathlib's
    `isInteriorPoint_iff_isInteriorPoint_val`, as Mathlib's instance
    `BoundarylessManifold.open` shows. Tau Ceti's `BoundarylessModel` gives
    it charts in the model vector space. For a connected `M` with a model of
    positive dimension it is connected (`ModelWithCorners.isConnected_interior`),
    since every boundary point has a neighbourhood whose interior part is
    connected. Blockers: none.
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
    for a compact base, without compactness. Blockers: none.
15. **Smoothing nowhere-zero sections.** `Section/Nonvanishing.lean`:
    `SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_continuous`,
    a continuous nowhere-zero section of a smooth bundle over a compact
    manifold (with boundary allowed) can be replaced by a smooth one, via
    `exists_contMDiffSection_forall_mem_convex_of_local` and a metric.
    Blockers: none.
16. **Nowhere-zero sections over surfaces with boundary.** Same file: step 1
    of the route above,
    `SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`
    for real bundles of rank at least $2$ over `S`. Blockers: 12, 13, 14, 15.
17. **Unitary frames and the third milestone.** `Hermitian/Surface.lean`:
    the frame theorem and its trivialization corollary. Blockers: 16.

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
