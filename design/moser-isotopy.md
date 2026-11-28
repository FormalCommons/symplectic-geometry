# Moser isotopy

This is the detailed design of part 17 of `DESIGN.md`, *Moser isotopy*. It
covers the milestones *Moser stability*, *Relative Moser theorem with
prescribed first derivative*, *Darboux theorem with prescribed derivative*
and *Relative Moser theorem fixing a submanifold* of
`atlas/symplectic-manifolds.md`. They follow McDuff–Salamon
[McDuffSalamon2017], §3.2 (Lemma 3.2.1, Theorem 3.2.2, Corollary 3.2.3,
Theorem 3.2.4 and Exercise 3.2.6), with the stronger first-order
conclusion of the relative theorem from the authors' errata
[McDuffSalamon2019Errata], p. 109, and Cannas da Silva [CannasdaSilva2001Lectures],
Lectures 6–7.

All names below are in the namespace `SymplecticGeometry` unless they are
written with another one. Paths of new files are under `SymplecticGeometry/`.
Tau Ceti paths are relative to `.lake/packages/TauCeti/TauCeti/`, as in
`DESIGN.md`. Throughout, `I : ModelWithCorners ℝ E H` with
`[FiniteDimensional ℝ E]`, `[IsManifold I ∞ M]`, `[I.Boundaryless]`,
`[T2Space M]` and `[SecondCountableTopology M]`, as *Manifolds, families and
signs* says. Each statement drops the instances it does not use. A
submanifold is `f : TauCeti.SmoothEmbedding J I ∞ Q M` with
`J : ModelWithCorners ℝ E' H'`, `[J.Boundaryless]` and `[FiniteDimensional ℝ E']`.
For a form `σ` on `N × M` and `t : N`, *the slice* `σ_t` is
`SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ`,
written out in the Lean statements, as Tau Ceti writes it.

## Decisions

`DESIGN.md` leaves three questions to this file.

- **"Cohomologous".** A family `ω` over $[0,1]$, a smooth two-form on
  `unitInterval × M`, is cohomologous when `ω_t - ω_0 ∈ TauCeti.exactForms I M 2`
  for every `t : unitInterval`. These are Tau Ceti's exact forms
  (`Geometry/Manifold/DeRham/Basic.lean`), the kernel of the map to
  `TauCeti.deRhamCohomology`, so the condition says that the classes
  $[\omega_t]$ are all equal. No predicate is defined for it: the one
  statement that uses it writes it out.
- **The isotopy of embeddings of `Isotopy.lean`.** It is the restriction of a
  compactly supported ambient diffeotopy. The cut-off Moser field of
  `Moser/Field.lean` below is smooth on `ℝ × M` and vanishes outside a
  compact set. Tau Ceti's `TauCeti.timeDependentFlowDiffeotopy` turns it into
  a `TauCeti.Diffeotopy I ∞ M`, and Tau Ceti's `Diffeotopy.smoothIsotopy`
  restricts that to a `TauCeti.SmoothIsotopy` of the inclusion of an open
  set `U ⊇ f(Q)`. The slices of a `SmoothIsotopy` are smooth embeddings
  because they are restrictions of diffeomorphisms
  (`isSmoothEmbedding_diffeomorph_comp`, with Mathlib's
  `Manifold.IsSmoothEmbedding.of_opens`). This file therefore does not use
  `Diffeotopy/Real.lean` of *Smooth families*, and the row of `DESIGN.md` that has
  the part build on *Smooth families* only through `Stability.lean` stays
  as it is. The library states the ambient version as a theorem of its own,
  since *Isotopy extension* needs that version.
- **Non-compact submanifolds.** This part builds no variable-radius
  construction. Tau Ceti's relative Poincaré lemma
  `TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`
  (`Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean`) already
  works for every embedding into a Hausdorff second-countable boundaryless
  manifold, with a compact or non-compact source and a closed or non-closed
  image. Its tube comes from Tau Ceti's tubular neighbourhood theorem. Its
  primitive vanishes along `f(Q)`, and its first jet vanishes where the form
  does. The Moser flow is then not complete. The relative theorem works on
  the open set of points whose trajectory exists up to time one, which is
  the source of Tau Ceti's `TauCeti.timeDependentFlowPartialDiffeomorph`,
  and uses the local versions of Moser's principle
  (`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem`)
  and of the first-jet statement
  (`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`), which need
  no completeness. *Symplectic neighbourhoods* uses the theorem of
  `Relative.lean` and Tau Ceti's tubular neighbourhoods
  (`Geometry/Manifold/TubularNeighborhood/`) directly.

Further choices of this design:

- **The relative theorem has no closedness hypothesis.** The milestone
  assumes a properly embedded submanifold. The proof above does not use
  this, so the library's theorem is stated for every embedded submanifold.
  That is more general than the plan, and needs no entry in `ERRATA.md`.
- **Darboux charts with a prescribed derivative.** These come from Tau
  Ceti's Darboux charts and not from the relative theorem for a point. Take
  a Tau Ceti chart `χ` with `χ p = 0` that pulls some constant form back to
  `ω`. Its derivative at `p` is a linear symplectomorphism. So
  `B := A ∘ (dχ_p)⁻¹` is a linear symplectomorphism, and `B ∘ χ` is a
  Darboux chart with derivative `A` at `p`. The derivative is prescribed
  only at the centre, and only a linear map is composed, so this is the
  milestone with no Moser step. The plan's route through the relative
  theorem is not needed.
- **Fixing a submanifold, with a weaker hypothesis.** The milestone assumes
  a primitive `σ` of `ω₁ - ω₀` with `f^*σ = 0`. The proof needs only
  `f^*ω₁ = f^*ω₀`, together with closedness. Tau Ceti's relative primitive
  then gives, on a tube around `f(Q)`, a primitive that vanishes as a full
  covector along `f(Q)`. This replaces the plan's correction of `σ` by `dF`
  with a function `F` built in tubular coordinates. The general theorem
  takes `f^*ω₁ = f^*ω₀`. The milestone is its corollary in the plan's form,
  since `f^*(dσ) = d(f^*σ) = 0`.
- **Two fields, two time parametrizations.** The relative theorem needs
  only the time-one map. It runs along the path
  $\sigma_0+c(t)(\sigma_1-\sigma_0)$ with `c = Real.smoothTransition`, as
  Tau Ceti's relative theorem does. Then $c(t)\in[0,1]$ for every real
  `t`, so on the open set where the whole segment is nondegenerate every
  slice is nondegenerate. Tau Ceti's public
  `TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`
  then gives a smooth Moser field, and no cutoff is needed. The theorem
  fixing a submanifold needs $\psi_t^*\omega_t=\omega_0$ for every
  $t\in[0,1]$, so it cannot use a time reparametrization that is flat at
  the ends (see *Manifolds, families and signs*). It runs along the path
  with `c = id`, which is nondegenerate only near $[0,1]\times f(Q)$. The
  field is cut off there by a function on `ℝ × M`. That field is
  `moserField` of `Moser/Field.lean`. *Isotopy extension*'s
  `Moser/Family.lean` uses it too, for a general family of two-forms,
  which it takes.
- **Moser stability goes through Tau Ceti's theorem over `ℝ`.** It uses
  `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`, as `DESIGN.md` says.
  The data for that theorem, a family over `ℝ` with symplectic slices and
  primitives of its velocity, come from *Smooth families*.

## Files and their contents

The part owns the folder `Geometry/Symplectic/Moser/`, except
`Moser/Family.lean`, a file of *Isotopy extension*
(`design/isotopy-extension.md`). Tau Ceti has the
files `Geometry/Symplectic/Manifold/Moser.lean` and `RelativeMoser.lean`, so
this library may not have folders with those names. The files outside
that folder have the names of the Tau Ceti files they extend, so that they
can join them. The table is in the order of the paths, and a new file's row
goes in at its place in that order: pull requests that each add a file then
change different lines.

| File | Contents | Issue |
|---|---|---|
| `Geometry/Manifold/ContMDiffMap/Basic.lean` | `ContMDiffMap.comp_mk_apply`, the `@[simp]` value of `g.comp ⟨f, hf⟩` at a point | — |
| `Geometry/Manifold/DifferentialForm/Opens.lean` | restriction of forms along `Subtype.val` to an open subset: surjectivity, regularity, and the exterior derivative; the pull-back of restricted forms along a partial diffeomorphism of open subsets, read in the ambient manifolds as a diffeomorphism between its source and its target (`PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens`) | — |
| `Geometry/Manifold/DifferentialForm/Pullback/Family.lean` | the slices of a reparametrized segment of forms (`SmoothForm.lineMapFamily`), for the underlying rough forms; the slices of a pullback along `Prod.map c f` | — |
| `Geometry/Manifold/DifferentialForm/Smooth.lean` | `TauCeti.SmoothForm.bilinFormAt` of sums, real multiples, zero, negatives and differences of two-forms; `TauCeti.SmoothForm.funSMulₗ` under sums and constants of functions and under pullback | — |
| `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean` | the differential of the inverse of a partial diffeomorphism at a point of its target, as a continuous linear equivalence (`PartialDiffeomorph.mfderivSymmEquiv`) | 5 |
| `Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean` | a primitive of the difference of two closed forms with the same pullback to `f(Q)`, as a smooth form on a tube around `f(Q)` | — |
| `Geometry/Symplectic/Manifold/Darboux.lean` | Darboux charts with prescribed derivative, symplectic transitions, the milestone | 5 |
| `Geometry/Symplectic/Manifold/Family.lean` | openness of nondegeneracy for families and segments of two-forms | 1 |
| `Geometry/Symplectic/Manifold/Flat.lean` | the inverse flat map of a covector field with zero first jet | 1 |
| `Geometry/Symplectic/Manifold/TwoForm.lean` | a smooth map whose differential at a point is a linear symplectomorphism for two nondegenerate two-forms pulls the second back to the first at that point (`TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`) | — |
| `Geometry/Symplectic/Moser/Field.lean` | `moserField`, the cut-off Moser field of a family of two-forms | 3 |
| `Geometry/Symplectic/Moser/Isotopy.lean` | the Moser isotopy fixing a compact submanifold, the milestone | 4 |
| `Geometry/Symplectic/Moser/Relative.lean` | the relative Moser theorem with prescribed first derivative, the milestone | 2 |
| `Geometry/Symplectic/Moser/Stability.lean` | Moser stability, the milestone | 6 |

### `Geometry/Symplectic/Manifold/Family.lean`

The file has the name of Tau Ceti's file on smooth families of nondegenerate
two-forms. It is in the namespace `TauCeti.SmoothTwoForm`.

- `isOpen_setOfPred_isInvertible_flat_mpullback_prodMk`: for a smooth two-form
  `σ` on `N × M`, the set of `p : N × M` at which the slice `σ_{p.1}` has an
  invertible flat map at `p.2` is open. Its proof is the one in Tau Ceti's
  private `exists_isOpen_isInvertible_flat`: the flat maps form a continuous
  section along `Prod.snd` (`contMDiffAt_sectionAlong_flat` with
  `SmoothForm.contMDiff_mpullback_prodMk`), and
  `Continuous.isOpen_setOf_clm_bundle_isInvertible` applies.
- `isOpen_setOfPred_isInvertible_flat_add_smul_sub`: for
  `σ₀ σ₁ : SmoothTwoForm I M`, the set of `p : ℝ × M` at which
  `σ₀ + p.1 • (σ₁ - σ₀)` has an invertible flat map at `p.2` is open. It is
  the previous lemma for `SmoothForm.lineMapFamily σ₀ σ₁ contDiff_id`.
- `isOpen_setOfPred_forall_mem_Icc_nondegenerate`: for `σ₀ σ₁ : SmoothTwoForm I M`,
  the set
  `{x | ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate}`
  is open. The proof starts from
  `isOpen_setOfPred_isInvertible_flat_add_smul_sub` and applies Mathlib's
  `generalized_tube_lemma` over `isCompact_Icc`, using
  `isInvertible_flat_iff` to pass between the flat map and nondegeneracy.

### `Geometry/Manifold/DifferentialForm/Pullback/Family.lean`

The file has the name of Tau Ceti's file that defines
`TauCeti.SmoothForm.lineMapFamily`. It is in the namespace
`TauCeti.SmoothForm`.

- `coe_mpullback_prodMk_lineMapFamily` (`@[simp]`): the slices of
  `SmoothForm.lineMapFamily α₀ α₁ hc` for the underlying rough forms, the
  `.val` form of Tau Ceti's `mpullback_prodMk_lineMapFamily`.
- `mpullback_prodMk_mpullback_prodMap'`: for smooth `c : P' → P` between parameter
  manifolds and `f : M → N`, the slice at `t` of the pullback of a form on
  `P × N` along `Prod.map c f` is the pullback along `f` of its slice at
  `c t`. Its case `f = id` is Tau Ceti's `mpullback_prodMk_mpullback_prodMap_id`.
  The case `c = id`, `mpullback_prodMk_mpullback_prodMap`, is Tau Ceti's, in
  `TauCeti/Geometry/Manifold/DifferentialForm/Flow/Family.lean`.
  They use only the functoriality of the pullback. *Contact geometry* uses
  them in `Flow/Family.lean`, `Contact/Family.lean` and `Contact/Gray.lean`.

The velocity of the same segment,
`SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily` (the slice at time
`t` of the time derivative of `SmoothForm.lineMapFamily α₀ α₁ hc` is
`deriv c t • (α₁ - α₀)`), is Tau Ceti's, in its
`Geometry/Manifold/DifferentialForm/Flow/Family.lean`.

### `Geometry/Manifold/DifferentialForm/Smooth.lean`

The file has the name of Tau Ceti's file that defines
`TauCeti.SmoothForm.bilinFormAt`. It has the `@[simp]` lemmas
`TauCeti.SmoothForm.bilinFormAt_add`, `_smul`, `_zero`, `_neg` and `_sub`,
in the namespace `TauCeti.SmoothForm`, for real smooth two-forms. They
rewrite the bilinear form at a point of a segment `σ₀ + s • (σ₁ - σ₀)` of
two-forms. It also has the `@[simp]` lemmas `TauCeti.SmoothForm.funSMulₗ_add`,
`_const`, `_one` and `mpullback_funSMulₗ`, for smooth `k`-forms with any
coefficient space. The file is about smooth forms in general, so any part may
import it. It imports `Geometry/Manifold/ContMDiffMap/Basic.lean` for
`ContMDiffMap.comp_mk_apply`, with which `simp` proves
`mpullback_funSMulₗ`.

### `Geometry/Manifold/DifferentialForm/Opens.lean`

The file has the name of Tau Ceti's file with `mpullback_liftOpens_apply_coe`.
It has `PartialDiffeomorph.mpullback_toDiffeomorphSourceTarget_liftOpens`:
for `Φ : PartialDiffeomorph I I' U V ∞` between open subsets, if `Φ` pulls
the restriction of `σ` to `V` back to `τ` at every point of its source, then
`(Φ.liftOpens hU hV).toDiffeomorphSourceTarget` pulls the restriction of `σ`
to its target back to the restriction of `τ` to its source, as smooth forms.
`Moser/Relative.lean` ends with it, and so may the neighbourhood theorems.

It also gives the `Subtype.val` counterparts of the Tau Ceti file's
`Opens.inclusion` lemmas, in the namespace `TauCeti`:
`mpullback_subtypeVal_surjective`, `contMDiffAt_mpullback_subtypeVal_iff`,
`RoughForm.inChartAt_mpullback_subtypeVal_eventuallyEq` and
`mpullback_subtypeVal_mextDeriv`, the last with no regularity hypothesis.
`RelativePoincare.lean` uses them. The file is about forms in general, so any
part may import it.

In the empty case, `Relative.lean` takes `Diffeomorph.ofIsEmpty` between the
empty open sets, and the restricted forms agree by `Subsingleton.elim`. For
this it imports *Symplectic neighbourhoods*'
`Geometry/Manifold/Diffeomorph/Basic.lean` and
`Topology/Sets/Opens/Basic.lean`, which import only Mathlib.

### `Geometry/Symplectic/Manifold/TwoForm.lean`

The file has the name of Tau Ceti's file that defines
`IsNondegenerate.symplecticFormAt`. It has
`TauCeti.SmoothTwoForm.coe_mpullback_apply_eq_of_mfderiv_eq`: for a smooth
`f` with `f x₀ = x₁` and `mfderiv I₀ I₁ f x₀ = A`, `A` a linear
symplectomorphism for `hω₀.symplecticFormAt x₀` and `hω₁.symplecticFormAt x₁`,
`(SmoothForm.mpullback f hf ω₁).val x₀ = ω₀.val x₀`.

### `Geometry/Manifold/TubularNeighborhood/RelativePoincare.lean`

The file has the name of Tau Ceti's file that proves
`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`. Its theorems are in
the namespace `TauCeti.SmoothEmbedding`. Its `exists_mextDeriv_eq_and_mpullback_eq`
extends a primitive from an open subset with the lemmas of
`Geometry/Manifold/DifferentialForm/Opens.lean`.

- `exists_smoothForm_relative_primitive_sub`: for a smooth embedding `f`,
  closed `η₀ η₁ : SmoothForm I M F (k + 1)` with `f^* η₁ = f^* η₀`, and an
  open `O ⊇ range f`, a tube `W` with `range f ⊆ W ⊆ O` and
  `β : SmoothForm I W F k` with `dβ` the difference of the restrictions of
  `η₁` and `η₀` to `W`. It vanishes at every `f q`, and its chart expression
  has zero derivative at each `f q` where `η₁` and `η₀` agree. Step 1 of
  `Relative.lean` and of `Isotopy.lean` both use it.

### `Geometry/Symplectic/Manifold/Flat.lean`

The file has the name of Tau Ceti's file that defines
`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`. It is in the
namespace `TauCeti.SmoothTwoForm`, with its lemmas about nondegenerate and
compatible forms under `IsNondegenerate` and `Compatible`.
It imports `Geometry/Manifold/VectorBundle/Pullback.lean` of *Symplectic
vector bundles*, which is merged, for the flat maps of a two-form along a
smooth map as sections of the bundle of bilinear forms on the pull-back.

- `hasFDerivAt_mpullbackWithin_interiorEquiv_symm`: let `σ` be a nondegenerate smooth
  two-form, let `β : SmoothForm I M ℝ 1`, and let `x` be a point with
  `β.val x = 0` at which the chart expression of `β` has zero derivative
  (`HasFDerivAt (RoughForm.inChartAt β.val x) 0 (extChartAt I x x)`, the
  form in which Tau Ceti's relative primitive states it). Then
  `HasFDerivAt (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
  (h.interiorEquiv.symm β) (range I)) 0 (extChartAt I x x)`. This gives the
  hypothesis of Tau Ceti's `mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`
  with no bridge through `FirstJetBundle.jet`.
  The proof adapts Tau Ceti's private `hasFDerivAt_mpullbackWithin_moserField`
  (`RelativeMoser.lean`). In the chart at `x`, the field is the inverse flat
  map of the coordinate form applied to `β`. The inverse flat map is bounded
  near `x`, and `β` is `o(‖z - x‖)`.

These lemmas cover the inverse flat map of a covector field that is smooth
only near a set. Each asks only that the flat map be invertible at a point,
not that the form be nondegenerate, so they are in `TauCeti.SmoothTwoForm`,
except the second:

- `interior_flat_inverse_apply`: if `(σ.flat x).IsInvertible`, then for a
  covector field `c`, `RoughForm.interior (fun y ↦ (σ.flat y).inverse (c y))
  σ.val x` is `c x` read as a one-form.
- `IsNondegenerate.interior_flat_inverse_ofSubsingleton`: for a nondegenerate
  `σ` and a rough one-form `β`, the field sending `x` to `(σ.flat x).inverse`
  of `β x` read as a covector contracts with `σ` to `β`.
- `contMDiffAt_sectionAlong_flat_inverse_apply`: for two-forms `σ m` and
  covectors `c m` at `b m`, along `b : N → M`, both `C^n` at `m₀`, with the
  flat map of `σ m₀` invertible at `b m₀`, the map
  `m ↦ ⟨b m, ((σ m).flat (b m)).inverse (c m)⟩` into the tangent bundle is
  `C^n` at `m₀`. `contMDiffAt_moserField` uses it along `Prod.snd`.

### `Geometry/Symplectic/Moser/Relative.lean`

In the namespace `TauCeti.SmoothEmbedding`, except for the public steps
`exists_partialDiffeomorph_mpullback_eq_of_mextDeriv_eq_sub` (Moser's
argument along the local flow) and
`exists_partialDiffeomorph_eq_timeDependentFlowOf_moserField`, which mention no
embedding and are in `TauCeti.SmoothTwoForm`. The milestone's name is that of Tau Ceti's
compact theorem `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`,
in another namespace. It generalizes that theorem and would replace it
upstream. It is reached by dot notation on `f`, as the relative primitive
is.

```lean
theorem exists_diffeomorph_opens_of_eq_along (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal σ₀
```

Milestone: *Relative Moser theorem with prescribed first derivative*. `Q` is
not assumed compact, and `range f` is not assumed closed (see *Decisions*).
The source is `Q` with its own topology, so an injectively immersed
submanifold that is not embedded is excluded.

Proof, in four steps.

1. *Primitive.* `f.exists_isSmoothForm_relative_primitive` with `O = univ`
   gives a tube `W ⊇ range f` and a smooth `β` on `W`. It has
   `dβ = (σ₁ - σ₀)|_W`, it vanishes at `f q`, and its first jet is zero
   there, because `heq` makes `σ₁ - σ₀` vanish at `f q`. The closedness
   input is `h₁.sub h₀`. The pullback `f^*(σ₁ - σ₀)` vanishes by `heq`.
2. *Nondegeneracy region.* `N := W ∩ {x | ∀ s ∈ Icc 0 1, …}` is open by
   `isOpen_setOfPred_forall_mem_Icc_nondegenerate`. It contains `range f`,
   because along `f(Q)` every point of the segment is `σ₀`
   (Tau Ceti's `bilinFormAt_add_smul_sub_of_eq`, in
   `Manifold/RelativeMoser.lean`). Work on the
   open submanifold `N`, with the forms restricted along `Subtype.val`.
3. *Moser flow.* With `c = Real.smoothTransition`, let
   `σ := SmoothForm.lineMapFamily σ₀ σ₁ c.contDiff` on `ℝ × N`. Its slices
   are closed and nondegenerate, since `c t ∈ [0, 1]`. Let `α` be the
   one-form `-(c' ∘ Prod.fst) • Prod.snd^* β` on `ℝ × N`. Tau Ceti's
   `exists_contMDiff_mpullback_timeDependentFlowOf_apply_eq` gives a smooth
   field `X` with `ι_{X_t} σ_t = α_t` whose flow pulls `σ_t` back to
   `σ_s` wherever it is defined; by injectivity of the contraction, `X t`
   is `(hσ t).interiorEquiv.symm α_t`, the Moser field without cutoff.
   `X t` vanishes at `f q`, and its chart expression has zero derivative
   there, by `hasFDerivAt_mpullbackWithin_interiorEquiv_symm`.
4. *Domain up to time one.* Let `Φ := timeDependentFlowPartialDiffeomorph
   (hn := le_top) hX 0 1` on `N`. Its source contains `f(Q)`, by
   `mem_timeDependentFlowDomain_of_forall_eq_zero`. Along its source, the
   flow property of step 3 gives `Φ^* σ₁ = σ₀`, since `c 0 = 0` and
   `c 1 = 1`. `Φ` fixes `f(Q)`
   (`timeDependentFlowOf_eq_self_of_forall_eq_zero`), and its differential
   there is the identity (`mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`).
   Tau Ceti's `PartialDiffeomorph.toDiffeomorphSourceTarget` makes `Φ` a
   diffeomorphism between opens of `N`. Reading these opens as opens of `M`
   gives `U₀`, `U₁` and `φ`. The differential is compared through
   Tau Ceti's `Manifold.mfderiv_eq_id_iff_of_comp_subtype_val`.

The module docstring credits Tau Ceti's
`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`
and `exists_diffeomorph_opens_of_eq_along`, whose proofs this one adapts to
the local flow.

### `Geometry/Symplectic/Moser/Field.lean`

The cut-off Moser field of a family of two-forms over a parameter manifold
`N` (model `J`). It is a new definition, so it is in `SymplecticGeometry`.
For `σ : SmoothForm (J.prod I) (N × M) ℝ 2`,
`β : SmoothForm (J.prod I) (N × M) ℝ 1` and `ρ : N × M → ℝ`, with slices
`σ_t` and `β_t` written out as above:

```lean
/-- The Moser field `X_t = ρ(t, ·) (σ_t♭)⁻¹(-β_t)` of the family `σ`. -/
def moserField (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (β : SmoothForm (J.prod I) (N × M) ℝ 1) (ρ : N × M → ℝ) (t : N) (x : M) :
    TangentSpace I x :=
  ρ (t, x) • (SmoothTwoForm.flat
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) x).inverse
      (-SmoothForm.degreeOneEquiv
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β) x)
```

The segment $\sigma_0+t(\sigma_1-\sigma_0)$ with a primitive `β` fixed in
time is `σ = SmoothForm.lineMapFamily σ₀ σ₁ contDiff_id` with `β` pulled
back along `Prod.snd`.

API, in the order the proofs need it. `hinv` stands for
`∀ p ∈ tsupport ρ, (SmoothTwoForm.flat σ_{p.1} p.2).IsInvertible`.

- `moserField_def` (by `(rfl)`).
- `moserField_eq_zero_of_apply_eq_zero`: `β_t.val x = 0 → moserField σ β ρ t x = 0`.
- `moserField_eq_zero_of_notMem_tsupport`: `(t, x) ∉ tsupport ρ → … = 0`.
- `interior_moserField`: if the flat map of `σ_t` at `x` is invertible, then
  `RoughForm.interior (moserField σ β ρ t) σ_t.val x = -ρ (t, x) • β_t.val x`.
  `interior_moserField_eq` is the same identity at every point, given `hinv`.
- `contMDiffAt_moserField`: if `ρ` is smooth at `p₀` and the flat map at
  `p₀` is invertible when `p₀ ∈ tsupport ρ`, the map
  `p ↦ ⟨p.2, moserField σ β ρ p.1 p.2⟩` into the tangent bundle is
  smooth at `p₀`. `contMDiff_moserField`: given
  `ContMDiff (J.prod I) 𝓘(ℝ) ∞ ρ` and `hinv`, that map is smooth on `N × M`.
  Near `tsupport ρ` the proof is that of Tau Ceti's
  `TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`,
  through `contMDiffAt_sectionAlong_flat_inverse_apply`, for which the file
  imports `Geometry/Symplectic/Manifold/Flat.lean`.
  Away from it, the field is the zero section.
- `moserField_rate_eq_zero`: Moser's equation at `(t, y)`, for `N = ℝ`.
  Assume `mextDeriv σ_t.val y = 0`,
  `∀ᶠ z in 𝓝 y, ρ (t, z) = 1 ∧ (SmoothTwoForm.flat σ_t z).IsInvertible`,
  and that the slice of `σ.timeDeriv` at `t` equals `mextDeriv β_t.val`
  at `y`. Then the rate of `σ` along `moserField σ β ρ` vanishes at
  `(t, y)`. This is the hypothesis of Tau Ceti's
  `mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`.
  Both conditions on the forms are asked only at `y`, so that `β` need be
  a primitive only near a set.
- No completeness lemma: when `tsupport ρ` is compact, `Moser/Family.lean`
  applies Tau Ceti's `isCompleteVectorField_timeDependentSuspensionField`
  directly, to the compact projection of `tsupport ρ` to `M` and
  `moserField_eq_zero_of_notMem_tsupport`.

The module docstring credits Tau Ceti's private `moserField`,
`moserField_eq_zero`, `interior_moserField`, `interior_moserField_eq`,
`contMDiff_moserField` and `moserRate_eq_zero` (`RelativeMoser.lean`). This
file adapts them from the reparametrized path, a fixed primitive and a
cutoff on `M` to a general family, a primitive depending on the parameter
and a cutoff on `N × M`.

### `Geometry/Symplectic/Moser/Isotopy.lean`

In the namespace `TauCeti.SmoothEmbedding`, with `[CompactSpace Q]`, and
`ω t := σ₀ + t • (σ₁ - σ₀)`.

```lean
theorem exists_diffeotopy_fix_eventually_mpullback_eq (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ Ψ : Diffeotopy I ∞ M, (∃ C, IsCompact C ∧ ∀ t, ∀ x ∉ C, Ψ (t, x) = x) ∧
      (∀ t q, Ψ (t, f q) = f q) ∧
      ∀ᶠ x in 𝓝ˢ (range f), ∀ t : unitInterval,
        (SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
          (σ₀ + (t : ℝ) • (σ₁ - σ₀))).val x = σ₀.val x
```

The neighbourhood of `range f` on which the identity holds is the same for
every `t`, as the order of the quantifiers says.

Proof. Take the tube `W` and the primitive `β` of
`exists_isSmoothForm_relative_primitive`. It vanishes along `f(Q)`, since
`f^*(σ₁ - σ₀) = 0` by `hf`. On the open submanifold `W`, apply *Isotopy
extension*'s Moser argument along a family fixing a submanifold,
`TauCeti.SmoothEmbedding.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`
(`Moser/Family.lean`), to `f.codRestrict W`, the family
`SmoothForm.lineMapFamily` of the restricted forms with `contDiff_id`, and
`SmoothForm.mpullback Prod.snd contMDiff_snd β`. Then extend the
diffeotopy of `W` by the identity with Tau Ceti's
`Diffeotopy.exists_extend_of_isCompact`, as Tau Ceti's
`exists_diffeomorph_fix_embedding_eventually_mpullback_eq` does for one
diffeomorphism. This replaces cutting `β` off and extending it by zero: on
`M` itself, `RoughForm.extendByZero` gives a form on the open set `⊤`, not on
`M`. The trajectory argument, the diffeotopy form of Tau Ceti's
`exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`, is
that of `Moser/Family.lean`, for a compact set
(`TauCeti.SmoothForm.exists_diffeotopy_fix_eventually_mpullback_eq_of_timeDeriv`).

The milestone, in the plan's form, with the isotopy of embeddings of `U`
starting at the inclusion `ι U := (SmoothEmbedding.ofOpens U).toContMDiffMap`.
(With the anonymous constructor `⟨Subtype.val, contMDiff_subtypeVal⟩` instead,
`ψ (t, x)` does not elaborate.) The time-one map is a conjunct.

```lean
theorem exists_smoothIsotopy_fix_mpullback_eq (f : SmoothEmbedding J I ∞ Q M)
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    {σ : SmoothForm I M ℝ 1} (hσ : mextDeriv σ.val = (σ₁ - σ₀).val)
    (hfσ : SmoothForm.mpullback f f.contMDiff σ = 0)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ (U : Opens M) (hU : range f ⊆ U) (g : C^∞⟮I, U; I, M⟯) (ψ : SmoothIsotopy (ι U) g),
      (∀ t q, ψ (t, ⟨f q, hU (mem_range_self q)⟩) = f q) ∧
      (∀ t : unitInterval, SmoothForm.mpullback (ψ.timeSlice t) (ψ.timeSlice t).contMDiff
          (σ₀ + (t : ℝ) • (σ₁ - σ₀)) =
        SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ₀) ∧
      ∃ (V : Opens M) (φ : U ≃ₘ⟮I, I⟯ V), ∀ x, (φ x : M) = g x
```

Milestone: *Relative Moser theorem fixing a submanifold*. It is
`Ψ.smoothIsotopy (ι U) (SmoothEmbedding.ofOpens U).isSmoothEmbedding` for the
`Ψ` of the previous theorem, with `g = Ψ.final ∘ ι U` and an open `U` from
`hasBasis_nhdsSet`. The milestone's `h₁ : σ₁.IsClosed` is dropped: it follows
from `h₀` and `hσ`. The hypothesis `hf` of the previous theorem follows from
`hσ` and `hfσ` by `SmoothForm.mextDerivₗ_mpullback`. The diffeomorphism `φ`
is `Ψ.final.subtype` onto `V = Ψ.final.symm ⁻¹' U`, as in Tau Ceti's
`exists_diffeomorph_opens_of_eq_along`; it fixes `f(Q)`, which is the final
remark of the milestone. The forms are given on `M`. Forms given only on an
open set `O ⊇ f(Q)` are those of the open submanifold `O`, so the theorem
applies to them with `M` replaced by `O` and `f` by `f.codRestrict O`.
`SmoothIsotopy.timeSlice t` is Tau Ceti's slice at `t`, as a `SmoothEmbedding`.

The module docstring credits Tau Ceti's
`exists_diffeomorph_fix_embedding_eventually_mpullback_eq` and
`exists_diffeomorph_opens_of_eq_along`.

The file imports `Geometry/Symplectic/Moser/Family.lean` of *Isotopy
extension*, for Moser's argument along a family.

### `Geometry/Symplectic/Manifold/Darboux.lean`

The file has the name of Tau Ceti's file. It is in the namespace
`TauCeti.SmoothTwoForm`. `F` is a finite-dimensional real normed space with
`form₀ : TauCeti.SymplecticForm F`. For the plan's statement, `F` is
`StdSpace (Fin n)` and `form₀` is `stdForm (Fin n)`.

```lean
theorem IsSymplectic.exists_darbouxChart_mvfderiv_eq {ω : SmoothTwoForm I M}
    (hω : ω.IsSymplectic) (form₀ : SymplecticForm F) {p : M} (A : TangentSpace I p ≃L[ℝ] F)
    (hA : ∀ v w, form₀ (A v) (A w) = ω.eval₂ p v w) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞,
      p ∈ chart.source ∧ chart p = 0 ∧ mvfderiv I chart p = A.toContinuousLinearMap ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace I x,
        ω.eval₂ x v w = form₀ (mvfderiv I chart x v) (mvfderiv I chart x w)
```

It is the corollary, for `[BoundarylessManifold I M]`, of
`exists_darbouxChart_mvfderiv_eq_of_isInteriorPoint`, which assumes only
`ω.IsClosed` and `I.IsInteriorPoint p`, as Tau Ceti's
`exists_darbouxChart_of_nondegenerate_of_isInteriorPoint` does: `hA` makes
`ω` nondegenerate at `p`.

Milestone: *Darboux theorem with prescribed derivative*. The milestone's
other two conclusions are the transition lemma below, and, for charts into
`StdSpace (Fin n)` at every point, this theorem at each point with `A` from
the linear Darboux theorem `exists_isSymplectomorphism_stdForm`. The
docstring names both. Take Tau Ceti's chart `χ` for some constant form on
`E`, and compose with `A ∘ (mvfderiv I χ p)⁻¹` as in *Decisions*. The
composition with a linear symplectomorphism is Tau Ceti's private
`trans_toDiffeomorph_darboux` (`chart.trans L.toDiffeomorph.toPartialDiffeomorph`).
This file restates it as a public lemma, `trans_toDiffeomorph_darbouxChart`,
credited in the module docstring, with the source, the values and the
derivative at every point; the derivative comes from Tau
Ceti's `ContinuousLinearEquiv.mvfderiv_comp_apply`. The derivative of `χ` at `p` is
invertible because `χ` is a partial diffeomorphism
(`PartialDiffeomorph.bijective_mvfderiv`). It is symplectic by the chart
identity at `p`.

In the namespace `TauCeti.SymplecticForm`, so that it is reached from
`form₀`, and at the image `φ x` of a point of both sources, as Tau Ceti's
`PartialDiffeomorph.fderiv_comp_symm_eq_comp` states transitions:

```lean
theorem apply_fderiv_transition_eq (form₀ : SymplecticForm F) {ω : SmoothTwoForm I M}
    {φ ψ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞} {x : M} (hxφ : x ∈ φ.source)
    (hxψ : x ∈ ψ.source)
    (hφ : ∀ v w, ω.eval₂ x v w = form₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hψ : ∀ v w, ω.eval₂ x v w = form₀ (mvfderiv I ψ x v) (mvfderiv I ψ x w))
    (v w : F) :
    form₀ (fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) v)
      (fderiv ℝ (fun z ↦ ψ (φ.symm z)) (φ x) w) = form₀ v w
```

It is the case `B = form₀`, `w = φ x` of
`PartialDiffeomorph.apply_fderiv_symm_trans_eq_of_mvfderiv`
(`Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean`). It needs only that both charts pull the same constant form
back to `ω` at `x`, so `ω` needs no hypothesis.

### `Geometry/Symplectic/Moser/Stability.lean`

In the namespace `TauCeti.SmoothTwoForm`, with `[CompactSpace M]` for the milestone. Here
`σ : SmoothTwoForm ((𝓡∂ 1).prod I) (unitInterval × M)` is a family over
$[0,1]$, as *Manifolds, families and signs* says. It is written with the
abbreviation `SmoothTwoForm`, so that dot notation reaches this namespace, and
named `σ`, since `ω` is a token under `open scoped ContDiff`.

```lean
theorem exists_diffeotopy_mpullback_eq
    (σ : SmoothTwoForm ((𝓡∂ 1).prod I) (unitInterval × M))
    (hσ : ∀ t, IsSymplectic (SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) σ))
    (hcoh : ∀ t, SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ -
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ ∈
      exactForms I M 2) :
    ∃ Ψ : Diffeotopy I ∞ M, ∀ t, SmoothForm.mpullback (Ψ.timeSlice t) (Ψ.timeSlice t).contMDiff
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
      SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ
```

Milestone: *Moser stability*. `Diffeotopy` starts at the identity by
definition (`Diffeotopy.apply_zero`), which is $\psi_0=\mathrm{id}$.

The proof follows the route of `DESIGN.md`. *Smooth families* supplies the
following; its design file, from #466, gives their names.

1. (★) of `DeRham/SmoothFamily/GoodCover.lean`, through
   `exists_isSmoothFamily_mextDerivₗ_eq`: a one-form `β` on
   `unitInterval × M` whose slices satisfy `d β_t = ω_t - ω_0`.
2. `DifferentialForm/TimeExtension.lean`: an extension `B` of `β` to `ℝ × M`.
3. `Diffeotopy/Real.lean`: the restriction of an isotopy over `ℝ` to a
   `Diffeotopy`.

The milestone is the case `K = univ` of
`exists_diffeotopy_mpullback_eq_of_isSmoothFamily` in the same file, which
takes a family `τ_t` of symplectic forms over $[0,1]$ on a boundaryless
manifold and a smooth family of primitives `β_t` of `τ_t - τ_0` vanishing
outside a compact set `K`, and gives a diffeotopy fixed outside `K`. Item 1
supplies `β`. In that theorem, item 2 extends `β` to `B` on `ℝ × M`, and
`ρ := Prod.snd^* τ_0 + mextDeriv B` is closed, with slices `τ_s` for
`s ∈ [0, 1]` and `τ_0` outside `K`. Nondegeneracy is open
(`isOpen_setOfPred_isInvertible_flat_mpullback_prodMk` of
`Manifold/Family.lean`) and `K` is compact, so the slices of `ρ` are
symplectic for times in some $(-\delta,1+\delta)$; pulling `ρ` back along
`h × id`, for a smooth `h` that is the identity on $[0,1]$ with values in
that interval, makes every slice symplectic. By Cartan's formula
(`SmoothForm.mextDerivₗ_timeInterior`, in `DifferentialForm/Flow/Family.lean`)
the contraction with `∂_t` of this closed form is a primitive of its time
derivative, and it vanishes outside `K`, so
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact` applies.
It gives `ψ : ℝ → M ≃ₘ⟮I, I⟯ M`, which item 3 restricts to `Ψ`.

## What the part uses

- Tau Ceti, Moser and Darboux: `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`,
  `exists_diffeomorph_opens_of_eq_along` (as the model for `Relative.lean`),
  `IsSymplectic.exists_darbouxChart_of_symplecticForm`,
  `IsSymplectic.mlieDerivForm_interiorEquiv_symm`,
  `contMDiff_interiorEquiv_symm_mpullback_prodMk`,
  `IsNondegenerate.interiorEquiv` with `interior_interiorEquiv_symm` and
  `interiorEquiv_symm_apply_eq_zero_iff`, `flat`, `isInvertible_flat_iff`,
  `contMDiffAt_sectionAlong_flat`, `SmoothForm.lineMapFamily` with
  `mpullback_prodMk_lineMapFamily`, `SmoothForm.degreeOneEquiv`.
- Tau Ceti, flows: `timeDependentFlowOf`, `timeDependentFlowDomain`,
  `timeDependentFlowPartialDiffeomorph`, `timeDependentFlowDiffeotopy`,
  `isCompleteVectorField_timeDependentSuspensionField`,
  `mem_timeDependentFlowDomain_of_forall_eq_zero`,
  `timeDependentFlowOf_eq_self_of_forall_eq_zero`,
  `mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`,
  `mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_mem` and
  `_of_forall_mem_uIcc`.
- Tau Ceti, submanifolds and forms: `SmoothEmbedding`,
  `SmoothEmbedding.exists_isSmoothForm_relative_primitive`, `SmoothIsotopy`,
  `Diffeotopy` with `timeSlice`, `final` and `Diffeotopy.smoothIsotopy`,
  `isSmoothEmbedding_diffeomorph_comp`,
  `PartialDiffeomorph.toDiffeomorphSourceTarget`,
  `RoughForm.extendByZero` with `IsSmoothForm.extendByZero`,
  `IsCompact.exists_contMDiff_one_nhds_tsupport_subset`,
  `Continuous.isOpen_setOf_clm_bundle_isInvertible`, `exactForms`,
  `Manifold.mfderiv_eq_id_iff_of_comp_subtype_val`, `ContMDiffAt.clm_bundle_inverse`.
- Mathlib: `generalized_tube_lemma`, `Real.smoothTransition`,
  `Manifold.IsSmoothEmbedding.of_opens`, `PartialDiffeomorph`, `Diffeomorph`.
- *Smooth families* (#466, #467), for `Stability.lean` only: (★), the time
  extension, and the restriction to a `Diffeotopy`.
- Tau Ceti: `Geometry/Manifold/DifferentialForm/Flow/Family.lean`,
  for `SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily` in `Relative.lean`
  and `Isotopy.lean`.
- *Liouville structures*: `Geometry/Manifold/MFDeriv/Opens.lean`
  (`mdifferentiableAt_subtypeVal`), in `DifferentialForm/Opens.lean` and
  `RelativePoincare.lean`.
- *Symplectic neighbourhoods*, merged: `Geometry/Manifold/Diffeomorph/Basic.lean`
  and `Topology/Sets/Opens/Basic.lean`, in `Relative.lean` and
  `DifferentialForm/Opens.lean`; and
  `Geometry/Manifold/DifferentialForm/Pullback/LocalDiffeomorph.lean`, in
  `DifferentialForm/Opens.lean`, for `PartialDiffeomorph.mpullback_symm_mpullback_apply`.
- *Standard model*, merged, only for the plan's case `F = StdSpace (Fin n)`
  of `Darboux.lean`. The general statement does not mention it.

Mathlib and Tau Ceti were searched, at the pinned versions, for each result
above. Tau Ceti has the compact relative theorem, ordinary Darboux charts,
Moser's theorem over `ℝ` with given primitives, and the time-one relative
theorem. The non-compact relative theorem, Darboux charts with a prescribed
derivative, symplectic transition derivatives, Moser isotopies for every
time, and stability for cohomologous families over $[0,1]$ are not there.
The pieces that Tau Ceti has only as `private` steps (`moserField`,
`exists_isOpen_isInvertible_flat`, `hasFDerivAt_mpullbackWithin_moserField`,
`trans_toDiffeomorph_darboux`) are made public here, in a more general form,
and credited.

## Building issues

In this order. Each issue is blocked by the ones listed, and all are
sub-issues of #472, *Build the part Moser isotopy*. Sizes are estimates.

| # | Issue | Files | Blocked by | Size |
|---|---|---|---|---|
| 1 | Openness of nondegeneracy and jets of inverse flat maps | `Geometry/Symplectic/Manifold/Family.lean`, `Geometry/Symplectic/Manifold/Flat.lean` | — | 250 |
| 2 | The relative Moser theorem with prescribed first derivative | `Moser/Relative.lean` | 1 | 300 |
| 3 | The cut-off Moser field of a segment of two-forms | `Moser/Field.lean` | — | 350 |
| 4 | The Moser isotopy fixing a compact submanifold | `Moser/Isotopy.lean` | 1, 3 | 300 |
| 5 | Darboux charts with prescribed derivative | `Geometry/Symplectic/Manifold/Darboux.lean`, `Geometry/Manifold/LocalDiffeomorph/MFDeriv.lean` | — | 200 |
| 6 | Moser stability | `Moser/Stability.lean` | 1; the issues of #467 that build `DeRham/SmoothFamily/GoodCover.lean`, `DifferentialForm/TimeExtension.lean` and `Diffeotopy/Real.lean` (#467 itself until it is split) | 250 |

Issues 1, 3 and 5 can start at once, and issues 2 and 4 need nothing outside the
part. The milestones are proved in issues 2 (*Relative Moser theorem with
prescribed first derivative*), 4 (*Relative Moser theorem fixing a
submanifold*), 5 (*Darboux theorem with prescribed derivative*) and 6
(*Moser stability*). *Symplectic neighbourhoods* waits for issue 2, and
*Isotopy extension* for issues 2 and 4.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.2.
* [D. McDuff, D. Salamon, errata to the third edition][McDuffSalamon2019Errata],
  p. 109 (the first-order conclusion of Lemma 3.2.1).
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in
  Mathematics 1764, Springer, Berlin, 2001][CannasdaSilva2001Lectures],
  Lectures 6–7. The plan's bibliography has no key for this book; its key
  `CannasdaSilva2001` is her 2001 notes *Symplectic Toric Manifolds*.
* J. Moser, *On the volume elements on a manifold*, Transactions of the
  American Mathematical Society 120 (1965), 286–294.
