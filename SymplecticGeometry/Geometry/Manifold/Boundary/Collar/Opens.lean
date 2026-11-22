/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Collars of an open neighbourhood of the boundary

Let `W` be a manifold modelled on the half-space `𝓡∂ (n + 1)` and `V` an open subset of `W` that
contains the boundary `∂W`. By Mathlib's `ModelWithCorners.boundary_open`, the boundary of `V`
is the set of points of `V` that lie in `∂W`, so the inclusion `V → W` maps `∂V` onto `∂W`. This
file shows that it is a diffeomorphism for Tau Ceti's manifold structures on the two boundaries
(`TauCeti.diffeomorphBoundaryOpens`): both directions are smooth, since a map into a boundary is
smooth when its composite with the inclusion of the boundary is (Tau Ceti's
`TauCeti.contMDiff_iff_comp_subtypeVal_boundary`).

Through it, a smooth collar of `∂V` in `V` is a smooth collar of `∂W` in `W`
(`TauCeti.SmoothCollar.ofOpens`), with the same image. So a collar of `∂W` may be built on any
open neighbourhood of `∂W`. When `∂W` is compact, there is always a σ-compact one, inside any
given open set containing `∂W`, even when `W` is not σ-compact: finitely many chart domains
cover a compact set, and their union is second countable
(`IsCompact.exists_opens_subset_sigmaCompactSpace`, for any charted space over a locally compact,
second-countable model).

## Main results

* `IsCompact.exists_opens_subset_sigmaCompactSpace`: in a charted space over a locally compact,
  second-countable model, a compact set has σ-compact open neighbourhoods inside any open set
  that contains it.
* `TauCeti.diffeomorphBoundaryOpens`: for an open `V ⊇ ∂W`, the inclusion gives a diffeomorphism
  `∂V ≃ ∂W`.
* `TauCeti.SmoothCollar.ofOpens`: a smooth collar of `∂V` as a smooth collar of `∂W`;
  `TauCeti.SmoothCollar.range_ofOpens` gives its image.
-/

public section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

open _root_.TauCeti.EuclideanHalfSpace

/-- In a charted space over a locally compact, second-countable model, a compact set `K` inside an
open set `U` has an open neighbourhood inside `U` that is σ-compact. It may be taken to be `U`
intersected with finitely many chart sources. -/
theorem IsCompact.exists_opens_subset_sigmaCompactSpace {H M : Type*} [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] [SecondCountableTopology H] [LocallyCompactSpace H]
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Opens M, K ⊆ V ∧ (V : Set M) ⊆ U ∧ SigmaCompactSpace V := by
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x ↦ (chartAt H x).source)
    fun x _ ↦ chart_source_mem_nhds H x
  let V : Opens M := ⟨U ∩ ⋃ x ∈ t, (chartAt H x).source,
    hU.inter (isOpen_biUnion fun x _ ↦ (chartAt H x).open_source)⟩
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace H V
  -- The charts of `V` at the finitely many points of `t` cover `V`.
  have : SecondCountableTopology V := by
    refine ChartedSpace.secondCountable_of_countable_cover H (s := Subtype.val ⁻¹' (t : Set M))
      ?_ (t.finite_toSet.preimage Subtype.val_injective.injOn).countable
    refine eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 y.property.2
    refine mem_iUnion₂.2 ⟨⟨x, hKU (htK x hxt), mem_iUnion₂.2 ⟨x, hxt, mem_chart_source H x⟩⟩,
      hxt, ?_⟩
    rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hyx
  exact ⟨V, subset_inter hKU hKt, inter_subset_left, inferInstance⟩

namespace TauCeti

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  {k : ℕ∞ω}

/-- For an open subset `V` of `W` that contains the boundary `∂W`, the inclusion `V → W` restricts
to a `C^k` diffeomorphism from the boundary of `V` onto the boundary of `W`, for Tau Ceti's
manifold structures on the boundaries. -/
noncomputable def diffeomorphBoundaryOpens [IsManifold (𝓡∂ (n + 1)) k W] (V : Opens W)
    (hV : (𝓡∂ (n + 1)).boundary W ⊆ V) :
    (𝓡∂ (n + 1)).boundary V ≃ₘ^k⟮𝓡 n, 𝓡 n⟯ (𝓡∂ (n + 1)).boundary W where
  toFun x := ⟨x.val.val, (Set.ext_iff.1 ModelWithCorners.boundary_open x.val).1 x.property⟩
  invFun x := ⟨⟨x.val, hV x.property⟩,
    (Set.ext_iff.1 ModelWithCorners.boundary_open _).2 x.property⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  contMDiff_toFun := by
    rw [contMDiff_iff_comp_subtypeVal_boundary]
    exact contMDiff_subtypeVal.comp (isSmoothEmbedding_subtypeVal_boundary (k := k) V).contMDiff
  contMDiff_invFun := by
    rw [contMDiff_iff_comp_subtypeVal_boundary]
    intro x
    -- A map into the open subset `V` is smooth when its composite with `V → W` is.
    refine (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := V) _ _ _).1 ?_
    exact (isSmoothEmbedding_subtypeVal_boundary (k := k) W).contMDiff x

section

variable [IsManifold (𝓡∂ (n + 1)) k W] {V : Opens W} (hV : (𝓡∂ (n + 1)).boundary W ⊆ V)

/-- The diffeomorphism `∂V ≃ ∂W` sends a boundary point of `V` to the same point of `W`. -/
@[simp]
theorem coe_diffeomorphBoundaryOpens_apply (x : (𝓡∂ (n + 1)).boundary V) :
    (diffeomorphBoundaryOpens (k := k) V hV x : W) = x := (rfl)

/-- The inverse of the diffeomorphism `∂V ≃ ∂W` sends a boundary point of `W` to the same point,
seen in `V`. -/
@[simp]
theorem coe_coe_diffeomorphBoundaryOpens_symm_apply (x : (𝓡∂ (n + 1)).boundary W) :
    (((diffeomorphBoundaryOpens (k := k) V hV).symm x : V) : W) = x := (rfl)

namespace SmoothCollar

/-- **A collar of an open neighbourhood of the boundary.** For an open subset `V` of `W` that
contains `∂W`, a `C^k` collar `c` of `∂V` in `V`, followed by the inclusion `V → W`, is a `C^k`
collar of `∂W` in `W`: its value at `(x, t)` is `c (x, t)`, reading the boundary point `x` of `W`
as a boundary point of `V` (`TauCeti.diffeomorphBoundaryOpens`). -/
noncomputable def ofOpens (c : SmoothCollar n k V) : SmoothCollar n k W where
  toFun p := c ((diffeomorphBoundaryOpens V hV).symm p.1, p.2)
  isLocalDiffeomorph' p :=
    ((((diffeomorphBoundaryOpens V hV).symm.prodCongr (Diffeomorph.refl _ _ _)).isLocalDiffeomorph
      p).comp (hg := c.isLocalDiffeomorph _)).comp (hg := isLocalDiffeomorph_subtype_val _)
  injective' p q h := by
    have := c.injective (Subtype.val_injective h)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext ((diffeomorphBoundaryOpens V hV).symm.injective this.1) this.2
  apply_zero' x := by
    rw [← coe_coe_diffeomorphBoundaryOpens_symm_apply (k := k) hV x, c.apply_zero]

/-- The value of `c.ofOpens hV` at `(x, t)` is that of `c` at `(x, t)`, with `x` read in `∂V`. -/
theorem ofOpens_apply (c : SmoothCollar n k V)
    (p : (𝓡∂ (n + 1)).boundary W × normalIioOpens 1) :
    c.ofOpens hV p = c ((diffeomorphBoundaryOpens (k := k) V hV).symm p.1, p.2) := (rfl)

/-- The collar `c.ofOpens hV` of `∂W` has the image of `c`, seen in `W`. -/
theorem range_ofOpens (c : SmoothCollar n k V) :
    range (c.ofOpens hV) = Subtype.val '' range c := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, (ofOpens_apply hV c p).symm⟩
  · rintro ⟨_, ⟨⟨x, t⟩, rfl⟩, rfl⟩
    exact ⟨(diffeomorphBoundaryOpens (k := k) V hV x, t), by simp [ofOpens_apply]⟩

end SmoothCollar

end

end TauCeti
