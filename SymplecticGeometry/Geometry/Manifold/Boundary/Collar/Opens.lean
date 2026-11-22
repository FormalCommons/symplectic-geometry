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
given open set containing `∂W`, even when `W` is not σ-compact, since `W` is locally compact
(`IsCompact.exists_isOpen_isSigmaCompact_subset`, in
`SymplecticGeometry/Topology/Compactness/SigmaCompact.lean`).

## Main results

* `TauCeti.diffeomorphBoundaryOpens`: for an open `V ⊇ ∂W`, the inclusion gives a diffeomorphism
  `∂V ≃ ∂W`.
* `TauCeti.SmoothCollar.ofOpens`: a smooth collar of `∂V` as a smooth collar of `∂W`;
  `TauCeti.SmoothCollar.range_ofOpens` gives its image.
-/

public section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

open _root_.TauCeti.EuclideanHalfSpace

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
@[simp]
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
    exact ⟨(diffeomorphBoundaryOpens (k := k) V hV x, t), by simp⟩

end SmoothCollar

end

end TauCeti
