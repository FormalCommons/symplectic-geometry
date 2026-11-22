/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Sets.Strip
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Symmetric strips as manifolds

For a manifold `M` modelled on `I`, the symmetric strip `SymplecticGeometry.symmStrip M ε`, the
open set `(-ε, ε) × M` of `ℝ × M`, is a manifold modelled on `𝓘(ℝ).prod I`. This file gives the
calculus of its slice maps `SymplecticGeometry.symmStripMk hr : M → symmStrip M ε`, `x ↦ (r, x)`:
they are smooth, their differential is `v ↦ (0, v)`, and so the pullback of a two-form `σ` on the
strip along the slice map at `r` is `σ` at `(r, x)` restricted to vectors `(0, v)`.

## Main results

* `SymplecticGeometry.contMDiff_symmStripMk`, `SymplecticGeometry.mfderiv_symmStripMk_apply`
* `TauCeti.SmoothForm.bilinFormAt_mpullback_symmStripMk`
-/

public section

open scoped ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

namespace SymplecticGeometry

/-- The slice map `x ↦ (r, x)` of a symmetric strip is smooth. -/
theorem contMDiff_symmStripMk {n : WithTop ℕ∞} {ε r : ℝ} (hr : |r| < ε) :
    ContMDiff I (𝓘(ℝ).prod I) n (symmStripMk (X := M) hr) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff, val_comp_symmStripMk]
  exact contMDiff_const.prodMk contMDiff_id

/-- The differential of the slice map `x ↦ (r, x)` sends `v` to `(0, v)`. -/
theorem mfderiv_symmStripMk_apply {ε r : ℝ} (hr : |r| < ε) (x : M) (v : TangentSpace I x) :
    mfderiv I (𝓘(ℝ).prod I) (symmStripMk hr) x v = ((0 : ℝ), v) := by
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, val_comp_symmStripMk, mfderiv_prod_right]
  exact ContinuousLinearMap.inr_apply ..

end SymplecticGeometry

namespace TauCeti.SmoothForm

open SymplecticGeometry

variable [IsManifold I ∞ M] {ε : ℝ}

/-- The slice at `r` of a two-form `σ` on the strip, evaluated on `v` and `w`, is the value of `σ`
at `(r, x)` on `(0, v)` and `(0, w)`. -/
theorem bilinFormAt_mpullback_symmStripMk {r : ℝ} (hr : |r| < ε)
    (σ : SmoothTwoForm (𝓘(ℝ).prod I) (symmStrip M ε)) (x : M) (v w : TangentSpace I x) :
    (mpullback (symmStripMk hr) (contMDiff_symmStripMk hr) σ).bilinFormAt x v w =
      σ.bilinFormAt (symmStripMk hr x) ((0 : ℝ), v) ((0 : ℝ), w) := by
  rw [bilinFormAt_apply, eval₂_mpullback, mfderiv_symmStripMk_apply, mfderiv_symmStripMk_apply]
  exact (bilinFormAt_apply σ _ _ _).symm

end TauCeti.SmoothForm

end
