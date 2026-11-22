/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization

/-!
# The contactization form

For a one-form `θ` on a manifold `W`, Tau Ceti's `TauCeti.SmoothForm.contactization θ` is the
one-form `dz - θ` on `W × ℝ`. This file adds two facts about it:

* `TauCeti.SmoothForm.coe_contactization`: the contactization form is `dz - pr₁^* θ`, with `z` the
  coordinate of `ℝ` and `pr₁` the projection to `W`;
* `TauCeti.SmoothForm.mpullback_prodMap_contactization`: for a smooth map `ι : S → W`, the map
  `Prod.map ι id : S × ℝ → W × ℝ` pulls the contactization form of `θ` back to the contactization
  form of `ι^* θ`.

Both follow from Tau Ceti's `TauCeti.SmoothForm.mpullback_prodMk_contactization`, the pull-back of
`dz - θ` along a map `x ↦ (ι x, h x)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Example 3.5.6.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]

/-- The contactization form of a one-form `θ` on `W` is `dz - θ`, with `z` the coordinate of `ℝ`
and `θ` pulled back along the projection to `W`. -/
theorem coe_contactization (θ : SmoothForm I W ℝ 1) :
    θ.contactization.val = mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (Prod.snd : W × ℝ → ℝ)) -
      (mpullback Prod.fst contMDiff_fst θ).val :=
  -- The map `p ↦ (p.1, p.2)` of `mpullback_prodMk_contactization` is the identity by `Prod` eta.
  (congrArg Subtype.val (LinearMap.congr_fun mpullback_id θ.contactization)).symm.trans
    (mpullback_prodMk_contactization θ contMDiff_fst contMDiff_snd)

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]

/-- For a smooth map `ι : S → W`, the map `(s, z) ↦ (ι s, z)` pulls the contactization form of a
one-form `θ` on `W` back to the contactization form of `ι^* θ`. -/
theorem mpullback_prodMap_contactization (θ : SmoothForm I W ℝ 1) {ι : S → W}
    (hι : ContMDiff J I ∞ ι) :
    mpullback (Prod.map ι id) (hι.prodMap contMDiff_id) θ.contactization =
      (mpullback ι hι θ).contactization := by
  have hmap : Prod.map ι id = fun p : S × ℝ ↦ ((ι ∘ Prod.fst) p, p.2) :=
    funext fun p ↦ by rw [Prod.map_apply, id_eq, Function.comp_apply]
  refine Subtype.ext ?_
  rw [coe_mpullback, hmap, ← coe_mpullback _ ((hι.comp contMDiff_fst).prodMk contMDiff_snd),
    mpullback_prodMk_contactization θ (hι.comp contMDiff_fst) contMDiff_snd, coe_contactization,
    mpullback_mpullback]

end TauCeti.SmoothForm

end
