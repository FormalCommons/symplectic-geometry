/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The contactization form under a product map

For a one-form `θ` on a manifold `W`, Tau Ceti's `TauCeti.SmoothForm.contactization θ` is the
one-form `dz - θ` on `W × ℝ`. For a smooth map `ι : S → W`, this file shows that the map
`(s, z) ↦ (ι s, z)` pulls the contactization form of `θ` back to the contactization form of
`ι^* θ` (`TauCeti.SmoothForm.mpullback_prodMap_contactization`).

It follows from Tau Ceti's `TauCeti.SmoothForm.mpullback_prodMk_contactization`, the pull-back of
`dz - θ` along a map `x ↦ (ι x, h x)`, with `TauCeti.SmoothForm.contactization_def` and
`TauCeti.SmoothForm.mpullback_realLineCoordForm` to read `dz` as the differential of `z`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, Example 3.5.6.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
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
    mpullback_prodMk_contactization θ (hι.comp contMDiff_fst) contMDiff_snd, contactization_def,
    Submodule.coe_sub, mpullback_mpullback, coe_mpullback Prod.snd, mpullback_realLineCoordForm,
    coe_mpullback (ι ∘ Prod.fst)]

end TauCeti.SmoothForm

end
