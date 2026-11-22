/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Slices of families of forms: linear interpolation and pullback along `c × f`

Tau Ceti's `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc` is the smooth form on `ℝ × M` whose slice
at time `t` is `α₀ + c(t) (α₁ - α₀)`, and `TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`
states this for the smooth pullback. This file states the same identity for the underlying rough
forms and the rough pullback `TauCeti.mpullback`, the form in which proofs that work pointwise
meet the slices.

It then computes the slices of the pullback of a form `α` on `ℝ × N` along `c × f`, for a smooth
reparametrization `c : ℝ → ℝ` of time and a smooth map `f : M → N`: since
`(c × f) ∘ ι_t = ι_{c t} ∘ f`, where `ι_t x = (t, x)`, functoriality of the pullback
(`TauCeti.SmoothForm.mpullback_comp`) gives `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`.

## Main results

* `TauCeti.SmoothForm.coe_mpullback_prodMk_lineMapFamily`: the slices of
  `TauCeti.SmoothForm.lineMapFamily`, stated for the underlying rough forms.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap'`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`
  for a reparametrization `c` of time, with its cases `c = id`,
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`, and `f = id`,
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id_right`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slices of `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc`, as rough forms: the pullback of
the underlying form along `x ↦ (t, x)` is the underlying form of `α₀ + c(t) (α₁ - α₀)`. -/
@[simp]
theorem coe_mpullback_prodMk_lineMapFamily (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) :
    TauCeti.mpullback (F := F) I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (lineMapFamily α₀ α₁ hc).val =
      (α₀ + c t • (α₁ - α₀)).val :=
  (coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_prodMk_lineMapFamily α₀ α₁ hc t))

/-! ### Slices of pullbacks along `c × f` -/

section prodMap

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × N` along `c × f`, for a smooth
reparametrization `c : ℝ → ℝ` of time, is the pullback along `f` of the slice of `α` at time
`c t`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap' {c : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ c)
    (f : M → N) (hf : ContMDiff I J ∞ f) (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c f) (hc.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α) := by
  rw [← LinearMap.comp_apply, ← mpullback_comp, ← LinearMap.comp_apply, ← mpullback_comp]
  have h : Prod.map c f ∘ Prod.mk t = Prod.mk (c t) ∘ f := by
    ext x <;> simp
  simp only [h]

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × N` along `id × f` is the pullback
along `f` of the slice of `α` at time `t`: `ι_t^* (id × f)^* α = f^* ι_t^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod J) (ℝ × N) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id f) (contMDiff_id.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  mpullback_prodMk_mpullback_prodMap' contMDiff_id f hf α t

/-- The slice at time `t` of the pullback of a form `α` on `ℝ × M` along `c × id`, for a smooth
`c : ℝ → ℝ`, is the slice of `α` at time `c t`. -/
theorem mpullback_prodMk_mpullback_prodMap_id_right {c : ℝ → ℝ}
    (hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ c) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k) (t : ℝ) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c id) (hc.prodMap contMDiff_id) α) =
      mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α := by
  rw [mpullback_prodMk_mpullback_prodMap' hc id contMDiff_id]
  exact LinearMap.congr_fun SmoothForm.mpullback_id _


end prodMap

end TauCeti.SmoothForm

end
