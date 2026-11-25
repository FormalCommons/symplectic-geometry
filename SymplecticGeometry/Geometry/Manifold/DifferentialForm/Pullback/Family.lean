/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Slices of families of forms, and pullbacks of families along families of maps

Tau Ceti's `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc` is the smooth form on `ℝ × M` whose slice
at time `t` is `α₀ + c(t) (α₁ - α₀)`, and `TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`
states this for the smooth pullback. This file states the same identity for the underlying rough
forms and the rough pullback `TauCeti.mpullback`, the form in which proofs that work pointwise
meet the slices.

It then computes the slices of the pullback of a form `α` on `P × N` along `c × f`, for a smooth
map `c : P' → P` of parameter manifolds and a smooth map `f : M → N`: since
`(c × f) ∘ ι_t = ι_{c t} ∘ f`, where `ι_t x = (t, x)`, functoriality of the pullback
(`TauCeti.SmoothForm.mpullback_comp`) gives `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`.

Finally, it extends Tau Ceti's `ContMDiffAt.mpullback_form_family`, the smoothness of the
pullbacks `(f p)^* φ` of one form `φ` along a smooth family of maps `f`, to a family of forms
`φ p` that varies smoothly with the parameter
(`ContMDiffAt.mpullback_form_family_of_family`). The proof is that of Tau Ceti's lemma, with the
coefficients of the family in place of those of the fixed form.

## Main results

* `TauCeti.SmoothForm.coe_mpullback_prodMk_lineMapFamily`: the slices of
  `TauCeti.SmoothForm.lineMapFamily`, stated for the underlying rough forms.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap'`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`
  for a smooth map `c` of parameter manifolds, with its case `f = id` over `ℝ`,
  `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap_id_right`; the case `c = id` is Tau
  Ceti's `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodMap`.
* `ContMDiffAt.mpullback_form_family_of_family`: the pullbacks `(f p)^* (φ p)` of a smooth
  family of forms along a smooth family of maps form a smooth section.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
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
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- The slice at `t` of the pullback of a form `α` on `P × N` along `c × f`, for smooth maps
`c : P' → P` of parameter manifolds and `f : M → N`, is the pullback along `f` of the slice of `α`
at `c t`: `ι_t^* (c × f)^* α = f^* ι_{c t}^* α`. -/
theorem mpullback_prodMk_mpullback_prodMap' {EP HP P EP' HP' P' : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold K 1 P]
    [NormedAddCommGroup EP'] [NormedSpace ℝ EP'] [TopologicalSpace HP']
    {K' : ModelWithCorners ℝ EP' HP'} [TopologicalSpace P'] [ChartedSpace HP' P']
    [IsManifold K' 1 P'] {c : P' → P} (hc : ContMDiff K' K ∞ c)
    (f : M → N) (hf : ContMDiff I J ∞ f) (α : SmoothForm (K.prod J) (P × N) F k) (t : P') :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map c f) (hc.prodMap hf) α) =
      mpullback f hf (mpullback (Prod.mk (c t)) (contMDiff_const.prodMk contMDiff_id) α) :=
  -- The square `Prod.map c f ∘ Prod.mk t = Prod.mk (c t) ∘ f` commutes by definition.
  mpullback_mpullback_of_comp_eq (contMDiff_const.prodMk contMDiff_id) (hc.prodMap hf) hf
    (contMDiff_const.prodMk contMDiff_id) rfl α

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

/-! ### Pullback of a family of forms along a family of maps -/

section family

variable {EN HN N E' H' M' : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  [IsManifold J 1 N] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  {m n : WithTop ℕ∞}

/-- **Pullback of a family of forms along a family of maps.** Let `f : N → M → M'` be jointly
`C^n` at `(p₀, g p₀)` and `g : N → M` be `C^m` at `p₀`, with `m + 1 ≤ n`, and let `φ` be a family
of rough forms on `M'` over `N` such that `p ↦ φ p (f p (g p))` is a `C^m` section along
`p ↦ f p (g p)` at `p₀`. Then the pullbacks `(f p)^* (φ p)` at `g p` form a `C^m` section along
`g` at `p₀`. -/
theorem _root_.ContMDiffAt.mpullback_form_family_of_family {φ : N → RoughForm I' M' F k}
    {f : N → M → M'} {g : N → M} {p₀ : N}
    (hφ : ContMDiffAt J (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M' ↦ TangentSpace I' y [⋀^Fin k]→L[ℝ] Trivial M' F y) (f p (g p))
        (φ p (f p (g p)))) p₀)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (p₀, g p₀))
    (hg : ContMDiffAt J I m g p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) (g p)
        (TauCeti.mpullback I I' (f p) (φ p) (g p))) p₀ := by
  have hfg : ContMDiffAt J I' m (fun p ↦ f p (g p)) p₀ :=
    (hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)).comp p₀
      (contMDiffAt_id.prodMk hg)
  have hc := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hφ).2
  have hd := hf.mfderiv f g hg hmn
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffAt hd).clm_apply hc
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨hg, hp.congr_of_eventuallyEq ?_⟩
  have hmem : (fun p ↦ f p (g p)) ⁻¹'
      (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet ∈ 𝓝 p₀ :=
    hfg.continuousAt.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f p₀ (g p₀))))
  filter_upwards [hmem] with p hp
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using inCoordinates_mpullback_family (I := I) (φ p) f g p₀ p hp


end family

end TauCeti.SmoothForm

end
