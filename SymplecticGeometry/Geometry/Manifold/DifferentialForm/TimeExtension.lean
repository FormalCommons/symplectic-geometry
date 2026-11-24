/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic

/-!
# Time extension of forms

Let `M` be a boundaryless manifold and `Ω` a smooth `k`-form on `unitInterval × M`. Its slices
`Ω_t = ι_t^* Ω`, with `ι_t : y ↦ (t, y)`, take their values at `x` in the fibre over `x`, which
does not depend on `t`. Applying Seeley's extension operator from `[0, 1]` to `t ↦ Ω_t(x)` at each
point `x` gives forms `TauCeti.SmoothForm.timeExtendSlice Ω s` on `M` for every real `s`, equal to
`Ω_s` for `s ∈ [0, 1]`. They form a smooth family over `ℝ`: read in a tangent trivialization of
`M`, which does not involve the time, their coordinates are the time extension
(`SymplecticGeometry.timeExtend`) of those of the slices of `Ω`, which is smooth by
`ContMDiffOn.timeExtend`. The form on `ℝ × M` with these slices
(`TauCeti.SmoothForm.ofSlices`) is the time extension `TauCeti.SmoothForm.timeExtend Ω`; it is
linear in `Ω`.

The extension keeps the slices of `Ω`, not its components along the time direction: the form
`timeExtend Ω` vanishes on that direction.

## Main definitions

* `TauCeti.SmoothForm.timeExtendSlice Ω s`: the slice at time `s : ℝ` of the extension of `Ω`.
* `TauCeti.SmoothForm.timeExtend`: the linear map from forms on `unitInterval × M` to forms on
  `ℝ × M` that extends the slices.

## Main results

* `TauCeti.SmoothForm.mpullback_prodMk_timeExtend`: the slice of `timeExtend Ω` at a time
  `t ∈ [0, 1]` is the slice of `Ω` at `t`.
* `TauCeti.SmoothForm.timeExtendSlice_mpullback_prodMap`,
  `TauCeti.SmoothForm.timeExtend_mpullback_prodMap`: the time extension commutes with pullback
  along `Prod.map id g` for a smooth map `g` of the space factor.
* `SymplecticGeometry.isSmoothFamily_timeExtendSlice`: the slices of the extension form a smooth
  family over `ℝ`.
* `SymplecticGeometry.IsSmoothFamily.exists_extend`: a smooth family of forms over
  `unitInterval` is the restriction of a smooth family over `ℝ`.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- On a boundaryless manifold `M`, let `Ω_t` be the slice at `t` of a smooth form `Ω` on
`unitInterval × M`. The section along the projection `ℝ × M → M` whose value at `(s, x)` is
Seeley's extension of `t ↦ Ω_t(x)` at `s` is smooth. -/
private theorem contMDiff_timeExtend_slice (Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        (SymplecticGeometry.timeExtend (F := E [⋀^Fin k]→L[ℝ] F) (fun q : unitInterval × M ↦
          (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2) p)) := by
  set g : unitInterval × M → E [⋀^Fin k]→L[ℝ] F := fun q ↦
    (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2
  have hS : ContMDiff ((𝓡∂ 1).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun q : unitInterval × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) q.2 (g q)) :=
    contMDiff_mpullback_prodMk Ω
  intro p₀
  set e := trivializationAt (E [⋀^Fin k]→L[ℝ] F)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p₀.2
  -- The coordinates of the slices of `Ω` in `e` are smooth over the base set of `e`, hence so
  -- is their time extension.
  have hh := ((e.contMDiffOn_iff (s := univ ×ˢ e.baseSet) fun q hq ↦
    e.mem_source.mpr hq.2).mp hS.contMDiffOn).2.timeExtend e.open_baseSet
  have hU : univ ×ˢ e.baseSet ∈ 𝓝 p₀ :=
    prod_mem_nhds univ_mem (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  refine (e.contMDiffAt_iff (e.mem_source.mpr
    (FiberBundle.mem_baseSet_trivializationAt' _))).mpr ⟨contMDiffAt_snd, ?_⟩
  refine (hh.contMDiffAt hU).congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_)
  -- At `q`, both sides precompose with the inverse tangent trivialization at `q.2`, which
  -- does not depend on the time. The fibres are read as the model fibre.
  let L : M → E →L[ℝ] E := (trivializationAt E (TangentSpace I) p₀.2).symmL ℝ
  have he : ∀ (y : M) (φ : E [⋀^Fin k]→L[ℝ] F),
      (e ⟨y, φ⟩).2 = φ.compContinuousLinearMap (L y) := fun y φ ↦
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd (𝕜 := ℝ) (F₁ := E)
      (V := TangentSpace I) (F := F) (ι := Fin k) p₀.2 (x := y) φ
  refine (he q.2 (SymplecticGeometry.timeExtend g q)).trans ?_
  refine ((ContinuousAlternatingMap.compContinuousLinearMapₗ (L q.2)).map_timeExtend g q).trans ?_
  exact SymplecticGeometry.timeExtend_congr (fun s ↦ (he q.2 (g (s, q.2))).symm) q.1
variable (Ω Θ : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k)

/-- The slice at time `s : ℝ` of the time extension of a smooth form `Ω` on `unitInterval × M`:
the form on `M` whose value at `x` is Seeley's extension of `t ↦ Ω_t(x)` at `s`, where `Ω_t` is
the slice of `Ω` at `t`. -/
def timeExtendSlice (s : ℝ) : SmoothForm I M F k :=
  ⟨fun x ↦ SymplecticGeometry.timeExtend (F := E [⋀^Fin k]→L[ℝ] F) (fun q : unitInterval × M ↦
      (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2) (s, x),
    IsSmoothForm.mem_smoothBundleForms <| (isSmoothForm_def _ _).mpr <|
      (contMDiff_timeExtend_slice Ω).comp (contMDiff_const.prodMk contMDiff_id)⟩

/-- The value at `x` of `TauCeti.SmoothForm.timeExtendSlice Ω s` is the time extension, at
`(s, x)`, of the values of the slices of `Ω`. -/
theorem coe_timeExtendSlice (s : ℝ) :
    (timeExtendSlice Ω s).val = fun x ↦ SymplecticGeometry.timeExtend (F := E [⋀^Fin k]→L[ℝ] F)
      (fun q : unitInterval × M ↦
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2) (s, x) :=
  (rfl)

/-- At a time `t ∈ [0, 1]`, the slice of the time extension of `Ω` is the slice of `Ω`. -/
@[simp]
theorem timeExtendSlice_coe (t : unitInterval) :
    timeExtendSlice Ω t = mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω :=
  Subtype.ext <| funext fun x ↦ by
    rw [coe_timeExtendSlice]
    exact SymplecticGeometry.timeExtend_apply_coe (F := E [⋀^Fin k]→L[ℝ] F) _ t x

/-- The slices of the time extension are additive in the form. -/
@[simp]
theorem timeExtendSlice_add (s : ℝ) :
    timeExtendSlice (Ω + Θ) s = timeExtendSlice Ω s + timeExtendSlice Θ s := by
  refine Subtype.ext <| funext fun x ↦ ?_
  have h : (fun q : unitInterval × M ↦
      ((mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (Ω + Θ)).val q.2 :
        E [⋀^Fin k]→L[ℝ] F)) =
      (fun q ↦ (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2) +
        fun q ↦ (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Θ).val q.2 := by
    funext q
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  rw [Submodule.coe_add, Pi.add_apply, coe_timeExtendSlice, coe_timeExtendSlice,
    coe_timeExtendSlice, h]
  exact congrFun (SymplecticGeometry.timeExtend_add (F := E [⋀^Fin k]→L[ℝ] F) _ _) (s, x)

/-- The slices of the time extension commute with multiplication by a scalar. -/
@[simp]
theorem timeExtendSlice_smul (c : ℝ) (s : ℝ) :
    timeExtendSlice (c • Ω) s = c • timeExtendSlice Ω s := by
  refine Subtype.ext <| funext fun x ↦ ?_
  have h : (fun q : unitInterval × M ↦
      ((mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) (c • Ω)).val q.2 :
        E [⋀^Fin k]→L[ℝ] F)) =
      c • fun q ↦ (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2 := by
    funext q
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply]
  rw [Submodule.coe_smul, Pi.smul_apply, coe_timeExtendSlice, coe_timeExtendSlice, h]
  exact congrFun (SymplecticGeometry.timeExtend_smul (F := E [⋀^Fin k]→L[ℝ] F) _ _) (s, x)

/-- The slices `TauCeti.SmoothForm.timeExtendSlice Ω s` have a smooth slice section over
`ℝ × M`. -/
theorem contMDiff_timeExtendSlice :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((timeExtendSlice Ω p.1).val p.2)) := by
  simpa only [coe_timeExtendSlice] using contMDiff_timeExtend_slice Ω

/-- **The time extension of forms.** On a boundaryless manifold `M`, the linear map that sends a
smooth form `Ω` on `unitInterval × M` to the smooth form on `ℝ × M` whose slices are the
`TauCeti.SmoothForm.timeExtendSlice Ω s`, obtained by applying Seeley's extension operator to the
slices of `Ω` at each point of `M`, and which vanishes on the time direction. -/
def timeExtend :
    SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k →ₗ[ℝ]
      SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F k where
  toFun Ω := ofSlices (timeExtendSlice Ω) (contMDiff_timeExtendSlice Ω)
  map_add' Ω Θ := by
    ext p v
    simp only [ofSlices_apply, timeExtendSlice_add, Submodule.coe_add, Pi.add_apply,
      ContinuousAlternatingMap.add_apply]
  map_smul' c Ω := by
    ext p v
    simp only [ofSlices_apply, timeExtendSlice_smul, Submodule.coe_smul, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, RingHom.id_apply]

/-- `TauCeti.SmoothForm.timeExtend Ω` is the form on `ℝ × M` with the slices
`TauCeti.SmoothForm.timeExtendSlice Ω s`. -/
theorem timeExtend_def :
    timeExtend Ω = ofSlices (timeExtendSlice Ω) (contMDiff_timeExtendSlice Ω) :=
  (rfl)

/-- The slice of `TauCeti.SmoothForm.timeExtend Ω` at a time `s : ℝ` is
`TauCeti.SmoothForm.timeExtendSlice Ω s`. -/
@[simp]
theorem mpullback_prodMk_timeExtend_eq_timeExtendSlice (s : ℝ) :
    mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) (timeExtend Ω) =
      timeExtendSlice Ω s := by
  rw [timeExtend_def, mpullback_prodMk_ofSlices]

/-- The slices of the time extension of the zero form vanish. -/
@[simp]
theorem timeExtendSlice_zero (s : ℝ) :
    timeExtendSlice (0 : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k) s = 0 := by
  simp only [← mpullback_prodMk_timeExtend_eq_timeExtendSlice, map_zero]

/-- The slices of the time extension commute with negation of the form. -/
@[simp]
theorem timeExtendSlice_neg (s : ℝ) : timeExtendSlice (-Ω) s = -timeExtendSlice Ω s := by
  simp only [← mpullback_prodMk_timeExtend_eq_timeExtendSlice, map_neg]

/-- The slices of the time extension commute with subtraction of forms. -/
@[simp]
theorem timeExtendSlice_sub (s : ℝ) :
    timeExtendSlice (Ω - Θ) s = timeExtendSlice Ω s - timeExtendSlice Θ s := by
  simp only [← mpullback_prodMk_timeExtend_eq_timeExtendSlice, map_sub]

/-- At a time `t ∈ [0, 1]`, the slice of the time extension `TauCeti.SmoothForm.timeExtend Ω` is
the slice of `Ω`. -/
theorem mpullback_prodMk_timeExtend (t : unitInterval) :
    mpullback (Prod.mk (t : ℝ)) (contMDiff_const.prodMk contMDiff_id) (timeExtend Ω) =
      mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω := by
  rw [mpullback_prodMk_timeExtend_eq_timeExtendSlice, timeExtendSlice_coe]

section Naturality

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ M']
  [BoundarylessManifold I' M'] {g : M → M'}

/-- **Naturality of the slices of the time extension.** For a smooth map `g : M → M'` and a
smooth form `Ω` on `unitInterval × M'`, the slices of the time extension of the pullback of `Ω`
along `id × g` are the pullbacks along `g` of the slices of the time extension of `Ω`. -/
theorem timeExtendSlice_mpullback_prodMap (hg : ContMDiff I I' ∞ g)
    (Ω : SmoothForm ((𝓡∂ 1).prod I') (unitInterval × M') F k) (s : ℝ) :
    timeExtendSlice (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) s =
      mpullback g hg (timeExtendSlice Ω s) := by
  refine Subtype.ext <| funext fun x ↦ ?_
  set G : unitInterval × M' → E' [⋀^Fin k]→L[ℝ] F := fun q ↦
    (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2
  -- Composing with the differential of `g` at `x`, on the values of the forms at `g x`.
  obtain ⟨L, hL⟩ : ∃ L : (E' [⋀^Fin k]→L[ℝ] F) →ₗ[ℝ] (E [⋀^Fin k]→L[ℝ] F),
      ∀ φ, L φ = φ.compContinuousLinearMap (mfderiv I I' g x : E →L[ℝ] E') :=
    ⟨_, ContinuousAlternatingMap.compContinuousLinearMapₗ_apply _⟩
  rw [coe_timeExtendSlice, coe_mpullback, TauCeti.mpullback_apply_eq_compContinuousLinearMap,
    coe_timeExtendSlice]
  refine (SymplecticGeometry.timeExtend_congr (g := L ∘ G ∘ Prod.map id g) (fun t ↦ ?_) s).trans ?_
  · -- The slice at `t` of the pullback is the pullback of the slice at `t`.
    have h : mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) =
          mpullback g hg (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω) :=
      mpullback_mpullback_of_comp_eq (contMDiff_const.prodMk contMDiff_id)
        (contMDiff_id.prodMap hg) hg (contMDiff_const.prodMk contMDiff_id) (by rfl) Ω
    dsimp only
    rw [h, coe_mpullback, TauCeti.mpullback_apply_eq_compContinuousLinearMap, Function.comp_apply,
      Function.comp_apply, hL]
    -- The two sides agree after unfolding the local abbreviation `G`.
    rfl
  · rw [← L.map_timeExtend, SymplecticGeometry.timeExtend_comp_prodMap_id, hL]
    -- As above, the two sides agree after unfolding `G`.
    rfl

/-- **Naturality of the time extension.** For a smooth map `g : M → M'` and a smooth form `Ω` on
`unitInterval × M'`, the time extension of the pullback of `Ω` along `id × g` is the pullback
along `id × g` of the time extension of `Ω`. -/
theorem timeExtend_mpullback_prodMap (hg : ContMDiff I I' ∞ g)
    (Ω : SmoothForm ((𝓡∂ 1).prod I') (unitInterval × M') F k) :
    timeExtend (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) =
      mpullback (Prod.map id g) (contMDiff_id.prodMap hg) (timeExtend Ω) := by
  refine Subtype.ext ?_
  rw [coe_mpullback, timeExtend_def, timeExtend_def, coe_ofSlices, coe_ofSlices,
    TauCeti.mpullback_prodMap_verticalForm _ mdifferentiable_id (hg.mdifferentiable (by simp))]
  congr 1
  funext t
  rw [timeExtendSlice_mpullback_prodMap hg, coe_mpullback, id_eq]

end Naturality

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slices of the time extension of a smooth form on `unitInterval × M` form a smooth family
over `ℝ`. -/
theorem isSmoothFamily_timeExtendSlice (Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k) :
    IsSmoothFamily 𝓘(ℝ, ℝ) (SmoothForm.timeExtendSlice Ω) :=
  isSmoothFamily_def.mpr
    ⟨SmoothForm.timeExtend Ω, SmoothForm.mpullback_prodMk_timeExtend_eq_timeExtendSlice Ω⟩

/-- **Extension of smooth families in time.** On a boundaryless manifold, every smooth family of
forms over `unitInterval` is the restriction of a smooth family over `ℝ`. -/
theorem IsSmoothFamily.exists_extend {α : unitInterval → SmoothForm I M F k}
    (hα : IsSmoothFamily (𝓡∂ 1) α) :
    ∃ β : ℝ → SmoothForm I M F k, IsSmoothFamily 𝓘(ℝ, ℝ) β ∧ ∀ t : unitInterval, β t = α t := by
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp hα
  exact ⟨SmoothForm.timeExtendSlice Ω, isSmoothFamily_timeExtendSlice Ω,
    fun t ↦ (SmoothForm.timeExtendSlice_coe Ω t).trans (hΩ t)⟩

end SymplecticGeometry
