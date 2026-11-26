/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Time extension of forms

Let `M` be a manifold, possibly with boundary, and `Ω` a smooth `k`-form on `unitInterval × M`.
Its slices `Ω_t = ι_t^* Ω`, with `ι_t : y ↦ (t, y)`, take their values at `x` in the fibre over
`x`, which does not depend on `t`. Applying Seeley's extension operator from `[0, 1]` to
`t ↦ Ω_t(x)` at each point `x` gives forms `TauCeti.SmoothForm.timeExtendSlice Ω s` on `M` for
every real `s`, equal to `Ω_s` for `s ∈ [0, 1]`. They form a smooth family over `ℝ`: read in a
tangent trivialization of `M`, which does not involve the time, their coordinates are the time
extension (`SymplecticGeometry.timeExtend`) of those of the slices of `Ω`, which is smooth by
`ContMDiffOn.timeExtend`. The form on `ℝ × M` with these slices
(`TauCeti.SmoothForm.ofSlices`) is the time extension `TauCeti.SmoothForm.timeExtend Ω`; it is
linear in `Ω`.

The extension keeps the slices of `Ω`, not its components along the time direction: the form
`timeExtend Ω` vanishes on that direction.

For `a < b`, the same construction applies to forms on `M × Icc a b`, with the interval as the
second factor: they are carried to `unitInterval × M` by swapping the factors and Mathlib's affine
homeomorphism `iccHomeoI a b`, extended, and carried back to `M × ℝ`.

## Main definitions

* `TauCeti.SmoothForm.timeExtendSlice Ω s`: the slice at time `s : ℝ` of the extension of `Ω`.
* `TauCeti.SmoothForm.timeExtend`: the linear map from forms on `unitInterval × M` to forms on
  `ℝ × M` that extends the slices.
* `TauCeti.SmoothForm.timeExtendIcc`: the linear map from forms on `M × Icc a b` to forms on
  `M × ℝ` that extends the slices.

## Main results

* `TauCeti.SmoothForm.mpullback_prodMk_timeExtend`: the slice of `timeExtend Ω` at a time
  `t ∈ [0, 1]` is the slice of `Ω` at `t`.
* `TauCeti.SmoothForm.timeExtendSlice_mpullback_prodMap`,
  `TauCeti.SmoothForm.timeExtend_mpullback_prodMap`: the time extension commutes with pullback
  along `Prod.map id g` for a smooth map `g` of the space factor.
* `TauCeti.SmoothForm.timeExtendSlice_apply_cons`: if the slices of `Ω` contracted with a
  vector field `V` on `M` are those of `Θ`, the same holds for the slices of their extensions.
* `TauCeti.SmoothForm.mpullback_prodMk_timeExtendIcc`,
  `TauCeti.SmoothForm.isSemibasic_fst_timeExtendIcc`,
  `TauCeti.SmoothForm.timeExtendIcc_mpullback_prodMap`: the extension of a form on `M × Icc a b`
  keeps its slices at the times of `[a, b]`, vanishes on vectors along `ℝ`, and commutes with
  pullback along `Prod.map g id`.
* `TauCeti.SmoothForm.timeExtendIcc_apply_cons_prodVectorField`: contracting the extension of
  `η` with the field `(V, 0)`, for a vector field `V` on `M`, gives the extension of the
  contraction of `η` with `(V, 0)`. Its proof reads the values of the extension through its
  slices (`TauCeti.SmoothForm.timeExtendIcc_apply`), where Tau Ceti's
  `TauCeti.mpullback_interior_at` carries the contraction to each slice.
* `TauCeti.SmoothForm.mpullback_prodMap_subtypeVal_timeExtendIcc`: restricted back to
  `M × Icc a b`, the extension of a form with no component along the interval is that form;
  `TauCeti.SmoothForm.mpullback_prodMap_subtypeVal_mextDerivₗ_timeExtendIcc`: the exterior
  derivative of the extension of such a form restricts to that of the form.
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
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Let `Ω_t` be the slice at `t` of a smooth form `Ω` on
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

/-- The value at `x` of `TauCeti.SmoothForm.timeExtendSlice Ω s`, read in the model fibre
`E [⋀^Fin k]→L[ℝ] F`, is the time extension, at `(s, x)`, of the values of the slices of `Ω`. -/
theorem timeExtendSlice_apply (s : ℝ) (x : M) :
    @Eq (E [⋀^Fin k]→L[ℝ] F) ((timeExtendSlice Ω s).val x)
      (SymplecticGeometry.timeExtend (fun q : unitInterval × M ↦
        ((mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) Ω).val q.2 :
          E [⋀^Fin k]→L[ℝ] F)) (s, x)) :=
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
  rw [Submodule.coe_add, Pi.add_apply, timeExtendSlice_apply, timeExtendSlice_apply,
    timeExtendSlice_apply]
  refine (SymplecticGeometry.timeExtend_congr (F := E [⋀^Fin k]→L[ℝ] F) (fun t ↦ ?_) s).trans
    (congrFun (SymplecticGeometry.timeExtend_add _ _) (s, x))
  -- The slice at `t` of `Ω + Θ` is the sum of those of `Ω` and `Θ`.
  exact congrArg (fun γ : SmoothForm I M F k ↦ γ.val x) (map_add _ Ω Θ)

/-- The slices of the time extension commute with multiplication by a scalar. -/
@[simp]
theorem timeExtendSlice_smul (c : ℝ) (s : ℝ) :
    timeExtendSlice (c • Ω) s = c • timeExtendSlice Ω s := by
  refine Subtype.ext <| funext fun x ↦ ?_
  rw [Submodule.coe_smul, Pi.smul_apply, timeExtendSlice_apply, timeExtendSlice_apply]
  refine (SymplecticGeometry.timeExtend_congr (F := E [⋀^Fin k]→L[ℝ] F) (fun t ↦ ?_) s).trans
    (congrFun (SymplecticGeometry.timeExtend_smul c _) (s, x))
  -- The slice at `t` of `c • Ω` is `c` times that of `Ω`.
  exact congrArg (fun γ : SmoothForm I M F k ↦ γ.val x) (map_smul _ c Ω)

/-- The slices `TauCeti.SmoothForm.timeExtendSlice Ω s` have a smooth slice section over
`ℝ × M`. -/
theorem contMDiff_timeExtendSlice :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((timeExtendSlice Ω p.1).val p.2)) := by
  simpa only [coe_timeExtendSlice] using contMDiff_timeExtend_slice Ω

/-- **The time extension of forms.** On a manifold `M`, the linear map that sends a
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
  {g : M → M'}

/-- **Naturality of the slices of the time extension.** For a smooth map `g : M → M'` and a
smooth form `Ω` on `unitInterval × M'`, the slices of the time extension of the pullback of `Ω`
along `id × g` are the pullbacks along `g` of the slices of the time extension of `Ω`. -/
theorem timeExtendSlice_mpullback_prodMap (hg : ContMDiff I I' ∞ g)
    (Ω : SmoothForm ((𝓡∂ 1).prod I') (unitInterval × M') F k) (s : ℝ) :
    timeExtendSlice (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) s =
      mpullback g hg (timeExtendSlice Ω s) := by
  refine Subtype.ext <| funext fun x ↦ ?_
  rw [timeExtendSlice_apply, coe_mpullback, TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM,
    timeExtendSlice_apply]
  refine (SymplecticGeometry.timeExtend_congr (F := E [⋀^Fin k]→L[ℝ] F) (fun t ↦ ?_) s).trans
    ((SymplecticGeometry.timeExtend_comp_prodMap_id _ g (s, x)).trans
      (LinearMap.map_timeExtend (F := E' [⋀^Fin k]→L[ℝ] F) (G := E [⋀^Fin k]→L[ℝ] F)
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := F)
          (mfderiv I I' g x : E →L[ℝ] E')).toLinearMap _ _).symm)
  -- The slice at `t` of the pullback is the pullback of the slice at `t`.
  rw [mpullback_prodMk_mpullback_prodMap' contMDiff_id g hg, coe_mpullback,
    TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM]
  -- `ContinuousLinearMap.coe_coe` up to `Function.comp`; `rw` cannot use it, since the two sides
  -- type the fibres of the forms differently (`TangentSpace` and the model space).
  rfl

/-- **Naturality of the time extension.** For a smooth map `g : M → M'` and a smooth form `Ω` on
`unitInterval × M'`, the time extension of the pullback of `Ω` along `id × g` is the pullback
along `id × g` of the time extension of `Ω`. -/
theorem timeExtend_mpullback_prodMap (hg : ContMDiff I I' ∞ g)
    (Ω : SmoothForm ((𝓡∂ 1).prod I') (unitInterval × M') F k) :
    timeExtend (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) =
      mpullback (Prod.map id g) (contMDiff_id.prodMap hg) (timeExtend Ω) := by
  have h : timeExtendSlice (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω) =
      fun t ↦ mpullback g hg (timeExtendSlice Ω (id t)) :=
    funext (timeExtendSlice_mpullback_prodMap hg Ω)
  have hα := contMDiff_timeExtendSlice (mpullback (Prod.map id g) (contMDiff_id.prodMap hg) Ω)
  rw [h] at hα
  rw [timeExtend_def, timeExtend_def, mpullback_prodMap_ofSlices contMDiff_id hg hα]
  congr 1

end Naturality

/-- **Contraction of the time extension with a field along `M`.** Let `V` be a vector field on
`M`, and `Ω`, `Θ` smooth forms on `unitInterval × M` of degrees `k + 1` and `k` whose slices
satisfy `Ω_t (V x, u) = Θ_t (u)` at every time `t ∈ [0, 1]` and point `x`. Then the slices of
their time extensions satisfy the same identity at every real time `s`. -/
theorem timeExtendSlice_apply_cons (V : Π x : M, TangentSpace I x)
    {Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F (k + 1)}
    {Θ : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k}
    (h : ∀ (t : unitInterval) (x : M) (u : Fin k → TangentSpace I x),
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω).val x (Fin.cons (V x) u) =
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Θ).val x u)
    (s : ℝ) (x : M) (u : Fin k → TangentSpace I x) :
    (timeExtendSlice Ω s).val x (Fin.cons (V x) u) = (timeExtendSlice Θ s).val x u := by
  rw [timeExtendSlice_apply, timeExtendSlice_apply]
  -- Evaluation on fixed vectors is linear on the values, so it commutes with the extension.
  exact (LinearMap.map_timeExtend (F := E [⋀^Fin (k + 1)]→L[ℝ] F) (G := F)
    (ContinuousAlternatingMap.apply ℝ E F _).toLinearMap _ _).trans <|
    (SymplecticGeometry.timeExtend_congr (fun t ↦ h t x u) _).trans
      (LinearMap.map_timeExtend (F := E [⋀^Fin k]→L[ℝ] F) (G := F)
        (ContinuousAlternatingMap.apply ℝ E F _).toLinearMap _ _).symm

section Icc

variable {a b : ℝ} [hab : Fact (a < b)]

/-- **The time extension of forms on `M × [a, b]`.** For a manifold `M` and
`a < b`, the linear map that sends a smooth form `η` on `M × Icc a b` to a smooth form on
`M × ℝ` with the same slices at the times of `[a, b]`: `η` is carried to `unitInterval × M` by
swapping the factors and the affine homeomorphism `iccHomeoI a b`, extended there by
`TauCeti.SmoothForm.timeExtend`, and carried back to `M × ℝ` by `s ↦ (s - a) / (b - a)`. -/
def timeExtendIcc :
    SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k →ₗ[ℝ]
      SmoothForm (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) F k :=
  mpullback (fun p : M × ℝ ↦ ((p.2 - a) / (b - a), p.1))
      ((((contDiff_id.sub contDiff_const).div_const _).contMDiff.comp contMDiff_snd).prodMk
        contMDiff_fst) ∘ₗ timeExtend ∘ₗ
    mpullback (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
      (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst))

/-- `TauCeti.SmoothForm.timeExtendIcc η` is the pullback along `(x, s) ↦ ((s - a) / (b - a), x)`
of the time extension of the pullback of `η` along `(u, x) ↦ (x, (iccHomeoI a b _).symm u)`. -/
theorem timeExtendIcc_def (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k) :
    timeExtendIcc η =
      mpullback (fun p : M × ℝ ↦ ((p.2 - a) / (b - a), p.1))
        ((((contDiff_id.sub contDiff_const).div_const _).contMDiff.comp contMDiff_snd).prodMk
          contMDiff_fst)
        (timeExtend (mpullback
          (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
          (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst)) η)) :=
  (rfl)

/-- The value of `TauCeti.SmoothForm.timeExtendIcc η` at `p` on vectors `v` is the value at
`p.1`, on the components of `v` along `M`, of the slice at time `(p.2 - a) / (b - a)` of the
extension of the form `η` carried to `unitInterval × M`. -/
theorem timeExtendIcc_apply (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k) (p : M × ℝ)
    (v : Fin k → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (timeExtendIcc η).val p v =
      (timeExtendSlice (mpullback
          (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
          (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst)) η)
        ((p.2 - a) / (b - a))).val p.1 (fun i ↦ (v i).1) := by
  rw [timeExtendIcc_def, mpullback_apply, timeExtend_def, ofSlices_apply]
  have hc : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : M × ℝ ↦ (p.2 - a) / (b - a)) p :=
    (((contDiff_id.sub contDiff_const).div_const (b - a)).contMDiff (n := 1).comp
      contMDiff_snd).mdifferentiableAt one_ne_zero
  congr 1
  funext i
  rw [mfderiv_prodMk hc mdifferentiableAt_fst, Manifold.tangentSpaceProdEquiv_apply]
  exact mfderiv_fst_apply p (v i)

/-- At a time `t ∈ [a, b]`, the slice of `TauCeti.SmoothForm.timeExtendIcc η` is the slice of
`η`. -/
@[simp]
theorem mpullback_prodMk_timeExtendIcc (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k)
    (t : Icc a b) :
    mpullback (fun x : M ↦ (x, (t : ℝ))) (contMDiff_id.prodMk contMDiff_const)
        (timeExtendIcc η) =
      mpullback (fun x : M ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) η := by
  set u := iccHomeoI a b hab.out t
  have h₁ : (fun p : M × ℝ ↦ ((p.2 - a) / (b - a), p.1)) ∘ (fun x : M ↦ (x, (t : ℝ))) =
      Prod.mk (u : ℝ) :=
    funext fun x ↦ by simp [u, iccHomeoI_apply_coe]
  have h₂ : (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1)) ∘
      Prod.mk u = fun x : M ↦ (x, t) :=
    funext fun x ↦ by simp [u]
  rw [timeExtendIcc_def, mpullback_mpullback,
    mpullback_congr (g := Prod.mk (u : ℝ)) _ (contMDiff_const.prodMk contMDiff_id) h₁,
    mpullback_prodMk_timeExtend,
    mpullback_mpullback]
  exact mpullback_congr _ _ h₂ η

/-- `TauCeti.SmoothForm.timeExtendIcc η` is semibasic for `Prod.fst : M × ℝ → M`: it vanishes
on tangent vectors `v` as soon as one of them, `v i`, has no component along `M`. -/
theorem isSemibasic_fst_timeExtendIcc (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k) :
    RoughForm.IsSemibasic (F := F) I Prod.fst (timeExtendIcc η).val := by
  refine RoughForm.isSemibasic_fst_iff.mpr fun p v i hv ↦ ?_
  rw [timeExtendIcc_apply]
  rw [Manifold.tangentSpaceProdEquiv_apply] at hv
  exact ContinuousAlternatingMap.map_coord_zero _ i hv

/-- **Restriction of the time extension to `M × [a, b]`.** Let `η` be a smooth form on
`M × Icc a b` semibasic for `Prod.fst`: it vanishes whenever one of its arguments has zero
component along `M`. Then the pullback of `TauCeti.SmoothForm.timeExtendIcc η` along
`id × Subtype.val : M × Icc a b → M × ℝ` is `η`. -/
theorem mpullback_prodMap_subtypeVal_timeExtendIcc
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k)
    (hη : RoughForm.IsSemibasic (F := F) I Prod.fst η.val) :
    mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
      (timeExtendIcc η) = η := by
  refine eq_of_forall_mpullback_eq ?_ hη fun t ↦ ?_
  · rw [coe_mpullback]
    exact (isSemibasic_fst_timeExtendIcc η).mpullback_prodMap mdifferentiable_id
      ((contMDiff_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero)
  rw [mpullback_mpullback,
    mpullback_congr (f := Prod.map id Subtype.val ∘ fun x : M ↦ (x, t))
      (g := fun x : M ↦ (x, (t : ℝ))) _ (contMDiff_id.prodMk contMDiff_const)
      (funext fun _ ↦ rfl)]
  exact mpullback_prodMk_timeExtendIcc η t

/-- **Restriction of the time extension of functions to `M × [a, b]`.** For a smooth `0`-form
`η` on `M × Icc a b`, the pullback of `TauCeti.SmoothForm.timeExtendIcc η` along
`id × Subtype.val : M × Icc a b → M × ℝ` is `η`. -/
@[simp]
theorem mpullback_prodMap_subtypeVal_timeExtendIcc₀
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 0) :
    mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
      (timeExtendIcc η) = η :=
  mpullback_prodMap_subtypeVal_timeExtendIcc η
    (RoughForm.isSemibasic_of_degree_zero (F := F) I Prod.fst η.val)

/-- **Restriction of the exterior derivative of a time extension.** Let `η` be a smooth form on
`M × Icc a b` semibasic for `Prod.fst`: it vanishes whenever one of its arguments has zero
component along `M`. Then the pullback of `d (TauCeti.SmoothForm.timeExtendIcc η)` along
`id × Subtype.val : M × Icc a b → M × ℝ` is `dη`. -/
theorem mpullback_prodMap_subtypeVal_mextDerivₗ_timeExtendIcc
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k)
    (hη : RoughForm.IsSemibasic (F := F) I Prod.fst η.val) :
    mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
      (mextDerivₗ (I.prod 𝓘(ℝ, ℝ)) k (timeExtendIcc η)) = mextDerivₗ (I.prod (𝓡∂ 1)) k η := by
  rw [← mextDerivₗ_mpullback, mpullback_prodMap_subtypeVal_timeExtendIcc η hη]

/-- **Restriction of the differential of the time extension of a function.** For a smooth
`0`-form `η` on `M × Icc a b`, the pullback of `d (TauCeti.SmoothForm.timeExtendIcc η)` along
`id × Subtype.val : M × Icc a b → M × ℝ` is `dη`. -/
theorem mpullback_prodMap_subtypeVal_mextDerivₗ_timeExtendIcc₀
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 0) :
    mpullback (Prod.map id Subtype.val) (contMDiff_id.prodMap contMDiff_subtypeVal_Icc)
      (mextDerivₗ (I.prod 𝓘(ℝ, ℝ)) 0 (timeExtendIcc η)) = mextDerivₗ (I.prod (𝓡∂ 1)) 0 η :=
  mpullback_prodMap_subtypeVal_mextDerivₗ_timeExtendIcc η
    (RoughForm.isSemibasic_of_degree_zero (F := F) I Prod.fst η.val)

section Naturality

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' ∞ M']
  {g : M → M'}

/-- **Naturality of the time extension on `M × [a, b]`.** For a smooth map `g : M → M'` and a
smooth form `η` on `M' × Icc a b`, the time extension of the pullback of `η` along `g × id` is
the pullback along `g × id` of the time extension of `η`. -/
theorem timeExtendIcc_mpullback_prodMap (hg : ContMDiff I I' ∞ g)
    (η : SmoothForm (I'.prod (𝓡∂ 1)) (M' × Icc a b) F k) :
    timeExtendIcc (mpullback (Prod.map g id) (hg.prodMap contMDiff_id) η) =
      mpullback (Prod.map g id) (hg.prodMap contMDiff_id) (timeExtendIcc η) := by
  rw [timeExtendIcc_def, timeExtendIcc_def,
    mpullback_mpullback_of_comp_eq
      (f := fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
      (g := Prod.map g id) (f' := Prod.map id g)
      (g' := fun q : unitInterval × M' ↦ (q.2, (iccHomeoI a b hab.out).symm q.1)) _ _
      (contMDiff_id.prodMap hg)
      (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst))
      (funext fun _ ↦ rfl) η,
    timeExtend_mpullback_prodMap hg]
  exact mpullback_mpullback_of_comp_eq (f := fun p : M × ℝ ↦ ((p.2 - a) / (b - a), p.1))
    (g := Prod.map id g) (f' := Prod.map g id)
    (g' := fun p : M' × ℝ ↦ ((p.2 - a) / (b - a), p.1)) _ _ _ _ (funext fun _ ↦ rfl) _

end Naturality

section Contraction

/-- The slice at a time `t ∈ [0, 1]` of the form `η` on `M × Icc a b` carried to
`unitInterval × M` is the slice of `η` at `(iccHomeoI a b _).symm t`. -/
private theorem mpullback_prodMk_mpullback_iccHomeoI
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k) (t : unitInterval) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (mpullback
        (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
        (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst)) η) =
      mpullback (fun y : M ↦ (y, (iccHomeoI a b hab.out).symm t))
        (contMDiff_id.prodMk contMDiff_const) η := by
  have h : (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1)) ∘
      Prod.mk t = fun y : M ↦ (y, (iccHomeoI a b hab.out).symm t) := rfl
  rw [mpullback_mpullback]
  exact mpullback_congr _ _ h η

/-- If `ζ` is the contraction of `η` with `(V, 0)`, the same holds for their slices at each
time, carried to `unitInterval × M`. -/
private theorem mpullback_prodMk_mpullback_iccHomeoI_apply_cons (V : Π x : M, TangentSpace I x)
    {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)}
    {ζ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k}
    (h : ∀ (q : M × Icc a b) (w : Fin k → TangentSpace (I.prod (𝓡∂ 1)) q),
      η.val q (Fin.cons (Manifold.prodVectorField V 0 q) w) = ζ.val q w)
    (t : unitInterval) (x : M) (u : Fin k → TangentSpace I x) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (mpullback
        (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
        (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst)) η)).val
      x (Fin.cons (V x) u) =
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (mpullback
        (fun q : unitInterval × M ↦ (q.2, (iccHomeoI a b hab.out).symm q.1))
        (contMDiff_snd.prodMk ((contMDiff_iccHomeoI_symm hab.out).comp contMDiff_fst)) ζ)).val
      x u := by
  rw [mpullback_prodMk_mpullback_iccHomeoI, mpullback_prodMk_mpullback_iccHomeoI, coe_mpullback,
    coe_mpullback]
  -- Pointwise, `h` says that `ζ` is the interior product of `η` with `(V, 0)`.
  have hζ : RoughForm.interior (I := I.prod (𝓡∂ 1)) (F := F) (Manifold.prodVectorField V 0) η.val =
      ζ.val :=
    funext fun q ↦ ContinuousAlternatingMap.ext fun w ↦ by
      rw [RoughForm.interior_apply, Matrix.vecCons, h]
  -- The slice inclusion `y ↦ (y, s)` relates `V` to `(V, 0)`.
  have hd : mfderiv I (I.prod (𝓡∂ 1)) (fun y : M ↦ (y, (iccHomeoI a b hab.out).symm t)) x (V x) =
      Manifold.prodVectorField V 0 (x, (iccHomeoI a b hab.out).symm t) := by
    apply (TauCeti.Manifold.tangentSpaceProdEquiv _).injective
    rw [TauCeti.Manifold.tangentSpaceProdEquiv_mfderiv_prodMk_left,
      TauCeti.Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]
  rw [← hζ, TauCeti.mpullback_interior_at _ V _ _ hd, RoughForm.interior_apply,
    Matrix.vecCons]

/-- **Contraction of the time extension on `M × [a, b]` with a field along `M`.** Let `V` be a
vector field on `M`, `η` a smooth `(k + 1)`-form on `M × Icc a b` and `ζ` a smooth `k`-form
there with `ζ = ι_{(V, 0)} η`, that is, `η_q ((V q.1, 0), w) = ζ_q (w)` at every point `q`.
Then the time extension of `η` contracted with `(V, 0)` is the time extension of `ζ`:
`(timeExtendIcc η)_p ((V p.1, 0), v) = (timeExtendIcc ζ)_p (v)` at every point `p` of `M × ℝ`. -/
theorem timeExtendIcc_apply_cons_prodVectorField (V : Π x : M, TangentSpace I x)
    {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)}
    {ζ : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k}
    (h : ∀ (q : M × Icc a b) (w : Fin k → TangentSpace (I.prod (𝓡∂ 1)) q),
      η.val q (Fin.cons (Manifold.prodVectorField V 0 q) w) = ζ.val q w)
    (p : M × ℝ) (v : Fin k → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (timeExtendIcc η).val p (Fin.cons (Manifold.prodVectorField V 0 p) v) =
      (timeExtendIcc ζ).val p v := by
  rw [timeExtendIcc_apply, timeExtendIcc_apply]
  have hcons : (fun i ↦ (Fin.cons (α := fun _ ↦ TangentSpace (I.prod 𝓘(ℝ, ℝ)) p)
      (Manifold.prodVectorField V 0 p) v i).1) =
      Fin.cons (α := fun _ ↦ E) (V p.1) (fun i ↦ (v i).1) :=
    funext fun i ↦ by
      cases i using Fin.cases
      -- `Fin.cons_zero` and `Fin.cons_succ` hold by definition, on both sides.
      · exact Manifold.prodVectorField_fst V 0 p
      · rfl
  rw [hcons]
  exact timeExtendSlice_apply_cons V
    (fun t x u ↦ mpullback_prodMk_mpullback_iccHomeoI_apply_cons V h t x u) _ _ _

/-- If a smooth `(k + 1)`-form `η` on `M × Icc a b` vanishes as soon as its first argument is
`(V q.1, 0)`, for a vector field `V` on `M`, then so does its time extension
`TauCeti.SmoothForm.timeExtendIcc η` on `M × ℝ`, at every point `p` with first argument
`(V p.1, 0)`. -/
theorem timeExtendIcc_apply_cons_prodVectorField_eq_zero (V : Π x : M, TangentSpace I x)
    {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)}
    (h : ∀ (q : M × Icc a b) (w : Fin k → TangentSpace (I.prod (𝓡∂ 1)) q),
      η.val q (Fin.cons (Manifold.prodVectorField V 0 q) w) = 0)
    (p : M × ℝ) (v : Fin k → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (timeExtendIcc η).val p (Fin.cons (Manifold.prodVectorField V 0 p) v) = 0 := by
  rw [timeExtendIcc_apply_cons_prodVectorField V (ζ := 0) (fun q w ↦ by simp [h]), map_zero]
  simp

end Contraction

end Icc

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slices of the time extension of a smooth form on `unitInterval × M` form a smooth family
over `ℝ`. -/
theorem isSmoothFamily_timeExtendSlice (Ω : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) F k) :
    IsSmoothFamily 𝓘(ℝ, ℝ) (SmoothForm.timeExtendSlice Ω) :=
  isSmoothFamily_def.mpr
    ⟨SmoothForm.timeExtend Ω, SmoothForm.mpullback_prodMk_timeExtend_eq_timeExtendSlice Ω⟩

/-- **Extension of smooth families in time.** On a manifold, every smooth family of
forms over `unitInterval` is the restriction of a smooth family over `ℝ`. -/
theorem IsSmoothFamily.exists_extend {α : unitInterval → SmoothForm I M F k}
    (hα : IsSmoothFamily (𝓡∂ 1) α) :
    ∃ β : ℝ → SmoothForm I M F k, IsSmoothFamily 𝓘(ℝ, ℝ) β ∧ ∀ t : unitInterval, β t = α t := by
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp hα
  exact ⟨SmoothForm.timeExtendSlice Ω, isSmoothFamily_timeExtendSlice Ω,
    fun t ↦ (SmoothForm.timeExtendSlice_coe Ω t).trans (hΩ t)⟩

end SymplecticGeometry
