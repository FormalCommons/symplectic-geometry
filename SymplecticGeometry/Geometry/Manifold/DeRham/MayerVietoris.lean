/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Metrizable
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris

/-!
# Cut-off functions and gluing of forms for a cover by two open sets

For open sets `U` and `V` of a manifold, this file gives the linear operations of a
Mayer–Vietoris argument on smooth forms, as linear maps, so that constructions built from them
are linear.

* `TauCeti.SmoothForm.glueₗ`: two linear maps with values in the forms on `U` and on `V`, whose
  values agree on `U ⊓ V`, glue to a linear map with values in the forms on `U ⊔ V`. It is
  the inverse of the restriction map on its range, which Tau Ceti's
  `TauCeti.SmoothForm.injective_mayerVietoris` and `TauCeti.SmoothForm.exact_mayerVietoris`
  describe, and it is the only such map (`TauCeti.SmoothForm.eq_glueₗ`).
* `SymplecticGeometry.MayerVietorisCutoff I U V`: a smooth function `ρ` on `U ⊔ V` whose support
  lies in `V` and such that the support of `1 - ρ` lies in `U`. One exists on a Hausdorff
  σ-compact manifold modelled on a finite-dimensional space
  (`SymplecticGeometry.MayerVietorisCutoff.nonempty`).
* `MayerVietorisCutoff.extendLeft` and `MayerVietorisCutoff.extendRight`: a form `φ` on `U ⊓ V`
  multiplied by `ρ` and extended by zero to `U`, and multiplied by `1 - ρ` and extended by zero
  to `V`. Their restrictions to `U ⊓ V` add up to `φ`.
* `MayerVietorisCutoff.connecting`: for a closed `k`-form `e` on `U ⊓ V`, the closed
  `(k + 1)`-form on `U ⊔ V` equal to `d (ρ e)` on `U` and to `-d ((1 - ρ) e)` on `V`, the form
  through which Bott and Tu describe the connecting map of the Mayer–Vietoris sequence
  [BottTu1982, §2].

## Adapted from Tau Ceti

Several proofs adapt those of Tau Ceti's file `TauCeti/Geometry/Manifold/DeRham/MayerVietoris.lean`:

* `MayerVietorisCutoff.nonempty` is the construction of the cut-off function in the proof of
  `TauCeti.SmoothForm.surjective_mayerVietoris`.
* `extendLeft`, `extendRight`, `eventually_eq_zero` and `eventually_one_sub_eq_zero` adapt the
  private `cutoffLeft`, `cutoffRight`, `eventually_eq_zero_of_tsupport_subset` and
  `eventually_sub_one_eq_zero_of_tsupport_subset` to linear maps, with `1 - ρ` in place of
  `ρ - 1`; `mpullback_extendLeft_add_mpullback_extendRight` adapts the private
  `mpullback_cutoffLeft_sub_mpullback_cutoffRight`, with the sign changed accordingly.
* `connecting` and `connecting_mem_closedForms` follow
  `TauCeti.exists_closedForms_coe_eq_extendByZero_mextDeriv` and
  `TauCeti.exists_closedForms_mpullback_eq_mextDerivₗ`.
* `mpullback_inclusion_inf_sup_left_eq_right` is the second half of the proof of
  `TauCeti.SmoothForm.exact_mayerVietoris`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982]
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {U V : Opens M}

namespace TauCeti.SmoothForm

section Glue

variable [IsManifold I 1 M]

/-- Restricting a form on `U ⊔ V` to `U ⊓ V` through `U` or through `V` gives the same form. -/
theorem mpullback_inclusion_inf_sup_left_eq_right (φ : SmoothForm I (U ⊔ V : Opens M) F k) :
    mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
        (mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) φ) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) φ) := by
  rw [mpullback_mpullback, mpullback_mpullback]
  -- Both composites of inclusions are, by definition, the inclusion of `U ⊓ V` in `U ⊔ V`.
  rfl

variable {X : Type*} [AddCommMonoid X] [Module ℝ X]

/-- Values of linear maps into the forms on `U` and on `V` that agree on `U ⊓ V` are restrictions
of a form on `U ⊔ V`. -/
private theorem prod_mem_range (TU : X →ₗ[ℝ] SmoothForm I U F k) (TV : X →ₗ[ℝ] SmoothForm I V F k)
    (h : ∀ x, mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (TU x) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) (TV x)) (x : X) :
    TU.prod TV x ∈ LinearMap.range ((mpullback (I := I) (I' := I) (F := F) (k := k)
      (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)).prod
        (mpullback (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _))) :=
  LinearMap.mem_range.mpr <| (exact_mayerVietoris U V _).mp <| by
    rw [LinearMap.prod_apply, Function.prod_apply, LinearMap.coprod_apply, LinearMap.neg_apply,
      h x, add_neg_cancel]

/-- **Gluing linear maps into forms on `U` and on `V`.** Two linear maps `TU` and `TV` with values
in the forms on `U` and on `V`, whose values have the same restrictions to `U ⊓ V`, glue to a
linear map with values in the forms on `U ⊔ V`. -/
def glueₗ (TU : X →ₗ[ℝ] SmoothForm I U F k) (TV : X →ₗ[ℝ] SmoothForm I V F k)
    (h : ∀ x, mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (TU x) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) (TV x)) :
    X →ₗ[ℝ] SmoothForm I (U ⊔ V : Opens M) F k :=
  (LinearEquiv.ofInjective _
    (injective_mayerVietoris (I := I) (F := F) (k := k) U V)).symm.toLinearMap ∘ₗ
    (TU.prod TV).codRestrict _ (prod_mem_range TU TV h)

private theorem prod_glueₗ (TU : X →ₗ[ℝ] SmoothForm I U F k) (TV : X →ₗ[ℝ] SmoothForm I V F k)
    (h : ∀ x, mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (TU x) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) (TV x)) (x : X) :
    (mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (glueₗ TU TV h x),
      mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (glueₗ TU TV h x)) =
      (TU x, TV x) := by
  have := (LinearEquiv.ofInjective _
    (injective_mayerVietoris (I := I) (F := F) (k := k) U V)).apply_symm_apply
      ((TU.prod TV).codRestrict _ (prod_mem_range TU TV h) x)
  rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at this
  -- The left side is, by definition, the pair of restrictions of the glued form.
  exact this

/-- The restriction to `U` of the glued map is the map into the forms on `U`. -/
@[simp]
theorem mpullback_glueₗ_left (TU : X →ₗ[ℝ] SmoothForm I U F k) (TV : X →ₗ[ℝ] SmoothForm I V F k)
    (h : ∀ x, mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (TU x) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) (TV x)) (x : X) :
    mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (glueₗ TU TV h x) = TU x :=
  congrArg Prod.fst (prod_glueₗ TU TV h x)

/-- The restriction to `V` of the glued map is the map into the forms on `V`. -/
@[simp]
theorem mpullback_glueₗ_right (TU : X →ₗ[ℝ] SmoothForm I U F k) (TV : X →ₗ[ℝ] SmoothForm I V F k)
    (h : ∀ x, mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (TU x) =
      mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) (TV x)) (x : X) :
    mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (glueₗ TU TV h x) = TV x :=
  congrArg Prod.snd (prod_glueₗ TU TV h x)

/-- A linear map into the forms on `U ⊔ V` whose restrictions to `U` and to `V` are `TU` and `TV`
is the map that glues `TU` and `TV`. They agree on `U ⊓ V`, being restrictions of `T`. -/
theorem eq_glueₗ {TU : X →ₗ[ℝ] SmoothForm I U F k} {TV : X →ₗ[ℝ] SmoothForm I V F k}
    (T : X →ₗ[ℝ] SmoothForm I (U ⊔ V : Opens M) F k)
    (hU : ∀ x, mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (T x) = TU x)
    (hV : ∀ x, mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (T x) = TV x) :
    T = glueₗ TU TV (fun x ↦ by rw [← hU, ← hV, mpullback_inclusion_inf_sup_left_eq_right]) :=
  LinearMap.ext fun x ↦ injective_mayerVietoris U V <| by
    rw [LinearMap.prod_apply, LinearMap.prod_apply, Function.prod_apply, Function.prod_apply,
      hU, hV, mpullback_glueₗ_left, mpullback_glueₗ_right]

end Glue

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable (I U V) in
/-- **Cut-off functions for a cover by two open sets.** A smooth function `ρ` on `U ⊔ V` whose
support lies in `V` and such that the support of `1 - ρ` lies in `U`. Multiplying a form on
`U ⊓ V` by `ρ`, or by `1 - ρ`, and extending by zero gives a form on `U`, or on `V`. -/
structure MayerVietorisCutoff where
  /-- The cut-off function. -/
  toFun : (U ⊔ V : Opens M) → ℝ
  contMDiff_toFun : ContMDiff I 𝓘(ℝ) ∞ toFun
  tsupport_subset : tsupport toFun ⊆ {x | (x : M) ∈ V}
  tsupport_one_sub_subset : tsupport (fun x ↦ 1 - toFun x) ⊆ {x | (x : M) ∈ U}

namespace MayerVietorisCutoff

instance : FunLike (MayerVietorisCutoff I U V) (U ⊔ V : Opens M) ℝ where
  coe := toFun
  coe_injective c c' h := by
    cases c
    cases c'
    congr

/-- The field `toFun` is the coercion to a function. -/
@[simp]
theorem toFun_eq_coe (c : MayerVietorisCutoff I U V) : c.toFun = ⇑c :=
  rfl

/-- Two cut-off functions with the same values are equal. -/
@[ext]
theorem ext {c c' : MayerVietorisCutoff I U V} (h : ∀ x, c x = c' x) : c = c' :=
  DFunLike.ext _ _ h

variable (c : MayerVietorisCutoff I U V)

/-- A cut-off function is smooth. -/
theorem contMDiff : ContMDiff I 𝓘(ℝ) ∞ c := by
  rw [← toFun_eq_coe]
  exact c.contMDiff_toFun

/-- The support of a cut-off function lies in `V`. -/
theorem tsupport_coe_subset : tsupport c ⊆ {x | (x : M) ∈ V} := by
  rw [← toFun_eq_coe]
  exact c.tsupport_subset

/-- The support of one minus a cut-off function lies in `U`. -/
theorem tsupport_one_sub_coe_subset : tsupport (fun x ↦ 1 - c x) ⊆ {x | (x : M) ∈ U} := by
  simp only [← toFun_eq_coe]
  exact c.tsupport_one_sub_subset

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, every cover by two
open sets has a cut-off function. -/
theorem nonempty [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (U V : Opens M) : Nonempty (MayerVietorisCutoff I U V) := by
  have := TauCeti.Manifold.sigmaCompactSpace_opens I (U ⊔ V)
  have := TauCeti.Manifold.normalSpace_opens I (U ⊔ V)
  have hA : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ V} :=
    (V.isOpen.preimage continuous_subtypeVal).isClosed_compl
  have hB : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ U} :=
    (U.isOpen.preimage continuous_subtypeVal).isClosed_compl
  have hAB : Disjoint {x : (U ⊔ V : Opens M) | (x : M) ∉ V} {x | (x : M) ∉ U} :=
    disjoint_left.mpr fun x hxV hxU ↦ (Opens.mem_sup.mp x.property).elim hxU hxV
  obtain ⟨ρ, hρ0, hρ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hA hB hAB
  refine ⟨⟨ρ, ρ.contMDiff, fun x hx ↦ not_not.mp fun hxV ↦
    notMem_tsupport_iff_eventuallyEq.mpr (hρ0.filter_mono (nhds_le_nhdsSet hxV)) hx,
    fun x hx ↦ not_not.mp fun hxU ↦ notMem_tsupport_iff_eventuallyEq.mpr
      ((hρ1.filter_mono (nhds_le_nhdsSet hxU)).mono fun _ hy ↦ sub_eq_zero.mpr hy.symm) hx⟩⟩

/-- The cut-off function vanishes near every point of `U` outside `U ⊓ V`. -/
theorem eventually_eq_zero {x : U} (hx : (x : M) ∉ U ⊓ V) :
    ∀ᶠ y in 𝓝 x, c (Opens.inclusion le_sup_left y) = 0 :=
  (continuous_inclusion (le_sup_left : U ≤ U ⊔ V)).continuousAt.eventually
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx ⟨x.property, c.tsupport_coe_subset h⟩)

/-- One minus the cut-off function vanishes near every point of `V` outside `U ⊓ V`. -/
theorem eventually_one_sub_eq_zero {x : V} (hx : (x : M) ∉ U ⊓ V) :
    ∀ᶠ y in 𝓝 x, 1 - c (Opens.inclusion le_sup_right y) = 0 :=
  (continuous_inclusion (le_sup_right : V ≤ U ⊔ V)).continuousAt.eventually
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦
      hx ⟨c.tsupport_one_sub_coe_subset h, x.property⟩)

variable [IsManifold I ∞ M]

/-- A form `φ` on `U ⊓ V`, multiplied by the cut-off function `ρ` and extended by zero to `U`. -/
def extendLeft : SmoothForm I (U ⊓ V : Opens M) F k →ₗ[ℝ] SmoothForm I U F k where
  toFun φ := ⟨RoughForm.extendByZero U fun y : (U ⊓ V : Opens M) ↦
      c (Opens.inclusion inf_le_sup y) • φ.val y,
    (φ.isSmoothForm.extendByZero_smul inf_le_left
      (c.contMDiff.comp (contMDiff_inclusion le_sup_left))
      fun _ hx ↦ c.eventually_eq_zero hx).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| by
    simp only [Submodule.coe_add, ← RoughForm.extendByZero_add]
    congr 1
    funext y
    simp [smul_add]
  map_smul' a φ := Subtype.ext <| by
    simp only [Submodule.coe_smul, RingHom.id_apply, ← RoughForm.extendByZero_smul]
    congr 1
    funext y
    simp [smul_comm a]

/-- A form `φ` on `U ⊓ V`, multiplied by `1 - ρ` and extended by zero to `V`. -/
def extendRight : SmoothForm I (U ⊓ V : Opens M) F k →ₗ[ℝ] SmoothForm I V F k where
  toFun φ := ⟨RoughForm.extendByZero V fun y : (U ⊓ V : Opens M) ↦
      (1 - c (Opens.inclusion inf_le_sup y)) • φ.val y,
    (φ.isSmoothForm.extendByZero_smul inf_le_right
      (contMDiff_const.sub (c.contMDiff.comp (contMDiff_inclusion le_sup_right)))
      fun _ hx ↦ c.eventually_one_sub_eq_zero hx).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| by
    simp only [Submodule.coe_add, ← RoughForm.extendByZero_add]
    congr 1
    funext y
    simp [smul_add]
  map_smul' a φ := Subtype.ext <| by
    simp only [Submodule.coe_smul, RingHom.id_apply, ← RoughForm.extendByZero_smul]
    congr 1
    funext y
    simp [smul_comm a]

/-- The underlying rough form of `extendLeft`. -/
theorem coe_extendLeft (φ : SmoothForm I (U ⊓ V : Opens M) F k) :
    (c.extendLeft φ).val = RoughForm.extendByZero U fun y : (U ⊓ V : Opens M) ↦
      c (Opens.inclusion inf_le_sup y) • φ.val y :=
  (rfl)

/-- The underlying rough form of `extendRight`. -/
theorem coe_extendRight (φ : SmoothForm I (U ⊓ V : Opens M) F k) :
    (c.extendRight φ).val = RoughForm.extendByZero V fun y : (U ⊓ V : Opens M) ↦
      (1 - c (Opens.inclusion inf_le_sup y)) • φ.val y :=
  (rfl)

/-- On `U ⊓ V`, the two cut-off forms of `φ` add up to `φ`. -/
theorem mpullback_extendLeft_add_mpullback_extendRight (φ : SmoothForm I (U ⊓ V : Opens M) F k) :
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) (c.extendLeft φ) +
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (c.extendRight φ) = φ := by
  apply Subtype.ext
  rw [Submodule.coe_add, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, coe_extendLeft,
    coe_extendRight, RoughForm.mpullback_inclusion_extendByZero,
    RoughForm.mpullback_inclusion_extendByZero]
  funext y
  simp only [Pi.add_apply, sub_smul, one_smul]
  -- The two cut-off factors are the same function, read through the two inclusions of `U ⊓ V`.
  exact add_sub_cancel _ _

/-- On `U ⊓ V`, the exterior derivatives of the two cut-off forms of `φ` add up to `dφ`. -/
theorem mpullback_mextDerivₗ_extendLeft_add_mpullback_mextDerivₗ_extendRight
    (φ : SmoothForm I (U ⊓ V : Opens M) F k) :
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
        (mextDerivₗ I k (c.extendLeft φ)) +
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (mextDerivₗ I k (c.extendRight φ)) = mextDerivₗ I k φ := by
  rw [← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback, ← map_add,
    mpullback_extendLeft_add_mpullback_extendRight]

/-- The connecting form `δ e` of a closed form `e` on `U ⊓ V`: the form on `U ⊔ V` that is
`d (ρ e)` on `U` and `-d ((1 - ρ) e)` on `V`. -/
def connecting (k : ℕ) : closedForms I (U ⊓ V : Opens M) k →ₗ[ℝ]
    SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1) :=
  SmoothForm.glueₗ (mextDerivₗ I k ∘ₗ c.extendLeft ∘ₗ (closedForms I _ k).subtype)
    (-(mextDerivₗ I k ∘ₗ c.extendRight ∘ₗ (closedForms I _ k).subtype))
      fun (e : closedForms I (U ⊓ V : Opens M) k) ↦ by
      have h := c.mpullback_mextDerivₗ_extendLeft_add_mpullback_mextDerivₗ_extendRight
        (e : SmoothForm I (U ⊓ V : Opens M) ℝ k)
      rw [(mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp e.property, add_eq_zero_iff_eq_neg] at h
      simpa [map_neg] using h

/-- The restriction of `δ e` to `U` is `d (ρ e)`. -/
@[simp]
theorem mpullback_connecting_left (e : closedForms I (U ⊓ V : Opens M) k) :
    SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (c.connecting k e) =
      mextDerivₗ I k (c.extendLeft e.val) :=
  SmoothForm.mpullback_glueₗ_left _ _ _ e

/-- The restriction of `δ e` to `V` is `-d ((1 - ρ) e)`. -/
@[simp]
theorem mpullback_connecting_right (e : closedForms I (U ⊓ V : Opens M) k) :
    SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (c.connecting k e) =
      -mextDerivₗ I k (c.extendRight e.val) :=
  SmoothForm.mpullback_glueₗ_right _ _ _ e

/-- The connecting form is closed. -/
theorem connecting_mem_closedForms (e : closedForms I (U ⊓ V : Opens M) k) :
    c.connecting k e ∈ closedForms I (U ⊔ V : Opens M) (k + 1) := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero]
  refine SmoothForm.injective_mayerVietoris U V ?_
  rw [map_zero, LinearMap.prod_apply, Function.prod_apply, ← SmoothForm.mextDerivₗ_mpullback,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_connecting_left, mpullback_connecting_right,
    map_neg]
  exact Prod.ext (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _)
    (neg_eq_zero.mpr (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _))

end MayerVietorisCutoff

end SymplecticGeometry
