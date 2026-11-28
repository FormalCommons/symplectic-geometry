/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import SymplecticGeometry.Geometry.Manifold.Submersion.Curvature
import SymplecticGeometry.Geometry.Manifold.Submersion.VerticalProjection
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The curvature of the connection of a two-form

Let `τ` be a two-form on `M` and `proj : M → B` a map such that the `τ`-orthogonals of the
vertical spaces form an Ehresmann connection `hD` (for a smooth submersion this holds when `τ` is
vertically nondegenerate, `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isEhresmannConnection`).
Lifting a field `v` on `B` horizontally gives `v♯`. This file shows that the
curvature of `hD` is determined, through `τ`, by the function `τ(v₁♯, v₂♯)` and the exterior
derivative of `τ`: for every vertical vector `η` at `x`,

`τ(Ω(v₁, v₂), η) = η(τ(v₁♯, v₂♯)) - dτ(v₁♯, v₂♯, η)`,

where `Ω(v₁, v₂) = [v₁♯, v₂♯] - [v₁, v₂]♯` is `hD.curvature v₁ v₂`. No closedness of `τ` is
assumed. When `τ` is closed, the last term vanishes, and the identity says that on each fibre the
contraction of `τ` with the curvature is the differential of the restriction of `τ(v₁♯, v₂♯)`.

As a consequence, two closed two-forms `τ` and `τ'` that agree whenever one argument is vertical
(so that they have the same connection) give functions `τ(v₁♯, v₂♯)` and `τ'(v₁♯, v₂♯)` with
the same derivative along every vertical vector: both sides of the identity for `τ'` agree with
those for `τ`.

The proof follows Guillemin–Lerman–Sternberg [GuilleminLermanSternberg1996], §1.3–1.4. Extend `η`
to a vertical vector field `W` (the vertical projection of a local extension of `η`) and expand
`dτ(v₁♯, v₂♯, W)` by the invariant formula `TauCeti.SmoothForm.mextDeriv_apply_two`. The
functions `τ(vᵢ♯, W)` vanish identically, since horizontal vectors are `τ`-orthogonal to vertical
ones. The brackets `[vᵢ♯, W]` are vertical, since `vᵢ♯` is `proj`-related to `vᵢ` and `W` to `0`
(`ContMDiffAt.mlieBracket_mem_ker_mfderiv_of_eventually_related`), so their pairings with the
lifts vanish too. In the remaining bracket term, `[v₁♯, v₂♯]` differs from the curvature by the
horizontal field `[v₁, v₂]♯`, which `τ` pairs with `W` to zero.

On signs: the bracket is Mathlib's `VectorField.mlieBracket`, as in [GuilleminLermanSternberg1996];
in McDuff–Salamon [McDuffSalamon2017], Lemma 6.4.8, the bracket and so the curvature have the
opposite sign (see also the errata [McDuffSalamon2019Errata]).

## Main results

* `TauCeti.IsEhresmannConnection.apply_curvature_eq_mvfderiv_sub_mextDeriv`: the curvature
  identity for the connection of a two-form.
* `TauCeti.IsEhresmannConnection.mvfderiv_val_horizontalLiftField_eq_of_isClosed`: for two
  closed forms with the same connection, `τ(v₁♯, v₂♯)` and `τ'(v₁♯, v₂♯)` have the same
  derivative along vertical vectors.

## References

* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3–1.4.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Lemma 6.4.8.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

noncomputable section

open Bundle Filter VectorField
open scoped Manifold ContDiff

namespace TauCeti.IsEhresmannConnection

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [CompleteSpace EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB 2 B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [CompleteSpace EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {τ : SmoothTwoForm IM M} {n : ℕ∞ω}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **The curvature identity.** Let `hD` be the connection of a two-form `τ` on `M`: the
`τ`-orthogonals of the vertical spaces of a `C^2` map `proj : M → B`, assumed to form a `C^n`
Ehresmann connection with `1 ≤ n`. Let `v₁ v₂` be vector fields on `B`, `C^1` at `proj x`, with
horizontal lifts `v₁♯ v₂♯`. Then for every vertical vector `η` at `x`, `τ` pairs the curvature
`[v₁♯, v₂♯] - [v₁, v₂]♯` with `η` to the derivative of `τ(v₁♯, v₂♯)` along `η` minus
`dτ(v₁♯, v₂♯, η)`.

Milestone: *Curvature identity for symplectic connections*. -/
theorem apply_curvature_eq_mvfderiv_sub_mextDeriv
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hproj : ContMDiff IM IB 2 proj) {v₁ v₂ : Π b : B, TangentSpace IB b} {x : M}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) (proj x))
    (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) (proj x))
    {η : TangentSpace IM x} (hη : η ∈ (mfderiv IM IB proj x).ker) :
    τ.val x ![hD.curvature v₁ v₂ x, η] =
      mvfderiv IM (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
          x η -
        mextDeriv τ.val x ![hD.horizontalLiftField v₁ x, hD.horizontalLiftField v₂ x, η] := by
  -- A vertical field `W` through `η`: the vertical part of a local extension of `η`.
  -- Read as a `C^1` connection, `hD` has a `C^1` vertical projection, `proj` being `C^2`.
  have hD₁ := hD.of_le hn
  obtain ⟨W, hWdef⟩ : ∃ W : Π y : M, TangentSpace IM y,
      W = fun y ↦ hD₁.verticalProjection y (FiberBundle.extend EM η y) := ⟨_, rfl⟩
  have hWx : W x = η := by
    simp only [hWdef, FiberBundle.extend_apply_self, hD₁.verticalProjection_apply_of_mem_ker hη]
  have hWv (y : M) : W y ∈ (mfderiv IM IB proj y).ker := by
    rw [hWdef]
    exact hD₁.verticalProjection_apply_mem y _
  have hW : MDifferentiableAt IM IM.tangent (T% W) x := by
    have h1 := hD₁.contMDiff_totalSpace_verticalProjection (by rwa [one_add_one_eq_two])
    have h2 := (h1 _).comp x (FiberBundle.contMDiffAt_extend (k := 1) (I := IM) EM η)
    rw [hWdef]
    exact h2.mdifferentiableAt one_ne_zero
  have hpx : ContMDiffAt IM IB 2 proj x := hproj x
  have hU := hD.mdifferentiableAt_horizontalLiftField hn hpx hv₁
  have hV := hD.mdifferentiableAt_horizontalLiftField hn hpx hv₂
  -- The brackets of the lifts with `W` are vertical.
  have hbr {v : Π b : B, TangentSpace IB b} (hv : ContMDiffAt IB IB.tangent 1 (T% v) (proj x)) :
      mlieBracket IM (hD.horizontalLiftField v) W x ∈ (mfderiv IM IB proj x).ker :=
    hpx.mlieBracket_mem_ker_mfderiv_of_eventually_related (by simp)
      (hD.mdifferentiableAt_horizontalLiftField hn hpx hv) hW
      (hv.mdifferentiableAt one_ne_zero)
      (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v y) (.of_forall hWv)
  have hzero {v : Π b : B, TangentSpace IB b} :
      (fun y ↦ τ.val y ![hD.horizontalLiftField v y, W y]) = 0 :=
    funext fun y ↦ SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
        (hD.horizontalLiftField_mem v y) (hWv y)
  have h := SmoothForm.mextDeriv_apply_two (φ := τ) hU hV hW
  rw [hzero, hzero, mvfderiv_zero, hWx,
    SmoothTwoForm.val_eq_zero_of_mem_ker_of_mem_horizontalDistribution (hbr hv₁)
      (hD.horizontalLiftField_mem v₂ x),
    SmoothTwoForm.val_eq_zero_of_mem_ker_of_mem_horizontalDistribution (hbr hv₂)
      (hD.horizontalLiftField_mem v₁ x)] at h
  -- The bracket of the lifts is the curvature plus the horizontal lift of the bracket.
  have hsplit : mlieBracket IM (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x =
      hD.curvature v₁ v₂ x + hD.horizontalLiftField (mlieBracket IB v₁ v₂) x := by
    rw [curvature_apply, sub_add_cancel]
  have hlift := SmoothTwoForm.val_eq_zero_of_mem_horizontalDistribution_of_mem_ker
    (hD.horizontalLiftField_mem (mlieBracket IB v₁ v₂) x) hη
  rw [hsplit, ContinuousAlternatingMap.vecCons_add, hlift, add_zero] at h
  rw [h, zero_apply, zero_apply]
  abel

/-- **Closed forms with the same connection.** Let `τ` and `τ'` be closed two-forms that agree on
`(η, v)` for every vertical vector `η` and every tangent vector `v`, so that they have the same
horizontal spaces, and let `hD` be the connection of `τ`, a `C^n` Ehresmann connection with
`1 ≤ n` on a `C^2` map `proj`. Let `v₁ v₂` be vector fields on `B`, `C^1` at `proj x`. Then the
functions `τ'(v₁♯, v₂♯)` and `τ(v₁♯, v₂♯)` have the same derivative along every vertical vector
`η` at `x`. -/
theorem mvfderiv_val_horizontalLiftField_eq_of_isClosed
    (hD : IsEhresmannConnection IM IB n proj (SmoothTwoForm.horizontalDistribution IB proj τ))
    (hn : 1 ≤ n) (hproj : ContMDiff IM IB 2 proj) {τ' : SmoothTwoForm IM M}
    (hτ : τ.IsClosed) (hτ' : τ'.IsClosed)
    (h : ∀ y, ∀ η ∈ (mfderiv IM IB proj y).ker, ∀ v : TangentSpace IM y,
      τ.bilinFormAt y η v = τ'.bilinFormAt y η v)
    {v₁ v₂ : Π b : B, TangentSpace IB b} {x : M}
    (hv₁ : ContMDiffAt IB IB.tangent 1 (T% v₁) (proj x))
    (hv₂ : ContMDiffAt IB IB.tangent 1 (T% v₂) (proj x))
    {η : TangentSpace IM x} (hη : η ∈ (mfderiv IM IB proj x).ker) :
    mvfderiv IM (fun y ↦ τ'.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
        x η =
      mvfderiv IM (fun y ↦ τ.val y ![hD.horizontalLiftField v₁ y, hD.horizontalLiftField v₂ y])
        x η := by
  -- `τ` and `τ'` have the same horizontal spaces, so `hD` is also the connection of `τ'`.
  have hdist : SmoothTwoForm.horizontalDistribution IB proj τ =
      SmoothTwoForm.horizontalDistribution IB proj τ' :=
    SmoothTwoForm.horizontalDistribution_eq_of_forall h
  have key : ∀ D (hD' : IsEhresmannConnection IM IB n proj D),
      D = SmoothTwoForm.horizontalDistribution IB proj τ' →
      τ'.val x ![hD'.curvature v₁ v₂ x, η] =
        mvfderiv IM (fun y ↦ τ'.val y ![hD'.horizontalLiftField v₁ y,
            hD'.horizontalLiftField v₂ y]) x η -
          mextDeriv τ'.val x ![hD'.horizontalLiftField v₁ x, hD'.horizontalLiftField v₂ x, η] := by
    rintro D hD' rfl
    exact apply_curvature_eq_mvfderiv_sub_mextDeriv hD' hn hproj hv₁ hv₂ hη
  have h' := key _ hD hdist
  have h₀ := apply_curvature_eq_mvfderiv_sub_mextDeriv hD hn hproj hv₁ hv₂ hη
  rw [(SmoothForm.isClosed_def τ).1 hτ] at h₀
  rw [(SmoothForm.isClosed_def τ').1 hτ'] at h'
  -- `τ` and `τ'` pair the curvature with the vertical vector `η` alike.
  have hΩ : τ'.val x ![hD.curvature v₁ v₂ x, η] = τ.val x ![hD.curvature v₁ v₂ x, η] := by
    have hη' := h x η hη (hD.curvature v₁ v₂ x)
    rw [SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply] at hη'
    rw [← SmoothBundleForm.eval₂_apply τ', ← SmoothBundleForm.eval₂_apply τ,
      SmoothBundleForm.eval₂_swap τ', SmoothBundleForm.eval₂_swap τ, hη']
  exact sub_left_injective (h'.symm.trans (hΩ.trans h₀))

end TauCeti.IsEhresmannConnection
