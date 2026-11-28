/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The differential of the inverse of a partial diffeomorphism

At a point `y` of the target of a partial diffeomorphism `Φ`, the differential of `Φ.symm` at `y`
and that of `Φ` at `Φ.symm y` are mutually inverse (Tau Ceti's
`PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply` and
`PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`), so together they form one continuous
linear equivalence.

For a partial diffeomorphism `Φ` into a normed space `E` and a chart of a manifold modelled on
`E`, the transitions between them, in both directions, are smooth with derivatives of nonzero
determinant on their sources. Smoothness is Tau Ceti's
`OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn`, and the determinants are Tau
Ceti's `TauCeti.det_fderiv_symm_trans_ne_zero`, since `Φ` lies in the maximal atlas of the
manifold.

For two `C^n` partial diffeomorphisms `Φ` and `Ψ` from a manifold into normed spaces, the
transition `Ψ ∘ Φ⁻¹` is `C^n` on its source and, for `n ≠ 0`, differentiable there, with the
chain rule `dΨ = dτ ∘ dΦ` at the points of its source. If `Φ` and `Ψ` take values in the same
space and pull a form `B` there back to the same form on the tangent space at `Φ⁻¹ w`, the
derivative of the transition at `w` preserves `B`. The proof of this last fact follows that of
Tau Ceti's `PartialDiffeomorph.inner_fderiv_comp_symm`, with `B` in place of the inner product.

## Main definitions

* `PartialDiffeomorph.mfderivSymmEquiv`: the differential of `Φ.symm` at a point `y` of the target,
  as a continuous linear equivalence whose inverse is the differential of `Φ` at `Φ.symm y`.

## Main results

* `PartialDiffeomorph.toOpenPartialHomeomorph_mdifferentiable`: `Φ` and its inverse are
  differentiable, in the sense of `OpenPartialHomeomorph.MDifferentiable`.
* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_target`: for `y` in the target of
  `Φ`, `d(Φ⁻¹)_y ∘ dΦ_{Φ⁻¹ y}` is the identity.
* `OpenPartialHomeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_maximalAtlas` and
  `OpenPartialHomeomorph.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas`: for a chart `e`
  of the `C^1` maximal atlas and `z` in its target, `d(e⁻¹)_z` and `de_{e⁻¹ z}` are mutually
  inverse.
* `PartialDiffeomorph.contDiffOn_symm_trans_chartAt`,
  `PartialDiffeomorph.contDiffOn_chartAt_symm_trans`,
  `PartialDiffeomorph.det_fderiv_symm_trans_chartAt_ne_zero` and
  `PartialDiffeomorph.det_fderiv_chartAt_symm_trans_ne_zero`: the transitions between `Φ` and a
  chart are smooth, with derivatives of nonzero determinant.
* `PartialDiffeomorph.isInvertible_fderiv_extChartAt_comp_comp`: for `Φ` from a normed space, the
  reading of `Φ` in a chart of the target, after a linear equivalence, has invertible derivative.
* `PartialDiffeomorph.contDiffOn_symm_trans`, `PartialDiffeomorph.differentiableAt_symm_trans`
  and `PartialDiffeomorph.mvfderiv_eq_fderiv_symm_trans_comp`: the transition between two
  partial diffeomorphisms into normed spaces is smooth, and the chain rule through it.
* `PartialDiffeomorph.apply_fderiv_symm_trans_eq_of_mvfderiv`: the derivative of the transition
  between two partial diffeomorphisms, at a point `w`, preserves a form that both pull back to the
  same form at `Φ⁻¹ w`.
-/

public section

open scoped Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

section MFDerivSymmEquiv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- A partial diffeomorphism of nonzero regularity, as an open partial homeomorphism, is
differentiable together with its inverse. -/
theorem toOpenPartialHomeomorph_mdifferentiable (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) :
    Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
  ⟨Φ.mdifferentiableOn hn, Φ.symm.mdifferentiableOn hn⟩

/-- At a point `y` of the target of a partial diffeomorphism `Φ` of nonzero regularity, the
differential of `Φ.symm` at `y` undoes the differential of `Φ` at `Φ.symm y`. -/
theorem mfderiv_symm_apply_mfderiv_apply_of_mem_target (Φ : PartialDiffeomorph I J M N n)
    (hn : n ≠ 0) {y : N} (hy : y ∈ Φ.target) (v : TangentSpace I (Φ.symm y)) :
    mfderiv J I Φ.symm y (mfderiv I J Φ (Φ.symm y) v) = v := by
  have h := Φ.mfderiv_symm_apply_mfderiv_apply hn (Φ.map_target hy) v
  rwa [Φ.right_inv hy] at h

/-- For a point `y` of the target of a partial diffeomorphism `Φ` of nonzero regularity, the
differential of `Φ.symm` at `y`, as a continuous linear equivalence from the tangent space at `y`
to the tangent space at `Φ.symm y`. Its inverse is the differential of `Φ` at `Φ.symm y`
(`PartialDiffeomorph.coe_mfderivSymmEquiv_symm`). -/
noncomputable def mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : TangentSpace J y ≃L[𝕜] TangentSpace I (Φ.symm y) :=
  .ofContinuousLinearMap (mfderiv J I Φ.symm y) (mfderiv I J Φ (Φ.symm y))
    (ContinuousLinearMap.ext (Φ.mfderiv_symm_apply_mfderiv_apply_of_mem_target hn hy))
    (ContinuousLinearMap.ext (Φ.mfderiv_apply_mfderiv_symm_apply hn hy))

@[simp]
theorem coe_mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : ⇑(Φ.mfderivSymmEquiv hn hy) = mfderiv J I Φ.symm y :=
  (rfl)

@[simp]
theorem coe_mfderivSymmEquiv_symm (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : ⇑(Φ.mfderivSymmEquiv hn hy).symm = mfderiv I J Φ (Φ.symm y) :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    {y : N} (hy : y ∈ Φ.target) :
    (Φ.mfderivSymmEquiv hn hy : TangentSpace J y →L[𝕜] TangentSpace I (Φ.symm y)) =
      mfderiv J I Φ.symm y :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_mfderivSymmEquiv_symm (Φ : PartialDiffeomorph I J M N n)
    (hn : n ≠ 0) {y : N} (hy : y ∈ Φ.target) :
    ((Φ.mfderivSymmEquiv hn hy).symm : TangentSpace I (Φ.symm y) →L[𝕜] TangentSpace J y) =
      mfderiv I J Φ (Φ.symm y) :=
  (rfl)

end MFDerivSymmEquiv

section ChartInverse

/-- For a chart `e` of the `C^1` maximal atlas and a point `z` of its target, the derivative of
`e.symm` at `z` undoes the derivative of `e` at `e.symm z`. -/
theorem _root_.OpenPartialHomeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M) {z : H}
    (hz : z ∈ e.target) (v : TangentSpace I (e.symm z)) :
    mfderiv I I e.symm z (mfderiv I I e (e.symm z) v) = v := by
  have h := (e.toPartialDiffeomorph he).mfderiv_symm_apply_mfderiv_apply_of_mem_target
    one_ne_zero (by simpa using hz) v
  rwa [e.coe_toPartialDiffeomorph_symm, e.coe_toPartialDiffeomorph] at h

/-- For a chart `e` of the `C^1` maximal atlas and a point `z` of its target, the derivative of
`e` at `e.symm z` undoes the derivative of `e.symm` at `z`. -/
theorem _root_.OpenPartialHomeomorph.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M) {z : H}
    (hz : z ∈ e.target) (u : TangentSpace I z) :
    mfderiv I I e (e.symm z) (mfderiv I I e.symm z u) = u :=
  e.mfderiv_apply_mfderiv_symm_apply hz
    (mdifferentiableAt_of_mem_maximalAtlas he (e.map_target hz))
    (mdifferentiableAt_symm_of_mem_maximalAtlas he hz) u

end ChartInverse

section ChartTransition

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] {n : WithTop ℕ∞}
  [IsManifold 𝓘(𝕜, E) n M']

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E` and `x : M'`, the transition
`chartAt E x ∘ Φ⁻¹` is `C^n` on its source. -/
theorem contDiffOn_symm_trans_chartAt (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (x : M') :
    ContDiffOn 𝕜 n (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x)
      (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source :=
  OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn contMDiffOn_chart
    Φ.symm.contMDiffOn

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E` and `x : M'`, the transition
`Φ ∘ (chartAt E x)⁻¹` is `C^n` on its source. -/
theorem contDiffOn_chartAt_symm_trans (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (x : M') :
    ContDiffOn 𝕜 n ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph)
      ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source :=
  OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn
    Φ.contMDiffOn (contMDiffOn_chart_symm (x := x))

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E`, `n ≠ 0`, and `x : M'`, the
derivative of the transition `chartAt E x ∘ Φ⁻¹` has nonzero determinant on its source. -/
theorem det_fderiv_symm_trans_chartAt_ne_zero
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (hn : n ≠ 0) (x : M') {z : E}
    (hz : z ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source) :
    (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x) z).det ≠ 0 :=
  TauCeti.det_fderiv_symm_trans_ne_zero hn
    (Φ.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Φ.contMDiffOn Φ.symm.contMDiffOn)
    (IsManifold.chart_mem_maximalAtlas x) hz

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E`, `n ≠ 0`, and `x : M'`, the
derivative of the transition `Φ ∘ (chartAt E x)⁻¹` has nonzero determinant on its source. -/
theorem det_fderiv_chartAt_symm_trans_ne_zero
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (hn : n ≠ 0) (x : M') {z : E}
    (hz : z ∈ ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source) :
    (fderiv 𝕜 ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph) z).det ≠ 0 :=
  TauCeti.det_fderiv_symm_trans_ne_zero hn (IsManifold.chart_mem_maximalAtlas x)
    (Φ.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Φ.contMDiffOn Φ.symm.contMDiffOn)
    hz

end ChartTransition

section ChartReading

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) 1 M']

/-- For a `C^n` partial diffeomorphism `Φ` from a normed space `F` to `M'`, `n ≠ 0`, a continuous
linear equivalence `L : F' ≃L[𝕜] F` and `p ∈ Φ.source`, the reading `κ ∘ Φ ∘ L` of `Φ` in the
extended chart `κ` at `x`, whose source contains `Φ p`, has invertible derivative at `L⁻¹ p`. -/
theorem isInvertible_fderiv_extChartAt_comp_comp {F F' : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (Φ : PartialDiffeomorph 𝓘(𝕜, F) 𝓘(𝕜, E) F M' n) (hn : n ≠ 0) (L : F' ≃L[𝕜] F) {p : F}
    (hp : p ∈ Φ.source) {x : M'} (hx : Φ p ∈ (chartAt E x).source) :
    (fderiv 𝕜 (extChartAt 𝓘(𝕜, E) x ∘ Φ ∘ L) (L.symm p)).IsInvertible := by
  have hκ := isInvertible_mfderiv_extChartAt (I := 𝓘(𝕜, E)) (x := x)
    (by rwa [extChartAt_source])
  have h := TauCeti.isInvertible_mfderiv_comp hκ (Φ.isInvertible_mfderiv hn hp)
  rw [mfderiv_eq_fderiv] at h
  rw [← Function.comp_assoc, L.comp_right_fderiv, L.apply_symm_apply]
  exact h.comp ⟨L, rfl⟩

end ChartReading

section SymmTrans

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
  [NormedSpace 𝕜 F']

/-- For `C^n` partial diffeomorphisms `Φ` and `Ψ` from `M` into normed spaces, the transition
`Ψ ∘ Φ⁻¹` is `C^n` on its source. -/
theorem contDiffOn_symm_trans (Φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n)
    (Ψ : PartialDiffeomorph I 𝓘(𝕜, F') M F' n) :
    ContDiffOn 𝕜 n (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph)
      (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).source :=
  OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn Ψ.contMDiffOn Φ.symm.contMDiffOn

/-- For `C^n` partial diffeomorphisms `Φ` and `Ψ` from `M` into normed spaces, `n ≠ 0`, the
transition `Ψ ∘ Φ⁻¹` is differentiable at each point of its source. -/
theorem differentiableAt_symm_trans (Φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n)
    (Ψ : PartialDiffeomorph I 𝓘(𝕜, F') M F' n) (hn : n ≠ 0) {w : F}
    (hw : w ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).source) :
    DifferentiableAt 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w :=
  ((Φ.contDiffOn_symm_trans Ψ).differentiableOn hn w hw).differentiableAt
    ((Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).open_source.mem_nhds hw)

/-- **The chain rule through a transition.** For `C^n` partial diffeomorphisms `Φ` and `Ψ` from
`M` into normed spaces, `n ≠ 0`, and `w` in the source of the transition `Ψ ∘ Φ⁻¹`, the
derivative of `Ψ` at `Φ⁻¹ w` is the derivative of the transition at `w` after the derivative of
`Φ` at `Φ⁻¹ w`. -/
theorem mvfderiv_eq_fderiv_symm_trans_comp (Φ : PartialDiffeomorph I 𝓘(𝕜, F) M F n)
    (Ψ : PartialDiffeomorph I 𝓘(𝕜, F') M F' n) (hn : n ≠ 0) {w : F}
    (hw : w ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).source) :
    mvfderiv I Ψ (Φ.symm w) =
      (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w).comp
        (mvfderiv I Φ (Φ.symm w)) := by
  have hw' : w ∈ Φ.target ∧ Φ.symm w ∈ Ψ.source := by simpa using hw
  exact Φ.toOpenPartialHomeomorph.mvfderiv_eq_fderiv_symm_trans_comp hw
    (Φ.mdifferentiableAt hn (Φ.map_target hw'.1)) (Φ.differentiableAt_symm_trans Ψ hn hw)

/-- **Transitions between charts that pull back the same form preserve it.** Let `Φ` and `Ψ` be
`C^n` partial diffeomorphisms from `M` into `F`, `n ≠ 0`, and `w` a point of the source of the
transition `Ψ ∘ Φ⁻¹`. If `Φ` and `Ψ` pull the form `B` on `F` back to the same form on the
tangent space at `Φ⁻¹ w`, then the derivative `T` of the transition at `w` satisfies
`B (T u) (T v) = B u v`. -/
theorem apply_fderiv_symm_trans_eq_of_mvfderiv {R : Type*}
    (Φ Ψ : PartialDiffeomorph I 𝓘(𝕜, F) M F n) (hn : n ≠ 0) (B : F → F → R) {w : F}
    (hw : w ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph).source)
    (hB : ∀ u v, B (mvfderiv I Ψ (Φ.symm w) u) (mvfderiv I Ψ (Φ.symm w) v) =
      B (mvfderiv I Φ (Φ.symm w) u) (mvfderiv I Φ (Φ.symm w) v))
    (u v : F) :
    B (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w u)
        (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w v) =
      B u v := by
  have hw' : w ∈ Φ.target ∧ Φ.symm w ∈ Ψ.source := by simpa using hw
  -- The preimage of a vector under the derivative of `Φ` at `Φ⁻¹ w`.
  have hinv (u : F) : mvfderiv I Φ (Φ.symm w) (mfderiv 𝓘(𝕜, F) I Φ.symm w u) = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact Φ.mfderiv_apply_mfderiv_symm_apply hn hw'.1 u
  have hT (u : F) :
      fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ Ψ.toOpenPartialHomeomorph) w u =
        mvfderiv I Ψ (Φ.symm w) (mfderiv 𝓘(𝕜, F) I Φ.symm w u) := by
    rw [Φ.mvfderiv_eq_fderiv_symm_trans_comp Ψ hn hw, ContinuousLinearMap.comp_apply, hinv]
  rw [hT, hT, hB, hinv, hinv]

end SymmTrans

end PartialDiffeomorph
