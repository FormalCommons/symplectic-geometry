/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The chart pushforward of a smooth almost complex structure

Tau Ceti's `SmoothAlmostComplexStructure.chartPushforward` pushes a smooth almost complex
structure `J` on `M` forward along a chart `ψ : M → G` into a normed space: at `p` it is
`dψ ∘ J ∘ dψ⁻¹`, taken at `ψ⁻¹ p`. This file gives its evaluation lemma, the counterpart of Tau
Ceti's `ContMDiffAlmostComplexStructure.chartPushforward_apply`, and, for a smooth chart
`ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞`, the facts that the derivatives of `ψ` and of its
inverse intertwine `J` with its pushforward, and that the pushforward squares to `-1` on the
target of `ψ`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_apply`: the value of the pushforward.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_chartPushforward_apply` and
  `TauCeti.SmoothAlmostComplexStructure.mfderiv_symm_apply_chartPushforward_apply`: the
  derivative of a smooth chart, and that of its inverse, intertwine `J` with its pushforward.
* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_apply_chartPushforward_apply`: the
  pushforward squares to `-1` on the target.
* `TauCeti.SmoothAlmostComplexStructure.forall_chartPushforward_apply_eq_iff`: a chart pushes `J`
  forward to a fixed map exactly when its derivative intertwines `J` with that map.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (J : SmoothAlmostComplexStructure I M)

/-- The value of the pushforward of `J` along `ψ` at `p` on `w` is `dψ (J (dψ⁻¹ w))`, with the
derivatives of `ψ` at `ψ⁻¹ p` and of `ψ⁻¹` at `p`. -/
theorem chartPushforward_apply (ψ : OpenPartialHomeomorph M G) (p w : G) :
    J.chartPushforward ψ p w =
      mfderiv I 𝓘(ℝ, G) ψ (ψ.symm p) (J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w)) := by
  -- Tau Ceti does not expose `chartPushforward`; its finite-regularity version has this lemma.
  rw [← toContMDiff_chartPushforward J ⊤, ContMDiffAlmostComplexStructure.chartPushforward_apply,
    toContMDiff_apply]

/-- The derivative of a smooth chart `ψ` into a normed space intertwines `J` with its pushforward
along `ψ`: `dψ_y (J v) = (ψ_* J)_{ψ y} (dψ_y v)` at every point `y` of the source of `ψ`. -/
theorem mfderiv_apply_eq_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) {y : M}
    (hy : y ∈ ψ.source) (v : TangentSpace I y) :
    mfderiv I 𝓘(ℝ, G) ψ y (J y v) =
      J.chartPushforward ψ.toOpenPartialHomeomorph (ψ y) (mfderiv I 𝓘(ℝ, G) ψ y v) := by
  have h := DFunLike.congr_fun ((J.toContMDiff ⊤).mfderiv_comp_toEndomorphism
    ψ.toOpenPartialHomeomorph hy (ψ.mdifferentiableAt (by simp) hy)
    (ψ.symm.mdifferentiableAt (by simp) (ψ.map_source hy))) v
  simp only [toContMDiff_chartPushforward, toContMDiff_toEndomorphism_apply,
    ψ.toFun'_toOpenPartialHomeomorph] at h
  exact h

/-- The derivative of the inverse of a smooth chart `ψ` into a normed space intertwines the
pushforward of `J` along `ψ` with `J`: `dψ⁻¹_p ((ψ_* J)_p w) = J (dψ⁻¹_p w)` at every point `p`
of the target of `ψ`. -/
theorem mfderiv_symm_apply_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) (w : G) :
    mfderiv 𝓘(ℝ, G) I ψ.symm p (J.chartPushforward ψ.toOpenPartialHomeomorph p w) =
      J (ψ.symm p) (mfderiv 𝓘(ℝ, G) I ψ.symm p w) := by
  rw [chartPushforward_apply, ψ.coe_toOpenPartialHomeomorph_symm, ψ.toFun'_toOpenPartialHomeomorph,
    ← ψ.coe_mfderivSymmEquiv (by simp) hp, ← ψ.coe_mfderivSymmEquiv_symm (by simp) hp]
  exact (ψ.mfderivSymmEquiv _ hp).apply_symm_apply _

/-- The pushforward of `J` along a smooth chart `ψ` into a normed space squares to `-1` at every
point of the target of `ψ`. -/
theorem chartPushforward_apply_chartPushforward_apply (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    {p : G} (hp : p ∈ ψ.target) (w : G) :
    J.chartPushforward ψ.toOpenPartialHomeomorph p
      (J.chartPushforward ψ.toOpenPartialHomeomorph p w) = -w := by
  have h := (J.toContMDiff ⊤).chartPushforward_apply_chartPushforward_apply
    ψ.toOpenPartialHomeomorph hp (ψ.mdifferentiableAt (by simp) (ψ.map_target hp))
    (ψ.symm.mdifferentiableAt (by simp) hp) w
  rwa [toContMDiff_chartPushforward] at h

/-- A smooth chart `ψ` into a normed space carries `J` to a fixed map `J₀` on its target exactly
when its derivative intertwines `J` with `J₀` at every point of its source. -/
theorem forall_chartPushforward_apply_eq_iff (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞)
    (J₀ : G → G) :
    (∀ p ∈ ψ.target, ∀ w : G, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) ↔
      ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v) := by
  refine ⟨fun h y hy v ↦ ?_, fun h p hp w ↦ ?_⟩
  · exact (J.mfderiv_apply_eq_chartPushforward_apply ψ hy v).trans (h _ (ψ.map_source hy) _)
  · rw [chartPushforward_apply]
    exact (h _ (ψ.map_target hp) _).trans
      (congrArg J₀ (ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hp w))

end SmoothAlmostComplexStructure

end TauCeti

end
