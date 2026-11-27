/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar

/-!
# Positive frames of the tangent bundle of a surface along a map from a curve

Let `M` be a surface, `J` a smooth almost complex structure on `M` tamed by a smooth two-form `σ`,
and `h : N → M` a smooth map from a compact Hausdorff manifold of dimension at most one, such as
a circle `AddCircle c`. The pulled-back tangent bundle `h^* TM` has rank two over a base of
dimension at most one, so it has a smooth section `v` that vanishes nowhere
(`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`). Then `(v t, J v t)` is a basis
of `T_(h t) M` (`TauCeti.SmoothAlmostComplexStructure.complexFrame`), on which `σ` is positive
since `σ` tames `J`. Sending `1` and `i` to these two vectors gives real linear isomorphisms
`e t : ℂ ≃L[ℝ] T_(h t) M`, smooth in `t`, with `σ (e t 1) (e t i) > 0`.

## Main results

* `TauCeti.SmoothTwoForm.Tames.exists_frame_along`: for `σ` taming `J` on a surface, such a
  family `e` along any smooth map from a compact Hausdorff manifold of dimension at most one.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_frame_along`: the same for a nondegenerate `σ` on
  a Hausdorff σ-compact surface, with `J` given by Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {X N : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace N] [ChartedSpace X N]
  [T2Space N] [CompactSpace N] [IsManifold 𝓘(ℝ, X) ∞ N]
  {σ : SmoothTwoForm I M}

/-- **Positive frames along a curve.** Let `σ` be a smooth two-form taming a smooth almost complex
structure `J` on a surface `M`, and `h : N → M` a smooth map from a compact Hausdorff manifold of
dimension at most one. Then there are real linear isomorphisms `e t : ℂ ≃L[ℝ] T_(h t) M`, smooth
as a map `N × ℂ → TM`, `(t, z) ↦ e t z`, with `σ (e t 1) (e t i) > 0` for every `t`. -/
theorem Tames.exists_frame_along {J : SmoothAlmostComplexStructure I M} (hJ : σ.Tames J)
    (hE : finrank ℝ E = 2) (hX : finrank ℝ X < 2) {h : N → M}
    (hh : ContMDiff 𝓘(ℝ, X) I ∞ h) :
    ∃ e : ∀ t, ℂ ≃L[ℝ] TangentSpace I (h t),
      ContMDiff (𝓘(ℝ, X).prod 𝓘(ℝ, ℂ)) I.tangent ∞
        (fun x : N × ℂ ↦ (⟨h x.1, e x.1 x.2⟩ : TangentBundle I M)) ∧
      ∀ t, 0 < σ.eval₂ (h t) (e t 1) (e t Complex.I) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  let hb : C^∞⟮𝓘(ℝ, X), N; I, M⟯ := ⟨h, hh⟩
  -- A smooth section of `h^* TM` that vanishes nowhere.
  obtain ⟨v, hv⟩ := TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt
    (X := X) (n := ∞) (F := E) (V := (hb : N → M) *ᵖ (TangentSpace I : M → Type _))
    (hdim := by rw [hE]; exact hX)
  -- The same section, with values read as tangent vectors of `M`.
  let w (t : N) : TangentSpace I (h t) := v t
  have hw (t : N) : w t ≠ 0 := hv t
  have hws : ContMDiff 𝓘(ℝ, X) I.tangent ∞ (fun t ↦ (⟨h t, w t⟩ : TangentBundle I M)) :=
    (Bundle.Pullback.contMDiff_lift hb hb.contMDiff).comp v.contMDiff
  have hJw := J.contMDiff_apply hws
  have hfin (t : N) : finrank ℝ (TangentSpace I (h t)) = 2 := hE
  -- The isomorphism sending `(1, i)` to the frame `(w t, J w t)` of `T_(h t) M`.
  let e (t : N) : ℂ ≃L[ℝ] TangentSpace I (h t) :=
    (Complex.basisOneI.equiv (J.complexFrame (hw t) (hfin t)) (Equiv.refl _))
      |>.toContinuousLinearEquiv
  have he (t : N) (z : ℂ) : e t z = z.re • w t + z.im • J (h t) (w t) := by
    have hz : z = z.re • Complex.basisOneI 0 + z.im • Complex.basisOneI 1 := by simp
    conv_lhs => rw [hz]
    rw [LinearEquiv.coe_toContinuousLinearEquiv', map_add, map_smul, map_smul,
      Basis.equiv_apply, Basis.equiv_apply]
    simp
  refine ⟨e, ?_, fun t ↦ ?_⟩
  · simp only [he]
    exact ((Complex.reCLM.contMDiff.comp contMDiff_snd).smul_totalSpace
      (hws.comp contMDiff_fst)).add_sectionAlong
      ((Complex.imCLM.contMDiff.comp contMDiff_snd).smul_totalSpace (hJw.comp contMDiff_fst))
  · rw [he, he]
    simpa using tames_iff.1 hJ (h t) (w t) (hw t)

/-- **Positive frames along a curve in a symplectic surface.** Let `σ` be a nondegenerate smooth
two-form on a Hausdorff σ-compact surface `M`, and `h : N → M` a smooth map from a compact
Hausdorff manifold of dimension at most one, such as a circle. Then there are real linear
isomorphisms `e t : ℂ ≃L[ℝ] T_(h t) M`, smooth as a map `N × ℂ → TM`, `(t, z) ↦ e t z`, with
`σ (e t 1) (e t i) > 0` for every `t`. -/
theorem IsNondegenerate.exists_frame_along [T2Space M] [SigmaCompactSpace M]
    (hσ : σ.IsNondegenerate) (hE : finrank ℝ E = 2) (hX : finrank ℝ X < 2) {h : N → M}
    (hh : ContMDiff 𝓘(ℝ, X) I ∞ h) :
    ∃ e : ∀ t, ℂ ≃L[ℝ] TangentSpace I (h t),
      ContMDiff (𝓘(ℝ, X).prod 𝓘(ℝ, ℂ)) I.tangent ∞
        (fun x : N × ℂ ↦ (⟨h x.1, e x.1 x.2⟩ : TangentBundle I M)) ∧
      ∀ t, 0 < σ.eval₂ (h t) (e t 1) (e t Complex.I) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  obtain ⟨J, hJ⟩ := hσ.exists_compatible
  exact hJ.tames.exists_frame_along hE hX hh

end TauCeti.SmoothTwoForm
