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
# Frames of the tangent bundle of a surface along a map from a curve

Let `M` be a surface with a smooth almost complex structure `J`, and `h : N → M` a smooth map
from a compact Hausdorff manifold of dimension at most one, such as a circle `AddCircle c`. The
pulled-back tangent bundle `h^* TM` has rank two over a base of dimension at most one, so it has a
smooth section `v` that vanishes nowhere
(`TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt`). Then `(v t, J v t)` is a basis
of `T_(h t) M` (`TauCeti.SmoothAlmostComplexStructure.complexFrame`), and sending `1` and `i` to
these two vectors gives real linear isomorphisms `e t : ℂ ≃L[ℝ] T_(h t) M`, smooth in `t`, that
carry multiplication by `i` to `J`. If a smooth two-form `σ` tames `J`, then
`σ (e t 1) (e t i) > 0`.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.complexFrameEquiv`: for a nonzero tangent vector `v` of
  an almost complex surface, the real linear isomorphism `ℂ ≃L[ℝ] T_c M` sending `1, i` to
  `v, J v`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.exists_frame_along`: a smooth family `e` of such
  isomorphisms along any smooth map from a compact Hausdorff manifold of dimension at most one,
  with `e t (i • z) = J (e t z)`.
* `TauCeti.SmoothTwoForm.Tames.exists_frame_along`: for `σ` taming `J`, such a family with
  `σ (e t 1) (e t i) > 0`.
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

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

section complexFrameEquiv

variable {c : M} {v : TangentSpace I c} (hv : v ≠ 0)
  (hc : finrank ℝ (TangentSpace I c) = 2)

/-- For a nonzero tangent vector `v` of an almost complex surface, the real linear isomorphism
`ℂ ≃L[ℝ] T_c M` that sends `1` to `v` and `i` to `J v`, that is, `z ↦ re z • v + im z • J v`. -/
def complexFrameEquiv : ℂ ≃L[ℝ] TangentSpace I c :=
  (Complex.basisOneI.equiv (J.complexFrame hv hc) (Equiv.refl _)).toContinuousLinearEquiv

/-- `complexFrameEquiv` sends `z` to `re z • v + im z • J v`. -/
@[simp]
theorem complexFrameEquiv_apply (z : ℂ) :
    J.complexFrameEquiv hv hc z = z.re • v + z.im • J c v := by
  have hb (i : Fin 2) :
      J.complexFrameEquiv hv hc (Complex.basisOneI i) = J.complexFrame hv hc i := by
    rw [complexFrameEquiv, LinearEquiv.coe_toContinuousLinearEquiv', Basis.equiv_apply,
      Equiv.refl_apply]
  have h1 : J.complexFrameEquiv hv hc 1 = v := by simpa using hb 0
  have hI : J.complexFrameEquiv hv hc Complex.I = J c v := by simpa using hb 1
  calc J.complexFrameEquiv hv hc z
      = z.re • J.complexFrameEquiv hv hc 1 + z.im • J.complexFrameEquiv hv hc Complex.I :=
        LinearMap.apply_eq_re_smul_one_add_im_smul_I
          (J.complexFrameEquiv hv hc : ℂ →L[ℝ] TangentSpace I c).toLinearMap z
    _ = z.re • v + z.im • J c v := by rw [h1, hI]

/-- `complexFrameEquiv` sends `1` to `v`. -/
theorem complexFrameEquiv_one : J.complexFrameEquiv hv hc 1 = v := by
  simp

/-- `complexFrameEquiv` sends `i` to `J v`. -/
theorem complexFrameEquiv_I : J.complexFrameEquiv hv hc Complex.I = J c v := by
  simp

/-- `complexFrameEquiv` carries multiplication by `i` to `J`. -/
theorem complexFrameEquiv_I_smul (z : ℂ) :
    J.complexFrameEquiv hv hc (Complex.I • z) = J c (J.complexFrameEquiv hv hc z) := by
  rw [smul_eq_mul, mul_comm]
  exact LinearMap.apply_mul_I_eq_of_apply_I_eq
    (J.complexFrameEquiv hv hc : ℂ →L[ℝ] TangentSpace I c).toLinearMap
    (A := (J.toEndomorphism c).toLinearMap) (by simp) (J.apply_apply c) z

end complexFrameEquiv

variable {X N : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace N]
  [ChartedSpace X N] [T2Space N] [CompactSpace N] [IsManifold 𝓘(ℝ, X) ∞ N]

/-- **Complex frames along a curve.** Let `J` be a smooth almost complex structure on a surface
`M`, and `h : N → M` a smooth map from a compact Hausdorff manifold of dimension at most one.
Then there are real linear isomorphisms `e t : ℂ ≃L[ℝ] T_(h t) M`, smooth as a map
`N × ℂ → TM`, `(t, z) ↦ e t z`, with `e t (i • z) = J (e t z)` for every `t` and `z`. -/
theorem exists_frame_along (hE : finrank ℝ E = 2) (hX : finrank ℝ X < 2) {h : N → M}
    (hh : ContMDiff 𝓘(ℝ, X) I ∞ h) :
    ∃ e : ∀ t, ℂ ≃L[ℝ] TangentSpace I (h t),
      ContMDiff (𝓘(ℝ, X).prod 𝓘(ℝ, ℂ)) I.tangent ∞
        (fun x : N × ℂ ↦ (⟨h x.1, e x.1 x.2⟩ : TangentBundle I M)) ∧
      ∀ t z, e t (Complex.I • z) = J (h t) (e t z) := by
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
  refine ⟨fun t ↦ J.complexFrameEquiv (hw t) (hfin t), ?_,
    fun t z ↦ J.complexFrameEquiv_I_smul (hw t) (hfin t) z⟩
  dsimp only
  simp only [complexFrameEquiv_apply]
  exact ((Complex.reCLM.contMDiff.comp contMDiff_snd).smul_totalSpace
    (hws.comp contMDiff_fst)).add_sectionAlong
    ((Complex.imCLM.contMDiff.comp contMDiff_snd).smul_totalSpace (hJw.comp contMDiff_fst))

end TauCeti.SmoothAlmostComplexStructure

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
  obtain ⟨e, he, hJe⟩ := J.exists_frame_along hE hX hh
  refine ⟨e, he, fun t ↦ ?_⟩
  have h1 : e t Complex.I = J (h t) (e t 1) := by simpa using hJe t 1
  rw [h1]
  exact tames_iff.1 hJ (h t) (e t 1) ((e t).map_ne_zero_iff.2 one_ne_zero)

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
