/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.ModelTransport
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# A unit-speed descending field on a manifold with an arbitrary boundaryless model

Tau Ceti's `TauCeti.exists_vectorField_mvfderiv_eq_neg_one` gives, on a manifold modelled on its
own model space, a smooth compactly supported vector field along which a smooth function `f`
never increases and decreases at unit speed near a compact set of regular points. This file
gives the same field on a manifold with an arbitrary boundaryless model `I`
(`TauCeti.exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless`).

The proof follows the model-transport step of Tau Ceti's
`TauCeti.exists_flow_apply_eq_sub_of_isCompact`: the field is built on the self-modelled copy
`TauCeti.BoundarylessModel I M` and pulled back to `M` along the identity with
`VectorField.mpullback`, and its properties carry over through
`TauCeti.BoundarylessModel.contMDiff_transportVectorField_iff`,
`TauCeti.BoundarylessModel.mvfderiv_transportVectorField` and
`TauCeti.BoundarylessModel.transportVectorField_eq_zero_iff`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ}

open BoundarylessModel in
/-- **A unit-speed descending field near a compact set of regular points**, on a manifold with an
arbitrary boundaryless model. If a compact set `K` contains no critical point of the smooth
function `f`, there is a smooth vector field `X` on `M`, vanishing outside a compact set, with
`df(X) ≤ 0` everywhere and `df(X) = -1` on an open neighbourhood of `K`. -/
theorem exists_vectorField_mvfderiv_eq_neg_one_of_boundaryless
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {K : Set M} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, mvfderiv I f x (X x) ≤ 0) ∧
      (∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, mvfderiv I f x (X x) = -1) ∧
      ∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0 := by
  -- Build the field on the self-modelled copy `M'` of `M` and pull it back.
  set e := homeomorph I M with he
  let M' := BoundarylessModel I M
  set f' : M' → ℝ := f ∘ e.symm with hf'_def
  have : T2Space M' := e.symm.isEmbedding.t2Space
  have hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f' := by
    have h := (diffeomorph I (M := M) ∞).symm.contMDiff
    rw [coe_diffeomorph_symm, ← he] at h
    exact hf.comp h
  have hreg' : ∀ y ∈ e '' K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f' y ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩ h0
    rw [hf'_def, he, mfderiv_source_eq_zero_iff] at h0
    exact hreg x hx (by rwa [Homeomorph.symm_apply_apply] at h0)
  obtain ⟨Y, hY, hYle, ⟨U, hUo, hKU, hYU⟩, C, hC, hYC⟩ :=
    TauCeti.exists_vectorField_mvfderiv_eq_neg_one hf' (hK.image e.continuous) hreg'
  set X := VectorField.mpullback I 𝓘(ℝ, E) e Y
  have hXY : transportVectorField I X = Y := transportVectorField_mpullback I Y
  have hdX : ∀ x, mvfderiv I f x (X x) = mvfderiv 𝓘(ℝ, E) f' (e x) (Y (e x)) := fun x ↦ by
    rw [← mvfderiv_transportVectorField I f X x, hXY]
  refine ⟨X, (contMDiff_transportVectorField_iff I X).1 (by rw [hXY]; exact hY),
    fun x ↦ by rw [hdX]; exact hYle _, ⟨e ⁻¹' U, hUo.preimage e.continuous,
      fun x hx ↦ hKU ⟨x, hx, rfl⟩, fun x hx ↦ by rw [hdX]; exact hYU _ hx⟩,
    e.symm '' C, hC.image e.symm.continuous, fun x hx ↦ ?_⟩
  refine (transportVectorField_eq_zero_iff I X x).1 ?_
  rw [hXY]
  exact hYC _ fun h ↦ hx ⟨e x, h, e.symm_apply_apply x⟩

end TauCeti

end
