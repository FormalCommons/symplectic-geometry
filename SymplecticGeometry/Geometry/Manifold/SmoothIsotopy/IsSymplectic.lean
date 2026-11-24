/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
public import TauCeti.Geometry.Manifold.TwoForm.Basic

/-!
# Symplectic isotopies

Let `F : [0, 1] × P → M` be a smooth isotopy of embeddings (`TauCeti.SmoothIsotopy`), and let `τ`
and `σ` be two-forms on `P` and `M`. The isotopy is symplectic
(`TauCeti.SmoothIsotopy.IsSymplectic τ σ F`) when every slice `F_t = F (t, ·)` pulls `σ` back to
`τ`. This file holds the predicate and the facts about it that need only pullbacks of forms. The
velocity forms of such isotopies, and the closedness of their slices, are in
`SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity`.

## Main definitions

* `TauCeti.SmoothIsotopy.IsSymplectic τ σ F`: every slice of `F` pulls `σ` back to `τ`.

## Main results

* `TauCeti.SmoothIsotopy.IsSymplectic.refl`, `TauCeti.Diffeotopy.isSymplectic_smoothIsotopy`: the
  constant isotopy of a map pulling `σ` back to `τ`, and the restriction of a diffeotopy whose
  slices preserve `σ` to an embedding `f`, are symplectic (for `f^* σ`).
* `TauCeti.SmoothIsotopy.IsSymplectic.mpullback_timeSlice`,
  `TauCeti.SmoothIsotopy.IsSymplectic.symm`: every slice of a symplectic isotopy, as a smooth
  embedding, pulls `σ` back to `τ`, and reversing time keeps an isotopy symplectic.
* `TauCeti.SmoothIsotopy.IsSymplectic.of_apply_eq_diffeotopy_apply`,
  `TauCeti.SmoothIsotopy.IsSymplectic.of_apply_eq_apply_diffeomorph`: an isotopy that is a
  symplectic isotopy composed with a diffeotopy preserving `σ`, or with a diffeomorphism of the
  source, is symplectic.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

namespace SmoothIsotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P] {f₀ f₁ : C^∞⟮J, P; I, M⟯}

/-- A smooth isotopy `F` from `P` to `M` is **symplectic** for two-forms `τ` on `P` and `σ` on
`M` when every slice `F_t = F (t, ·)` pulls `σ` back to `τ`. -/
def IsSymplectic (τ : SmoothTwoForm J P) (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁) :
    Prop :=
  ∀ t, mpullback J I (fun x ↦ F (t, x)) σ.val = τ.val

/-- Unfolding `TauCeti.SmoothIsotopy.IsSymplectic`. -/
theorem isSymplectic_def {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} :
    F.IsSymplectic τ σ ↔ ∀ t, mpullback J I (fun x ↦ F (t, x)) σ.val = τ.val :=
  Iff.rfl

/-! ### Examples and invariance -/

/-- The constant isotopy of a smooth embedding that pulls `σ` back to `τ` is symplectic. -/
theorem IsSymplectic.refl {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {f : C^∞⟮J, P; I, M⟯} (hf : Manifold.IsSmoothEmbedding J I ∞ f)
    (h : mpullback J I f σ.val = τ.val) : (f.smoothIsotopyRefl hf).IsSymplectic τ σ :=
  fun _ ↦ by simpa only [ContMDiffMap.smoothIsotopyRefl_apply] using h

/-- A slice of a symplectic isotopy, as a smooth embedding, pulls `σ` back to `τ`. -/
theorem IsSymplectic.mpullback_timeSlice {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} (hF : F.IsSymplectic τ σ) (t : unitInterval) :
    mpullback J I (F.timeSlice t) σ.val = τ.val := by
  simpa only [← timeSlice_apply] using hF t

/-- Reversing time keeps an isotopy symplectic. -/
theorem IsSymplectic.symm {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} (hF : F.IsSymplectic τ σ) : F.symm.IsSymplectic τ σ := fun t ↦ by
  simpa only [symm_apply] using hF (unitInterval.symm t)

/-- **Composition with a symplectic diffeotopy.** If `F` is symplectic and every slice of the
diffeotopy `Φ` of `M` preserves `σ`, then an isotopy `G` with `G (t, x) = Φ (t, F (t, x))` is
symplectic. -/
theorem IsSymplectic.of_apply_eq_diffeotopy_apply {g₀ g₁ : C^∞⟮J, P; I, M⟯}
    {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M} {F : SmoothIsotopy f₀ f₁}
    {G : SmoothIsotopy g₀ g₁} (hF : F.IsSymplectic τ σ) {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ)
    (hG : ∀ t x, G (t, x) = Φ (t, F (t, x))) : G.IsSymplectic τ σ := fun t ↦ by
  have hfun : (fun x ↦ G (t, x)) = Φ.timeSlice t ∘ F.timeSlice t :=
    funext fun x ↦ by rw [hG, Function.comp_apply, Diffeotopy.timeSlice_apply, timeSlice_apply]
  have hΦt : mpullback I I (Φ.timeSlice t) σ.val = σ.val := by
    rw [← SmoothForm.coe_mpullback _ (Φ.timeSlice t).contMDiff,
      SmoothForm.mem_diffeomorphStabilizer.1 (hΦ t)]
  rw [hfun, mpullback_comp ((F.timeSlice t).contMDiff.mdifferentiable (by simp))
    ((Φ.timeSlice t).contMDiff.mdifferentiable (by simp)), hΦt]
  exact hF.mpullback_timeSlice t

/-- **Composition with a diffeomorphism of the source.** If `F` is symplectic for `τ` and `σ`, and
`χ : Q → P` is a diffeomorphism, then an isotopy `G` with `G (t, y) = F (t, χ y)` is symplectic for
`χ^* τ` and `σ`. -/
theorem IsSymplectic.of_apply_eq_apply_diffeomorph {E'' H'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {J' : ModelWithCorners ℝ E'' H''} {Q : Type*}
    [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold J' ∞ Q] {g₀ g₁ : C^∞⟮J', Q; I, M⟯}
    {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M} {F : SmoothIsotopy f₀ f₁}
    {G : SmoothIsotopy g₀ g₁} (hF : F.IsSymplectic τ σ) (χ : Q ≃ₘ⟮J', J⟯ P)
    (hG : ∀ t y, G (t, y) = F (t, χ y)) :
    G.IsSymplectic (SmoothForm.mpullback χ χ.contMDiff τ) σ := fun t ↦ by
  have hfun : (fun y ↦ G (t, y)) = F.timeSlice t ∘ χ :=
    funext fun y ↦ by rw [hG, Function.comp_apply, timeSlice_apply]
  rw [hfun, mpullback_comp (χ.contMDiff.mdifferentiable (by simp))
    ((F.timeSlice t).contMDiff.mdifferentiable (by simp)), hF.mpullback_timeSlice t,
    SmoothForm.coe_mpullback]

end SmoothIsotopy

namespace Diffeotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P]

/-- The restriction `t ↦ φ_t ∘ f` of a diffeotopy whose slices preserve `σ` to a smooth embedding
`f` is a symplectic isotopy, for `f^* σ` on the source. -/
theorem isSymplectic_smoothIsotopy {σ : SmoothTwoForm I M} {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) (f : C^∞⟮J, P; I, M⟯)
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    (Φ.smoothIsotopy f hf).IsSymplectic (SmoothForm.mpullback f f.contMDiff σ) σ :=
  SmoothIsotopy.IsSymplectic.of_apply_eq_diffeotopy_apply
    (SmoothIsotopy.IsSymplectic.refl hf (SmoothForm.coe_mpullback _ _ _).symm) hΦ
    fun _ _ ↦ by simp

end Diffeotopy

end TauCeti

end
