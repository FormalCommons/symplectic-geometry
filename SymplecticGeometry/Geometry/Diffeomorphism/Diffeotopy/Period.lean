/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Cohomological.Primitive

/-!
# Line integrals of closed one-forms along loops moved by a diffeotopy

Let `Φ` be a diffeotopy of a manifold `M` and `α` a closed `C¹` one-form on `M`. Each slice
`Φ (s, ·)` is homotopic to the identity, through the slices `Φ (r s, ·)`, so the line integral of
`α` along a `C¹` loop `c` equals its line integral along the moved loop `θ ↦ Φ (s, c θ)`.

The proof goes through the periods on first singular homology (`TauCeti.homologyPeriodHom`): the
restriction of `Φ` to the identity embedding is a smooth isotopy, whose slices pull `α` back to
forms with the same periods (`TauCeti.SmoothIsotopy.homologyPeriodHom_mpullback_eq`), and the
period on the class of a loop is the line integral along it.

## Main results

* `TauCeti.homologyPeriodHom_mpullback_loopClass`: the period of a pullback `f^* α` on the class
  of a `C¹` loop `c` is the line integral of `α` along `f ∘ c`.
* `TauCeti.Diffeotopy.pathIntegral_apply_eq`: the line integral of a closed one-form along a loop
  moved by a slice of a diffeotopy is its line integral along the loop.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
-/

public section

open TauCeti.HurewiczOne
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The period of a pullback on the class of a loop.** Let `γ` be a loop in `M` that agrees on
`[0, 1]` with a `C¹` curve `c : ℝ → M`. For a `C²` map `f : M → M'` and a closed `C¹` one-form `α`
on `M'`, the period of `f^* α` on the class of `γ` in `H₁(M; ℤ)` is the line integral of `α` along
`f ∘ c` from `0` to `1`. -/
theorem homologyPeriodHom_mpullback_loopClass {E' H' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' ∞ M'] [T2Space M'] {f : M → M'} (hf : ContMDiff I I' 2 f)
    {α : RoughForm I' M' F 1} (hα : IsSmoothForm I' 1 α) (hcl : mextDeriv α = 0) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ) I 1 c) {γ : Path (c 0) (c 0)} (hγ : ∀ t : unitInterval, γ t = c t) :
    homologyPeriodHom (mpullback I I' f α)
        (H₁AddEquivHomology ℤ (.of M) (loopClass ℤ (X := .of M) γ)) =
      pathIntegral α (f ∘ c) 0 1 := by
  rw [← homologyPeriodHom_singularHomologyMap hf hα hcl,
    ContinuousMap.singularHomologyMap_loopClass, homologyPeriodHom_loopClass]
  refine pathClassIntegral_mk_eq_pathIntegral hα hcl
    ((hf.of_le (by norm_num)).comp hc) fun t ↦ ?_
  simp [hγ]

/-- **Line integrals of a closed one-form are unchanged along the slices of a diffeotopy.** For a
diffeotopy `Φ` of `M`, a closed `C¹` one-form `α`, a `C¹` curve `c : ℝ → M` with `c 1 = c 0` (such
as a loop of period one) and a time `s`, the line integral of `α` from `0` to `1` along the moved
loop `θ ↦ Φ (s, c θ)` is its line integral along `c`. -/
theorem Diffeotopy.pathIntegral_apply_eq (Φ : Diffeotopy I ∞ M) {α : RoughForm I M F 1}
    (hα : IsSmoothForm I 1 α) (hcl : mextDeriv α = 0) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ) I 1 c) (hc₁ : c 1 = c 0) (s : unitInterval) :
    pathIntegral α (fun θ ↦ Φ (s, c θ)) 0 1 = pathIntegral α c 0 1 := by
  -- The loop traced by `c` on `[0, 1]`.
  let γ : Path (c 0) (c 0) :=
    { toFun := fun t ↦ c t
      continuous_toFun := hc.continuous.comp continuous_subtypeVal
      source' := rfl
      target' := hc₁ }
  have hγ (t : unitInterval) : γ t = c t := by simp only [γ, Path.coe_mk_mk]
  -- The restriction of `Φ` to the identity embedding is a smooth isotopy with the same slices.
  let G := Φ.smoothIsotopy ContMDiffMap.id Manifold.IsSmoothEmbedding.id
  have hGs : (fun x ↦ G (s, x)) = fun x ↦ Φ (s, x) :=
    funext fun x ↦ (Φ.smoothIsotopy_apply _ _ (s, x)).trans (by rw [ContMDiffMap.id_apply])
  have h := DFunLike.congr_fun (G.homologyPeriodHom_mpullback_eq hα hcl s)
    (H₁AddEquivHomology ℤ (.of M) (loopClass ℤ (X := .of M) γ))
  rw [hGs, homologyPeriodHom_mpullback_loopClass (f := fun x ↦ Φ (s, x))
      ((Φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).of_le (by simp)) hα hcl hc
      hγ,
    homologyPeriodHom_mpullback_loopClass (ContMDiffMap.id.contMDiff.of_le (by simp)) hα hcl hc
      hγ] at h
  simpa only [ContMDiffMap.id_apply, Function.comp_def] using h

end TauCeti

end
