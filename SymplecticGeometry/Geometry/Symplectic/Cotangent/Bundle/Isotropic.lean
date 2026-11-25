/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph

/-!
# Maps through the zero section are isotropic

Let `L` be a finite-dimensional manifold, `ω = TauCeti.CotangentBundle.symplecticForm` the
canonical symplectic form of `T*L`, and `ι : U → V` a smooth map from an open set `U` of `T*L` to
an open set `V` of a manifold `M` with a two-form `σ`, such that `ι` pulls `σ` back to `-ω`.
If `f : L → M` agrees with `ι` on the zero section, `f q = ι 0_q`, then `f` pulls `σ` back to
`0`: the pullback is that of `-ω` along the zero section, which is `0` because the zero section
is Lagrangian (Tau Ceti's `TauCeti.CotangentBundle.isLagrangianMap_zeroSection`).

## Main results

* `TauCeti.CotangentBundle.mpullback_eq_zero_of_apply_zeroSection`: if `ι` pulls `σ` back to
  `-ω` and sends `0_q` to `f q`, then `f` pulls `σ` back to `0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
-/

public section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L]
  [ChartedSpace H L] [IsManifold I ∞ L]
  {F HM : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ F HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]

/-- **Maps through the zero section are isotropic.** Let `ι : U → V` be a smooth map from an
open set of `T*L` to an open set of `M` that pulls `σ` back to `-ω`, `ω` the canonical symplectic
form of `T*L`. If the zero covector at each `q ∈ L` lies in `U` and `ι` sends it to `f q`, then
`f` pulls `σ` back to `0`. -/
theorem mpullback_eq_zero_of_apply_zeroSection {σ : SmoothTwoForm IM M}
    {U : Opens (CotangentBundle I L)} {V : Opens M} {ι : U → V}
    (hι : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) IM ∞ ι)
    (hισ : SmoothForm.mpullback ι hι (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (-symplecticForm I L))
    {f : L → M} (hf : ContMDiff I IM ∞ f)
    (hιf : ∀ q, ∃ h : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace I x →L[ℝ] ℝ) q ∈ U,
      (ι ⟨_, h⟩ : M) = f q) :
    SmoothForm.mpullback f hf σ = 0 := by
  set s : L → U := fun q ↦ ⟨_, (hιf q).1⟩
  have hs : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ s :=
    (ContMDiff.subtypeVal_comp_iff U s).1 (contMDiff_zeroSection _ _)
  have hz := (isSymplectic_symplecticForm (I := I) (M := L)).isNondegenerate
    |>.isIsotropicMap_iff_mpullback_eq_zero (contMDiff_zeroSection _ _) |>.1
      isLagrangianMap_zeroSection.isIsotropicMap
  rw [SmoothForm.mpullback_congr hf (contMDiff_subtypeVal.comp (hι.comp hs))
      (funext fun q ↦ (hιf q).2.symm), SmoothForm.mpullback_comp_comp_eq_of_mpullback_eq hισ hs,
    map_neg, SmoothForm.mpullback_congr (f := Subtype.val ∘ s) _ (contMDiff_zeroSection _ _) rfl,
    hz, neg_zero]

end TauCeti.CotangentBundle

end
