/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.Relative.Period
public import SymplecticGeometry.Geometry.Symplectic.Blowup.SliceIntegral
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ExceptionalClass
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Real
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Integral
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.TransverseDisc
import SymplecticGeometry.Geometry.Manifold.Orientation.Simplex
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.RelativeCycle
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Geometry.Manifold.Orientation.AddCircle

/-!
# The class of the form of the symplectic blowup

Let `ψ` be a normalized ball embedding for a normalization `hN` of `(σ, J)` at `p₀`, with radius
`r`, weight `l` and width `ε`, and let `h` be a profile of the blowup of weight `l` with collar
`ε`. This file compares the form `ω̃_{ψ,l,ε} = normalizedBlowupForm hψ h` of the blowup
`Blowup hN.blowupChart` with the pull-back `π^* σ` of `σ` by the blowdown `π`.

Off the exceptional divisor `Z`, the difference `ω̃_{ψ,l,ε} - π^* σ` is exact, with a primitive
that vanishes off the image under the lift `ψ̃` of the compact set
`L(l + ε) = closedNbhd n (l + ε)`. On the model, `ω̃_{l,ε} - π^* ω₀` has such a primitive off the
divisor (`BlowupModel.exists_mextDeriv_eq_mpullback_subtypeVal_profileForm_sub`). The lift sends
the model's divisor into `Z`, so off `Z` it restricts to a partial diffeomorphism from the
complement of the model's divisor; the primitive of the blowup is the push-forward of that of the
model along it, extended by zero, which is legitimate since the model's primitive vanishes off
`L(l + ε)` (`PartialDiffeomorph.exists_smoothForm_mpullback_eq_and_mextDeriv_eq`). The same
lemma gives `exists_mextDeriv_eq_normalizedBlowupForm_sub`, for two profiles, on the whole blowup.

This is the first step of the proof of McDuff–Salamon, Theorem 7.1.21 (v): by it, the difference
class lifts to the cohomology of the blowup relative to the complement of `Z`.

The file then evaluates that relative class on a disc through `Z`. For `v ≠ 0`, let `S` be a
smooth `2`-simplex of the blowup that is the lift `ψ̃` of the image in the model of a simplex `τ`
of the line `t ↦ curveLift (· • v) t`, as in
`BlowupModel.integral_curveLift_smul_profileForm_sub`, whose faces avoid `L(l + ε)`. For any
relative cocycle `(ω̃_{ψ,l,ε} - π^* σ, β)` with `β` vanishing off the image of `L(l + ε)`, the
relative de Rham class pairs with the relative class of `S` to `-π l²`: by
`TauCeti.singularKronecker_relativeDeRhamHom_mk_relClass` the pairing is `∫_S (ω̃ - π^* σ)` minus
the integral of `β` over the faces of `S`; the latter vanishes, as `ψ̃` is injective on
`openNbhd n r`, and the former is the model integral, by the local naturality of integration
(`TauCeti.SmoothSimplex.integral_eq_integral_mpullback_of_eq_comp`) and since `ψ̃` pulls
`ω̃_{ψ,l,ε} - π^* σ` back to `ω̃_{l,ε} - π^* ω₀` on `openNbhd n r`
(`IsNormalizedBallEmbedding.mpullback_ballLiftPartialDiffeomorph_normalizedBlowupForm_sub`).

Finally, the relative class is `π l²` times the real relative dual class `D` of `Z`
(`TauCeti.SmoothEmbedding.realRelDualClass`, for `Blowup.divisorNormalOrientation`), read on
`(Blowup, W)` through the identity of pairs to `(Blowup, Blowup ∖ Z)`. As
`Z ≅ ℙ ℂ (Fin (n + 1) → ℂ)` is connected, the class is `m • D` for some real `m`
(`TauCeti.SmoothEmbedding.exists_eq_smul_realRelDualClass`). Both are evaluated on one simplex:
the line disc `hψ.lineDisc v` (`Normalized/TransverseDisc.lean`) after a positively oriented
simplex around `0`, with radii scaled by the norm of `v`
(`TauCeti.Manifold.Orientation.exists_smoothSimplex_complex_closedBall_subset_image`). The
relative class gives `-π l²` by the evaluation above, and `D` gives `-1`, since the line disc is
transverse to `Z` and oriented as its normal bundle
(`singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp`, in the namespace
`TauCeti.SmoothEmbedding`). So `m = π l²`.

## Main results

* `IsNormalizedBallEmbedding.exists_mextDeriv_eq_mpullback_subtypeVal_normalizedBlowupForm_sub`:
  on the complement of the exceptional divisor, `ω̃_{ψ,l,ε} - π^* σ` is `d β` for a one-form `β`
  that vanishes off the image of `L(l + ε)` under the lift.
* `IsNormalizedBallEmbedding.singularKronecker_relativeDeRhamHom_mk_relClass_curveLift_smul`:
  the class of such a relative cocycle pairs to `-π l²` with a disc through `Z` along a line.
* `IsNormalizedBallEmbedding.relativeDeRhamHom_mk_eq_smul_realRelDualClass`: that class is
  `π l²` times the real relative dual class of `Z`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  proof of Theorem 7.1.21 (v).
-/

public section

noncomputable section

open Set Metric Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] [T2Space M]
  {σ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) M}
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M} {p₀ : M} {δ : ℝ}
  {ψ₀ : StdSpace (Fin (n + 1)) → M} {hN : IsNormalizedAt σ J p₀ δ ψ₀}
  {ψ : StdSpace (Fin (n + 1)) → M} {r l ε : ℝ}

namespace IsNormalizedBallEmbedding

open BlowupModel

variable (hψ : IsNormalizedBallEmbedding hN ψ r l ε)
include hψ

attribute [local instance high] IsManifold.instOfNatWithTopENat_1

/-- On `openNbhd n r`, the lift `ψ̃` pulls `ω̃_{ψ,l,ε} - π^* σ` back to `ω̃_{l,ε} - π^* ω₀`. -/
theorem mpullback_ballLiftPartialDiffeomorph_normalizedBlowupForm_sub {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h) {y : BlowupModel n} (hy : y ∈ openNbhd n r) :
    TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) hψ.ballLiftPartialDiffeomorph
        (hψ.normalizedBlowupForm h - SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ).val y =
      (profileForm n l ε h - SmoothForm.mpullback blowdown
        ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n)).val y := by
  rw [Submodule.coe_sub, Submodule.coe_sub, mpullback_sub, Pi.sub_apply, Pi.sub_apply,
    hψ.normalizedBlowupForm_eq_on_ballLift hh _ hy,
    hψ.mpullback_ballLiftPartialDiffeomorph_mpullback_blowdown hy]

/-- Let `Ψ` be a partial diffeomorphism from the complement of the model's divisor to that of the
blowup's divisor that agrees with the lift `ψ̃` on its source. At each point of its source in
`openNbhd n r`, `Ψ` pulls the restriction of `ω̃_{ψ,l,ε} - π^* σ` back to that of
`ω̃_{l,ε} - π^* ω₀`. -/
private theorem mpullback_normalizedBlowupForm_sub_of_coe_apply {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (offDivisorOpens n)
      (Blowup.offDivisorOpens hN.blowupChart) ∞)
    (hΨ : ∀ y ∈ Ψ.source, (Ψ y : Blowup hN.blowupChart) = hψ.ballLiftPartialDiffeomorph y)
    {y : offDivisorOpens n} (hy : y ∈ Ψ.source) (hyr : (y : BlowupModel n) ∈ openNbhd n r) :
    TauCeti.mpullback 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Ψ
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (hψ.normalizedBlowupForm h - SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
            (Blowup.contMDiff_blowdown_real _) σ)).val y =
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (profileForm n l ε h - SmoothForm.mpullback blowdown
          ((contMDiff_blowdown ∞).restrictScalars' ℝ) (ω₀E n))).val y := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  have hfun : Subtype.val ∘ Ψ =ᶠ[𝓝 y] Φ ∘ Subtype.val :=
    Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hy) hΨ
  simp only [SmoothForm.coe_mpullback]
  rw [← mpullback_comp_at (Ψ.mdifferentiableAt (by simp) hy)
      ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp)), hfun.mpullback_eq,
    mpullback_comp_at ((contMDiff_subtypeVal (n := ∞)).mdifferentiableAt (by simp))
      (Φ.mdifferentiableAt (by simp) (by rwa [ballLiftPartialDiffeomorph_source])),
    mpullback_subtype_val_apply, mpullback_subtype_val_apply,
    hψ.mpullback_ballLiftPartialDiffeomorph_normalizedBlowupForm_sub hh hyr]

/-- **A primitive of `ω̃_{ψ,l,ε} - π^* σ` off the exceptional divisor.** For a profile `h` of the
blowup of weight `l` with collar `ε`, the restriction of
`hψ.normalizedBlowupForm h - π^* σ` to the complement `Blowup.offDivisorOpens` of the exceptional
divisor is `d β` for a one-form `β` there that vanishes at every point off the image under the
lift `ψ̃` of `L(l + ε) = closedNbhd n (l + ε)`. -/
theorem exists_mextDeriv_eq_mpullback_subtypeVal_normalizedBlowupForm_sub {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h) :
    ∃ β : SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) ℝ 1,
      mextDeriv β.val = (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (hψ.normalizedBlowupForm h - SmoothForm.mpullback (Blowup.blowdown hN.blowupChart)
          (Blowup.contMDiff_blowdown_real _) σ)).val ∧
      ∀ x : Blowup.offDivisorOpens hN.blowupChart,
        (x : Blowup hN.blowupChart) ∉ hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) →
          β.val x = 0 := by
  set W := Blowup.offDivisorOpens hN.blowupChart
  set Φ := hψ.ballLiftPartialDiffeomorph
  set K := Φ '' closedNbhd n (l + ε)
  rcases isEmpty_or_nonempty W with hW | hW
  · exact ⟨0, funext fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  have hU : Nonempty (offDivisorOpens n) := by
    obtain ⟨y, hy⟩ := (dense_exceptionalDivisor_compl (n := n)).nonempty
    exact ⟨⟨y, mem_offDivisorOpens.2 hy⟩⟩
  set Φ₁ := Φ.subtypeRestr (offDivisorOpens n) hU
  set Ψ := (Φ₁.symm.subtypeRestr W hW).symm
  have hΨsource : Ψ.source = {y : offDivisorOpens n | (y : BlowupModel n) ∈ openNbhd n r ∧
      Φ y ∈ W} := by
    ext y
    simp [Ψ, Φ₁, Φ]
  have hΨapply : ∀ y ∈ Ψ.source, (Ψ y : Blowup hN.blowupChart) = Φ y := fun y hy ↦ by
    rw [PartialDiffeomorph.coe_subtypeRestr_symm_apply _ _ _ hy]
    simp [Φ₁]
  have hK : closedNbhd n (l + ε) ⊆ openNbhd n r :=
    closedNbhd_subset_openNbhd hψ.weight_add_width_lt
  -- A point of `W` in `K` is the image under `Ψ` of a point of its source.
  have hKΨ : ∀ x : W, (x : Blowup hN.blowupChart) ∈ K →
      ∃ y ∈ Ψ.source, (y : BlowupModel n) ∈ closedNbhd n (l + ε) ∧ Ψ y = x := by
    rintro x ⟨y, hy, hyx⟩
    have hyZ : y ∈ offDivisorOpens n := mem_offDivisorOpens.2 fun hZ ↦
      (Blowup.mem_offDivisorOpens _).1 x.property
        (hyx ▸ hψ.ballLiftPartialDiffeomorph_mem_exceptionalDivisor hZ)
    have hyS : (⟨y, hyZ⟩ : offDivisorOpens n) ∈ Ψ.source := by
      rw [hΨsource]
      exact ⟨hK hy, hyx ▸ x.property⟩
    exact ⟨⟨y, hyZ⟩, hyS, hy, Subtype.ext ((hΨapply _ hyS).trans hyx)⟩
  obtain ⟨β₀, hβ₀, hβ₀0⟩ := exists_mextDeriv_eq_mpullback_subtypeVal_profileForm_sub n hh
  obtain ⟨β, -, hβ0, hdβ⟩ := PartialDiffeomorph.exists_smoothForm_mpullback_eq_and_mextDeriv_eq Ψ
    ((hψ.isCompact_ballLiftPartialDiffeomorph_image_closedNbhd
      hψ.weight_add_width_lt).isClosed.preimage continuous_subtypeVal)
    (fun x hx ↦ by
      obtain ⟨y, hy, -, rfl⟩ := hKΨ x hx
      exact Ψ.map_source hy)
    β₀ (fun y hy hyK ↦ hβ₀0 y fun hyL ↦ hyK (by
      rw [mem_preimage, hΨapply y hy]
      exact mem_image_of_mem Φ hyL))
    (fun y hy ↦ by
      rw [hβ₀, mpullback_normalizedBlowupForm_sub_of_coe_apply hψ hh Ψ hΨapply hy
        (hΨsource ▸ hy).1])
    fun x hx ↦ by
      rw [SmoothForm.coe_mpullback, mpullback_subtype_val_apply, Submodule.coe_sub, Pi.sub_apply,
        hψ.normalizedBlowupForm_eq_on_compl _ hx, sub_self]
      -- The zero lies in the fibre at `x` of the blowup, which is that at `x` of `W`: both are
      -- the model fibre.
      rfl
  exact ⟨β, hdβ, hβ0⟩

open CategoryTheory Opposite Simplicial in
/-- **The relative class of `ω̃_{ψ,l,ε} - π^* σ` on a disc through the divisor.** Let `h` be a
profile of the blowup of weight `l` with collar `ε`, `v ≠ 0`, and `τ` a smooth `2`-simplex of `ℂ`
as in `BlowupModel.integral_curveLift_smul_profileForm_sub`: positively oriented, and covering
every `t` whose point `curveLift (· • v) t` lies in `L(l + ε) = closedNbhd n (l + ε)`. Suppose
that the image of `τ` under `curveLift (· • v)` lies in `openNbhd n r` and that of each of its
faces off `L(l + ε)`. Let `S` be a smooth `2`-simplex of the blowup that is the lift `ψ̃` of that
image, with faces the simplices `t i` of the complement `W` of the exceptional divisor. For a
relative cocycle `y = (α, β)` of `(Blowup, W)` with `α = ω̃_{ψ,l,ε} - π^* σ` and `β` vanishing off
the image of `L(l + ε)` under `ψ̃`, the class `relativeDeRhamHom [y]` pairs with the relative
class of `S` to `-π l²`. -/
theorem singularKronecker_relativeDeRhamHom_mk_relClass_curveLift_smul
    [SigmaCompactSpace (Blowup hN.blowupChart)] {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) (τ : SmoothSimplex 𝓘(ℝ, ℂ) ℂ 2)
    {U : Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hgτ : ∀ x : fullSimplex 2, g x = τ.toContinuousMap x)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) ((complexManifoldOrientation ℂ ℂ).reindex
        (finCongr Complex.two_mul_finrank_self)) g x)
    (hD : ∀ t : ℂ, curveLift (· • v) t ∈ closedNbhd n (l + ε) → t ∈ g '' fullSimplex 2)
    (hτr : ∀ x, curveLift (· • v) (τ.toContinuousMap x) ∈ openNbhd n r)
    (hface : ∀ (i : Fin 3) (x : fullSimplex 1),
      curveLift (· • v) (τ.toContinuousMap (simplexFace 1 i x)) ∉ closedNbhd n (l + ε))
    (S : SmoothSimplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2)
    (hS : ∀ x, S.toContinuousMap x =
      hψ.ballLiftPartialDiffeomorph (curveLift (· • v) (τ.toContinuousMap x)))
    (t : Fin 3 → SmoothSimplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) 1)
    (ht : ∀ i, (smoothSingularSubcomplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) :
        SSet).δ i S = (smoothSingularSubcomplexMap
          (Subtype.val : Blowup.offDivisorOpens hN.blowupChart → Blowup hN.blowupChart)
          contMDiff_subtypeVal).app _ (t i))
    (y : relativeDeRhamCohomology.cocycles 𝓘(ℝ, Fin (n + 1) → ℂ)
      (Blowup.offDivisorOpens hN.blowupChart) 1)
    (hy : y.val.1 = hψ.normalizedBlowupForm h - SmoothForm.mpullback
      (Blowup.blowdown hN.blowupChart) (Blowup.contMDiff_blowdown_real _) σ)
    (hβ : ∀ x : Blowup.offDivisorOpens hN.blowupChart, (x : Blowup hN.blowupChart) ∉
      hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) → y.val.2.val x = 0) :
    (TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart)) :
        Set (TopCat.of (Blowup hN.blowupChart)))).singularKronecker ℝ 2
        (relativeDeRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) 2
          (relativeDeRhamCohomology.mk _ _ 1 y))
        ((TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart :
          Set (Blowup hN.blowupChart)) : Set (TopCat.of (Blowup hN.blowupChart)))).relClass
          (ModuleCat.of ℝ ℝ) S.val
          (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app S t ht) 1) =
      -(Real.pi * l ^ 2) := by
  set Φ := hψ.ballLiftPartialDiffeomorph
  refine (singularKronecker_relativeDeRhamHom_mk_relClass _ _ 1 S t ht y).trans ?_
  rw [integrationCochain_ιChainComplex, one_smul]
  have hsrc : ∀ {z : BlowupModel n}, z ∈ openNbhd n r → z ∈ Φ.source := fun hz ↦ by
    rwa [ballLiftPartialDiffeomorph_source]
  -- The boundary term vanishes: the faces of `S` avoid the image of `L(l + ε)`.
  have hβ0 : ∀ i, (t i).integral y.val.2.val = 0 := fun i ↦
    SmoothSimplex.integral_eq_zero_of_forall_eq_zero _ fun x ↦ hβ _ fun ⟨z, hz, hzx⟩ ↦ by
      have hx : ((t i).toContinuousMap x : Blowup hN.blowupChart) =
          Φ (curveLift (· • v) (τ.toContinuousMap (simplexFace 1 i x))) := by
        rw [← hS, ← SmoothSimplex.toContinuousMap_δ_apply, ht i,
          SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app]
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [hx] at hzx
      have hK : closedNbhd n (l + ε) ⊆ openNbhd n r :=
        closedNbhd_subset_openNbhd hψ.weight_add_width_lt
      exact hface i x (Φ.injOn (hsrc (hK hz)) (hsrc (hτr _)) hzx ▸ hz)
  -- The integral over `S` is that of the model form over the image of `τ` in the fibre.
  have hσ : S.integral y.val.1.val = -(Real.pi * l ^ 2) := by
    set τL : SmoothSimplex 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) 2 :=
      (smoothSingularSubcomplexMap (curveLift (· • v))
        (contMDiff_curveLift_smul_real hv)).app (op ⦋2⦌) τ
    have hτL : ∀ x, τL.toContinuousMap x = curveLift (· • v) (τ.toContinuousMap x) := fun x ↦ by
      rw [SmoothSimplex.toContinuousMap_smoothSingularSubcomplexMap_app]
      simp
    have hτLr : ∀ x, τL.toContinuousMap x ∈ openNbhd n r := fun x ↦ hτL x ▸ hτr x
    rw [τL.integral_eq_integral_mpullback_of_eq_comp S (fun x ↦ by rw [hS, hτL])
        (fun x ↦ Φ.mdifferentiableAt (by simp) (hsrc (hτLr x))),
      ← integral_curveLift_smul_profileForm_sub hh hv τ hU hgτ hg ho hD]
    refine τL.integral_congr fun x ↦ ?_
    rw [hy, hψ.mpullback_ballLiftPartialDiffeomorph_normalizedBlowupForm_sub hh (hτLr x)]
  simp only [hσ, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  rw [sub_eq_self]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [integrationCochain_ιChainComplex, one_smul, hβ0, smul_zero]

/-- The order `∞` of smoothness is not zero, as Tau Ceti's normal spaces ask. -/
local notation "hn" => (Iff.mpr WithTop.coe_ne_zero ENat.top_ne_zero : (∞ : ℕ∞ω) ≠ 0)

open CategoryTheory Opposite Simplicial in
/-- A smooth `2`-simplex `S` of the blowup through the exceptional divisor `Z`, with faces in its
complement `W`, on which both classes can be evaluated: every relative cocycle
`(ω̃_{ψ,l,ε} - π^* σ, β)` with `β` vanishing off the image of `L(l + ε)` pairs to `-π l²` with the
class of `S` in `H₂(Blowup, W; ℝ)`, and the real relative dual class of `Z` pairs to `-1` with
its class in `H₂(Blowup, Blowup ∖ Z; ℝ)`. The simplex is the line disc `hψ.lineDisc v` after a
positively oriented simplex of `ℝ²` around `0`. -/
private theorem exists_smoothSimplex_singularKronecker_relClass [SecondCountableTopology M]
    [SigmaCompactSpace (Blowup hN.blowupChart)] :
    ∃ (S : SmoothSimplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) 2)
      (t : Fin 3 → SmoothSimplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) 1)
      (ht : ∀ i, (smoothSingularSubcomplex 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup hN.blowupChart) :
        SSet).δ i S = (smoothSingularSubcomplexMap
          (Subtype.val : Blowup.offDivisorOpens hN.blowupChart → Blowup hN.blowupChart)
          contMDiff_subtypeVal).app _ (t i)),
      (∀ {h : ℝ → ℝ}, IsBlowupProfile l ε h →
        ∀ y : relativeDeRhamCohomology.cocycles 𝓘(ℝ, Fin (n + 1) → ℂ)
          (Blowup.offDivisorOpens hN.blowupChart) 1,
        y.val.1 = hψ.normalizedBlowupForm h - SmoothForm.mpullback
          (Blowup.blowdown hN.blowupChart) (Blowup.contMDiff_blowdown_real _) σ →
        (∀ x : Blowup.offDivisorOpens hN.blowupChart, (x : Blowup hN.blowupChart) ∉
          hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) → y.val.2.val x = 0) →
        (TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart :
            Set (Blowup hN.blowupChart)) : Set (TopCat.of (Blowup hN.blowupChart)))
            ).singularKronecker ℝ 2 (relativeDeRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ)
              (Blowup.offDivisorOpens hN.blowupChart) 2 (relativeDeRhamCohomology.mk _ _ 1 y))
            ((TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart :
              Set (Blowup hN.blowupChart)) : Set (TopCat.of (Blowup hN.blowupChart)))).relClass
              (ModuleCat.of ℝ ℝ) S.val
              (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app S t ht) 1) =
          -(Real.pi * l ^ 2)) ∧
      ∀ hS : ∀ i, Set.range ((TopCat.of (Blowup hN.blowupChart)).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of (Blowup hN.blowupChart))).δ i S.val)) ⊆
          Set.range (TopPair.ofSubset
            ((range (Blowup.divisorRealEmbedding hN.blowupChart))ᶜ :
              Set (TopCat.of (Blowup hN.blowupChart)))).map,
        (TopPair.ofSubset ((range (Blowup.divisorRealEmbedding hN.blowupChart))ᶜ :
            Set (TopCat.of (Blowup hN.blowupChart)))).singularKronecker ℝ 2
          ((Blowup.divisorRealEmbedding hN.blowupChart).realRelDualClass hn
            (Complex.finrank_real_eq_finrank_pi_succ_sub n)
            (Blowup.isClosed_range_divisorRealEmbedding _)
            (Blowup.divisorNormalOrientation hN.blowupChart) Complex.finrank_real_complex)
          ((TopPair.ofSubset ((range (Blowup.divisorRealEmbedding hN.blowupChart))ᶜ :
            Set (TopCat.of (Blowup hN.blowupChart)))).relClass (ModuleCat.of ℝ ℝ) (n := 1)
            S.val hS 1) = -1 := by
  -- A line through `0`, and the Euclidean norm `N` of its direction `v`.
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin (n + 1) → ℂ)
  set N := ‖complexToRealEuclidean (Fin (n + 1)) v‖
  have hN0 : 0 < N := norm_pos_iff.2 fun h0 ↦ hv ((complexToRealEuclidean _).map_eq_zero_iff.1 h0)
  have hnorm : ∀ t : ℂ, ‖complexToRealEuclidean (Fin (n + 1)) (curveLift (· • v) t).blowdown‖ =
      ‖t‖ * N := fun t ↦ by
    rw [blowdown_curveLift, norm_complexToRealEuclidean_smul]
  have hr : 0 < r := hψ.width_pos.trans hψ.width_lt_radius
  -- A positively oriented simplex `τ = g|Δ²` of `ℂ` covering the disc of radius `(l + ε) / N`,
  -- with faces off it, inside the disc of radius `r / N`.
  obtain ⟨g, τ, hgτ, hgs, hge, hgo, hga, hgface, hgb⟩ :=
    Manifold.Orientation.exists_smoothSimplex_complex_closedBall_subset_image
      (a := (l + ε) / N) (b := r / N) (div_pos hr hN0)
      (div_lt_div_of_pos_right hψ.weight_add_width_lt hN0)
  have hgr : ∀ x, curveLift (· • v) (g x) ∈ openNbhd n r := fun x ↦ by
    have hx := hgb (mem_range_self x)
    rw [mem_ball_zero_iff, lt_div_iff₀ hN0] at hx
    rw [mem_openNbhd_iff, hnorm]
    exact hx
  -- The same simplex read on `ℝ²`, and its image `S` under the line disc.
  set R := Complex.orthonormalBasisOneI.repr
  have hRg : ContDiff ℝ ∞ (R ∘ g) := R.contDiff.comp hgs
  set σ₀ := SmoothSimplex.ofContMDiff hRg.contMDiff
  have hσ₀ : ∀ x, σ₀.toContinuousMap x = R (g x) := fun x ↦
    SmoothSimplex.toContinuousMap_ofContMDiff_apply _ x
  set B : Set (EuclideanSpace ℝ (Fin 2)) :=
    {w | curveLift (· • v) (Complex.orthonormalBasisOneI.repr.symm w) ∈ openNbhd n r}
  have hRgB : ∀ x, R (g x) ∈ B := fun x ↦ by
    have hx := hgr x
    rw [← R.symm_apply_apply (g x)] at hx
    exact hx
  have hSs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (hψ.lineDisc v ∘ (R ∘ g)) :=
    contMDiffOn_univ.1 ((hψ.contMDiffOn_lineDisc hv).comp hRg.contMDiff.contMDiffOn
      fun x _ ↦ hRgB x)
  set S := SmoothSimplex.ofContMDiff hSs
  have hs : ∀ x, (TopCat.of (Blowup hN.blowupChart)).toSSetObjEquiv _ S.val
      (fullSimplexEquivStdSimplex 2 x) = hψ.lineDisc v (σ₀.toContinuousMap x) := fun x ↦ by
    rw [← SmoothSimplex.toContinuousMap_apply, SmoothSimplex.toContinuousMap_ofContMDiff_apply,
      hσ₀]
    rfl
  have hφ : IsOpenEmbedding ((R ∘ g) ∘ ((↑) : (⊤ : Opens (EuclideanSpace ℝ (Fin 2))) →
      EuclideanSpace ℝ (Fin 2))) :=
    (R.toHomeomorph.isOpenEmbedding.comp hge).comp isOpen_univ.isOpenEmbedding_subtypeVal
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ (R ∘ g) '' interior (fullSimplex 2) := by
    obtain ⟨x, hx, hx0⟩ := hga (mem_closedBall_self (div_nonneg (hψ.weight_pos.le.trans
      (le_add_of_nonneg_right hψ.width_pos.le)) hN0.le))
    exact ⟨x, hx, by simp [hx0]⟩
  -- The faces of `S` lie off the divisor.
  have hSW : ∀ i, Set.range ((TopCat.of (Blowup hN.blowupChart)).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (Blowup hN.blowupChart))).δ i S.val)) ⊆
        Set.range (TopPair.ofSubset (X := TopCat.of (Blowup hN.blowupChart))
          (Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart))).map := by
    intro i
    have hgK : ∀ w ∈ B, hψ.lineDisc v w ∈ Blowup.exceptionalDivisor hN.blowupChart → w = 0 :=
      fun w hw hZ ↦ hψ.eq_zero_of_lineDisc_mem_range hv hw
        (by rwa [Blowup.range_divisorRealEmbedding])
    refine (SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl_of_eq_comp hgK σ₀ (U := ⊤)
      (subset_univ _) (fun x ↦ (hσ₀ x).symm) hφ h0 (fun x ↦ hσ₀ x ▸ hRgB x) S.val hs i).trans
      (subset_of_eq ?_)
    exact congrArg (fun A ↦ range (TopPair.ofSubset (X := TopCat.of (Blowup hN.blowupChart)) A).map)
      (Blowup.coe_offDivisorOpens _).symm
  obtain ⟨t, ht⟩ := exists_δ_eq_smoothSingularSubcomplexMap_app_of_range_subset S hSW
  refine ⟨S, t, ht, fun hh y hy hβ ↦ ?_, fun hS ↦ ?_⟩
  · -- The relative class of the blowup form, by the model integral.
    refine hψ.singularKronecker_relativeDeRhamHom_mk_relClass_curveLift_smul hh hv τ
      (U := ⊤) (subset_univ _) hgτ (hge.comp isOpen_univ.isOpenEmbedding_subtypeVal)
      (fun x _ ↦ hgo x) (fun t ht ↦ ?_) (fun x ↦ hgτ x ▸ hgr x) (fun i x hx ↦ hgface i x ?_) S
      (fun x ↦ ?_) t ht y hy hβ
    · rw [mem_closedNbhd_iff, hnorm, ← le_div_iff₀ hN0] at ht
      obtain ⟨x, hx, rfl⟩ := hga (mem_closedBall_zero_iff.2 ht)
      exact ⟨x, interior_subset hx, rfl⟩
    · rw [mem_closedNbhd_iff, hnorm, ← le_div_iff₀ hN0] at hx
      exact mem_closedBall_zero_iff.2 hx
    · rw [SmoothSimplex.toContinuousMap_ofContMDiff_apply, Function.comp_apply, lineDisc_def,
        Function.comp_apply, LinearIsometryEquiv.symm_apply_apply, hgτ]
  · -- The dual class, on the line disc, which is transverse to the divisor.
    have hO : (complexManifoldOrientation ℂ ℂ).reindex (finCongr Complex.two_mul_finrank_self) =
        Manifold.Orientation.complex :=
      (complexCurveOrientation_def _).symm.trans complexCurveOrientation_complex
    obtain ⟨μ, hμ, hAμ⟩ := hψ.exists_orientation_map_eq_divisorNormalOrientation_lineDisc hv
    have hA := (hψ.mdifferentiableAt_lineDisc hv).hasMFDerivAt
    exact (Blowup.divisorRealEmbedding hN.blowupChart
      ).singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp hn
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
            (Blowup.isClosed_range_divisorRealEmbedding _)
      (Blowup.divisorNormalOrientation hN.blowupChart) Complex.finrank_real_complex
      (Projectivization.mk ℂ v hv) μ hμ
      ((isOpen_setOf_curveLift_smul_mem_openNbhd hv r).mem_nhds
        (zero_mem_setOf_curveLift_smul_mem_openNbhd hv hr))
      (hψ.contMDiffOn_lineDisc hv).continuousOn (hψ.lineDisc_zero hv)
      (fun w hw hZ ↦ hψ.eq_zero_of_lineDisc_mem_range hv hw hZ) hA (hAμ _ hA) σ₀
      (U := ⊤) (subset_univ _) (fun x ↦ (hσ₀ x).symm) hφ
      (fun x _ ↦ (Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr (g x)).comp
        (hO ▸ hgo x)) h0 (fun x ↦ hσ₀ x ▸ hRgB x) S.val hs

open CategoryTheory in
/-- **The relative class of `ω̃_{ψ,l,ε} - π^* σ` is `π l²` times the dual class of the divisor.**
Let `h` be a profile of the blowup of weight `l` with collar `ε`, and `y = (α, β)` a relative
cocycle of the pair `(Blowup, W)`, `W` the complement of the exceptional divisor `Z`, with
`α = ω̃_{ψ,l,ε} - π^* σ` and `β` vanishing off the image of `L(l + ε) = closedNbhd n (l + ε)`
under the lift `ψ̃` (such as the primitive of
`exists_mextDeriv_eq_mpullback_subtypeVal_normalizedBlowupForm_sub`). Then the class
`relativeDeRhamHom [y] ∈ H²(Blowup, W; ℝ)` is `π l²` times the image of the real relative dual
class `TauCeti.SmoothEmbedding.realRelDualClass` of `Z` (`Blowup.divisorRealEmbedding`, oriented
by `Blowup.divisorNormalOrientation`) under the identity map of pairs from `(Blowup, W)` to
`(Blowup, Blowup ∖ Z)`. -/
theorem relativeDeRhamHom_mk_eq_smul_realRelDualClass [SecondCountableTopology M]
    [SigmaCompactSpace (Blowup hN.blowupChart)] {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    (y : relativeDeRhamCohomology.cocycles 𝓘(ℝ, Fin (n + 1) → ℂ)
      (Blowup.offDivisorOpens hN.blowupChart) 1)
    (hy : y.val.1 = hψ.normalizedBlowupForm h - SmoothForm.mpullback
      (Blowup.blowdown hN.blowupChart) (Blowup.contMDiff_blowdown_real _) σ)
    (hβ : ∀ x : Blowup.offDivisorOpens hN.blowupChart, (x : Blowup hN.blowupChart) ∉
      hψ.ballLiftPartialDiffeomorph '' closedNbhd n (l + ε) → y.val.2.val x = 0) :
    relativeDeRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) 2
        (relativeDeRhamCohomology.mk _ _ 1 y) =
      (Real.pi * l ^ 2) • TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (𝟙 (TopCat.of (Blowup hN.blowupChart)))
          (B := ((Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart)) :
            Set (TopCat.of (Blowup hN.blowupChart))))
          (B' := (range (Blowup.divisorRealEmbedding hN.blowupChart))ᶜ) fun x hx ↦ by
            rw [Blowup.range_divisorRealEmbedding, ← Blowup.coe_offDivisorOpens]
            exact hx) 2
        ((Blowup.divisorRealEmbedding hN.blowupChart).realRelDualClass hn
          (Complex.finrank_real_eq_finrank_pi_succ_sub n)
            (Blowup.isClosed_range_divisorRealEmbedding _)
          (Blowup.divisorNormalOrientation hN.blowupChart) Complex.finrank_real_complex) := by
  set f := Blowup.divisorRealEmbedding hN.blowupChart
  have hWf : ((Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart)) :
      Set (TopCat.of (Blowup hN.blowupChart))) = (range f)ᶜ := by
    rw [Blowup.coe_offDivisorOpens, Blowup.range_divisorRealEmbedding]
  -- The identity maps of pairs between `(Blowup, W)` and `(Blowup, (range f)ᶜ)`.
  set F := TopPair.ofSubsetMap (𝟙 (TopCat.of (Blowup hN.blowupChart)))
    (B := ((Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart)) :
      Set (TopCat.of (Blowup hN.blowupChart))))
    (B' := (range f)ᶜ) fun x hx ↦ by
      rw [Blowup.range_divisorRealEmbedding, ← Blowup.coe_offDivisorOpens]
      exact hx
  set G := TopPair.ofSubsetMap (𝟙 (TopCat.of (Blowup hN.blowupChart))) (B := (range f)ᶜ)
    (B' := ((Blowup.offDivisorOpens hN.blowupChart : Set (Blowup hN.blowupChart)) :
      Set (TopCat.of (Blowup hN.blowupChart)))) fun x hx ↦ hWf ▸ hx
  have hFG : F ≫ G = 𝟙 _ :=
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hx ↦ hx)
      (Category.id_comp _)).trans (TopPair.ofSubsetMap_id _)
  -- The class is a multiple of the dual class, since the divisor is connected.
  set b := relativeDeRhamHom 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup.offDivisorOpens hN.blowupChart) 2
    (relativeDeRhamCohomology.mk _ _ 1 y) with hbdef
  set D := f.realRelDualClass hn (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    (Blowup.isClosed_range_divisorRealEmbedding _) (Blowup.divisorNormalOrientation hN.blowupChart)
    Complex.finrank_real_complex
  obtain ⟨m, hm⟩ := f.exists_eq_smul_realRelDualClass hn
    (Complex.finrank_real_eq_finrank_pi_succ_sub n)
            (Blowup.isClosed_range_divisorRealEmbedding _)
    (Blowup.divisorNormalOrientation hN.blowupChart) Complex.finrank_real_complex
    (TopPair.singularCohomologyMap G 2 b)
  have hb : b = m • TopPair.singularCohomologyMap F 2 D := by
    rw [← map_smul, ← hm, ← TopPair.singularCohomologyMap_comp_apply, hFG,
      TopPair.singularCohomologyMap_id]
    -- The identity of `ModuleCat` acts as the identity on elements.
    rfl
  -- Compare the pairings of both sides with the class of the simplex `S`.
  obtain ⟨S, t, ht, h1, h2⟩ := hψ.exists_smoothSimplex_singularKronecker_relClass
  have h1 := h1 hh y hy hβ
  have hF : (TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart :
      Set (Blowup hN.blowupChart)) : Set (TopCat.of (Blowup hN.blowupChart)))).singularKronecker
        ℝ 2 (TopPair.singularCohomologyMap F 2 D)
        ((TopPair.ofSubset ((Blowup.offDivisorOpens hN.blowupChart :
          Set (Blowup hN.blowupChart)) : Set (TopCat.of (Blowup hN.blowupChart)))).relClass
          (ModuleCat.of ℝ ℝ) S.val
          (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app S t ht) 1) =
      -1 := by
    -- The pairs' ambient spaces agree only up to unfolding `TopPair.ofSubset`, so `rw` cannot
    -- rewrite here.
    erw [TopPair.singularKronecker_naturality]
    have hS : ∀ i, Set.range ((TopCat.of (Blowup hN.blowupChart)).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of (Blowup hN.blowupChart))).δ i S.val)) ⊆
        Set.range (TopPair.ofSubset (range f)ᶜ).map := fun i ↦
      (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app S t ht i).trans
        (subset_of_eq (congrArg (fun A : Set (TopCat.of (Blowup hN.blowupChart)) ↦
          range (TopPair.ofSubset A).map) hWf))
    refine (ConcreteCategory.comp_apply _ _ _).trans ((congrArg _ ?_).trans (h2 hS))
    refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
    erw [TopPair.relClass_singularHomologyMap]
    congr 3
    erw [show TopPair.Hom.fst F = 𝟙 _ from TopPair.ofSubsetMap_fst _ _,
      CategoryTheory.Functor.map_id]
    -- The identity natural transformation of `TopCat.toSSet` acts as the identity on simplices.
    rfl
  rw [← hbdef, hb] at h1
  erw [map_smul] at h1
  have hm' : m * -1 = -(Real.pi * l ^ 2) := by
    rw [← hF]
    exact h1
  rw [mul_neg_one, neg_inj] at hm'
  rw [hb, hm']

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
