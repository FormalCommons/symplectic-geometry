/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Normalized.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.Relative.Period
public import SymplecticGeometry.Geometry.Symplectic.Blowup.SliceIntegral
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.Integral
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

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

## Main results

* `IsNormalizedBallEmbedding.exists_mextDeriv_eq_mpullback_subtypeVal_normalizedBlowupForm_sub`:
  on the complement of the exceptional divisor, `ω̃_{ψ,l,ε} - π^* σ` is `d β` for a one-form `β`
  that vanishes off the image of `L(l + ε)` under the lift.
* `IsNormalizedBallEmbedding.singularKronecker_relativeDeRhamHom_mk_relClass_curveLift_smul`:
  the class of such a relative cocycle pairs to `-π l²` with a disc through `Z` along a line.

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

end IsNormalizedBallEmbedding

end SymplecticGeometry

end
