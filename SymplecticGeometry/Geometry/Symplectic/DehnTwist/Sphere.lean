/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Model
public import SymplecticGeometry.Geometry.Symplectic.Neighborhood.Lagrangian
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSection
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Extend
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise

/-!
# The Dehn twist along a Lagrangian sphere

Let `M` be a Hausdorff manifold with a two-form `σ`, and let `Sⁿ ⊆ ℝⁿ⁺¹` be the unit sphere,
with Tau Ceti's symplectic form `ω_can = CotangentBundle.symplecticForm` on `T*Sⁿ`. Tau Ceti
defines it as `-dλ`, for the Liouville form `λ`: it is the negative of the form `dλ` that the
cited sources take as canonical. Given a diffeomorphism `ι : U ≃ V` from an open set `U` of
`T*Sⁿ` onto an open set `V` of `M`, and a twist profile `R` of support radius `r₀` with
`{z | μ z ≤ r₀} ⊆ U` (`μ = cotangentNorm`), the Dehn twist `dehnTwist ι hR hU` is the
diffeomorphism of `M` that is `ι ∘ τ_R ∘ ι⁻¹` on `V`, `τ_R` the model twist `modelTwist hR`, and
the identity off `V`.

When `ι` pulls `σ` back to `-ω_can = dλ`, that is, when `ι` is symplectic for the sources' form,
the twist preserves `σ`, and when `ι` sends the zero covector at `q` to `f q` for a map
`f : Sⁿ → M`, it maps `f q` to `f (-q)`. For a Lagrangian embedding `f` of the sphere into a
symplectic manifold without boundary such a `ι` exists.

## Main definitions

* `SymplecticGeometry.dehnTwist ι hR hU`: the Dehn twist built from `ι` and the model twist of
  `R`.

## Main results

* `SymplecticGeometry.dehnTwist_apply_val`: on `V` the twist is `ι ∘ τ_R ∘ ι⁻¹`;
  `SymplecticGeometry.dehnTwist_apply_of_notMem`: it is the identity off the compact set
  `ι '' {z | μ z ≤ r₀}`.
* `SymplecticGeometry.mpullback_dehnTwist`: if `ι` pulls `σ` back to `-ω_can`, the twist
  preserves `σ`.
* `SymplecticGeometry.dehnTwist_apply_embedding`: if `ι` sends the zero covector at `q` to `f q`,
  the twist maps `f q` to `f (-q)`.
* `SymplecticGeometry.dehnTwist_eq_of_le`: restricting `ι` to a smaller open set that still
  contains `{z | μ z ≤ r₀}` does not change the twist.
* `SymplecticGeometry.exists_diffeotopy_dehnTwist_eq_of_isTwistProfile`: if `ι` pulls `σ` back
  to `-ω_can`, the twists of `ι` for two profiles differ by the final map of a compactly
  supported diffeotopy of `M` that preserves `σ` at all times.
* `SymplecticGeometry.exists_symplecticEmbedding`: for a Lagrangian embedding `f` of `Sⁿ` into a
  symplectic manifold there is such a `ι`, pulling `σ` back to `-ω_can` and extending `f` along
  the zero section.

## Implementation notes

The model twist is the identity where `μ ≥ r₀` and preserves `μ`, so it maps `U` onto itself
(`modelTwist_mem_iff`) and restricts to a diffeomorphism of `U` (Tau Ceti's
`Diffeomorph.subtype`) that is the identity off the compact set `{z | μ z ≤ r₀}`
(`isCompact_setOf_cotangentNorm_le`). Tau Ceti's
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`, applied to the open embedding `ι` of
`U` into `M`, turns it into a diffeomorphism of `M` that is the identity off the image of that
compact set. The twist preserves `σ` by `TauCeti.SmoothForm.mem_diffeomorphStabilizer_of_semiconj`
for the same embedding: the restriction of `τ_R` to `U` preserves the restriction of `-ω_can`,
since `τ_R` preserves `ω_can` (`mpullback_modelTwist_symplecticForm`).

The Lagrangian neighbourhood theorem
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent` gives a
diffeomorphism `ψ` that pulls `σ` back to `ω_can = -dλ` and extends `f`. The Dehn twist of the
sources asks for an `ι` that pulls `σ` back to their form `dλ = -ω_can` instead, so `ι = ψ ∘ N`
for the fibrewise negation `N` of `T*Sⁿ`, Tau Ceti's `vectorBundleScalarDiffeomorph` by `-1`,
which pulls `ω_can` back to `-ω_can`
(`TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm`) and fixes the
zero section (`TauCeti.vectorBundleScalarDiffeomorph_zeroSection`).

To change the profile, both profiles are read with the larger of their two radii
(`IsTwistProfile.mono`, `modelTwist_congr`).
`exists_isCompactlySupportedHamiltonian_modelTwist` joins their model twists by a diffeotopy of
`T*Sⁿ` that preserves `ω_can` and fixes `{z | r ≤ μ z}`. It maps `U` onto itself
(`TauCeti.Diffeotopy.apply_mem_iff_of_subset`), so it restricts to `U`
(`TauCeti.Diffeotopy.subtype`), and Tau Ceti's `TauCeti.Diffeotopy.exists_extend_of_isCompact`
carries it along `ι` to `M`. Its slices preserve `σ` by
`TauCeti.SmoothForm.mem_diffeomorphStabilizer_of_semiconj`, as for `mpullback_dehnTwist`.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], the paragraph
  before Proposition 1.11 (arXiv version 2): the Dehn twist along a framed Lagrangian sphere.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], 3rd ed.,
  Theorem 3.4.13 (the Lagrangian neighbourhood theorem) and p. 270 (the compactly supported
  twist).
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 2.2:
  the twist does not depend on the profile, up to symplectic isotopy.
* [P. Seidel, *Lectures on four-dimensional Dehn twists*][Seidel2008], §1a.
-/

public section

noncomputable section

namespace SymplecticGeometry

open _root_.Bundle Metric Set TauCeti TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ}

/-- The unit sphere `Sⁿ` of `ℝⁿ⁺¹`. -/
local notation "𝕊" n => sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The model with corners of `T*Sⁿ`. -/
local notation "𝓣" n => ModelWithCorners.prod (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)

/-- The cotangent bundle `T*Sⁿ` of the unit sphere. -/
local notation "𝕋" n => CotangentBundle (𝓡 n) (𝕊 n)

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
section Twist

variable [T2Space M] {U : Opens (𝕋 n)} {V : Opens M} {R : ℝ → ℝ} {r₀ : ℝ}

/-- The restriction to `U` of the model twist of radius `r₀`, when `U ⊇ {z | μ z ≤ r₀}`. -/
private def modelTwistOn (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) : U ≃ₘ⟮𝓣 n, 𝓣 n⟯ U :=
  (modelTwist hR).subtype fun z ↦ (modelTwist_mem_iff hR hU z).symm

private theorem modelTwistOn_apply_coe (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) (z : U) :
    (modelTwistOn hR hU z : 𝕋 n) = modelTwist hR z :=
  Diffeomorph.subtype_apply_coe _ _ z

/-- The model twist, carried to `V` by `ι`, extends by the identity to a diffeomorphism of `M`. -/
private theorem exists_dehnTwist (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ z : U, Φ (ι z) = ι (modelTwistOn hR hU z)) ∧
      ∀ x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}, Φ x = x :=
  IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact
    (fun z ↦ (ι.isLocalDiffeomorph z).comp (hg := isLocalDiffeomorph_subtype_val (ι z)))
    (V.isOpen.isOpenEmbedding_subtypeVal.comp ι.toHomeomorph.isOpenEmbedding) _
    (Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_setOf_cotangentNorm_le r₀)
      (by rwa [Subtype.range_coe]))
    fun z hz ↦ Subtype.ext <| by
      rw [modelTwistOn_apply_coe, modelTwist_apply_of_le hR (le_of_not_ge hz)]

/-- **The Dehn twist along a Lagrangian sphere**, built from a diffeomorphism `ι` from an open set
`U` of `T*Sⁿ` onto an open set `V` of `M` and a twist profile `R` of support radius `r₀` with
`{z | μ z ≤ r₀} ⊆ U`: the diffeomorphism of `M` that is `ι ∘ τ_R ∘ ι⁻¹` on `V`, for the model twist
`τ_R` of `R` (`dehnTwist_apply_val`), and the identity off the compact set `ι '' {z | μ z ≤ r₀}`
(`dehnTwist_apply_of_notMem`, `isCompact_image_setOf_cotangentNorm_le`). -/
def dehnTwist (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) : M ≃ₘ⟮I, I⟯ M :=
  (exists_dehnTwist ι hR hU).choose

/-- On `V`, the Dehn twist is the conjugate `ι ∘ τ_R ∘ ι⁻¹` of the model twist. -/
@[simp]
theorem dehnTwist_apply_val (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) (z : U) :
    dehnTwist ι hR hU (ι z) = ι ⟨modelTwist hR z, (modelTwist_mem_iff hR hU z).2 z.property⟩ := by
  rw [dehnTwist, (exists_dehnTwist ι hR hU).choose_spec.1]
  congr 2
  exact Subtype.ext (modelTwistOn_apply_coe hR hU z)

/-- The Dehn twist is the identity off the image under `ι` of `{z | μ z ≤ r₀}`. -/
theorem dehnTwist_apply_of_notMem (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {x : M}
    (hx : x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}) :
    dehnTwist ι hR hU x = x :=
  (exists_dehnTwist ι hR hU).choose_spec.2 x hx

omit [T2Space M] in
/-- The set `ι '' {z | μ z ≤ r₀}`, off which the Dehn twist is the identity, is compact. -/
theorem isCompact_image_setOf_cotangentNorm_le (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) :
    IsCompact ((fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}) :=
  (Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_setOf_cotangentNorm_le r₀)
    (by rwa [Subtype.range_coe])).image (continuous_subtypeVal.comp ι.continuous)

/-- **The Dehn twist is symplectic.** If `ι` pulls the restriction of `σ` to `V` back to the
restriction of `-ω_can` to `U`, the Dehn twist preserves `σ`. As `ω_can = -dλ`, the hypothesis
says that `ι` is symplectic for the form `dλ` of the cited sources. -/
theorem mpullback_dehnTwist [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hι : SmoothForm.mpullback ι ι.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) :
    SmoothForm.mpullback (dehnTwist ι hR hU) (dehnTwist ι hR hU).contMDiff σ = σ := by
  -- The restricted model twist preserves the restriction of `-ω_can` to `U`.
  have hτ : modelTwistOn hR hU ∈ SmoothForm.diffeomorphStabilizer
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) :=
    SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_subtypeVal
      (modelTwistOn_apply_coe hR hU) (by
        rw [SmoothForm.mem_diffeomorphStabilizer, map_neg, mpullback_modelTwist_symplecticForm])
  have hΦ (z : U) : dehnTwist ι hR hU (ι z) = ι (modelTwistOn hR hU z) := by
    rw [dehnTwist, (exists_dehnTwist ι hR hU).choose_spec.1]
  exact SmoothForm.mem_diffeomorphStabilizer.1 <| SmoothForm.mem_diffeomorphStabilizer_of_semiconj
    (fun z ↦ (ι.isLocalDiffeomorph z).comp (hg := isLocalDiffeomorph_subtype_val (ι z)))
    (by rw [← hι, SmoothForm.mpullback_mpullback]) hτ (fun z ↦ (hΦ z).symm)
    (isCompact_image_setOf_cotangentNorm_le ι hU).isClosed (image_subset_range _ _)
    fun x hx ↦ dehnTwist_apply_of_notMem ι hR hU hx

/-- If `ι` sends the zero covector at each `q ∈ Sⁿ` to `f q`, the Dehn twist maps `f q` to
`f (-q)`. -/
theorem dehnTwist_apply_embedding (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {f : (𝕊 n) → M}
    (hιf : ∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ U, (ι ⟨_, h⟩ : M) = f q) (q : 𝕊 n) :
    dehnTwist ι hR hU (f q) = f (-q) := by
  obtain ⟨h, hq⟩ := hιf q
  obtain ⟨h', hq'⟩ := hιf (-q)
  simp [← hq, ← hq']

/-- **Shrinking the neighbourhood.** If `ι'` is the restriction of `ι` to an open set `U' ≤ U`
that still contains `{z | μ z ≤ r₀}`, onto an open set `V'` of `M`, then `ι'` and `ι` give the
same Dehn twist. -/
theorem dehnTwist_eq_of_le {U' : Opens (𝕋 n)} {V' : Opens M} (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (ι' : U' ≃ₘ⟮𝓣 n, I⟯ V') (hUU' : U' ≤ U) (hι : ∀ z : U', (ι' z : M) = ι ⟨z, hUU' z.property⟩)
    (hR : IsTwistProfile R r₀) (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n))) :
    dehnTwist ι' hR hU' = dehnTwist ι hR hU := by
  ext x
  by_cases hx : x ∈ range fun z : U' ↦ (ι' z : M)
  · obtain ⟨z, rfl⟩ := hx
    dsimp only
    rw [dehnTwist_apply_val, hι, hι, dehnTwist_apply_val]
  · -- Off the image of `ι'`, neither twist moves `x`: the support of the twist of `ι` lies in it.
    rw [dehnTwist_apply_of_notMem ι' hR hU' fun h ↦ hx (image_subset_range _ _ h),
      dehnTwist_apply_of_notMem ι hR hU]
    rintro ⟨z, hz, rfl⟩
    exact hx ⟨⟨z, hU' hz⟩, hι _⟩

/-- **Changing the profile.** If `ι` pulls `σ` back to `-ω_can`, the Dehn twists of `ι` for two
twist profiles `R₁` and `R₂` differ by the final map of a diffeotopy of `M` that preserves `σ` at
all times and fixes every point outside a compact set at all times. -/
theorem exists_diffeotopy_dehnTwist_eq_of_isTwistProfile [IsManifold I ∞ M]
    {σ : SmoothTwoForm I M} (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : SmoothForm.mpullback ι ι.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
    {R₁ R₂ : ℝ → ℝ} {r₁ r₂ : ℝ} (hR₁ : IsTwistProfile R₁ r₁)
    (hU₁ : {z : 𝕋 n | cotangentNorm z ≤ r₁} ⊆ (U : Set (𝕋 n))) (hR₂ : IsTwistProfile R₂ r₂)
    (hU₂ : {z : 𝕋 n | cotangentNorm z ≤ r₂} ⊆ (U : Set (𝕋 n))) :
    ∃ (Φ : Diffeotopy I ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (dehnTwist ι hR₁ hU₁ x) = dehnTwist ι hR₂ hU₂ x := by
  -- Both profiles have the support radius `r = max r₁ r₂`.
  have h₁ := hR₁.mono (le_max_left r₁ r₂)
  have h₂ := hR₂.mono (le_max_right r₁ r₂)
  have hU : {z : 𝕋 n | cotangentNorm z ≤ max r₁ r₂} ⊆ (U : Set (𝕋 n)) := by
    rcases max_choice r₁ r₂ with h | h <;> rw [h]
    exacts [hU₁, hU₂]
  obtain ⟨Φ₀, hΦ₀, hΦ₀r, hΦ₀τ⟩ := exists_isCompactlySupportedHamiltonian_modelTwist h₁ h₂
  have hΦ₀K : ∀ t, ∀ z ∉ {z : 𝕋 n | cotangentNorm z ≤ max r₁ r₂}, Φ₀ (t, z) = z :=
    fun t z hz ↦ hΦ₀r t z (le_of_not_ge hz)
  -- The diffeotopy restricts to `U`, and `ι` carries it to `M`.
  let Ψ := Φ₀.subtype U (Φ₀.apply_mem_iff_of_subset hU hΦ₀K)
  obtain ⟨Φ, hΦι, hΦK⟩ := Ψ.exists_extend_of_isCompact (χ := fun z : U ↦ (ι z : M))
    (fun z ↦ (ι.isLocalDiffeomorph z).comp (hg := isLocalDiffeomorph_subtype_val (ι z)))
    (V.isOpen.isOpenEmbedding_subtypeVal.comp ι.toHomeomorph.isOpenEmbedding)
    (Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_setOf_cotangentNorm_le (max r₁ r₂)) (by rwa [Subtype.range_coe]))
    fun t z hz ↦ Subtype.ext <| by
      rw [Diffeotopy.subtype_apply_coe]; exact hΦ₀K t z hz
  refine ⟨Φ, _, isCompact_image_setOf_cotangentNorm_le ι hU, fun t ↦ ?_, hΦK, fun x ↦ ?_⟩
  · -- The slices of `Ψ` preserve the restriction of `-ω_can`, and `ι` intertwines them with
    -- those of `Φ`, which are the identity off a compact subset of `V`.
    have hΨ : Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) :=
      SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_subtypeVal
        (f := Φ₀.timeSlice t) (fun z ↦ by rw [Diffeotopy.timeSlice_apply,
          Diffeotopy.timeSlice_apply, Diffeotopy.subtype_apply_coe]) (by
        rw [SmoothForm.mem_diffeomorphStabilizer, map_neg, SmoothForm.mem_diffeomorphStabilizer.1
          (hΦ₀.isHamiltonian.timeSlice_mem_diffeomorphStabilizer t)])
    exact SmoothForm.mem_diffeomorphStabilizer_of_semiconj
      (fun z ↦ (ι.isLocalDiffeomorph z).comp (hg := isLocalDiffeomorph_subtype_val (ι z)))
      (by rw [← hι, SmoothForm.mpullback_mpullback]) hΨ
      (fun z ↦ by rw [Diffeotopy.timeSlice_apply, Diffeotopy.timeSlice_apply, Function.comp_apply,
        Function.comp_apply, hΦι])
      (isCompact_image_setOf_cotangentNorm_le ι hU).isClosed (image_subset_range _ _)
      fun x hx ↦ by rw [Diffeotopy.timeSlice_apply, hΦK t x hx]
  · by_cases hx : x ∈ range fun z : U ↦ (ι z : M)
    · obtain ⟨z, rfl⟩ := hx
      rw [dehnTwist_apply_val, dehnTwist_apply_val, Diffeotopy.final_apply, hΦι]
      have key : Φ₀.final (modelTwist hR₁ z) = modelTwist hR₂ z := by
        rw [modelTwist_congr hR₁ h₁, hΦ₀τ, modelTwist_congr h₂ hR₂]
      congr 2
      apply Subtype.ext
      rw [Diffeotopy.subtype_apply_coe]
      exact (Diffeotopy.final_apply _ _).symm.trans key
    · have hK : x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ max r₁ r₂} :=
        fun h ↦ hx (image_subset_range _ _ h)
      rw [dehnTwist_apply_of_notMem ι hR₁ hU₁ fun h ↦ hx (image_subset_range _ _ h),
        dehnTwist_apply_of_notMem ι hR₂ hU₂ fun h ↦ hx (image_subset_range _ _ h),
        Diffeotopy.final_apply, hΦK 1 x hK]

end Twist

/-- **Symplectic embeddings around a Lagrangian sphere.** For a Lagrangian embedding `f` of the
unit sphere `Sⁿ` into a symplectic manifold `(M, σ)`, there is a diffeomorphism `ι` from an open
neighbourhood `U` of the zero section of `T*Sⁿ` onto an open set `V` of `M` that pulls the
restriction of `σ` back to that of `-ω_can`, so that `ι` is symplectic for the form `dλ` of the
cited sources, and sends the zero covector at `q` to `f q`. -/
theorem exists_symplecticEmbedding [FiniteDimensional ℝ F] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M] {σ : SmoothTwoForm I M} {hσ : σ.IsSymplectic}
    {f : SmoothEmbedding (𝓡 n) I ∞ (𝕊 n) M} (hf : hσ.isNondegenerate.IsLagrangianMap (𝓡 n) f) :
    ∃ (U : Opens (𝕋 n)) (V : Opens M) (ι : U ≃ₘ⟮𝓣 n, I⟯ V),
      SmoothForm.mpullback ι ι.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) ∧
      ∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ U, (ι ⟨_, h⟩ : M) = f q := by
  obtain ⟨U, V, ψ, hψ0, hψσ⟩ := hf.exists_symplectomorphism_cotangent (hσ := hσ)
  -- The fibrewise negation `N` of `T*Sⁿ`, which fixes the zero section.
  let N := vectorBundleScalarDiffeomorph (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (V := fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) (fun _ ↦ (-1 : ℝ))
    (contMDiff_const (n := ∞)) fun _ ↦ by norm_num
  have hN0 (q : 𝕊 n) : N (zeroSection _ _ q) = zeroSection _ _ q :=
    vectorBundleScalarDiffeomorph_zeroSection _ _ _ q
  let U' : Opens (𝕋 n) := ⟨N ⁻¹' U, U.isOpen.preimage N.continuous⟩
  let N' : U' ≃ₘ⟮𝓣 n, 𝓣 n⟯ U := N.subtype fun _ ↦ Iff.rfl
  refine ⟨U', V, N'.trans ψ, ?_, fun q ↦ ?_⟩
  · rw [SmoothForm.mpullback_trans, hψσ, SmoothForm.mpullback_mpullback_of_comp_eq _ _
      contMDiff_subtypeVal N.contMDiff (funext fun z ↦ Diffeomorph.subtype_apply_coe _ _ z),
      CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm]
    rw [← neg_one_smul ℝ (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))]
  · obtain ⟨h, hq, -⟩ := hψ0 q
    refine ⟨show N (zeroSection _ _ q) ∈ U by rwa [hN0], ?_⟩
    rw [Diffeomorph.coe_trans, Function.comp_apply, ← hq]
    congr 2
    exact Subtype.ext ((Diffeomorph.subtype_apply_coe _ _ _).trans (hN0 q))

end SymplecticGeometry

end
