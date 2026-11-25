/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Model
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift

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
second countable symplectic manifold without boundary such a `ι` exists, by the Lagrangian
neighbourhood theorem for the form `dλ`,
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent_neg`
(`Geometry/Symplectic/Neighborhood/Lagrangian.lean`).

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
* `SymplecticGeometry.dehnTwist_eq_of_apply_eq_comp`: precomposing `ι` with a diffeomorphism `c` of
  `T*Sⁿ` that commutes with the model twist does not change the twist.
* `SymplecticGeometry.exists_dehnTwist_eq_comp_orthogonal`: for `A ∈ O(n + 1)`, precomposing `ι`
  with the cotangent lift of `A` gives an embedding of the same kind for `f ∘ A`, with the same
  twist.

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

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], the paragraph
  before Proposition 1.11 (arXiv version 2): the Dehn twist along a framed Lagrangian sphere.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], 3rd ed.,
  p. 270 (the compactly supported twist).
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Proposition
  2.3 (for `n = 2`): the twist does not depend on the choices, one of which is a parametrization
  of the sphere up to `O(n + 1)`.
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


/-- **Reparametrizing by a symmetry of the model.** Let `c` be a diffeomorphism of `T*Sⁿ` that
commutes with the model twist `τ_R`, and let `ι'`, from an open set `U'` onto an open set `V'` of
`M`, be `ι ∘ c` on `U' = c⁻¹(U)`. Then `ι'` and `ι` give the same Dehn twist. -/
theorem dehnTwist_eq_of_apply_eq_comp {U' : Opens (𝕋 n)} {V' : Opens M}
    (c : (𝕋 n) ≃ₘ⟮𝓣 n, 𝓣 n⟯ 𝕋 n) (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (ι' : U' ≃ₘ⟮𝓣 n, I⟯ V')
    (hUU' : ∀ z, z ∈ U' ↔ c z ∈ U) (hι : ∀ z : U', (ι' z : M) = ι ⟨c z, (hUU' z).1 z.property⟩)
    (hR : IsTwistProfile R r₀) (hc : ∀ z, modelTwist hR (c z) = c (modelTwist hR z))
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n))) :
    dehnTwist ι' hR hU' = dehnTwist ι hR hU := by
  ext x
  by_cases hx : x ∈ range fun z : U ↦ (ι z : M)
  · obtain ⟨y, rfl⟩ := hx
    -- Every point of `U` is `c z` for a point `z` of `U'`.
    obtain ⟨z, rfl⟩ : ∃ z : U', (⟨c z, (hUU' z).1 z.property⟩ : U) = y :=
      ⟨⟨c.symm y, (hUU' _).2 (by rw [c.apply_symm_apply]; exact y.property)⟩,
        Subtype.ext (c.apply_symm_apply _)⟩
    dsimp only
    rw [← hι z, dehnTwist_apply_val, hι, hι z, dehnTwist_apply_val]
    simp only [hc]
  · -- Off the image of `ι`, which contains that of `ι'`, neither twist moves `x`.
    rw [dehnTwist_apply_of_notMem ι' hR hU' ?_,
      dehnTwist_apply_of_notMem ι hR hU fun h ↦ hx (image_subset_range _ _ h)]
    rintro ⟨z, -, rfl⟩
    exact hx ⟨_, (hι z).symm⟩

/-- **Reparametrizing the sphere by an orthogonal map.** Let `ι` pull `σ` back to `-ω_can` and
send the zero covector at each `q ∈ Sⁿ` to `f q`, and let `A ∈ O(n + 1)`, acting on `Sⁿ` by the
diffeomorphism `a = orthogonalToDiffSphere n ∞ A`. Then `ι ∘ c`, for the cotangent lift `c` of
`a`, is defined on an open set `U'` containing `{z | μ z ≤ r₀}`, pulls `σ` back to `-ω_can`,
sends the zero covector at `q` to `f (a q)`, and gives the same Dehn twist as `ι`. -/
theorem exists_dehnTwist_eq_comp_orthogonal [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hι : SmoothForm.mpullback ι ι.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
    {f : (𝕊 n) → M}
    (hιf : ∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ U, (ι ⟨_, h⟩ : M) = f q)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    ∃ (U' : Opens (𝕋 n)) (ι' : U' ≃ₘ⟮𝓣 n, I⟯ V)
      (hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n))),
      SmoothForm.mpullback ι' ι'.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) ∧
      (∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ U',
        (ι' ⟨_, h⟩ : M) = f (orthogonalToDiffSphere n ∞ A q)) ∧
      dehnTwist ι' hR hU' = dehnTwist ι hR hU := by
  set c := (orthogonalToDiffSphere n ∞ A).cotangent
  let U' : Opens (𝕋 n) := ⟨c ⁻¹' U, U.isOpen.preimage c.continuous⟩
  have hUU' (z : 𝕋 n) : z ∈ U' ↔ c z ∈ U := Iff.rfl
  let ι' : U' ≃ₘ⟮𝓣 n, I⟯ V := (c.subtype hUU').trans ι
  have hι' (z : U') : (ι' z : M) = ι ⟨c z, (hUU' z).1 z.property⟩ := by
    rw [Diffeomorph.coe_trans, Function.comp_apply]
    exact congrArg (fun w ↦ (ι w : M)) (Subtype.ext (c.subtype_apply_coe hUU' z))
  have hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n)) := fun z hz ↦
    hU (by rwa [mem_ofPred_eq, cotangentNorm_cotangent_orthogonal])
  refine ⟨U', ι', hU', ?_, fun q ↦ ?_,
    dehnTwist_eq_of_apply_eq_comp c ι ι' hUU' hι' hR (modelTwist_cotangent_orthogonal hR A) hU hU'⟩
  · -- `ι'` is the restriction of `c` followed by `ι`, and `c` preserves `ω_can`.
    rw [SmoothForm.mpullback_congr ι'.contMDiff (ι.contMDiff.comp (c.subtype hUU').contMDiff)
        (Diffeomorph.coe_trans _ _),
      ← SmoothForm.mpullback_mpullback _ _ (c.subtype hUU').contMDiff ι.contMDiff, hι,
      SmoothForm.mpullback_mpullback_of_comp_eq (c.subtype hUU').contMDiff contMDiff_subtypeVal
        contMDiff_subtypeVal c.contMDiff
        (funext (c.subtype_apply_coe hUU')),
      map_neg, Diffeomorph.mpullback_cotangent_symplecticForm, map_neg]
  · obtain ⟨h, hq⟩ := hιf (orthogonalToDiffSphere n ∞ A q)
    have hc := Diffeomorph.cotangent_zeroSection (orthogonalToDiffSphere n ∞ A) q
    refine ⟨(hUU' _).2 (by rwa [hc]), ?_⟩
    rw [hι', ← hq]
    exact congrArg (fun w ↦ (ι w : M)) (Subtype.ext hc)

end Twist

end SymplecticGeometry

end
