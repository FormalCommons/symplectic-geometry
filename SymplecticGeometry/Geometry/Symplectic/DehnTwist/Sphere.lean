/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.DehnTwist.Model
public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic
public import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.WeinsteinChart
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Extend
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Stabilizer
public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Submanifold
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Rescaling
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Isotropic
import TauCeti.Data.Set.Function
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Extend
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

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

When `ι` pulls `σ` back to `-ω_can = dλ` (a `TauCeti.SmoothTwoForm.IsSymplectomorphism` from the
restriction of `-ω_can` to `U` to that of `σ` to `V`), that is, when `ι` is symplectic for the
sources' form, the twist preserves `σ`, and when `ι` sends the
zero covector at `q` to `f q` for a map `f : Sⁿ → M` (`CotangentBundle.AgreesOnZeroSection f ι`),
it maps `f q` to `f (-q)`. The two conditions together are `CotangentBundle.IsWeinsteinChart`.
For a Lagrangian embedding `f` of the sphere into a second countable symplectic manifold without
boundary such a `ι` exists, by the Lagrangian neighbourhood theorem for the form `dλ`,
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.exists_symplectomorphism_cotangent_neg`
(`Geometry/Symplectic/Neighborhood/Lagrangian.lean`).

## Main definitions

* `SymplecticGeometry.dehnTwist ι hR hU`: the Dehn twist built from `ι` and the model twist of
  `R`.

## Main results

* `SymplecticGeometry.dehnTwist_apply_val`: on `V` the twist is `ι ∘ τ_R ∘ ι⁻¹`;
  `SymplecticGeometry.dehnTwist_apply_of_notMem`: it is the identity off the compact set
  `ι '' {z | μ z ≤ r₀}`.
* `SymplecticGeometry.mem_diffeomorphStabilizer_of_semiconj_cotangent`: if `ι` pulls `σ` back to
  `-ω_can`, a diffeomorphism of `M` that `ι` intertwines with the restriction to `U` of a
  diffeomorphism preserving `ω_can`, and that is the identity off `ι '' {z | μ z ≤ r₀}`, preserves
  `σ`.
* `SymplecticGeometry.mpullback_dehnTwist`: if `ι` pulls `σ` back to `-ω_can`, the twist
  preserves `σ`.
* `SymplecticGeometry.dehnTwist_apply_embedding`: if `ι` sends the zero covector at `q` to `f q`,
  the twist maps `f q` to `f (-q)`.
* `SymplecticGeometry.dehnTwist_eq_of_le`: restricting `ι` to a smaller open set that still
  contains `{z | μ z ≤ r₀}` does not change the twist.
* `SymplecticGeometry.exists_diffeotopy_dehnTwist_eq_of_isTwistProfile`: if `ι` pulls `σ` back
  to `-ω_can`, the twists of `ι` for two profiles differ by the final map of a compactly
  supported diffeotopy of `M` that preserves `σ` at all times.
* `SymplecticGeometry.dehnTwist_eq_of_apply_eq_comp`: precomposing `ι` with a diffeomorphism `c` of
  `T*Sⁿ` that commutes with the model twist does not change the twist.
* `SymplecticGeometry.exists_dehnTwist_eq_comp_orthogonal`: for `A ∈ O(n + 1)`, precomposing `ι`
  with the cotangent lift `c` of `A`, on `c⁻¹(U)`, gives an embedding of the same kind for
  `f ∘ A`, with the same twist.
* `SymplecticGeometry.eq_dehnTwist`: a diffeomorphism of `M` that satisfies the two apply lemmas
  on `ι '' {z | μ z ≤ r₀}` and off it is the twist.
* `SymplecticGeometry.exists_diffeotopy_dehnTwist_eq_of_smoothIsotopy`: if a smooth isotopy of
  local diffeomorphisms from an open set `W ⊇ {z | μ z ≤ r₀}` into `M`, each pulling `σ` back
  to `-ω_can`, runs from the restriction of `ι₀` to `W` to that of `ι₁`, the twists of `ι₀`
  and `ι₁` differ by the final map of a compactly supported diffeotopy of `M` that preserves `σ`
  at all times.
* `SymplecticGeometry.exists_diffeotopy_dehnTwist_eq_of_apply_zeroSection`: if `ι₁` and `ι₂` both
  pull `σ` back to `-ω_can` and send the zero covector at `q` to `f q`, their twists, for any
  two profiles, differ by the final map of a compactly supported diffeotopy of `M` that
  preserves `σ` at all times.
* `SymplecticGeometry.exists_smoothIsotopy_of_diffeotopy`: for such `ι` and a symplectic `σ`, a
  diffeotopy `Φ` of `Sⁿ` moves `ι`, near the zero section, by an isotopy of open embeddings
  pulling `σ` back to `-ω_can` along which the zero covector at `q` goes to `f (Φ (t, q))`; its
  end is an embedding of the same kind for `f ∘ Φ₁`.
* `SymplecticGeometry.exists_diffeotopy_dehnTwist_eq_of_diffeotopy`: for such `ι` and a
  diffeotopy `Φ` of `Sⁿ`, there is an embedding `ι'` of the same kind for `f ∘ Φ₁` whose twists
  differ from the twist of `ι` by the final map of a compactly supported diffeotopy of `M` that
  preserves `σ` at all times.

## Implementation notes

The model twist is the identity where `μ ≥ r₀` and preserves `μ`, so it maps `U` onto itself
(`modelTwist_mem_iff`) and restricts to a diffeomorphism of `U` (Tau Ceti's
`Diffeomorph.subtype`) that is the identity off the compact set `{z | μ z ≤ r₀}`
(`isCompact_setOf_cotangentNorm_le`, `isCompact_setOf_cotangentNorm_coe_le`). Tau Ceti's
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact`, applied to the open embedding `ι` of
`U` into `M`, turns it into a diffeomorphism of `M` that is the identity off the image of that
compact set. A diffeomorphism of `M` obtained in this way from the restriction of a
diffeomorphism preserving `ω_can` preserves `σ`
(`mem_diffeomorphStabilizer_of_semiconj_cotangent`), by
`TauCeti.SmoothForm.mem_diffeomorphStabilizer_of_semiconj` for the same embedding: the
restriction preserves the restriction of `-ω_can`. This applies to the twist, since `τ_R`
preserves `ω_can` (`mpullback_modelTwist_symplecticForm`).

To change the profile, both profiles are read with the larger of their two radii
(`IsTwistProfile.mono`, `modelTwist_congr`).
`exists_isCompactlySupportedHamiltonian_modelTwist` joins their model twists by a diffeotopy of
`T*Sⁿ` that preserves `ω_can` and fixes `{z | r ≤ μ z}`. Its time slices are injective, so they
map `U` onto itself (Tau Ceti's `Function.Injective.apply_mem_iff_of_eq_self`); it restricts to
`U` (`TauCeti.Diffeotopy.subtype`), and Tau Ceti's `TauCeti.Diffeotopy.exists_extend_of_isCompact`
carries it along `ι` to `M`. Its slices preserve `σ` by
`mem_diffeomorphStabilizer_of_semiconj_cotangent`, as the twist does.

For two embeddings `ι₁` and `ι₂` that agree on the zero section,
`CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq_neg` joins their restrictions to
an open neighbourhood `U` of the zero section by an isotopy `G` of open embeddings whose slices
pull `σ` back to `-ω_can`. By compactness `U` contains `{z | μ z ≤ r}` for some `r > 0`
(`exists_pos_setOf_cotangentNorm_le_subset`), and the change
of profile above replaces both profiles by one profile `R` of radius `r`. The slices of `G` are
smooth embeddings between manifolds of the same dimension (Tau Ceti's
`IsLocalDiffeomorphAt.finrank_eq`, applied to `ι₁`), hence local diffeomorphisms (Tau Ceti's
`Manifold.IsImmersion.isLocalDiffeomorph`). For such an isotopy
(`exists_diffeotopy_dehnTwist_eq_of_smoothIsotopy`),
`TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend_of_isSymplectic` moves the restriction
of `τ_R` to `U` along `G`. Its transplant along `G_0` is the twist of `ι₁`, and its transplant
along `G_1` is the twist of `ι₂` (`eq_dehnTwist`). The three diffeotopies compose in the
subgroup `TauCeti.SmoothForm.compactlySupportedIsotopyStabilizer σ`.

To move `ι` along a diffeotopy `Φ` of `Sⁿ`, the isotopy `t ↦ f ∘ Φ_t`
(`TauCeti.Diffeotopy.precompSmoothIsotopy`) keeps the pullback of `σ` at `0`
(`TauCeti.CotangentBundle.mpullback_eq_zero_of_apply_zeroSection`: the zero section is
Lagrangian), so
`TauCeti.SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq` extends it to a symplectic
isotopy `F` of an open neighbourhood `U₀` of `f(Sⁿ)`. On the open set `W` of the points of `U`
that `ι` maps into `U₀`, `ι` is an injective local diffeomorphism into `U₀`, hence a smooth
embedding (`IsLocalDiffeomorph.isSmoothEmbedding`), and precomposing `F` with it
(`TauCeti.SmoothIsotopy.precompSmoothEmbedding`) gives the isotopy `t ↦ F_t ∘ ι`. Its
slices are injective, as the slices of `F` are smooth embeddings, and local diffeomorphisms
(`Manifold.IsImmersion.isLocalDiffeomorph` for `F_t`), so the slice at time `1` is a
diffeomorphism onto its open image (Tau Ceti's `IsLocalDiffeomorph.diffeomorphOfInjective`).
That slice is the new embedding `ι'`; to compare twists, the profile of `ι` is first changed to
one that fits the domain of `ι'`, and the twist for that profile is then moved along the
isotopy (`exists_diffeotopy_dehnTwist_eq_of_diffeotopy`).

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], the paragraph
  before Proposition 1.11 (arXiv version 2): the Dehn twist along a framed Lagrangian sphere.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], 3rd ed.,
  p. 270 (the compactly supported twist).
* [P. Seidel, *Floer homology and the symplectic isotopy problem*][Seidel1997Thesis], Lemma 2.2:
  the twist does not depend on the profile, up to symplectic isotopy; Proposition 2.3 (for
  `n = 2`): it does not depend on the choices, one of which is a parametrization of the sphere
  up to `O(n + 1)`.
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

private theorem modelTwistOn_apply_of_notMem (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {z : U}
    (hz : z ∉ {z : U | cotangentNorm (z : 𝕋 n) ≤ r₀}) : modelTwistOn hR hU z = z :=
  Subtype.ext <| by rw [modelTwistOn_apply_coe, modelTwist_apply_of_le hR (le_of_not_ge hz)]

/-- The model twist, carried to `V` by `ι`, extends by the identity to a diffeomorphism of `M`. -/
private theorem exists_dehnTwist (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ z : U, Φ (ι z) = ι (modelTwistOn hR hU z)) ∧
      ∀ x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}, Φ x = x :=
  IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact
    (isLocalDiffeomorph_subtypeVal_comp_iff.2 ι.isLocalDiffeomorph)
    (V.isOpen.isOpenEmbedding_subtypeVal.comp ι.toHomeomorph.isOpenEmbedding) _
    (isCompact_setOf_cotangentNorm_coe_le hU) fun _ ↦ modelTwistOn_apply_of_notMem hR hU

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

/-- **The twist is determined by its apply lemmas.** A diffeomorphism `Φ` of `M` that is
`ι ∘ τ_R ∘ ι⁻¹` on `ι '' {z | μ z ≤ r₀}` and the identity off that set is the Dehn twist. -/
theorem eq_dehnTwist (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {Φ : M ≃ₘ⟮I, I⟯ M}
    (hΦ : ∀ z : U, cotangentNorm (z : 𝕋 n) ≤ r₀ →
      Φ (ι z) = ι ⟨modelTwist hR z, (modelTwist_mem_iff hR hU z).2 z.property⟩)
    (hΦr : ∀ x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}, Φ x = x) :
    Φ = dehnTwist ι hR hU := by
  ext x
  by_cases hx : x ∈ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}
  · obtain ⟨z, hz, rfl⟩ := hx
    rw [hΦ z hz, dehnTwist_apply_val]
  · rw [hΦr x hx, dehnTwist_apply_of_notMem ι hR hU hx]

omit [T2Space M] in
/-- The set `ι '' {z | μ z ≤ r₀}`, off which the Dehn twist is the identity, is compact. -/
theorem isCompact_image_setOf_cotangentNorm_le (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) :
    IsCompact ((fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}) :=
  (isCompact_setOf_cotangentNorm_coe_le hU).image (continuous_subtypeVal.comp ι.continuous)

/-- **Transplanted symplectic maps.** Let `ι` pull the restriction of `σ` to `V` back to the
restriction of `-ω_can` to `U`, and let `f` be a diffeomorphism of `T*Sⁿ` preserving `ω_can` that
restricts to a diffeomorphism `f'` of `U`. A diffeomorphism `Φ` of `M` with `Φ ∘ ι = ι ∘ f'` that
is the identity off `ι '' {z | μ z ≤ r₀}`, for `{z | μ z ≤ r₀} ⊆ U`, preserves `σ`. -/
theorem mem_diffeomorphStabilizer_of_semiconj_cotangent [IsManifold I ∞ M]
    {σ : SmoothTwoForm I M} (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : SmoothTwoForm.IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) ι)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {f : (𝕋 n) ≃ₘ⟮𝓣 n, 𝓣 n⟯ 𝕋 n}
    (hf : f ∈ SmoothForm.diffeomorphStabilizer (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
    {f' : U ≃ₘ⟮𝓣 n, 𝓣 n⟯ U} (hf' : ∀ z, (f' z : 𝕋 n) = f z) {Φ : M ≃ₘ⟮I, I⟯ M}
    (hΦ : ∀ z, Φ (ι z) = ι (f' z))
    (hΦr : ∀ x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}, Φ x = x) :
    Φ ∈ SmoothForm.diffeomorphStabilizer σ := by
  exact SmoothForm.mem_diffeomorphStabilizer_of_semiconj
    (isLocalDiffeomorph_subtypeVal_comp_iff.2 ι.isLocalDiffeomorph)
    (by rw [← SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 hι,
      SmoothForm.mpullback_mpullback])
    (SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_subtypeVal hf'
      (by rwa [SmoothForm.diffeomorphStabilizer_neg])) (fun z ↦ (hΦ z).symm)
    (isCompact_image_setOf_cotangentNorm_le ι hU).isClosed (image_subset_range _ _) hΦr

/-- **The Dehn twist is symplectic.** If `ι` pulls the restriction of `σ` to `V` back to the
restriction of `-ω_can` to `U`, the Dehn twist preserves `σ`. As `ω_can = -dλ`, the hypothesis
says that `ι` is symplectic for the form `dλ` of the cited sources. -/
theorem mpullback_dehnTwist [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hι : SmoothTwoForm.IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) ι) :
    SmoothForm.mpullback (dehnTwist ι hR hU) (dehnTwist ι hR hU).contMDiff σ = σ :=
  SmoothForm.mem_diffeomorphStabilizer.1 <| mem_diffeomorphStabilizer_of_semiconj_cotangent ι hι
    hU (SmoothForm.mem_diffeomorphStabilizer.2 (mpullback_modelTwist_symplecticForm hR))
    (modelTwistOn_apply_coe hR hU)
    (fun z ↦ by rw [dehnTwist, (exists_dehnTwist ι hR hU).choose_spec.1])
    fun _ hx ↦ dehnTwist_apply_of_notMem ι hR hU hx

/-- If `ι` sends the zero covector at each `q ∈ Sⁿ` to `f q`, the Dehn twist maps `f q` to
`f (-q)`. -/
theorem dehnTwist_apply_embedding (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {f : (𝕊 n) → M}
    (hιf : CotangentBundle.AgreesOnZeroSection f ι) (q : 𝕊 n) :
    dehnTwist ι hR hU (f q) = f (-q) := by
  obtain ⟨h, hq⟩ := hιf.exists_apply_eq q
  obtain ⟨h', hq'⟩ := hιf.exists_apply_eq (-q)
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
  refine (eq_dehnTwist ι' hR hU' (fun z _ ↦ ?_) fun x hx ↦ ?_).symm
  · rw [hι, dehnTwist_apply_val, hι]
    simp only [hc]
  · by_cases hx' : x ∈ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ r₀}
    · obtain ⟨y, -, rfl⟩ := hx'
      -- Every point of `U` is `c z` for a point `z` of `U'`.
      obtain ⟨z, rfl⟩ := (c.toEquiv.subtypeEquiv hUU').surjective y
      -- The point `ι (c z) = ι' z` lies off `ι' '' {μ ≤ r₀}`, so the model twist fixes `z`.
      have hz : r₀ ≤ cotangentNorm (z : 𝕋 n) := le_of_not_ge fun hz ↦ hx ⟨z, hz, hι z⟩
      rw [dehnTwist_apply_val]
      simp only [Equiv.subtypeEquiv_apply, Diffeomorph.coe_toEquiv, hc,
        modelTwist_apply_of_le hR hz]
    · exact dehnTwist_apply_of_notMem ι hR hU hx'

/-- **Reparametrizing the sphere by an orthogonal map.** Let `ι` pull `σ` back to `-ω_can` and
send the zero covector at each `q ∈ Sⁿ` to `f q`, and let `A ∈ O(n + 1)`, acting on `Sⁿ` by the
diffeomorphism `a = orthogonalToDiffSphere n ∞ A`. Then `ι ∘ c`, for the cotangent lift `c` of
`a`, is defined on the open set `U' = c⁻¹(U)`, which contains `{z | μ z ≤ r₀}`; it pulls `σ`
back to `-ω_can`, sends the zero covector at `q` to `f (a q)`, and gives the same Dehn twist as
`ι`. -/
theorem exists_dehnTwist_eq_comp_orthogonal [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (ι : U ≃ₘ⟮𝓣 n, I⟯ V) (hR : IsTwistProfile R r₀)
    (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n))) {f : (𝕊 n) → M}
    (hι : CotangentBundle.IsWeinsteinChart σ f ι) (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    ∃ (U' : Opens (𝕋 n)) (ι' : U' ≃ₘ⟮𝓣 n, I⟯ V)
      (hUU' : ∀ z, z ∈ U' ↔ (orthogonalToDiffSphere n ∞ A).cotangent z ∈ U)
      (hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n))),
      (∀ z : U', (ι' z : M) = ι ⟨(orthogonalToDiffSphere n ∞ A).cotangent z,
        (hUU' z).1 z.property⟩) ∧
      CotangentBundle.IsWeinsteinChart σ (f ∘ orthogonalToDiffSphere n ∞ A) ι' ∧
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
  exact ⟨U', ι', hUU', hU', hι', hι.cotangent_subtype_trans hUU',
    dehnTwist_eq_of_apply_eq_comp c ι ι' hUU' hι' hR (modelTwist_cotangent_orthogonal hR A) hU hU'⟩

/-- **Shrinking the neighbourhood.** If `ι'` is the restriction of `ι` to an open set `U' ≤ U`
that still contains `{z | μ z ≤ r₀}`, onto an open set `V'` of `M`, then `ι'` and `ι` give the
same Dehn twist. -/
theorem dehnTwist_eq_of_le {U' : Opens (𝕋 n)} {V' : Opens M} (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (ι' : U' ≃ₘ⟮𝓣 n, I⟯ V') (hUU' : U' ≤ U) (hι : ∀ z : U', (ι' z : M) = ι ⟨z, hUU' z.property⟩)
    (hR : IsTwistProfile R r₀) (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (hU' : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U' : Set (𝕋 n))) :
    dehnTwist ι' hR hU' = dehnTwist ι hR hU :=
  (eq_dehnTwist ι' hR hU' (fun z _ ↦ by rw [hι, dehnTwist_apply_val, hι])
    fun x hx ↦ dehnTwist_apply_of_notMem ι hR hU fun ⟨z, hz, h⟩ ↦
      hx ⟨⟨z, hU' hz⟩, hz, (hι _).trans h⟩).symm

/-- **Changing the profile.** If `ι` pulls `σ` back to `-ω_can`, the Dehn twists of `ι` for two
twist profiles `R₁` and `R₂` differ by the final map of a diffeotopy of `M` that preserves `σ` at
all times and fixes every point outside a compact set at all times. -/
theorem exists_diffeotopy_dehnTwist_eq_of_isTwistProfile [IsManifold I ∞ M]
    {σ : SmoothTwoForm I M} (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : SmoothTwoForm.IsSymplectomorphism (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) ι)
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
  have hΦ₀K (t) : ∀ z ∉ {z : 𝕋 n | cotangentNorm z ≤ max r₁ r₂}, Φ₀.timeSlice t z = z :=
    fun z hz ↦ by rw [Diffeotopy.timeSlice_apply]; exact hΦ₀r t z (le_of_not_ge hz)
  -- The diffeotopy maps `U` onto itself, so it restricts to `U`, and `ι` carries it to `M`.
  have hΦ₀U (t) (z : 𝕋 n) : z ∈ U ↔ Φ₀ (t, z) ∈ U := by
    rw [← Diffeotopy.timeSlice_apply]
    exact ((Φ₀.timeSlice t).injective.apply_mem_iff_of_eq_self (hΦ₀K t) hU z).symm
  let Ψ := Φ₀.subtype U hΦ₀U
  obtain ⟨Φ, hΦι, hΦK⟩ := Ψ.exists_extend_of_isCompact (χ := fun z : U ↦ (ι z : M))
    (isLocalDiffeomorph_subtypeVal_comp_iff.2 ι.isLocalDiffeomorph)
    (V.isOpen.isOpenEmbedding_subtypeVal.comp ι.toHomeomorph.isOpenEmbedding)
    (isCompact_setOf_cotangentNorm_coe_le hU) fun t z hz ↦ Subtype.ext <| by
      rw [Diffeotopy.subtype_apply_coe, ← Diffeotopy.timeSlice_apply]; exact hΦ₀K t z hz
  refine ⟨Φ, _, isCompact_image_setOf_cotangentNorm_le ι hU, fun t ↦ ?_, hΦK, fun x ↦ ?_⟩
  · -- The slices of `Φ` are transplanted along `ι` from those of `Φ₀`, which preserve `ω_can`.
    refine mem_diffeomorphStabilizer_of_semiconj_cotangent ι hι hU
      (hΦ₀.isHamiltonian.timeSlice_mem_diffeomorphStabilizer t) (f' := Ψ.timeSlice t)
      (fun z ↦ by rw [Diffeotopy.timeSlice_subtype, Diffeomorph.subtype_apply_coe]) (fun z ↦ ?_)
      fun x hx ↦ by rw [Diffeotopy.timeSlice_apply, hΦK t x hx]
    rw [Diffeotopy.timeSlice_apply, Diffeotopy.timeSlice_apply, hΦι]
  · by_cases hx : x ∈ range fun z : U ↦ (ι z : M)
    · obtain ⟨z, rfl⟩ := hx
      rw [dehnTwist_apply_val, dehnTwist_apply_val, Diffeotopy.final_apply, hΦι,
        ← Diffeotopy.final_apply, Diffeotopy.final_subtype]
      congr 2
      apply Subtype.ext
      rw [Diffeomorph.subtype_apply_coe]
      dsimp only
      rw [modelTwist_congr hR₁ h₁, hΦ₀τ, modelTwist_congr h₂ hR₂]
    · have hK : x ∉ (fun z : U ↦ (ι z : M)) '' {z | cotangentNorm (z : 𝕋 n) ≤ max r₁ r₂} :=
        fun h ↦ hx (image_subset_range _ _ h)
      rw [dehnTwist_apply_of_notMem ι hR₁ hU₁ fun h ↦ hx (image_subset_range _ _ h),
        dehnTwist_apply_of_notMem ι hR₂ hU₂ fun h ↦ hx (image_subset_range _ _ h),
        Diffeotopy.final_apply, hΦK 1 x hK]

/-- **Moving the neighbourhood along a symplectic isotopy moves the twist.** Let `W` be an open set
of `T*Sⁿ` containing `{z | μ z ≤ r₀}` and contained in the domains `U₀` and `U₁` of
`ι₀ : U₀ ≃ V₀` and `ι₁ : U₁ ≃ V₁`. Let `G` be a smooth isotopy from the restriction of `ι₀` to
`W` to that of `ι₁`, whose slices are local diffeomorphisms pulling `σ` back to `-ω_can`. Then the
twists of `ι₀` and `ι₁` for a profile `R` of radius `r₀` differ by the final map of a diffeotopy
of `M` that preserves `σ` at all times and fixes every point outside a compact set at all
times. -/
theorem exists_diffeotopy_dehnTwist_eq_of_smoothIsotopy [IsManifold I ∞ M]
    [BoundarylessManifold I M]
    {σ : SmoothTwoForm I M} {W U₀ U₁ : Opens (𝕋 n)} {V₀ V₁ : Opens M}
    (ι₀ : U₀ ≃ₘ⟮𝓣 n, I⟯ V₀) (ι₁ : U₁ ≃ₘ⟮𝓣 n, I⟯ V₁) (hW₀ : W ≤ U₀) (hW₁ : W ≤ U₁)
    {g₀ g₁ : C^∞⟮𝓣 n, W; I, M⟯} (hg₀ : ∀ z : W, g₀ z = ι₀ ⟨z, hW₀ z.property⟩)
    (hg₁ : ∀ z : W, g₁ z = ι₁ ⟨z, hW₁ z.property⟩) (G : SmoothIsotopy g₀ g₁)
    (hGd : ∀ t, IsLocalDiffeomorph (𝓣 n) I ∞ fun z : W ↦ G (t, z))
    (hGσ : G.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) σ)
    (hR : IsTwistProfile R r₀) (hrW : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (W : Set (𝕋 n))) :
    ∃ (Φ : Diffeotopy I ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (dehnTwist ι₀ hR (hrW.trans hW₀) x) = dehnTwist ι₁ hR (hrW.trans hW₁) x := by
  -- Move the model twist, restricted to `W`, along `G`.
  obtain ⟨Λ₀, Φ, hΦG, hΦK, hΛ₀g, hΛ₀K, -, hΦσ, hΦΛ₀K⟩ :=
    G.exists_diffeotopy_comp_eq_extend_of_isSymplectic hGd hGσ (modelTwistOn hR hrW)
      (SmoothForm.mem_diffeomorphStabilizer_mpullback_of_semiconj contMDiff_subtypeVal
        (modelTwistOn_apply_coe hR hrW) (by
          rw [SmoothForm.diffeomorphStabilizer_neg, SmoothForm.mem_diffeomorphStabilizer]
          exact mpullback_modelTwist_symplecticForm hR))
      (isCompact_setOf_cotangentNorm_coe_le hrW) fun _ ↦ modelTwistOn_apply_of_notMem hR hrW
  -- At either end of `G`, a map that commutes with the model twist through that end
  -- agrees with the twist of the corresponding `ι` on `{z | μ z ≤ r₀}`.
  have hend {U' : Opens (𝕋 n)} {V' : Opens M} (ι : U' ≃ₘ⟮𝓣 n, I⟯ V') (h' : W ≤ U') (g : W → M)
      (hg : ∀ z : W, g z = ι ⟨z, h' z.property⟩) (Λ : M → M) (z : U')
      (hz : cotangentNorm (z : 𝕋 n) ≤ r₀)
      (hΛ : Λ (g ⟨z, hrW hz⟩) = g (modelTwistOn hR hrW ⟨z, hrW hz⟩)) :
      Λ (ι z) = ι ⟨modelTwist hR z, (modelTwist_mem_iff hR (hrW.trans h') z).2 z.property⟩ := by
    rw [hg, hg] at hΛ
    rw [hΛ]
    exact congrArg (fun w ↦ (ι w : M)) (Subtype.ext (modelTwistOn_apply_coe hR hrW _))
  -- `Λ₀` is the twist of `ι₀`, and `Φ₁ ∘ Λ₀` that of `ι₁`.
  have h₀ : Λ₀ = dehnTwist ι₀ hR (hrW.trans hW₀) := by
    refine eq_dehnTwist ι₀ hR _ (fun z hz ↦ hend ι₀ hW₀ g₀ hg₀ Λ₀ z hz (hΛ₀g _))
      fun x hx ↦ hΛ₀K x ?_
    rintro ⟨w, hw, rfl⟩
    exact hx ⟨⟨w, hW₀ w.property⟩, hw, (hg₀ w).symm⟩
  have h₁ : Φ.final * Λ₀ = dehnTwist ι₁ hR (hrW.trans hW₁) := by
    refine eq_dehnTwist ι₁ hR _ (fun z hz ↦ ?_) fun x hx ↦ ?_
    · rw [Diffeomorph.mul_apply, Diffeotopy.final_apply, ← Diffeotopy.timeSlice_apply]
      have h := hΦG 1 ⟨z, hrW hz⟩
      rw [G.apply_one, G.apply_one] at h
      exact hend ι₁ hW₁ g₁ hg₁ (fun x ↦ Φ.timeSlice 1 (Λ₀ x)) z hz h
    · rw [Diffeomorph.mul_apply, Diffeotopy.final_apply, ← Diffeotopy.timeSlice_apply]
      refine hΦΛ₀K 1 x ?_
      rintro ⟨w, hw, rfl⟩
      exact hx ⟨⟨w, hW₁ w.property⟩, hw, by simp [G.apply_one, hg₁]⟩
  refine ⟨Φ, _, (isCompact_univ.prod (isCompact_setOf_cotangentNorm_coe_le hrW)).image
    G.contMDiff.continuous, hΦσ, hΦK, fun x ↦ ?_⟩
  rw [← h₀, ← h₁, Diffeomorph.mul_apply]

/-- **Two neighbourhoods of the same sphere give isotopic twists.** Let `ι₁ : U₁ ≃ V₁` and
`ι₂ : U₂ ≃ V₂` be diffeomorphisms from open sets of `T*Sⁿ` onto open sets of a manifold `M`
without boundary modelled on a finite-dimensional space, both pulling `σ` back to `-ω_can` and
both sending the zero covector at each `q ∈ Sⁿ` to `f q`. For twist profiles `R₁` and `R₂`
with `{z | μ z ≤ rᵢ} ⊆ Uᵢ`, the twists of `ι₁` and `ι₂` differ by the final map of a diffeotopy
of `M` that preserves `σ` at all times and fixes every point outside a compact set at all
times. -/
theorem exists_diffeotopy_dehnTwist_eq_of_apply_zeroSection [IsManifold I ∞ M] [I.Boundaryless]
    [FiniteDimensional ℝ F] {σ : SmoothTwoForm I M} {f : (𝕊 n) → M} {U₁ U₂ : Opens (𝕋 n)}
    {V₁ V₂ : Opens M} (ι₁ : U₁ ≃ₘ⟮𝓣 n, I⟯ V₁) (ι₂ : U₂ ≃ₘ⟮𝓣 n, I⟯ V₂)
    (hι₁ : CotangentBundle.IsWeinsteinChart σ f ι₁) (hι₂ : CotangentBundle.IsWeinsteinChart σ f ι₂)
    {R₁ R₂ : ℝ → ℝ} {r₁ r₂ : ℝ} (hR₁ : IsTwistProfile R₁ r₁)
    (hU₁ : {z : 𝕋 n | cotangentNorm z ≤ r₁} ⊆ (U₁ : Set (𝕋 n))) (hR₂ : IsTwistProfile R₂ r₂)
    (hU₂ : {z : 𝕋 n | cotangentNorm z ≤ r₂} ⊆ (U₂ : Set (𝕋 n))) :
    ∃ (Φ : Diffeotopy I ∞ M) (K : Set M), IsCompact K ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t x, x ∉ K → Φ (t, x) = x) ∧
      ∀ x, Φ.final (dehnTwist ι₁ hR₁ hU₁ x) = dehnTwist ι₂ hR₂ hU₂ x := by
  rw [← SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff]
  -- `ι₁` and `ι₂` are joined near the zero section by a symplectic isotopy `G`, on an open set
  -- `U` containing `{z | μ z ≤ r}` for some `r > 0`; take a profile `R` of radius `r`.
  obtain ⟨U, hU, hzero, G, hGσ, -, -⟩ :=
    CotangentBundle.exists_smoothIsotopy_of_apply_zeroSection_eq_neg ι₁ ι₂
      hι₁.isSymplectomorphism hι₂.isSymplectomorphism
      hι₁.range_zeroSection_subset hι₂.range_zeroSection_subset
      fun q ↦ (hι₁.exists_apply_eq q).2.trans (hι₂.exists_apply_eq q).2.symm
  obtain ⟨r, hr, hrU⟩ := exists_pos_setOf_cotangentNorm_le_subset (U.isOpen.mem_nhdsSet.2 hzero)
  obtain ⟨R, hR⟩ := exists_isTwistProfile hr
  -- Change both profiles to `R`, and join the twists of `R` for `ι₁` and `ι₂` along `G`.
  have hA := exists_diffeotopy_dehnTwist_eq_of_isTwistProfile ι₁ hι₁.isSymplectomorphism hR₁
    hU₁ hR (hrU.trans (hU.trans inf_le_left))
  have hC := exists_diffeotopy_dehnTwist_eq_of_isTwistProfile ι₂ hι₂.isSymplectomorphism hR
    (hrU.trans (hU.trans inf_le_right)) hR₂ hU₂
  rw [← SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff] at hA hC
  -- The slices of `G` are local diffeomorphisms: smooth embeddings between manifolds of the
  -- same dimension, as `ι₁` shows.
  have hGd (t : unitInterval) : IsLocalDiffeomorph (𝓣 n) I ∞ fun z : U ↦ G (t, z) := by
    rcases isEmpty_or_nonempty U with _ | ⟨⟨z, hz⟩⟩
    · exact fun z ↦ isEmptyElim z
    have hd := (ι₁.isLocalDiffeomorph ⟨z, (le_inf_iff.1 hU).1 hz⟩).finrank_eq (by simp)
    exact (G.isSmoothEmbedding t).isImmersion.isLocalDiffeomorph hd (by simp)
  have hB := SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff.2 <|
    exists_diffeotopy_dehnTwist_eq_of_smoothIsotopy ι₁ ι₂ (hU.trans inf_le_left)
      (hU.trans inf_le_right) (fun z ↦ by simp) (fun z ↦ by simp) G hGd hGσ hR hrU
  simpa only [mul_assoc, inv_mul_cancel_left] using mul_mem (mul_mem hC hB) hA

/-- The first step of `exists_smoothIsotopy_of_diffeotopy`: the isotopy `t ↦ f ∘ Φ_t` keeps the
pullback of `σ` at `0`, as the zero section is Lagrangian, so it extends to a symplectic isotopy
`F` of an open neighbourhood `U₀` of `f(Sⁿ)`, starting at the inclusion. -/
private theorem exists_isSymplectic_extension_precompSmoothIsotopy [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ F] [SigmaCompactSpace M] {σ : SmoothTwoForm I M}
    (hσ : σ.IsSymplectic) (f : SmoothEmbedding (𝓡 n) I ∞ (𝕊 n) M) (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : CotangentBundle.IsWeinsteinChart σ f ι)
    (Φ : Diffeotopy (𝓡 n) ∞ (𝕊 n)) :
    ∃ (U₀ : Opens M) (hU₀ : Set.range f ⊆ U₀) (e₀ e₁ : C^∞⟮I, U₀; I, M⟯) (_ : ∀ x, e₀ x = x)
      (F : SmoothIsotopy e₀ e₁),
      F.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) σ ∧
      ∀ t q, F (t, ⟨f q, hU₀ ⟨q, rfl⟩⟩) = f (Φ (t, q)) := by
  obtain ⟨U₀, hU₀, e₀, e₁, he₀, F, hFσ, hFe⟩ :=
    SmoothIsotopy.exists_isSymplectic_extension_of_mpullback_eq hσ f (Φ.precompSmoothIsotopy f)
      fun t ↦ by
        have h0 :=
          CotangentBundle.mpullback_eq_zero_of_apply_zeroSection ι.contMDiff
            (SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 hι.isSymplectomorphism)
            f.contMDiff hι.exists_apply_eq
        have ht : (fun q ↦ Φ.precompSmoothIsotopy f (t, q)) = f ∘ Φ.timeSlice t :=
          funext fun q ↦ by simp [Diffeotopy.timeSlice_apply]
        rw [ht, ← SmoothForm.coe_mpullback _ (f.contMDiff.comp (Φ.timeSlice t).contMDiff),
          ← SmoothForm.coe_mpullback _ f.contMDiff,
          ← SmoothForm.mpullback_mpullback (Φ.timeSlice t) f (Φ.timeSlice t).contMDiff f.contMDiff,
          h0, map_zero]
  exact ⟨U₀, hU₀, e₀, e₁, he₀, F, hFσ, fun t q ↦ (hFe t q).trans (Φ.precompSmoothIsotopy_apply _ _)⟩

omit [T2Space M] in
/-- The second step of `exists_smoothIsotopy_of_diffeotopy`: for an open set `U₀` of `M`, the
points of `U` that `ι` maps into `U₀` form an open set `W`, on which `ι` is a smooth injective
local diffeomorphism `χ : W → U₀` that pulls the restriction of `σ` back to that of `-ω_can`. -/
private theorem exists_restrict_of_mpullback_eq [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
    (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : SmoothForm.mpullback ι ι.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
    (U₀ : Opens M) :
    ∃ (W : Opens (𝕋 n)) (hW : W ≤ U) (χ : W → U₀) (hχs : ContMDiff (𝓣 n) I ∞ χ),
      IsLocalDiffeomorph (𝓣 n) I ∞ χ ∧ Function.Injective χ ∧
      (∀ z, (χ z : M) = ι (Opens.inclusion hW z)) ∧ (∀ z : U, (ι z : M) ∈ U₀ → (z : 𝕋 n) ∈ W) ∧
      SmoothForm.mpullback χ hχs (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) := by
  set W : Opens (𝕋 n) := ⟨Subtype.val '' ((fun z : U ↦ (ι z : M)) ⁻¹' U₀),
    U.isOpen.isOpenMap_subtypeVal _
      (U₀.isOpen.preimage (continuous_subtypeVal.comp ι.continuous))⟩
  have hW : W ≤ U := by
    rintro _ ⟨z, -, rfl⟩
    exact z.property
  have hχ (z : W) : (ι (Opens.inclusion hW z) : M) ∈ U₀ := by
    obtain ⟨w, hw, hwz⟩ := z.property
    rwa [show Opens.inclusion hW z = w from Subtype.ext hwz.symm]
  set χ : W → U₀ := fun z ↦ ⟨ι (Opens.inclusion hW z), hχ z⟩
  have hιW : ContMDiff (𝓣 n) I ∞ (Subtype.val ∘ ι ∘ Opens.inclusion hW) :=
    contMDiff_subtypeVal.comp (ι.contMDiff.comp (contMDiff_inclusion hW))
  have hχs : ContMDiff (𝓣 n) I ∞ χ := (ContMDiff.subtypeVal_comp_iff U₀ χ).1 hιW
  have hχd : IsLocalDiffeomorph (𝓣 n) I ∞ χ := by
    have h : IsLocalDiffeomorph (𝓣 n) I ∞ (Subtype.val ∘ ι ∘ Opens.inclusion hW) := fun z ↦
      (isLocalDiffeomorph_inclusion hW z).comp I M
        (isLocalDiffeomorph_subtypeVal_comp_iff.2 ι.isLocalDiffeomorph _)
    exact isLocalDiffeomorph_subtypeVal_comp_iff.1 h
  have hχinj : Function.Injective χ := fun a b h ↦ by
    have h' : ((χ a : U₀) : M) = χ b := congrArg Subtype.val h
    have h'' := Subtype.ext_iff.1 (ι.injective (Subtype.ext h'))
    exact Subtype.ext h''
  refine ⟨W, hW, χ, hχs, hχd, hχinj, fun _ ↦ rfl, fun z hz ↦ ⟨z, hz, rfl⟩, ?_⟩
  rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_congr (f := Subtype.val ∘ χ) _ hιW rfl,
    SmoothForm.mpullback_comp_comp_eq_of_mpullback_eq hι (contMDiff_inclusion hW)]
  exact SmoothForm.mpullback_congr _ _ rfl _

/-- **Carrying the neighbourhood of the sphere along an isotopy.** Let `M` be a Hausdorff,
σ-compact manifold without boundary, modelled on a finite-dimensional space, with a symplectic
form `σ`; let `f` be a smooth embedding of `Sⁿ` into `M` and `ι : U ≃ V` a diffeomorphism
from an open set of `T*Sⁿ` onto an open set of `M` that pulls `σ` back to `-ω_can` and sends the
zero covector at each `q` to `f q`. For a diffeotopy `Φ` of `Sⁿ` there are an open `W ≤ U`
containing the zero section, a diffeomorphism `ι'` from `W` onto an open set `V'` of `M`, and a
smooth isotopy `G` of `W` into `M` from `ι` (restricted to `W`) to `ι'`, such that:
* every slice of `G` is a local diffeomorphism, and pulls `σ` back to `-ω_can`;
* `G (t, 0_q) = f (Φ (t, q))` for all `t` and `q`;
* `ι'` pulls `σ` back to `-ω_can` and sends the zero covector at `q` to `f (Φ₁ q)`. -/
theorem exists_smoothIsotopy_of_diffeotopy [IsManifold I ∞ M] [I.Boundaryless]
    [FiniteDimensional ℝ F] [SigmaCompactSpace M] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (f : SmoothEmbedding (𝓡 n) I ∞ (𝕊 n) M) (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : CotangentBundle.IsWeinsteinChart σ f ι)
    (Φ : Diffeotopy (𝓡 n) ∞ (𝕊 n)) :
    ∃ (W : Opens (𝕋 n)) (hW : W ≤ U) (V' : Opens M) (ι' : W ≃ₘ⟮𝓣 n, I⟯ V')
      (G : SmoothIsotopy
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V).toContMDiffMap.comp
          (ι.toContMDiffMap.comp (SmoothEmbedding.inclusion hW).toContMDiffMap))
        ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V').toContMDiffMap.comp ι'.toContMDiffMap)),
      (∀ t, IsLocalDiffeomorph (𝓣 n) I ∞ fun z : W ↦ G (t, z)) ∧
      G.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) σ ∧
      (∀ t q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ W, G (t, ⟨_, h⟩) = f (Φ (t, q))) ∧
      CotangentBundle.IsWeinsteinChart σ (f ∘ Φ.final) ι' := by
  -- Extend the isotopy `t ↦ f ∘ Φ_t` to a symplectic isotopy `F` of a neighbourhood `U₀` of
  -- `f(Sⁿ)`.
  obtain ⟨U₀, hU₀, e₀, e₁, he₀, F, hFσ, hFe⟩ :=
    exists_isSymplectic_extension_precompSmoothIsotopy hσ f ι hι Φ
  -- `W`: the points of `U` that `ι` maps into `U₀`, and `χ : W → U₀` the map `ι`.
  obtain ⟨W, hW, χ, hχs, hχd, hχinj, hχ, hWmem, hτ⟩ := exists_restrict_of_mpullback_eq ι
    (SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 hι.isSymplectomorphism) U₀
  -- The slices `F_t ∘ χ` are injective local diffeomorphisms: `F_t` is an immersion between
  -- manifolds of the same dimension.
  have hmd (t : unitInterval) : IsLocalDiffeomorph (𝓣 n) I ∞ fun z ↦ F (t, χ z) :=
    fun z ↦ (hχd z).comp I M
      ((F.isSmoothEmbedding t).isImmersion.isLocalDiffeomorph rfl (by simp) _)
  have hminj (t : unitInterval) : Function.Injective fun z ↦ F (t, χ z) :=
    (F.isSmoothEmbedding t).isEmbedding.injective.comp hχinj
  -- `ι'` is the slice at time `1`, onto its open image, and `G` the isotopy `t ↦ F_t ∘ χ`.
  obtain ⟨ι', hι'⟩ : ∃ ι' : W ≃ₘ⟮𝓣 n, I⟯ (hmd 1).image, ∀ z, (ι' z : M) = F (1, χ z) :=
    ⟨(hmd 1).diffeomorphOfInjective (hminj 1),
      fun z ↦ IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply ..⟩
  obtain ⟨G, hG⟩ : ∃ G : SmoothIsotopy
      ((SmoothEmbedding.ofOpens (I := I) (n := ∞) V).toContMDiffMap.comp
        (ι.toContMDiffMap.comp (SmoothEmbedding.inclusion hW).toContMDiffMap))
      ((SmoothEmbedding.ofOpens (I := I) (n := ∞) (hmd 1).image).toContMDiffMap.comp
        ι'.toContMDiffMap), ∀ p, G p = F (p.1, χ p.2) :=
    ⟨F.precompSmoothEmbedding χ (hχd.isSmoothEmbedding (by simp) hχinj) (by simp) _ _
      (fun z ↦ by simp [he₀, hχ])
      (fun z ↦ by simp [hι']), fun p ↦ SmoothIsotopy.precompSmoothEmbedding_apply ..⟩
  -- `G` is symplectic, since `χ` pulls the restriction of `σ` back to that of `-ω_can`.
  have hGσ : G.IsSymplectic (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
      (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n))) σ := by
    rw [← hτ]
    exact hFσ.of_apply_eq_apply_comp hχs fun t y ↦ hG (t, y)
  have hGd (t : unitInterval) : IsLocalDiffeomorph (𝓣 n) I ∞ fun z : W ↦ G (t, z) := by
    simpa only [hG] using hmd t
  -- The zero section lies in `W`, and `χ` maps it to `f(Sⁿ)`.
  have hzW (q : 𝕊 n) : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ W :=
    hWmem ⟨_, (hι.exists_apply_eq q).1⟩
      (by simpa [(hι.exists_apply_eq q).2] using hU₀ ⟨q, rfl⟩)
  have hχz (q : 𝕊 n) : χ ⟨_, hzW q⟩ = ⟨f q, hU₀ ⟨q, rfl⟩⟩ :=
    Subtype.ext ((hχ _).trans (hι.exists_apply_eq q).2)
  have hGz (t : unitInterval) (q : 𝕊 n) : G (t, ⟨_, hzW q⟩) = f (Φ (t, q)) := by
    rw [hG, hχz, hFe]
  have h1 : (Subtype.val ∘ ι' : W → M) = fun z ↦ G (1, z) :=
    funext fun z ↦ by simp [hG, hι']
  refine ⟨W, hW, _, ι', G, hGd, hGσ, fun t q ↦ ⟨hzW q, hGz t q⟩,
    ⟨⟨fun q ↦ ⟨hzW q, ?_⟩⟩, SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2 ?_⟩⟩
  · rw [Function.comp_apply, Diffeotopy.final_apply, ← hGz]
    exact congrFun h1 _
  · rw [SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr _ (G.timeSlice 1).contMDiff
        (h1.trans (funext fun z ↦ (G.timeSlice_apply 1 z).symm))]
    exact Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans (hGσ.mpullback_timeSlice 1))

/-- **Moving the sphere by a diffeotopy moves the twist.** Let `M` be a Hausdorff, σ-compact
manifold without boundary, modelled on a finite-dimensional space, with a symplectic form `σ`;
let `f` be a smooth embedding of `Sⁿ` into `M`, and `ι : U ≃ V` a diffeomorphism from an open
set of `T*Sⁿ` onto an open set of `M` that pulls `σ` back to `-ω_can` and sends the zero
covector at each `q` to `f q`. Let `R` be a twist profile of radius `r₀` with
`{z | μ z ≤ r₀} ⊆ U`, and `Φ` a diffeotopy of `Sⁿ`. Then there are an open `W ≤ U` and a
diffeomorphism `ι'` from `W` onto an open set of `M` that pulls `σ` back to `-ω_can` and sends
the zero covector at `q` to `f (Φ₁ q)`, such that for every twist profile `R'` of radius `r'`
with `{z | μ z ≤ r'} ⊆ W`, the twist of `ι` for `R` and that of `ι'` for `R'` differ by the
final map of a diffeotopy of `M` that preserves `σ` at all times and fixes every point outside a
compact set at all times. -/
theorem exists_diffeotopy_dehnTwist_eq_of_diffeotopy [IsManifold I ∞ M] [I.Boundaryless]
    [FiniteDimensional ℝ F] [SigmaCompactSpace M] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (f : SmoothEmbedding (𝓡 n) I ∞ (𝕊 n) M) (ι : U ≃ₘ⟮𝓣 n, I⟯ V)
    (hι : SmoothForm.mpullback ι ι.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)))
    (hιf : ∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ U, (ι ⟨_, h⟩ : M) = f q)
    (hR : IsTwistProfile R r₀) (hU : {z : 𝕋 n | cotangentNorm z ≤ r₀} ⊆ (U : Set (𝕋 n)))
    (Φ : Diffeotopy (𝓡 n) ∞ (𝕊 n)) :
    ∃ (W : Opens (𝕋 n)) (_ : W ≤ U) (V' : Opens M) (ι' : W ≃ₘ⟮𝓣 n, I⟯ V'),
      SmoothForm.mpullback ι' ι'.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (-CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) ∧
      (∀ q, ∃ h : zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q ∈ W, (ι' ⟨_, h⟩ : M) = f (Φ.final q)) ∧
      ∀ {R' : ℝ → ℝ} {r' : ℝ} (hR' : IsTwistProfile R' r')
        (hU' : {z : 𝕋 n | cotangentNorm z ≤ r'} ⊆ (W : Set (𝕋 n))),
        ∃ (Ψ : Diffeotopy I ∞ M) (K : Set M), IsCompact K ∧
          (∀ t, Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
          (∀ t x, x ∉ K → Ψ (t, x) = x) ∧
          ∀ x, Ψ.final (dehnTwist ι hR hU x) = dehnTwist ι' hR' hU' x := by
  obtain ⟨W, hW, V', ι', G, hGd, hGσ, -, hι', hι'f⟩ :=
    exists_smoothIsotopy_of_diffeotopy hσ f ι hι hιf Φ
  refine ⟨W, hW, V', ι', hι', hι'f, fun {R' r'} hR' hU' ↦ ?_⟩
  rw [← SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff]
  -- Change the profile of `ι` to `R'`, then move the twist of `R'` along `G` to `ι'`.
  have hA := SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff.2 <|
    exists_diffeotopy_dehnTwist_eq_of_isTwistProfile ι hι hR hU hR' (hU'.trans hW)
  have hB := SmoothForm.mul_inv_mem_compactlySupportedIsotopyStabilizer_iff.2 <|
    exists_diffeotopy_dehnTwist_eq_of_smoothIsotopy ι ι' hW le_rfl (fun z ↦ by simp)
      (fun z ↦ by simp) G hGd hGσ hR' hU'
  simpa only [mul_assoc, inv_mul_cancel_left] using mul_mem hB hA

end Twist

end SymplecticGeometry

end
