/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.CleanIntersection
public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Reduction
public import TauCeti.Geometry.Manifold.RegularValue.Rank
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# The reduced Lagrangian, pointwise

Let `f : N → M` be a coisotropic immersion whose characteristic foliation is regular, so that its
leaf space is the reduced space (`Coisotropic/Reduction.lean`), and let `g : P → M` be a Lagrangian
map that meets `f` cleanly along `c : C → N` (`SymplecticGeometry.IsCleanIntersection`). This file
studies the map `leafSpaceMk ∘ c` from the clean intersection to the reduced space, point by point.
Writing `p` for a point of the intersection, `T_pQ` for the range of the derivative of `f` and
`T_pL` for that of `g`:

* the kernel of the derivative of `leafSpaceMk ∘ c` is the part of the tangent space of `C` that
  is tangent to the characteristic foliation, and `f ∘ c` carries it onto `T_pL ∩ (T_pQ)^σ`;
* hence, by the dimension count `TauCeti.SymplecticForm.IsLagrangian.finrank_inf_add_finrank`, the
  rank `r` of `leafSpaceMk ∘ c` satisfies `2 r + dim M = 2 dim N`; for a Lagrangian immersion `g`
  it is `dim P - codim Q` at every point;
* for a nondegenerate two-form `τ` on the leaf space that pulls back to `f^* σ`, the ranges of the
  derivatives of `leafSpaceMk ∘ c` are Lagrangian subspaces, since `σ` vanishes on `T_pL`;
* when `T_pQ + T_pL` is the whole tangent space of `M` at every point of the intersection,
  `T_pL ∩ (T_pQ)^σ ⊆ (T_pL + T_pQ)^σ = 0`, so `leafSpaceMk ∘ c` is a Lagrangian immersion.

These are the pointwise facts behind the reduction of a Lagrangian submanifold by a coisotropic
one, following McDuff–Salamon, Proposition 5.4.7.

## Main results

In the namespace `SymplecticGeometry.IsCleanIntersection`:

* `ker_mfderiv_leafSpaceMk_comp` and `map_ker_mfderiv_leafSpaceMk_comp`: the kernel of the
  derivative of `leafSpaceMk ∘ c`, and its image in `M`.
* `two_mul_mfderivRank_leafSpaceMk_comp_add` and `mfderivRank_leafSpaceMk_comp_eq`: its rank.
* `isLagrangianMap_leafSpaceMk_comp`: `leafSpaceMk ∘ c` is a Lagrangian map.
* `isLagrangianImmersion_leafSpaceMk_comp_of_transverse`: under transversality it is a Lagrangian
  immersion.

The reduced form `τ` is a hypothesis, as in `design/coisotropic-reduction.md`: by
`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.existsUnique_isSymplectic_mpullback_eq` a
symplectic one exists and is unique, and the statements here only use that it is nondegenerate.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Proposition 5.4.7
-/

public section

open Function Manifold Module TauCeti TauCeti.Manifold TauCeti.SmoothTwoForm.IsNondegenerate
open scoped Manifold ContDiff

namespace SymplecticGeometry.IsCleanIntersection

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [IsManifold J (∞ + 1) N]
  {G H'' P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {E₀ H₀ C : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {L : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace C] [ChartedSpace H₀ C]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}
  {h : hσ.IsCoisotropicMap J f} {hi : IsImmersion J I ∞ f} {hf : ContMDiff J I ∞ f}
  {hσc : σ.IsClosed} {hn : (1 : ℕ∞ω) ≤ ∞} {g : P → M} {c : C → N}

/-- The kernel of the derivative at `x` of the map `leafSpaceMk ∘ c` from the clean intersection
to the reduced space is the preimage, under the derivative of `c`, of the tangent space of the
characteristic foliation at `c x`. -/
theorem ker_mfderiv_leafSpaceMk_comp (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (x : C) :
    letI := Foliation.leafSpaceChartedSpace hR
    LinearMap.ker (mfderiv L
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap =
      ((h.characteristicFoliation hi hf hσc hn).distribution (c x)).comap
        (mfderiv L J c x).toLinearMap := by
  let := Foliation.leafSpaceChartedSpace hR
  rw [mfderiv_comp x ((Foliation.contMDiff_leafSpaceMk hR).mdifferentiableAt (by simp))
    (hc.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp)),
    ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp, Foliation.ker_mfderiv_leafSpaceMk hR]

/-- The derivative of `f ∘ c` at `x` carries the kernel of the derivative of `leafSpaceMk ∘ c` onto
`T L ∩ (T Q)^σ`: the intersection of the range of the derivative of `g` at a point `y` over
`f (c x)` with the symplectic complement of the range of the derivative of `f` at `c x`. -/
theorem map_ker_mfderiv_leafSpaceMk_comp (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) {x : C} {y : P}
    (hxy : g y = f (c x)) :
    letI := Foliation.leafSpaceChartedSpace hR
    (LinearMap.ker (mfderiv L
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap).map
        (mfderiv L I (f ∘ c) x).toLinearMap =
      LinearMap.range (mfderiv K I g y).toLinearMap ⊓
        (hσ.symplecticFormAt (f (c x))).orthogonal
          (LinearMap.range (mfderiv J I f (c x)).toLinearMap) := by
  let := Foliation.leafSpaceChartedSpace hR
  have hcd : mfderiv L I (f ∘ c) x = (mfderiv J I f (c x)).comp (mfderiv L J c x) :=
    mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (hc.isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
  have hrange := hc.range_mfderiv_comp x y hxy
  rw [hcd, ContinuousLinearMap.toLinearMap_comp] at hrange ⊢
  rw [hc.ker_mfderiv_leafSpaceMk_comp hR, Submodule.map_comp, Submodule.map_comap_eq,
    Submodule.map_inf _ (hi.mfderiv_injective (by simp) (c x)),
    h.map_characteristicFoliation_distribution, ← LinearMap.range_comp, hrange]
  have hco := SymplecticForm.isCoisotropic_iff_le.1 (isCoisotropicMap_iff.1 h (c x))
  ext v
  simp only [Submodule.mem_inf]
  exact ⟨fun ⟨⟨_, hv⟩, hv'⟩ ↦ ⟨hv, hv'⟩, fun ⟨hv, hv'⟩ ↦ ⟨⟨hco hv', hv⟩, hv'⟩⟩

/-- **The rank of the reduced Lagrangian, as a dimension count.** If `g` is a Lagrangian map, the
rank `r` of `leafSpaceMk ∘ c` at any point satisfies `2 r + dim M = 2 dim Q`. -/
theorem two_mul_mfderivRank_leafSpaceMk_comp_add (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (x : C) :
    letI := Foliation.leafSpaceChartedSpace hR
    2 * mfderivRank L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x + finrank ℝ E =
      2 * finrank ℝ F := by
  let := Foliation.leafSpaceChartedSpace hR
  obtain ⟨y, hxy⟩ := hc.range_subset ⟨x, rfl⟩
  have hcx := hc.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x
  have : FiniteDimensional ℝ E₀ := FiniteDimensional.of_injective _ hcx
  have hfc := ((hi.isDiffImmersionAt (by simp) (c x)).comp
    (hc.isSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) x)).mfderiv_injective
  -- The ranges of the derivatives of `f` at `c x` and of `g` at `y`, as subspaces of the tangent
  -- space of `M` at `f (c x)`.
  obtain ⟨W, Λ, hW, hΛ, hrange, hker⟩ : ∃ W Λ : Submodule ℝ (TangentSpace I (f (c x))),
      finrank ℝ W = finrank ℝ F ∧ (hσ.symplecticFormAt (f (c x))).IsLagrangian Λ ∧
      LinearMap.range (mfderiv L I (f ∘ c) x).toLinearMap = Λ ⊓ W ∧
      (LinearMap.ker (mfderiv L
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap).map
        (mfderiv L I (f ∘ c) x).toLinearMap =
      Λ ⊓ (hσ.symplecticFormAt (f (c x))).orthogonal W := by
    refine ⟨_, _, LinearMap.finrank_range_of_inj (hi.mfderiv_injective (by simp) (c x)), ?_,
      (hc.range_mfderiv_comp x y hxy).trans (inf_comm _ _),
      hc.map_ker_mfderiv_leafSpaceMk_comp hR hxy⟩
    rw [← hxy]
    exact isLagrangianMap_iff_forall.1 hg y
  rw [mfderivRank_def]
  set D := (mfderiv L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
    ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap
  have h₁ : finrank ℝ (LinearMap.range D) + finrank ℝ (LinearMap.ker D) = finrank ℝ E₀ :=
    LinearMap.finrank_range_add_finrank_ker D
  have h₂ : finrank ℝ (LinearMap.ker D) =
      finrank ℝ ↥(Λ ⊓ (hσ.symplecticFormAt (f (c x))).orthogonal W) := by
    rw [← hker]
    exact (Submodule.equivMapOfInjective _ hfc _).finrank_eq
  have h₃ : finrank ℝ ↥(Λ ⊓ W) = finrank ℝ E₀ := by
    rw [← hrange]
    exact LinearMap.finrank_range_of_inj hfc
  have h₄ := hΛ.finrank_inf_add_finrank W
  rw [finrank_tangentSpace] at h₄
  omega

/-- **The rank of the reduced Lagrangian.** If `g` is a Lagrangian map and an immersion, the map
`leafSpaceMk ∘ c` has rank `dim P - codim Q` at every point. -/
theorem mfderivRank_leafSpaceMk_comp_eq (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (hgi : IsImmersion K I ∞ g) (x : C) :
    letI := Foliation.leafSpaceChartedSpace hR
    mfderivRank L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x =
      finrank ℝ G - (finrank ℝ E - finrank ℝ F) := by
  obtain ⟨y, -⟩ := hc.range_subset ⟨x, rfl⟩
  have h₁ := hc.two_mul_mfderivRank_leafSpaceMk_comp_add hR hg x
  have h₂ := hg.two_mul_finrank (hgi.mfderiv_injective (by simp) y)
  have h₃ := LinearMap.finrank_le_finrank_of_injective (hi.mfderiv_injective (by simp) (c x))
  simp only [finrank_tangentSpace] at h₃
  omega

/-- **The reduced Lagrangian is Lagrangian.** Let `τ` be a nondegenerate two-form on the leaf space
of `Q` whose pullback to `N` is `f^* σ`. If `g` is a Lagrangian map, the range of the derivative of
`leafSpaceMk ∘ c` at every point is a Lagrangian subspace for `τ`. -/
theorem isLagrangianMap_leafSpaceMk_comp (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      hτ.IsLagrangianMap L ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  intro τ hτ hτσ
  rw [isLagrangianMap_iff_forall]
  intro x
  obtain ⟨y, hxy⟩ := hc.range_subset ⟨x, rfl⟩
  have hcx := hc.isSmoothEmbedding.contMDiff.mdifferentiableAt (n := ∞) (x := x) (by simp)
  -- The range of the derivative of `g` at `y`, as a subspace of the tangent space at `f (c x)`.
  obtain ⟨Λ, hΛ, hrange⟩ : ∃ Λ : Submodule ℝ (TangentSpace I (f (c x))),
      (hσ.symplecticFormAt (f (c x))).IsLagrangian Λ ∧
      LinearMap.range (mfderiv L I (f ∘ c) x).toLinearMap ≤ Λ := by
    refine ⟨_, ?_, (hc.range_mfderiv_comp x y hxy).trans_le inf_le_right⟩
    rw [← hxy]
    exact isLagrangianMap_iff_forall.1 hg y
  have hiso : (hτ.symplecticFormAt _).IsIsotropic (LinearMap.range (mfderiv L
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
      ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap) := by
    rw [SymplecticForm.isIsotropic_iff]
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    have := SymplecticForm.isIsotropic_iff.1 hΛ.isIsotropic _ (hrange ⟨v, rfl⟩) _
      (hrange ⟨w, rfl⟩)
    rw [symplecticFormAt_apply] at this ⊢
    rw [mfderiv_comp x ((Foliation.contMDiff_leafSpaceMk hR).mdifferentiableAt (by simp)) hcx]
    rw [mfderiv_comp x (hf.mdifferentiableAt (by simp)) hcx] at this
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, comp_apply] at this ⊢
    rw [← SmoothForm.eval₂_mpullback _ (Foliation.contMDiff_leafSpaceMk hR), hτσ,
      SmoothForm.eval₂_mpullback]
    exact this
  refine hiso.isLagrangian_of_finrank ?_
  have h₁ := hc.two_mul_mfderivRank_leafSpaceMk_comp_add hR hg x
  have h₂ := LinearMap.finrank_le_finrank_of_injective (hi.mfderiv_injective (by simp) (c x))
  rw [mfderivRank_def] at h₁
  rw [finrank_tangentSpace, finrank_euclideanSpace_fin]
  simp only [finrank_tangentSpace] at h₂
  omega

/-- **The transverse case.** Let `τ` be a nondegenerate two-form on the leaf space of `Q` whose
pullback to `N` is `f^* σ`, and let `g` be a Lagrangian map whose tangent spaces, at each point
over the clean intersection, span the tangent space of `M` together with those of `f`. Then, for a
nonempty boundaryless `C`, the map `leafSpaceMk ∘ c` is a Lagrangian immersion for `τ`. -/
theorem isLagrangianImmersion_leafSpaceMk_comp_of_transverse [L.Boundaryless] [Nonempty C]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (htr : ∀ (x : C) (y : P), g y = f (c x) →
      LinearMap.range (mfderiv J I f (c x)).toLinearMap ⊔
        LinearMap.range (mfderiv K I g y).toLinearMap = ⊤) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      hτ.IsLagrangianImmersion L ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  intro τ hτ hτσ
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  rw [isLagrangianImmersion_iff]
  refine ⟨((Foliation.contMDiff_leafSpaceMk hR).comp
    hc.isSmoothEmbedding.contMDiff).isImmersion_of_injective_mfderiv (by simp) fun x ↦ ?_,
    hc.isLagrangianMap_leafSpaceMk_comp hR hg hτ hτσ⟩
  obtain ⟨y, hxy⟩ := hc.range_subset ⟨x, rfl⟩
  have hfc := ((hi.isDiffImmersionAt (by simp) (c x)).comp
    (hc.isSmoothEmbedding.isImmersion.isDiffImmersionAt (by simp) x)).mfderiv_injective
  -- The range of the derivative of `g` at `y`, as a subspace of the tangent space at `f (c x)`.
  obtain ⟨Λ, hΛ, hsup, hker⟩ : ∃ Λ : Submodule ℝ (TangentSpace I (f (c x))),
      (hσ.symplecticFormAt (f (c x))).IsLagrangian Λ ∧
      LinearMap.range (mfderiv J I f (c x)).toLinearMap ⊔ Λ = ⊤ ∧
      (LinearMap.ker (mfderiv L
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) x).toLinearMap).map
        (mfderiv L I (f ∘ c) x).toLinearMap =
      Λ ⊓ (hσ.symplecticFormAt (f (c x))).orthogonal
        (LinearMap.range (mfderiv J I f (c x)).toLinearMap) := by
    refine ⟨_, ?_, htr x y hxy, hc.map_ker_mfderiv_leafSpaceMk_comp hR hxy⟩
    rw [← hxy]
    exact isLagrangianMap_iff_forall.1 hg y
  -- `T L ∩ (T Q)^σ` lies in `(T L)^σ ∩ (T Q)^σ = (T L + T Q)^σ = 0`.
  have hbot : Λ ⊓ (hσ.symplecticFormAt (f (c x))).orthogonal
      (LinearMap.range (mfderiv J I f (c x)).toLinearMap) = ⊥ := by
    refine eq_bot_iff.2 ((inf_le_inf_right _
      (SymplecticForm.isIsotropic_iff_le.1 hΛ.isIsotropic)).trans ?_)
    rw [← SymplecticForm.orthogonal_sup, sup_comm, hsup, SymplecticForm.orthogonal_top]
  rw [hbot, ← Submodule.map_bot (mfderiv L I (f ∘ c) x).toLinearMap] at hker
  exact LinearMap.ker_eq_bot.1 (Submodule.map_injective_of_injective hfc hker)

end SymplecticGeometry.IsCleanIntersection

end
