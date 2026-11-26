/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Gluing.Pair
public import SymplecticGeometry.Geometry.Symplectic.Sum.Collar
public import SymplecticGeometry.Geometry.Symplectic.Sum.ProductNeighborhood
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The symplectic fiber sum

Let `f₁` and `f₂` be product neighbourhoods of radius `ε` of two embeddings of one compact
manifold `Q` into Hausdorff manifolds `M₁` and `M₂` over one model, and let `0 ≤ δ < ε`. Each
`Mᵢ` loses the image of the closed tube `Q × B̄²(δ)`; what is left,
`ProductNeighborhood.complTube`, is open, and contains the open collar `fᵢ (Q × A(δ, ε))`, where
`A(δ, ε)` is the open annulus `δ < |z| < ε`. The collar is a copy of `Q × A(δ, ε)`
(`ProductNeighborhood.collarDiffeomorph`), and the two collars are glued by
`f₂ ∘ (id_Q × a) ∘ f₁⁻¹`, where `a` is the annulus map of `Sum/Collar.lean`, which exchanges the
two boundary circles of the annulus. The fiber sum `FiberSum f₁ f₂ hδ hδε` is the space
`GluedAlong` of `Geometry/Manifold/Gluing/Pair.lean` glued along this diffeomorphism, a smooth
manifold over the model of `M₁` and `M₂`.

It is Hausdorff (`FiberSum.instT2Space`), by `GluedAlong.t2Space_of_isClosed_graph`: the graph
of the gluing map is closed (`isClosed_graph_fiberSumGluing`). A point in the closure of the
graph comes, by compactness of `Q × B̄²(ε)`, from a cluster point `(q, z)` of the collar
coordinates with `δ ≤ |z| ≤ ε`. If `|z| = δ`, the first component would be `f₁ (q, z)`, which
lies in the removed tube; if `|z| = ε`, the annulus map sends `z` to radius `δ` and the second
component would lie in the removed tube of `M₂`. So `δ < |z| < ε`, and the point is on the graph.
Gluing along open collars rather than along the circles of a fixed radius is what makes the
glued space a manifold directly.

When `ι₁` and `ι₂` pull `σ₁` and `σ₂` back to one form `τ` on `Q`, each collar diffeomorphism
pulls the restriction of `σᵢ` back to the product form `τ ⊕ ω₀` of `Q × A(δ, ε)`
(`ProductNeighborhood.mpullback_collarDiffeomorph`), and `id_Q × a` preserves that form
(`mpullback_prodAnnulusDiffeomorph`). So the gluing map matches the two restrictions
(`mpullback_fiberSumGluing`), and they glue, by `GluedAlong.gluedForm`, to a form on the fiber
sum, which is symplectic when `σ₁` and `σ₂` are.

## Main definitions

* `SymplecticGeometry.ProductNeighborhood.complTube`: the open complement of the closed tube.
* `SymplecticGeometry.ProductNeighborhood.collarMap`: the collar `(q, z) ↦ f (q, z)` on
  `Q × A(δ, ε)`, as a map into the complement of the tube;
  `SymplecticGeometry.ProductNeighborhood.collar`, its image, and
  `SymplecticGeometry.ProductNeighborhood.collarDiffeomorph`, the diffeomorphism onto it.
* `SymplecticGeometry.fiberSumGluing`: the gluing diffeomorphism between the two collars.
* `SymplecticGeometry.FiberSum`: the fiber sum.
* `SymplecticGeometry.FiberSum.symplecticForm`: the form of the fiber sum glued from `σ₁` and
  `σ₂`.

## Main results

* `SymplecticGeometry.FiberSum.inl_collarMap`: `inl (f₁ (q, z)) = inr (f₂ (q, a z))`, and
  `SymplecticGeometry.FiberSum.inl_eq_inr_iff`: these are the only points that the gluing
  identifies.
* `SymplecticGeometry.isClosed_graph_fiberSumGluing` and the instance
  `SymplecticGeometry.FiberSum.instT2Space`: the fiber sum is Hausdorff.
* `SymplecticGeometry.FiberSum.mpullback_inl_symplecticForm`, `mpullback_inr_symplecticForm`,
  `eq_symplecticForm_iff` and `isSymplectic_symplecticForm`: the form of the fiber sum is the
  unique form that restricts to `σ₁` and `σ₂` on the two pieces, and it is symplectic.
* `SymplecticGeometry.exists_isSymplectic_fiberSum`: for symplectic `σᵢ`, compact `Q` and
  symplectic framings, product neighbourhoods exist for all small radii, and every fiber sum
  built from them is a Hausdorff, second countable manifold with such a symplectic form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2, pp. 318–319.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Filter Module Set Topology TopologicalSpace TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

universe u

variable {EQ HQ E H : Type*}
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ] [TopologicalSpace HQ]
  {J : ModelWithCorners ℝ EQ HQ} {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
  [IsManifold J ∞ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

/-! ### Points of the annulus as points of the disc -/

section AnnulusToProdBall

variable {ε δ : ℝ}

/-- A point of `Q × A(δ, ε)` as a point of the domain `Q × B²(ε)` of a product neighbourhood. -/
def annulusToProdBall (p : Q × annulus ℂ δ ε) : prodBall Q ε :=
  ⟨(p.1, p.2), mem_prodBall.2 (mem_annulus.1 p.2.property).2⟩

@[simp]
theorem coe_annulusToProdBall (p : Q × annulus ℂ δ ε) :
    (annulusToProdBall p : Q × ℂ) = (p.1, (p.2 : ℂ)) :=
  (rfl)

theorem annulusToProdBall_injective :
    Function.Injective (annulusToProdBall : Q × annulus ℂ δ ε → prodBall Q ε) := by
  intro p p' h
  have h' := congrArg Subtype.val h
  simp only [coe_annulusToProdBall, Prod.mk.injEq] at h'
  exact Prod.ext h'.1 (Subtype.ext h'.2)

omit [FiniteDimensional ℝ EQ] [IsManifold J ∞ Q] in
theorem isLocalDiffeomorph_annulusToProdBall :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℂ)) (J.prod 𝓘(ℝ, ℂ)) ∞
      (annulusToProdBall : Q × annulus ℂ δ ε → prodBall Q ε) :=
  isLocalDiffeomorph_subtypeVal_comp_iff.1
    (isLocalDiffeomorph_id.prodMap isLocalDiffeomorph_subtype_val)

end AnnulusToProdBall

/-! ### The complement of the tube and the collar of one product neighbourhood -/

namespace ProductNeighborhood

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {ι : SmoothEmbedding J I ∞ Q M}
  {hι : hσ.HasSymplecticTangentImages J ι} {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ : SymplecticFraming hι hP} {ε δ : ℝ} (f : ProductNeighborhood Φ ε)

/-- For compact `Q`, Hausdorff `M` and `δ < ε`, the complement in `M` of the image of the closed
tube `Q × B̄²(δ)` under the product neighbourhood `f`, as an open set. -/
def complTube [CompactSpace Q] [T2Space M] (hδε : δ < ε) : Opens M :=
  ⟨(f '' {p | ‖(p : Q × ℂ).2‖ ≤ δ})ᶜ, f.isOpen_compl_image_closedBall hδε⟩

@[simp]
theorem mem_complTube [CompactSpace Q] [T2Space M] {hδε : δ < ε} {x : M} :
    x ∈ f.complTube hδε ↔ x ∉ f '' {p | ‖(p : Q × ℂ).2‖ ≤ δ} :=
  Iff.rfl

variable [CompactSpace Q] [T2Space M]

theorem apply_annulusToProdBall_mem_complTube (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    f (annulusToProdBall p) ∈ f.complTube hδε := by
  rintro ⟨p', hp', heq⟩
  rw [f.isOpenEmbedding.injective heq] at hp'
  exact (mem_annulus.1 p.2.property).1.not_ge hp'

/-- The collar `(q, z) ↦ f (q, z)` of a product neighbourhood on `Q × A(δ, ε)`, as a map into the
complement of the closed tube `Q × B̄²(δ)`. -/
def collarMap (hδε : δ < ε) (p : Q × annulus ℂ δ ε) : f.complTube hδε :=
  ⟨f (annulusToProdBall p), f.apply_annulusToProdBall_mem_complTube hδε p⟩

@[simp]
theorem coe_collarMap (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    (f.collarMap hδε p : M) = f (annulusToProdBall p) :=
  (rfl)

theorem collarMap_injective (hδε : δ < ε) : Function.Injective (f.collarMap hδε) := fun _ _ h ↦
  annulusToProdBall_injective (f.isOpenEmbedding.injective (congrArg Subtype.val h))

theorem isLocalDiffeomorph_collarMap (hδε : δ < ε) :
    IsLocalDiffeomorph (J.prod 𝓘(ℝ, ℂ)) I ∞ (f.collarMap hδε) :=
  isLocalDiffeomorph_subtypeVal_comp_iff.1 fun p ↦
    (isLocalDiffeomorph_annulusToProdBall p).comp (hg := f.isLocalDiffeomorph _)

theorem continuous_collarMap (hδε : δ < ε) : Continuous (f.collarMap hδε) :=
  (f.isLocalDiffeomorph_collarMap hδε).contMDiff.continuous

/-- The open collar `f (Q × A(δ, ε))`, as an open subset of the complement of the closed tube
`Q × B̄²(δ)`. -/
def collar (hδε : δ < ε) : Opens (f.complTube hδε) :=
  (f.isLocalDiffeomorph_collarMap hδε).image

@[simp]
theorem mem_collar_iff {hδε : δ < ε} {x : f.complTube hδε} :
    x ∈ f.collar hδε ↔ x ∈ range (f.collarMap hδε) := by
  rw [collar, ← SetLike.mem_coe, ← Opens.carrier_eq_coe, IsLocalDiffeomorph.image_coe]

theorem collarMap_mem_collar (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    f.collarMap hδε p ∈ f.collar hδε :=
  f.mem_collar_iff.2 (mem_range_self p)

/-- The collar of a product neighbourhood is diffeomorphic to `Q × A(δ, ε)`. -/
def collarDiffeomorph (hδε : δ < ε) :
    (Q × annulus ℂ δ ε) ≃ₘ⟮J.prod 𝓘(ℝ, ℂ), I⟯ f.collar hδε :=
  (f.isLocalDiffeomorph_collarMap hδε).diffeomorphOfInjective (f.collarMap_injective hδε)

@[simp]
theorem coe_collarDiffeomorph_apply (hδε : δ < ε) (p : Q × annulus ℂ δ ε) :
    (f.collarDiffeomorph hδε p : f.complTube hδε) = f.collarMap hδε p :=
  IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply _ _ p

/-- The collar map pulls the restriction of `σ` back to the product form `ι^* σ ⊕ ω₀` of
`Q × A(δ, ε)`, where `ω₀` is the area form of `ℂ` restricted to the annulus. -/
theorem mpullback_collarMap (hδε : δ < ε) :
    SmoothForm.mpullback (f.collarMap hδε) (f.isLocalDiffeomorph_collarMap hδε).contMDiff
        (SmoothForm.mpullback (Subtype.val : f.complTube hδε → M) contMDiff_subtypeVal σ) =
      SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
        (SmoothForm.mpullback (Subtype.val : annulus ℂ δ ε → ℂ) contMDiff_subtypeVal
          stdComplexSymplecticForm.constSmooth) := by
  have hA := isLocalDiffeomorph_annulusToProdBall (Q := Q) (J := J) (δ := δ) (ε := ε)
  rw [SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr (f := Subtype.val ∘ f.collarMap hδε) _
      (f.contMDiff.comp hA.contMDiff) (funext fun p ↦ f.coe_collarMap hδε p),
    ← SmoothForm.mpullback_mpullback _ _ hA.contMDiff f.contMDiff, f.mpullback_eq,
    SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr (f := Subtype.val ∘ annulusToProdBall) _
      (contMDiff_id.prodMap contMDiff_subtypeVal) (funext coe_annulusToProdBall),
    SmoothTwoForm.mpullback_prodMap_prod contMDiff_id contMDiff_subtypeVal,
    SmoothForm.mpullback_id, LinearMap.id_apply]

/-- The diffeomorphism of `Q × A(δ, ε)` onto the collar pulls the restriction of `σ` back to the
product form `ι^* σ ⊕ ω₀`, where `ω₀` is the area form of `ℂ` restricted to the annulus. -/
theorem mpullback_collarDiffeomorph (hδε : δ < ε) :
    SmoothForm.mpullback (f.collarDiffeomorph hδε) (f.collarDiffeomorph hδε).contMDiff
        (SmoothForm.mpullback (Subtype.val : f.collar hδε → f.complTube hδε) contMDiff_subtypeVal
          (SmoothForm.mpullback (Subtype.val : f.complTube hδε → M) contMDiff_subtypeVal σ)) =
      SmoothTwoForm.prod (SmoothForm.mpullback ι ι.contMDiff σ)
        (SmoothForm.mpullback (Subtype.val : annulus ℂ δ ε → ℂ) contMDiff_subtypeVal
          stdComplexSymplecticForm.constSmooth) := by
  rw [SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr (f := Subtype.val ∘ f.collarDiffeomorph hδε) _
      (f.isLocalDiffeomorph_collarMap hδε).contMDiff
      (funext fun p ↦ f.coe_collarDiffeomorph_apply hδε p), f.mpullback_collarMap]

/-- A product neighbourhood cannot send a filter of collar points to a point outside the closed
tube while the collar coordinates cluster at a point `w` of the tube. -/
theorem not_mapClusterPt_of_tendsto (hδε : δ < ε) {α : Type*} {F : Filter α}
    {ρ : α → prodBall Q ε} {g : α → f.complTube hδε} (hg : ∀ a, (g a : M) = f (ρ a))
    {x : f.complTube hδε} (hx : Tendsto g F (𝓝 x)) {w : Q × ℂ} (hw : ‖w.2‖ ≤ δ) :
    ¬ MapClusterPt w F (fun a ↦ (ρ a : Q × ℂ)) := by
  intro hc
  set w' : prodBall Q ε := ⟨w, mem_prodBall.2 (hw.trans_lt hδε)⟩
  have h₁ : MapClusterPt w' F ρ :=
    IsInducing.subtypeVal.mapClusterPt_iff.1 (by rwa [MapClusterPt, Filter.map_map])
  have h₂ : MapClusterPt (f w') F (f ∘ ρ) := h₁.continuousAt_comp f.continuous.continuousAt
  have h₃ : Tendsto (f ∘ ρ) F (𝓝 (x : M)) := by
    rw [show f ∘ ρ = Subtype.val ∘ g from funext fun a ↦ (hg a).symm]
    exact (continuous_subtypeVal.tendsto _).comp hx
  exact (f.mem_complTube.1 x.property)
    ⟨w', hw, eq_of_nhds_neBot (h₂.neBot.mono (inf_le_inf_left _ h₃))⟩

end ProductNeighborhood

/-! ### The fiber sum -/

section FiberSum

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁] [IsManifold I ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₁ : SmoothTwoForm I M₁} {hσ₁ : σ₁.IsNondegenerate} {ι₁ : SmoothEmbedding J I ∞ Q M₁}
  {hι₁ : hσ₁.HasSymplecticTangentImages J ι₁} {hP₁ : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ₁ : SymplecticFraming hι₁ hP₁}
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate} {ι₂ : SmoothEmbedding J I ∞ Q M₂}
  {hι₂ : hσ₂.HasSymplecticTangentImages J ι₂} {hP₂ : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
  {Φ₂ : SymplecticFraming hι₂ hP₂}
  [CompactSpace Q] [T2Space M₁] [T2Space M₂] {ε δ : ℝ}
  (f₁ : ProductNeighborhood Φ₁ ε) (f₂ : ProductNeighborhood Φ₂ ε) (hδ : 0 ≤ δ) (hδε : δ < ε)

/-- The gluing diffeomorphism `f₂ ∘ (id_Q × a) ∘ f₁⁻¹` of the fiber sum, from the collar of `f₁`
to that of `f₂`, where `a` is the annulus map, which exchanges the two boundary circles of the
annulus `A(δ, ε)`. -/
def fiberSumGluing : f₁.collar hδε ≃ₘ⟮I, I⟯ f₂.collar hδε :=
  (f₁.collarDiffeomorph hδε).symm.trans
    ((prodAnnulusDiffeomorph (I := J) Q δ ε hδ).trans (f₂.collarDiffeomorph hδε))

theorem fiberSumGluing_def :
    fiberSumGluing f₁ f₂ hδ hδε = (f₁.collarDiffeomorph hδε).symm.trans
      ((prodAnnulusDiffeomorph (I := J) Q δ ε hδ).trans (f₂.collarDiffeomorph hδε)) :=
  (rfl)

@[simp]
theorem fiberSumGluing_collarDiffeomorph (p : Q × annulus ℂ δ ε) :
    fiberSumGluing f₁ f₂ hδ hδε (f₁.collarDiffeomorph hδε p) =
      f₂.collarDiffeomorph hδε (prodAnnulusDiffeomorph (I := J) Q δ ε hδ p) := by
  simp only [fiberSumGluing, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.symm_apply_apply]

/-- The **symplectic fiber sum** of `M₁` and `M₂` along the product neighbourhoods `f₁` and `f₂`
of radius `ε`, for `0 ≤ δ < ε`: the complements of the closed tubes `Q × B̄²(δ)`, glued along
their collars `Q × A(δ, ε)` by `fiberSumGluing`. -/
abbrev FiberSum : Type u :=
  GluedAlong (fiberSumGluing f₁ f₂ hδ hδε)

namespace FiberSum

/-- The point `f₁ (q, z)` of the collar of `M₁` is glued to the point `f₂ (q, a z)` of the collar
of `M₂`, where `a` is the annulus map. -/
theorem inl_collarMap (p : Q × annulus ℂ δ ε) :
    GluedAlong.inl (fiberSumGluing f₁ f₂ hδ hδε) (f₁.collarMap hδε p) =
      GluedAlong.inr (fiberSumGluing f₁ f₂ hδ hδε)
        (f₂.collarMap hδε (prodAnnulusDiffeomorph (I := J) Q δ ε hδ p)) := by
  rw [← f₁.coe_collarDiffeomorph_apply, ← f₂.coe_collarDiffeomorph_apply,
    ← fiberSumGluing_collarDiffeomorph f₁ f₂ hδ hδε, GluedAlong.inr_apply]

/-- A point `x` of the complement of the tube in `M₁` and a point `y` of that in `M₂` have the
same image in the fiber sum exactly when they are `f₁ (q, z)` and `f₂ (q, a z)` for a point
`(q, z)` of `Q × A(δ, ε)`, where `a` is the annulus map. -/
theorem inl_eq_inr_iff {x : f₁.complTube hδε} {y : f₂.complTube hδε} :
    GluedAlong.inl (fiberSumGluing f₁ f₂ hδ hδε) x =
        GluedAlong.inr (fiberSumGluing f₁ f₂ hδ hδε) y ↔
      ∃ p : Q × annulus ℂ δ ε,
        f₁.collarMap hδε p = x ∧
          f₂.collarMap hδε (prodAnnulusDiffeomorph (I := J) Q δ ε hδ p) = y := by
  refine ⟨fun h ↦ ?_, fun ⟨p, hx, hy⟩ ↦ ?_⟩
  swap
  · rw [← hx, ← hy]
    exact inl_collarMap f₁ f₂ hδ hδε p
  obtain ⟨hx, rfl⟩ := (GluedAlong.inl_eq_inr_iff _).1 h
  obtain ⟨p, hp⟩ : ∃ p, f₁.collarDiffeomorph hδε p = ⟨x, hx⟩ :=
    (f₁.collarDiffeomorph hδε).surjective _
  refine ⟨p, ?_, ?_⟩
  · rw [← f₁.coe_collarDiffeomorph_apply, hp]
  · rw [← f₂.coe_collarDiffeomorph_apply, ← fiberSumGluing_collarDiffeomorph f₁ f₂ hδ hδε, hp]

end FiberSum

/-- The pairs of glued points: the image of `Q × A(δ, ε)` under `(q, z) ↦ (f₁ (q, z), f₂ (q, a z))`
is closed in the product of the two complements of the tubes. -/
private theorem isClosed_range_collarMap_prod :
    IsClosed (range fun p : Q × annulus ℂ δ ε ↦
      (f₁.collarMap hδε p, f₂.collarMap hδε (prodAnnulusDiffeomorph (I := J) Q δ ε hδ p))) := by
  set Ψ := fun p : Q × annulus ℂ δ ε ↦
    (f₁.collarMap hδε p, f₂.collarMap hδε (prodAnnulusDiffeomorph (I := J) Q δ ε hδ p))
  have hΨ : Continuous Ψ := (f₁.continuous_collarMap hδε).prodMk
    ((f₂.continuous_collarMap hδε).comp (prodAnnulusDiffeomorph (I := J) Q δ ε hδ).continuous)
  refine isClosed_iff_clusterPt.2 fun xy hxy ↦ ?_
  set F := comap Ψ (𝓝 xy)
  have hF : F.NeBot := comap_neBot fun t ht ↦ by
    obtain ⟨_, hts, p, rfl⟩ := clusterPt_principal_iff.1 hxy t ht
    exact ⟨p, hts⟩
  have htend : Tendsto Ψ F (𝓝 xy) := tendsto_comap
  -- The collar coordinates of `F` cluster at a point `(q, z)` with `δ ≤ |z| ≤ ε`.
  set ν : Q × annulus ℂ δ ε → Q × ℂ := fun p ↦ (p.1, (p.2 : ℂ))
  have hK : IsCompact (univ ×ˢ {w : ℂ | δ ≤ ‖w‖ ∧ ‖w‖ ≤ ε}) :=
    (isCompact_univ (X := Q)).prod ((isCompact_closedBall (0 : ℂ) ε).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun w hw ↦ mem_closedBall_zero_iff.2 hw.2)
  obtain ⟨⟨q, z⟩, ⟨-, hz₁, hz₂⟩, hc⟩ := hK (f := map ν F) (le_principal_iff.2 <| mem_map.2 <|
    univ_mem' fun p ↦
      ⟨mem_univ _, (mem_annulus.1 p.2.property).1.le, (mem_annulus.1 p.2.property).2.le⟩)
  rcases hz₁.eq_or_lt with hz₁ | hz₁
  · -- At radius `δ`, the first component would lie in the tube removed from `M₁`.
    exact absurd hc (f₁.not_mapClusterPt_of_tendsto hδε (g := Prod.fst ∘ Ψ)
      (ρ := annulusToProdBall) (fun _ ↦ rfl)
      ((continuous_fst.tendsto _).comp htend) (w := (q, z)) hz₁.ge)
  rcases hz₂.eq_or_lt with hz₂ | hz₂
  · -- At radius `ε`, the annulus map sends `z` to radius `δ`, in the tube removed from `M₂`.
    have hz : z ≠ 0 := norm_pos_iff.1 (hδ.trans_lt hz₁)
    have hc' := MapClusterPt.continuousAt_comp
      (f := Prod.map id (annulusMap δ ε)) (continuousAt_id.prodMap (continuousAt_annulusMap δ ε hz))
      hc
    have hA : Prod.map id (annulusMap δ ε) ∘ ν = fun a ↦ (annulusToProdBall
        (prodAnnulusDiffeomorph (I := J) Q δ ε hδ a) : Q × ℂ) :=
      funext fun a ↦ by simp [ν]
    rw [hA] at hc'
    refine absurd hc' (f₂.not_mapClusterPt_of_tendsto hδε (g := Prod.snd ∘ Ψ)
      (ρ := annulusToProdBall ∘ prodAnnulusDiffeomorph (I := J) Q δ ε hδ)
      (fun _ ↦ rfl) ((continuous_snd.tendsto _).comp htend) ?_)
    rw [Prod.map_snd, norm_annulusMap δ ε hz, hz₂, add_sub_cancel_left, Real.sqrt_sq hδ]
  -- Otherwise `(q, z)` lies in the collar, and the point is on the graph.
  set p₀ : Q × annulus ℂ δ ε := (q, ⟨z, mem_annulus.2 ⟨hz₁, hz₂⟩⟩)
  have hp₀ : ClusterPt p₀ F :=
    (IsInducing.id.prodMap IsInducing.subtypeVal).mapClusterPt_iff.1 hc
  exact ⟨p₀, eq_of_nhds_neBot ((hΨ.continuousAt.mapClusterPt hp₀).neBot.mono
    (inf_le_inf_left _ htend))⟩

/-- **The graph of the gluing map of the fiber sum is closed**, in the product of the complements
of the closed tubes in `M₁` and `M₂`. -/
theorem isClosed_graph_fiberSumGluing :
    IsClosed {p : f₁.complTube hδε × f₂.complTube hδε |
      ∃ u : f₁.collar hδε, (u : f₁.complTube hδε) = p.1 ∧
        (fiberSumGluing f₁ f₂ hδ hδε u : f₂.complTube hδε) = p.2} := by
  convert isClosed_range_collarMap_prod f₁ f₂ hδ hδε using 1
  ext ⟨x, y⟩
  constructor
  · rintro ⟨u, rfl, rfl⟩
    obtain ⟨p, rfl⟩ : ∃ p, f₁.collarDiffeomorph hδε p = u := (f₁.collarDiffeomorph hδε).surjective u
    exact ⟨p, by rw [fiberSumGluing_collarDiffeomorph, f₁.coe_collarDiffeomorph_apply,
      f₂.coe_collarDiffeomorph_apply]⟩
  · rintro ⟨p, hp⟩
    refine ⟨f₁.collarDiffeomorph hδε p, ?_, ?_⟩
    · rw [f₁.coe_collarDiffeomorph_apply]
      exact congrArg Prod.fst hp
    · rw [fiberSumGluing_collarDiffeomorph, f₂.coe_collarDiffeomorph_apply]
      exact congrArg Prod.snd hp

/-- **The fiber sum is Hausdorff.** -/
instance FiberSum.instT2Space : T2Space (FiberSum f₁ f₂ hδ hδε) :=
  GluedAlong.t2Space_of_isClosed_graph _ (isClosed_graph_fiberSumGluing f₁ f₂ hδ hδε)

/-- If `ι₁` and `ι₂` pull `σ₁` and `σ₂` back to the same form on `Q`, the gluing diffeomorphism
of the fiber sum pulls the restriction of `σ₂` to the collar of `M₂` back to the restriction of
`σ₁` to the collar of `M₁`. -/
theorem mpullback_fiberSumGluing
    (h : SmoothForm.mpullback ι₁ ι₁.contMDiff σ₁ = SmoothForm.mpullback ι₂ ι₂.contMDiff σ₂) :
    SmoothForm.mpullback (fiberSumGluing f₁ f₂ hδ hδε) (fiberSumGluing f₁ f₂ hδ hδε).contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁) := by
  rw [SmoothForm.mpullback_congr _ (Diffeomorph.contMDiff _)
      (congrArg DFunLike.coe (fiberSumGluing_def f₁ f₂ hδ hδε)),
    SmoothForm.mpullback_trans, SmoothForm.mpullback_trans, f₂.mpullback_collarDiffeomorph,
    mpullback_prodAnnulusDiffeomorph, ← h, ← f₁.mpullback_collarDiffeomorph,
    SmoothForm.mpullback_symm_mpullback]

namespace FiberSum

variable {f₁ f₂ hδ hδε}
  (h : SmoothForm.mpullback ι₁ ι₁.contMDiff σ₁ = SmoothForm.mpullback ι₂ ι₂.contMDiff σ₂)

variable (f₁ f₂ hδ hδε) in
/-- The **symplectic form of the fiber sum**, for embeddings `ι₁` and `ι₂` that pull `σ₁` and `σ₂`
back to the same form on `Q`: the two-form on `FiberSum f₁ f₂ hδ hδε` that restricts to `σ₁` on
the complement of the tube in `M₁` and to `σ₂` on that in `M₂`. -/
def symplecticForm : SmoothTwoForm I (FiberSum f₁ f₂ hδ hδε) :=
  GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁)
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂)
    (mpullback_fiberSumGluing f₁ f₂ hδ hδε h)

theorem symplecticForm_def :
    symplecticForm f₁ f₂ hδ hδε h =
      GluedAlong.gluedForm _ (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂)
        (mpullback_fiberSumGluing f₁ f₂ hδ hδε h) :=
  (rfl)

/-- The symplectic form of the fiber sum pulls back by `inl` to the restriction of `σ₁` to the
complement of the tube in `M₁`. -/
@[simp]
theorem mpullback_inl_symplecticForm :
    SmoothForm.mpullback (GluedAlong.inl (fiberSumGluing f₁ f₂ hδ hδε))
        (GluedAlong.isLocalDiffeomorph_inl _).contMDiff (symplecticForm f₁ f₂ hδ hδε h) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁ :=
  GluedAlong.mpullback_inl_gluedForm

/-- The symplectic form of the fiber sum pulls back by `inr` to the restriction of `σ₂` to the
complement of the tube in `M₂`. -/
@[simp]
theorem mpullback_inr_symplecticForm :
    SmoothForm.mpullback (GluedAlong.inr (fiberSumGluing f₁ f₂ hδ hδε))
        (GluedAlong.isLocalDiffeomorph_inr _).contMDiff (symplecticForm f₁ f₂ hδ hδε h) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂ :=
  GluedAlong.mpullback_inr_gluedForm

/-- A two-form on the fiber sum is its symplectic form exactly when it pulls back by `inl` and
`inr` to the restrictions of `σ₁` and `σ₂` to the complements of the tubes. -/
theorem eq_symplecticForm_iff {α : SmoothTwoForm I (FiberSum f₁ f₂ hδ hδε)} :
    α = symplecticForm f₁ f₂ hδ hδε h ↔
      SmoothForm.mpullback (GluedAlong.inl (fiberSumGluing f₁ f₂ hδ hδε))
          (GluedAlong.isLocalDiffeomorph_inl _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁ ∧
      SmoothForm.mpullback (GluedAlong.inr (fiberSumGluing f₁ f₂ hδ hδε))
          (GluedAlong.isLocalDiffeomorph_inr _).contMDiff α =
        SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂ :=
  GluedAlong.eq_gluedForm_iff

/-- For symplectic `σ₁` and `σ₂`, the symplectic form of the fiber sum is symplectic. -/
theorem isSymplectic_symplecticForm (hω₁ : σ₁.IsSymplectic) (hω₂ : σ₂.IsSymplectic) :
    (symplecticForm f₁ f₂ hδ hδε h).IsSymplectic :=
  GluedAlong.isSymplectic_gluedForm_iff.2
    ⟨hω₁.mpullback_subtype_val _, hω₂.mpullback_subtype_val _⟩

end FiberSum

end FiberSum

/-- **The symplectic fiber sum.** Let `σ₁` and `σ₂` be symplectic forms on Hausdorff, second
countable manifolds `M₁` and `M₂` without boundary, over one model, and let `ι₁ : Q → M₁` and
`ι₂ : Q → M₂` be smooth embeddings of codimension two, with symplectic tangent images, of a
compact Hausdorff manifold `Q` without boundary, that pull `σ₁` and `σ₂` back to the same form
`τ`, and let `Φ₁` and `Φ₂` be symplectic framings of their normal bundles. Then there is
`ε₀ > 0` such that for every `0 < ε < ε₀` both framings have product neighbourhoods of radius
`ε`, and for all product neighbourhoods `f₁`, `f₂` of radius `ε` and every `0 < δ < ε` the fiber
sum `FiberSum f₁ f₂ hδ hδε` is a Hausdorff, second countable smooth manifold with a symplectic
form that pulls back by `inl` and `inr` to the restrictions of `σ₁` and `σ₂` to the complements
of the closed tubes of radius `δ`.

Milestone: *Symplectic fibre connected sum with trivial normal bundles*. -/
theorem exists_isSymplectic_fiberSum [J.Boundaryless] [I.Boundaryless] [T2Space Q]
    [CompactSpace Q] {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace H M₁]
    [IsManifold I ∞ M₁] [T2Space M₁] [SecondCountableTopology M₁] [TopologicalSpace M₂]
    [ChartedSpace H M₂] [IsManifold I ∞ M₂] [T2Space M₂] [SecondCountableTopology M₂]
    {σ₁ : SmoothTwoForm I M₁} (hσ₁ : σ₁.IsSymplectic) {σ₂ : SmoothTwoForm I M₂}
    (hσ₂ : σ₂.IsSymplectic) {τ : SmoothTwoForm J Q}
    {ι₁ : SmoothEmbedding J I ∞ Q M₁} {hι₁ : hσ₁.isNondegenerate.HasSymplecticTangentImages J ι₁}
    {ι₂ : SmoothEmbedding J I ∞ Q M₂} {hι₂ : hσ₂.isNondegenerate.HasSymplecticTangentImages J ι₂}
    (h₁ : SmoothForm.mpullback ι₁ ι₁.contMDiff σ₁ = τ)
    (h₂ : SmoothForm.mpullback ι₂ ι₂.contMDiff σ₂ = τ)
    {hP : finrank ℝ ℂ = finrank ℝ E - finrank ℝ EQ}
    (Φ₁ : SymplecticFraming hι₁ hP) (Φ₂ : SymplecticFraming hι₂ hP) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      Nonempty (ProductNeighborhood Φ₁ ε) ∧ Nonempty (ProductNeighborhood Φ₂ ε) ∧
      ∀ (f₁ : ProductNeighborhood Φ₁ ε) (f₂ : ProductNeighborhood Φ₂ ε) (δ : ℝ) (hδ : 0 < δ)
        (hδε : δ < ε),
        T2Space (FiberSum f₁ f₂ hδ.le hδε) ∧ SecondCountableTopology (FiberSum f₁ f₂ hδ.le hδε) ∧
        IsManifold I ∞ (FiberSum f₁ f₂ hδ.le hδε) ∧
        ∃ α : SmoothTwoForm I (FiberSum f₁ f₂ hδ.le hδε), α.IsSymplectic ∧
          SmoothForm.mpullback (GluedAlong.inl (fiberSumGluing f₁ f₂ hδ.le hδε))
              (GluedAlong.isLocalDiffeomorph_inl _).contMDiff α =
            SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₁ ∧
          SmoothForm.mpullback (GluedAlong.inr (fiberSumGluing f₁ f₂ hδ.le hδε))
              (GluedAlong.isLocalDiffeomorph_inr _).contMDiff α =
            SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ₂ := by
  obtain ⟨ε₁, hε₁, hf₁⟩ := ProductNeighborhood.exists hσ₁ Φ₁
  obtain ⟨ε₂, hε₂, hf₂⟩ := ProductNeighborhood.exists hσ₂ Φ₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε _ hε ↦ ⟨hf₁ ε (hε.le.trans (min_le_left _ _)),
    hf₂ ε (hε.le.trans (min_le_right _ _)), fun f₁ f₂ δ hδ hδε ↦
      ⟨inferInstance, inferInstance, inferInstance,
      FiberSum.symplecticForm f₁ f₂ hδ.le hδε (h₁.trans h₂.symm),
      FiberSum.isSymplectic_symplecticForm _ hσ₁ hσ₂, FiberSum.mpullback_inl_symplecticForm _,
      FiberSum.mpullback_inr_symplecticForm _⟩⟩⟩

end SymplecticGeometry

end
