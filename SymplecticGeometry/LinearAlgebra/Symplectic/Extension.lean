/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
public import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.Submodule.Compl
public import TauCeti.Geometry.Symplectic.LinearReduction
import SymplecticGeometry.LinearAlgebra.Symplectic.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Reduction
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# An explicit linear symplectic extension

Let `ω` be a symplectic form on a finite-dimensional real vector space `V`, `J` an
`ω`-compatible complex structure, `g = ω(·, J ·)` the associated inner product
(`TauCeti.SymplecticForm.associatedBilinForm`) and `W` a subspace, with radical
`K = W ∩ W^ω`. The complex structure splits `V` without any choice:

* `H = W ∩ K^{⊥g}` (`TauCeti.SymplecticForm.radicalComplement`), a symplectic complement
  of `K` in `W`;
* `J K`, an isotropic subspace with `W ∩ J K = 0`, such that `W ⊕ J K` is symplectic;
* `E = (W ⊕ J K)^ω = W^ω ∩ K^{⊥g}` (`TauCeti.SymplecticForm.normalComplement`), a symplectic
  complement of `K` in `W^ω`, which maps isomorphically and symplectically onto the reduced
  space `W^ω ⧸ K`.

So `V = H ⊕ K ⊕ J K ⊕ E`, with `H`, `K ⊕ J K` and `E` pairwise `ω`-orthogonal.

Given two such data `(V₀, ω₀, J₀, W₀)` and `(V₁, ω₁, J₁, W₁)` of equal dimension, a linear
isomorphism `b : W₀ ≃ W₁` preserving the restricted forms, and a linear map `L : V₀ → V₁` which
maps `W₀^ω` into `W₁^ω` and preserves `ω` there, `Compatible.extendAlong` is a linear
symplectomorphism `A : V₀ ≃ V₁` given by a formula: it is `b` on `W₀`, the projection of `L`
onto `E₁` along `W₁ ⊕ J₁ K₁` on `E₀`, and on `J₀ K₀` the map determined by the pairing with
`W₁`, corrected by an element of `K₁` so that the image of `J₀ K₀` is isotropic. It induces
the same map as `L` on the reduced spaces: `A v - L v ∈ W₁` for `v ∈ W₀^ω`. Tau Ceti's
`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend` (Witt's theorem) only gives the
existence of such an extension; a formula is what a smooth family of extensions along a
submanifold needs.

## Main definitions

* `TauCeti.SymplecticForm.radicalComplement ω J W`: `H = W ∩ K^{⊥g}`.
* `TauCeti.SymplecticForm.normalComplement ω J W`: `E = (W ⊕ J K)^ω`.
* `TauCeti.SymplecticForm.Compatible.normalComplementEquiv`: `E ≃ W^ω ⧸ K`.
* `TauCeti.SymplecticForm.Compatible.extendAlong`: the extension `A`.

## Main results

* `TauCeti.SymplecticForm.Compatible.radicalComplement_sup_inf`,
  `TauCeti.SymplecticForm.Compatible.inf_sup_normalComplement`,
  `TauCeti.SymplecticForm.Compatible.isCompl_sup_map_normalComplement`: the splittings.
* `TauCeti.SymplecticForm.Compatible.isSymplectic_radicalComplement`,
  `TauCeti.SymplecticForm.Compatible.isSymplectic_sup_map`,
  `TauCeti.SymplecticForm.Compatible.isSymplectic_normalComplement`: `H`, `W ⊕ J K` and `E`
  are symplectic.
* `TauCeti.SymplecticForm.Compatible.isSymplectomorphism_normalComplementEquiv`: the map
  `E ≃ W^ω ⧸ K` carries the restriction of `ω` to `E` to the reduced form.
* `TauCeti.SymplecticForm.Compatible.isSymplectomorphism_extendAlong`,
  `TauCeti.SymplecticForm.Compatible.extendAlong_apply_coe`,
  `TauCeti.SymplecticForm.Compatible.extendAlong_sub_mem`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §3.4: the linear algebra in the proofs of Theorem 3.4.10 and Exercise 3.4.18.
-/

public section

open Module

namespace TauCeti.SymplecticForm

section Pieces

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}
  {J : AlmostComplexStructure V} {W : Submodule ℝ V} {v : V}

variable (ω J) in
/-- The complement `H = W ∩ K^{⊥g}` of the radical `K = W ∩ W^ω` in `W`, for the inner product
`g = ω(·, J ·)` of a compatible `J`. It is symplectic
(`TauCeti.SymplecticForm.Compatible.isSymplectic_radicalComplement`) and `W = H ⊕ K`
(`TauCeti.SymplecticForm.Compatible.radicalComplement_sup_inf`). -/
def radicalComplement (W : Submodule ℝ V) : Submodule ℝ V :=
  W ⊓ (ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W)

variable (ω J) in
theorem radicalComplement_def (W : Submodule ℝ V) :
    ω.radicalComplement J W = W ⊓ (ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W) :=
  (rfl)

/-- Membership in the radical complement `H = W ∩ K^{⊥g}`. -/
theorem mem_radicalComplement_iff :
    v ∈ ω.radicalComplement J W ↔ v ∈ W ∧ ∀ k ∈ W ⊓ ω.orthogonal W, ω k (J v) = 0 := by
  simp [radicalComplement_def]

variable (ω J) in
/-- The complement `E = (W ⊕ J K)^ω` of the radical `K = W ∩ W^ω` in `W^ω`, for a compatible `J`.
It equals `W^ω ∩ K^{⊥g}` (`TauCeti.SymplecticForm.Invariant.normalComplement_eq_inf`), is
symplectic, `W^ω = K ⊕ E`, and it maps isomorphically onto the reduced space `W^ω ⧸ K`
(`TauCeti.SymplecticForm.Compatible.normalComplementEquiv`). -/
def normalComplement (W : Submodule ℝ V) : Submodule ℝ V :=
  ω.orthogonal (W ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap)

variable (ω J) in
theorem normalComplement_def (W : Submodule ℝ V) :
    ω.normalComplement J W = ω.orthogonal (W ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap) :=
  (rfl)

/-- Membership in the normal complement `E = (W ⊕ J K)^ω`. -/
theorem mem_normalComplement_iff :
    v ∈ ω.normalComplement J W ↔
      (∀ w ∈ W, ω w v = 0) ∧ ∀ k ∈ W ⊓ ω.orthogonal W, ω (J k) v = 0 := by
  simp only [normalComplement_def, orthogonal_sup, Submodule.mem_inf, mem_orthogonal_iff,
    Submodule.mem_map, forall_exists_index, and_imp]
  exact and_congr_right fun _ =>
    ⟨fun h k hk hk' => h _ k hk hk' rfl, fun h _ k hk hk' hy => hy ▸ h k hk hk'⟩

/-- The normal complement of `W` lies in `W^ω`. -/
theorem normalComplement_le_orthogonal : ω.normalComplement J W ≤ ω.orthogonal W :=
  orthogonal_le le_sup_left

/-- For a `J`-invariant form, the normal complement of `W` is `W^ω ∩ K^{⊥g}`, `K = W ∩ W^ω`. -/
theorem Invariant.normalComplement_eq_inf (hJ : ω.Invariant J) :
    ω.normalComplement J W =
      ω.orthogonal W ⊓ (ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W) := by
  rw [normalComplement_def, orthogonal_sup, hJ.orthogonal_map]

variable (hJ : ω.Compatible J)
include hJ

/-- `W` meets `J K` only in `0`, `K = W ∩ W^ω`. -/
theorem Compatible.disjoint_map : Disjoint W ((W ⊓ ω.orthogonal W).map J.toLinearMap) := by
  rw [Submodule.disjoint_def]
  rintro _ hx ⟨k, hk, rfl⟩
  have : ω.associatedBilinForm J k k = 0 := by
    rw [associatedBilinForm_apply]
    linarith [ω.neg_eq (J k) k, mem_orthogonal_iff.1 hk.2 _ hx]
  simp [hJ.associatedBilinForm_self_eq_zero.1 this]

/-- A vector of `W ⊕ J K` that is `ω`-orthogonal to `W` lies in `W`, hence in `K`. -/
theorem Compatible.orthogonal_inf_sup_map_le :
    ω.orthogonal W ⊓ (W ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap) ≤ W := by
  rintro v ⟨hv, hvS⟩
  obtain ⟨w, hw, _, ⟨k, hk, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hvS
  have h₁ : ω k (w + J k) = 0 := mem_orthogonal_iff.1 hv k hk.1
  have h₂ : ω w k = 0 := mem_orthogonal_iff.1 hk.2 w hw
  have : ω.associatedBilinForm J k k = 0 := by
    simp only [map_add] at h₁
    rw [associatedBilinForm_apply]
    linarith [ω.neg_eq w k]
  simpa [hJ.associatedBilinForm_self_eq_zero.1 this] using hw

/-- `W ⊕ J K` is a symplectic subspace, `K = W ∩ W^ω`. -/
theorem Compatible.isSymplectic_sup_map :
    ω.IsSymplectic (W ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap) := by
  rw [isSymplectic_iff_disjoint, Submodule.disjoint_def]
  intro x hx hx'
  rw [orthogonal_sup, hJ.invariant.orthogonal_map] at hx'
  have hxW : x ∈ W := hJ.orthogonal_inf_sup_map_le ⟨hx'.1, hx⟩
  exact hJ.associatedBilinForm_self_eq_zero.1
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hx'.2 x ⟨hxW, hx'.1⟩)

/-- The normal complement is a symplectic subspace. -/
theorem Compatible.isSymplectic_normalComplement [FiniteDimensional ℝ V] :
    ω.IsSymplectic (ω.normalComplement J W) :=
  hJ.isSymplectic_sup_map.orthogonal

/-- `V = (W ⊕ J K) ⊕ E`, `K = W ∩ W^ω`, `E` the normal complement. -/
theorem Compatible.isCompl_sup_map_normalComplement [FiniteDimensional ℝ V] :
    IsCompl (W ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap) (ω.normalComplement J W) :=
  hJ.isSymplectic_sup_map.isCompl

/-- `V = W ⊕ (J K ⊕ E)`, `K = W ∩ W^ω`, `E` the normal complement. -/
theorem Compatible.isCompl_map_sup_normalComplement [FiniteDimensional ℝ V] :
    IsCompl W ((W ⊓ ω.orthogonal W).map J.toLinearMap ⊔ ω.normalComplement J W) :=
  ⟨hJ.disjoint_map.disjoint_sup_right_of_disjoint_sup_left
      hJ.isCompl_sup_map_normalComplement.disjoint,
    by rw [codisjoint_iff, ← sup_assoc, hJ.isCompl_sup_map_normalComplement.sup_eq_top]⟩

/-- `V = J K ⊕ (W ⊕ E)`, `K = W ∩ W^ω`, `E` the normal complement. -/
theorem Compatible.isCompl_map_self_sup_normalComplement [FiniteDimensional ℝ V] :
    IsCompl ((W ⊓ ω.orthogonal W).map J.toLinearMap) (W ⊔ ω.normalComplement J W) :=
  ⟨hJ.disjoint_map.symm.disjoint_sup_right_of_disjoint_sup_left
      (by rw [sup_comm]; exact hJ.isCompl_sup_map_normalComplement.disjoint),
    by rw [codisjoint_iff, ← sup_assoc, sup_comm _ W,
      hJ.isCompl_sup_map_normalComplement.sup_eq_top]⟩

/-- The radical complement meets the radical only in `0`. -/
theorem Compatible.disjoint_radicalComplement_inf :
    Disjoint (ω.radicalComplement J W) (W ⊓ ω.orthogonal W) := by
  rw [Submodule.disjoint_def]
  exact fun x hx hx' => hJ.associatedBilinForm_self_eq_zero.1
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hx.2 x hx')

/-- `W = H ⊕ K`: the radical complement and the radical span `W`. -/
theorem Compatible.radicalComplement_sup_inf [FiniteDimensional ℝ V] :
    ω.radicalComplement J W ⊔ (W ⊓ ω.orthogonal W) = W := by
  have h := sup_inf_assoc_of_le ((ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W))
    (inf_le_left : W ⊓ ω.orthogonal W ≤ W)
  rw [(hJ.isCompl_orthogonal_associatedBilinForm _).sup_eq_top, top_inf_eq] at h
  rw [radicalComplement_def, sup_comm,
    inf_comm W ((ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W))]
  exact h.symm

/-- The radical complement `H` is the image of `W` under the projection onto `K^{⊥g}` along the
radical `K = W ∩ W^ω`. -/
theorem Compatible.map_projection_orthogonal_eq_radicalComplement [FiniteDimensional ℝ V] :
    W.map (((ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W)).projection
        (W ⊓ ω.orthogonal W) (hJ.isCompl_orthogonal_associatedBilinForm _).symm) =
      ω.radicalComplement J W := by
  ext x
  rw [radicalComplement_def, Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, Submodule.projection_apply_mem _ _⟩
    rw [Submodule.projection_eq_self_sub_projection (hJ.isCompl_orthogonal_associatedBilinForm _)]
    exact W.sub_mem hw (Submodule.mem_inf.1 (Submodule.projection_apply_mem _ _)).1
  · rintro ⟨hxW, hxS⟩
    exact ⟨x, hxW, Submodule.projection_apply_of_mem_left _ hxS⟩

/-- The radical complement is `ω`-orthogonal to `K ⊕ J K`. -/
theorem Compatible.radicalComplement_le_orthogonal_sup_map :
    ω.radicalComplement J W ≤
      ω.orthogonal ((W ⊓ ω.orthogonal W) ⊔ (W ⊓ ω.orthogonal W).map J.toLinearMap) := by
  rw [orthogonal_sup, hJ.invariant.orthogonal_map]
  exact fun x hx => ⟨mem_orthogonal_iff'.2 fun k hk => mem_orthogonal_iff.1 hk.2 x hx.1, hx.2⟩

/-- The radical complement is a symplectic subspace. -/
theorem Compatible.isSymplectic_radicalComplement [FiniteDimensional ℝ V] :
    ω.IsSymplectic (ω.radicalComplement J W) := by
  rw [isSymplectic_iff_disjoint, Submodule.disjoint_def]
  intro x hx hx'
  have hxW : x ∈ ω.orthogonal W := by
    rw [← hJ.radicalComplement_sup_inf (W := W), orthogonal_sup]
    exact ⟨hx', mem_orthogonal_iff'.2 fun k hk => mem_orthogonal_iff.1 hk.2 x hx.1⟩
  exact Submodule.disjoint_def.1 hJ.disjoint_radicalComplement_inf x hx ⟨hx.1, hxW⟩

/-- The radical meets the normal complement only in `0`. -/
theorem Compatible.disjoint_inf_normalComplement :
    Disjoint (W ⊓ ω.orthogonal W) (ω.normalComplement J W) := by
  rw [hJ.invariant.normalComplement_eq_inf, Submodule.disjoint_def]
  exact fun x hx hx' => hJ.associatedBilinForm_self_eq_zero.1
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hx'.2 x hx)

/-- `W^ω = K ⊕ E`: the radical and the normal complement span `W^ω`. -/
theorem Compatible.inf_sup_normalComplement [FiniteDimensional ℝ V] :
    (W ⊓ ω.orthogonal W) ⊔ ω.normalComplement J W = ω.orthogonal W := by
  have h := sup_inf_assoc_of_le ((ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W))
    (inf_le_right : W ⊓ ω.orthogonal W ≤ ω.orthogonal W)
  rw [(hJ.isCompl_orthogonal_associatedBilinForm _).sup_eq_top, top_inf_eq] at h
  rw [hJ.invariant.normalComplement_eq_inf,
    inf_comm (ω.orthogonal W) ((ω.associatedBilinForm J).orthogonal (W ⊓ ω.orthogonal W))]
  exact h.symm

variable (W) in
/-- The normal complement `E` of `W` maps isomorphically onto the reduced space `W^ω ⧸ K`,
`K = W ∩ W^ω`, by `e ↦ [e]` (`TauCeti.SymplecticForm.Compatible.normalComplementEquiv_apply`).
Its inverse is the projection of `W^ω` onto `E` along `K`. It is a symplectomorphism
(`TauCeti.SymplecticForm.Compatible.isSymplectomorphism_normalComplementEquiv`). -/
noncomputable def Compatible.normalComplementEquiv [FiniteDimensional ℝ V] :
    ω.normalComplement J W ≃ₗ[ℝ] ω.ReducedSpace (ω.orthogonal W) :=
  (Submodule.comapSubtypeEquivOfLe normalComplement_le_orthogonal).symm ≪≫ₗ
    (Submodule.quotientEquivOfIsCompl _ _ <| ker_restrict_orthogonal ω W ▸
      Submodule.isCompl_comap_subtype_iff.2
        ⟨by rw [inf_eq_right.2 inf_le_right, inf_eq_right.2 normalComplement_le_orthogonal]
            exact hJ.disjoint_inf_normalComplement,
          by rw [inf_eq_right.2 inf_le_right, inf_eq_right.2 normalComplement_le_orthogonal,
            hJ.inf_sup_normalComplement]⟩).symm

/-- The identification of the normal complement with the reduced space sends `e` to its class
`[e]`. -/
@[simp]
theorem Compatible.normalComplementEquiv_apply [FiniteDimensional ℝ V]
    (x : ω.normalComplement J W) :
    hJ.normalComplementEquiv W x =
      Submodule.Quotient.mk ⟨x, normalComplement_le_orthogonal x.property⟩ :=
  (rfl)

/-- The identification of the normal complement with the reduced space `W^ω ⧸ K` is a
symplectomorphism for the restriction of `ω` and the reduced form. -/
theorem Compatible.isSymplectomorphism_normalComplementEquiv [FiniteDimensional ℝ V] :
    IsSymplectomorphism (ω.restrict _ hJ.isSymplectic_normalComplement.nondegenerate_restrict)
      (ω.reduction (ω.orthogonal W)) (hJ.normalComplementEquiv W) := by
  rw [isSymplectomorphism_iff]
  intro x y
  rw [hJ.normalComplementEquiv_apply, hJ.normalComplementEquiv_apply, reduction_mk,
    restrict_apply]

end Pieces

section Construction

variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
  [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁]
  {ω₀ : SymplecticForm V₀} {ω₁ : SymplecticForm V₁}
  {J₀ : AlmostComplexStructure V₀} {J₁ : AlmostComplexStructure V₁}
  (hJ₀ : ω₀.Compatible J₀) (hJ₁ : ω₁.Compatible J₁)
  {W₀ : Submodule ℝ V₀} {W₁ : Submodule ℝ V₁} (b : W₀ ≃ₗ[ℝ] W₁) (L : V₀ →ₗ[ℝ] V₁)

/-- `b⁻¹` composed with the projection of `V₁` onto `W₁` along `J₁ K₁ ⊕ E₁`. -/
private noncomputable def backMap : V₁ →ₗ[ℝ] V₀ :=
  W₀.subtype ∘ₗ b.symm.toLinearMap ∘ₗ
    W₁.projectionOnto _ hJ₁.isCompl_map_sup_normalComplement

variable (ω₀) in
/-- The map `x ↦ u` with `ω₁ u y = ω₀ x (backMap y)` for all `y`. -/
private noncomputable def pairMap : V₀ →ₗ[ℝ] V₁ :=
  (ω₁.toBilinForm.toDual ω₁.nondegenerate).symm.toLinearMap ∘ₗ
    (backMap hJ₁ b).dualMap ∘ₗ ω₀.toBilinForm

/-- The value of the extension on `J₀ K₀`: `pairMap` corrected by an element of `K₁`. -/
private noncomputable def mapJ : V₀ →ₗ[ℝ] V₁ :=
  pairMap ω₀ hJ₁ b - (2⁻¹ : ℝ) • (W₁.subtype ∘ₗ b.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (W₀ ⊓ ω₀.orthogonal W₀).projectionOnto _
      (hJ₀.isCompl_orthogonal_associatedBilinForm _) ∘ₗ backMap hJ₁ b ∘ₗ pairMap ω₀ hJ₁ b)

/-- The linear map underlying `TauCeti.SymplecticForm.Compatible.extendAlong`. -/
private noncomputable def extendAlongMap : V₀ →ₗ[ℝ] V₁ :=
  W₁.subtype ∘ₗ b.toLinearMap ∘ₗ W₀.projectionOnto _ hJ₀.isCompl_map_sup_normalComplement +
    mapJ hJ₀ hJ₁ b ∘ₗ ((W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap).projection _
      hJ₀.isCompl_map_self_sup_normalComplement +
    (ω₁.normalComplement J₁ W₁).projection _ hJ₁.isCompl_sup_map_normalComplement.symm ∘ₗ L ∘ₗ
      (ω₀.normalComplement J₀ W₀).projection _ hJ₀.isCompl_sup_map_normalComplement.symm

omit [FiniteDimensional ℝ V₀] in
private theorem backMap_apply_coe (w : W₀) : backMap hJ₁ b (b w : V₁) = w := by
  simp [backMap]

omit [FiniteDimensional ℝ V₀] in
private theorem backMap_eq_zero {y : V₁} (hy : y ∈ ω₁.normalComplement J₁ W₁) :
    backMap hJ₁ b y = 0 := by
  simp [backMap, Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_sup_right hy)]

omit [FiniteDimensional ℝ V₀] in
private theorem pairMap_apply_apply (x : V₀) (y : V₁) :
    ω₁ (pairMap ω₀ hJ₁ b x) y = ω₀ x (backMap hJ₁ b y) := by
  simp [pairMap]

/-- Against a vector of `J₀ K₀`, a vector pairs as its `g₀`-orthogonal projection onto
`K₀ = W₀ ∩ W₀^ω`. -/
private theorem apply_projectionOnto_inf {x : V₀}
    (hx : x ∈ (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap) (z : V₀) :
    ω₀ x ((W₀ ⊓ ω₀.orthogonal W₀).projectionOnto _
      (hJ₀.isCompl_orthogonal_associatedBilinForm _) z) = ω₀ x z := by
  have h := Submodule.projection_add_projection_eq_self
    (hJ₀.isCompl_orthogonal_associatedBilinForm (W₀ ⊓ ω₀.orthogonal W₀)) z
  have hc := Submodule.projection_apply_mem
    (hJ₀.isCompl_orthogonal_associatedBilinForm (W₀ ⊓ ω₀.orthogonal W₀)).symm z
  have hc' := (hJ₀.invariant.orthogonal_map _).ge hc
  conv_rhs => rw [← h]
  simp only [map_add, mem_orthogonal_iff.1 hc' x hx, add_zero,
    Submodule.coe_projectionOnto_apply]

/-- The correction term of `mapJ`, in `K₀`. -/
private noncomputable def corr (x : V₀) : W₀ :=
  Submodule.inclusion inf_le_left ((W₀ ⊓ ω₀.orthogonal W₀).projectionOnto _
    (hJ₀.isCompl_orthogonal_associatedBilinForm _) (backMap hJ₁ b (pairMap ω₀ hJ₁ b x)))

private theorem corr_mem (x : V₀) :
    (corr hJ₀ hJ₁ b x : V₀) ∈ ω₀.orthogonal W₀ :=
  ((W₀ ⊓ ω₀.orthogonal W₀).projectionOnto _
    (hJ₀.isCompl_orthogonal_associatedBilinForm _) (backMap hJ₁ b (pairMap ω₀ hJ₁ b x))).property.2

private theorem mapJ_apply (x : V₀) :
    mapJ hJ₀ hJ₁ b x = pairMap ω₀ hJ₁ b x - (2⁻¹ : ℝ) • (b (corr hJ₀ hJ₁ b x) : V₁) :=
  (rfl)

private theorem apply_corr {x y : V₀} (hy : y ∈ (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap) :
    ω₀ y (corr hJ₀ hJ₁ b x) = ω₁ (pairMap ω₀ hJ₁ b y) (pairMap ω₀ hJ₁ b x) := by
  rw [pairMap_apply_apply, corr, Submodule.coe_inclusion, apply_projectionOnto_inf hJ₀ hy]

variable {b} (hb : ∀ x y : W₀, ω₁ (b x) (b y) = ω₀ x y)
include hb

omit hb in
private theorem apply_mapJ_eq_zero (x : V₀) {y : V₁} (hy : y ∈ ω₁.normalComplement J₁ W₁) :
    ω₁ (mapJ hJ₀ hJ₁ b x) y = 0 := by
  have h : ω₁ (b (corr hJ₀ hJ₁ b x)) y = 0 :=
    mem_orthogonal_iff.1 (normalComplement_le_orthogonal hy) _ (b _).property
  simp only [mapJ_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    pairMap_apply_apply, backMap_eq_zero hJ₁ b hy, h, map_zero, smul_zero, sub_zero]

private theorem apply_coe_mapJ (w : W₀) (x : V₀) :
    ω₁ (b w) (mapJ hJ₀ hJ₁ b x) = ω₀ w x := by
  have h₁ : ω₁ (b w) (pairMap ω₀ hJ₁ b x) = ω₀ w x := by
    rw [← ω₁.neg_eq, pairMap_apply_apply, backMap_apply_coe, ω₀.neg_eq]
  have h₂ : ω₁ (b w) (b (corr hJ₀ hJ₁ b x)) = 0 := by
    rw [hb]
    exact mem_orthogonal_iff.1 (corr_mem hJ₀ hJ₁ b x) w w.property
  simp only [mapJ_apply, map_sub, map_smul, h₁, h₂, smul_zero, sub_zero]

/-- The image of `J₀ K₀` is isotropic: this is what the correction term is for. -/
private theorem mapJ_apply_mapJ {x x' : V₀}
    (hx : x ∈ (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap)
    (hx' : x' ∈ (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap) :
    ω₁ (mapJ hJ₀ hJ₁ b x) (mapJ hJ₀ hJ₁ b x') = 0 := by
  have f₁ : ω₁ (pairMap ω₀ hJ₁ b x) (b (corr hJ₀ hJ₁ b x')) =
      ω₁ (pairMap ω₀ hJ₁ b x) (pairMap ω₀ hJ₁ b x') := by
    rw [pairMap_apply_apply, backMap_apply_coe, apply_corr hJ₀ hJ₁ b hx]
  have f₂ : ω₁ (b (corr hJ₀ hJ₁ b x)) (pairMap ω₀ hJ₁ b x') =
      ω₁ (pairMap ω₀ hJ₁ b x) (pairMap ω₀ hJ₁ b x') := by
    rw [← ω₁.neg_eq, pairMap_apply_apply, backMap_apply_coe, apply_corr hJ₀ hJ₁ b hx',
      ω₁.neg_eq]
  have f₃ : ω₁ (b (corr hJ₀ hJ₁ b x)) (b (corr hJ₀ hJ₁ b x')) = 0 := by
    rw [hb]
    exact mem_orthogonal_iff.1 (corr_mem hJ₀ hJ₁ b x') _ (corr hJ₀ hJ₁ b x).property
  simp only [mapJ_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  linear_combination (-2⁻¹ : ℝ) * f₁ - 2⁻¹ * f₂ + 4⁻¹ * f₃

omit hb

variable {L} (hL : ∀ v ∈ ω₀.orthogonal W₀, L v ∈ ω₁.orthogonal W₁)
include hL

omit [FiniteDimensional ℝ V₀] in
/-- On `E₀`, projecting `L` onto `E₁` along `W₁ ⊕ J₁ K₁` changes it by a vector of `K₁`. -/
private theorem projection_sub_mem {e : V₀} (he : e ∈ ω₀.normalComplement J₀ W₀) :
    (ω₁.normalComplement J₁ W₁).projection _ hJ₁.isCompl_sup_map_normalComplement.symm (L e) -
      L e ∈ W₁ ⊓ ω₁.orthogonal W₁ := by
  have hz := hL e (normalComplement_le_orthogonal he)
  have h := Submodule.projection_add_projection_eq_self
    (hJ₁.isCompl_sup_map_normalComplement (W := W₁)).symm (L e)
  have hE := normalComplement_le_orthogonal
    (Submodule.projection_apply_mem (hJ₁.isCompl_sup_map_normalComplement (W := W₁)).symm (L e))
  have hS := Submodule.projection_apply_mem (hJ₁.isCompl_sup_map_normalComplement (W := W₁)) (L e)
  have hd : (W₁ ⊔ (W₁ ⊓ ω₁.orthogonal W₁).map J₁.toLinearMap).projection _
      hJ₁.isCompl_sup_map_normalComplement (L e) ∈ ω₁.orthogonal W₁ := by
    rw [eq_sub_of_add_eq' h]
    exact Submodule.sub_mem _ hz hE
  rw [eq_sub_of_add_eq h, sub_sub_cancel_left]
  exact Submodule.neg_mem _ ⟨hJ₁.orthogonal_inf_sup_map_le ⟨hd, hS⟩, hd⟩

omit [FiniteDimensional ℝ V₀] in
private theorem projection_apply_projection
    (hLω : ∀ v ∈ ω₀.orthogonal W₀, ∀ w ∈ ω₀.orthogonal W₀, ω₁ (L v) (L w) = ω₀ v w)
    {e e' : V₀} (he : e ∈ ω₀.normalComplement J₀ W₀) (he' : e' ∈ ω₀.normalComplement J₀ W₀) :
    ω₁ ((ω₁.normalComplement J₁ W₁).projection _ hJ₁.isCompl_sup_map_normalComplement.symm (L e))
      ((ω₁.normalComplement J₁ W₁).projection _ hJ₁.isCompl_sup_map_normalComplement.symm
        (L e')) = ω₀ e e' := by
  have hd := projection_sub_mem hJ₁ hL he
  have hd' := projection_sub_mem hJ₁ hL he'
  have hz := hL e (normalComplement_le_orthogonal he)
  have hz' := hL e' (normalComplement_le_orthogonal he')
  rw [← sub_add_cancel ((ω₁.normalComplement J₁ W₁).projection _ _ (L e)) (L e),
    ← sub_add_cancel ((ω₁.normalComplement J₁ W₁).projection _ _ (L e')) (L e')]
  simp only [map_add, LinearMap.add_apply, mem_orthogonal_iff.1 hd'.2 _ hd.1,
    mem_orthogonal_iff.1 hz' _ hd.1, mem_orthogonal_iff'.1 hz _ hd'.1,
    hLω e (normalComplement_le_orthogonal he) e' (normalComplement_le_orthogonal he'),
    zero_add]

omit hL

private theorem extendAlongMap_apply_coe (w : W₀) : extendAlongMap hJ₀ hJ₁ b L w = b w := by
  have h₁ := Submodule.projection_apply_of_mem_right
    hJ₀.isCompl_map_self_sup_normalComplement (Submodule.mem_sup_left w.property)
  have h₂ := Submodule.projection_apply_of_mem_right
    hJ₀.isCompl_sup_map_normalComplement.symm (Submodule.mem_sup_left w.property)
  simp [extendAlongMap, h₁, h₂]

private theorem extendAlongMap_apply_of_mem_map {x : V₀}
    (hx : x ∈ (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap) :
    extendAlongMap hJ₀ hJ₁ b L x = mapJ hJ₀ hJ₁ b x := by
  have h₀ := Submodule.projectionOnto_apply_of_mem_right
    hJ₀.isCompl_map_sup_normalComplement (Submodule.mem_sup_left hx)
  have h₁ := Submodule.projection_apply_of_mem_left
    hJ₀.isCompl_map_self_sup_normalComplement hx
  have h₂ := Submodule.projection_apply_of_mem_right
    hJ₀.isCompl_sup_map_normalComplement.symm (Submodule.mem_sup_right hx)
  simp [extendAlongMap, h₀, h₁, h₂]

private theorem extendAlongMap_apply_of_mem_normalComplement {e : V₀}
    (he : e ∈ ω₀.normalComplement J₀ W₀) :
    extendAlongMap hJ₀ hJ₁ b L e = (ω₁.normalComplement J₁ W₁).projection _
      hJ₁.isCompl_sup_map_normalComplement.symm (L e) := by
  have h₀ := Submodule.projectionOnto_apply_of_mem_right
    hJ₀.isCompl_map_sup_normalComplement (Submodule.mem_sup_right he)
  have h₁ := Submodule.projection_apply_of_mem_right
    hJ₀.isCompl_map_self_sup_normalComplement (Submodule.mem_sup_right he)
  have h₂ := Submodule.projection_apply_of_mem_left
    hJ₀.isCompl_sup_map_normalComplement.symm he
  simp [extendAlongMap, h₀, h₁, h₂]

private theorem extendAlongMap_apply_apply (hb : ∀ x y : W₀, ω₁ (b x) (b y) = ω₀ x y)
    (hL : ∀ v ∈ ω₀.orthogonal W₀, L v ∈ ω₁.orthogonal W₁)
    (hLω : ∀ v ∈ ω₀.orthogonal W₀, ∀ w ∈ ω₀.orthogonal W₀, ω₁ (L v) (L w) = ω₀ v w)
    (v v' : V₀) :
    ω₁ (extendAlongMap hJ₀ hJ₁ b L v) (extendAlongMap hJ₀ hJ₁ b L v') = ω₀ v v' := by
  set A := extendAlongMap hJ₀ hJ₁ b L
  set P := (W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap
  set E := ω₀.normalComplement J₀ W₀
  have swap : ∀ x y, ω₁ (A y) (A x) = ω₀ y x → ω₁ (A x) (A y) = ω₀ x y := fun x y h => by
    rw [← ω₁.neg_eq, h, ω₀.neg_eq]
  have hE : ∀ x ∈ W₀ ⊔ P, ∀ y ∈ E, ω₀ x y = 0 := fun x hx y hy => mem_orthogonal_iff.1 hy x hx
  have hAW (w : W₀) : A w = b w := extendAlongMap_apply_coe hJ₀ hJ₁ w
  have hAP {x : V₀} (hx : x ∈ P) : A x = mapJ hJ₀ hJ₁ b x :=
    extendAlongMap_apply_of_mem_map hJ₀ hJ₁ hx
  have hAE {e : V₀} (he : e ∈ E) : A e = (ω₁.normalComplement J₁ W₁).projection _
      hJ₁.isCompl_sup_map_normalComplement.symm (L e) :=
    extendAlongMap_apply_of_mem_normalComplement hJ₀ hJ₁ he
  have hWW : ∀ x ∈ W₀, ∀ y ∈ W₀, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    simpa [hAW ⟨x, hx⟩, hAW ⟨y, hy⟩] using hb ⟨x, hx⟩ ⟨y, hy⟩
  have hWP : ∀ x ∈ W₀, ∀ y ∈ P, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    simpa [hAW ⟨x, hx⟩, hAP hy] using apply_coe_mapJ hJ₀ hJ₁ hb ⟨x, hx⟩ y
  have hWE : ∀ x ∈ W₀, ∀ y ∈ E, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    rw [hE x (Submodule.mem_sup_left hx) y hy, hAW ⟨x, hx⟩, hAE hy]
    exact mem_orthogonal_iff.1 (normalComplement_le_orthogonal
      (Submodule.projection_apply_mem _ _)) _ (b _).property
  have hPP : ∀ x ∈ P, ∀ y ∈ P, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    rw [hAP hx, hAP hy, mapJ_apply_mapJ hJ₀ hJ₁ hb hx hy,
      isIsotropic_iff.1 (hJ₀.invariant.isIsotropic_map (isIsotropic_inf_orthogonal W₀)) x hx y hy]
  have hPE : ∀ x ∈ P, ∀ y ∈ E, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    rw [hE x (Submodule.mem_sup_right hx) y hy, hAP hx, hAE hy]
    exact apply_mapJ_eq_zero hJ₀ hJ₁ (b := b) x (Submodule.projection_apply_mem _ _)
  have hEE : ∀ x ∈ E, ∀ y ∈ E, ω₁ (A x) (A y) = ω₀ x y := fun x hx y hy => by
    rw [hAE hx, hAE hy]
    exact projection_apply_projection hJ₁ hL hLω hx hy
  have decomp : ∀ z : V₀, ∃ w ∈ W₀, ∃ x ∈ P, ∃ e ∈ E, z = w + x + e := fun z => by
    obtain ⟨s, e, hs, he, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.1 hJ₀.isCompl_sup_map_normalComplement.codisjoint z
    obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.1 hs
    exact ⟨w, hw, x, hx, e, he, rfl⟩
  obtain ⟨w, hw, x, hx, e, he, rfl⟩ := decomp v
  obtain ⟨w', hw', x', hx', e', he', rfl⟩ := decomp v'
  simp only [map_add, LinearMap.add_apply]
  linear_combination hWW w hw w' hw' + hWP w hw x' hx' + hWE w hw e' he' +
    swap x w' (hWP w' hw' x hx) + hPP x hx x' hx' + hPE x hx e' he' +
    swap e w' (hWE w' hw' e he) + swap e x' (hPE x' hx' e he) + hEE e he e' he'

private theorem extendAlongMap_injective (hb : ∀ x y : W₀, ω₁ (b x) (b y) = ω₀ x y)
    (hL : ∀ v ∈ ω₀.orthogonal W₀, L v ∈ ω₁.orthogonal W₁)
    (hLω : ∀ v ∈ ω₀.orthogonal W₀, ∀ w ∈ ω₀.orthogonal W₀, ω₁ (L v) (L w) = ω₀ v w) :
    Function.Injective (extendAlongMap hJ₀ hJ₁ b L) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  refine ω₀.separatingLeft v fun y => ?_
  have h := extendAlongMap_apply_apply hJ₀ hJ₁ hb hL hLω v y
  rw [LinearMap.mem_ker.1 hv] at h
  simpa using h.symm

end Construction

section Extension

variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
  [FiniteDimensional ℝ V₀] [FiniteDimensional ℝ V₁]
  {ω₀ : SymplecticForm V₀} {ω₁ : SymplecticForm V₁}
  {J₀ : AlmostComplexStructure V₀} {J₁ : AlmostComplexStructure V₁}
  (hJ₀ : ω₀.Compatible J₀) (hJ₁ : ω₁.Compatible J₁)
  {W₀ : Submodule ℝ V₀} {W₁ : Submodule ℝ V₁} (b : W₀ ≃ₗ[ℝ] W₁)
  (hb : ∀ x y : W₀, ω₁ (b x) (b y) = ω₀ x y) (L : V₀ →ₗ[ℝ] V₁)
  (hL : ∀ v ∈ ω₀.orthogonal W₀, L v ∈ ω₁.orthogonal W₁)
  (hLω : ∀ v ∈ ω₀.orthogonal W₀, ∀ w ∈ ω₀.orthogonal W₀, ω₁ (L v) (L w) = ω₀ v w)
  (hdim : finrank ℝ V₀ = finrank ℝ V₁)

/-- **The explicit linear symplectic extension.** For compatible pairs `(ω₀, J₀)` on `V₀` and
`(ω₁, J₁)` on `V₁` of equal dimension, subspaces `W₀`, `W₁` with radicals `Kⱼ = Wⱼ ∩ Wⱼ^ω`, an
isomorphism `b : W₀ ≃ W₁` preserving the restricted forms, and a linear map `L` mapping `W₀^ω`
into `W₁^ω` and preserving `ω` there, this is the linear symplectomorphism `V₀ ≃ V₁`
(`TauCeti.SymplecticForm.Compatible.isSymplectomorphism_extendAlong`) which is

* `b` on `W₀` (`TauCeti.SymplecticForm.Compatible.extendAlong_apply_coe`);
* on the normal complement `E₀`, `L` followed by the projection onto `E₁` along `W₁ ⊕ J₁ K₁`
  (`TauCeti.SymplecticForm.Compatible.extendAlong_apply_of_mem_normalComplement`);
* on `J₀ K₀`, `x ↦ u - ½ b κ`, where `u` is the vector with `ω₁(u, y) = ω₀(x, b⁻¹ p y)` for
  all `y`, `p` the projection onto `W₁` along `J₁ K₁ ⊕ E₁`, and `κ` the `g₀`-orthogonal projection
  of `b⁻¹ p u` onto `K₀`; the correction makes the image of `J₀ K₀` isotropic.

Its formula is `TauCeti.SymplecticForm.Compatible.extendAlong_def`. -/
noncomputable def Compatible.extendAlong : V₀ ≃ₗ[ℝ] V₁ :=
  (extendAlongMap hJ₀ hJ₁ b L).linearEquivOfInjective
    (extendAlongMap_injective hJ₀ hJ₁ hb hL hLω) hdim

/-- The formula for `TauCeti.SymplecticForm.Compatible.extendAlong`. -/
theorem Compatible.extendAlong_def :
    (hJ₀.extendAlong hJ₁ b hb L hL hLω hdim : V₀ →ₗ[ℝ] V₁) =
      W₁.subtype ∘ₗ b.toLinearMap ∘ₗ W₀.projectionOnto _ hJ₀.isCompl_map_sup_normalComplement +
      ((ω₁.toBilinForm.toDual ω₁.nondegenerate).symm.toLinearMap ∘ₗ
          (W₀.subtype ∘ₗ b.symm.toLinearMap ∘ₗ
            W₁.projectionOnto _ hJ₁.isCompl_map_sup_normalComplement).dualMap ∘ₗ
          ω₀.toBilinForm -
        (2⁻¹ : ℝ) • (W₁.subtype ∘ₗ b.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
          (W₀ ⊓ ω₀.orthogonal W₀).projectionOnto _
            (hJ₀.isCompl_orthogonal_associatedBilinForm _) ∘ₗ
          (W₀.subtype ∘ₗ b.symm.toLinearMap ∘ₗ
            W₁.projectionOnto _ hJ₁.isCompl_map_sup_normalComplement) ∘ₗ
          (ω₁.toBilinForm.toDual ω₁.nondegenerate).symm.toLinearMap ∘ₗ
          (W₀.subtype ∘ₗ b.symm.toLinearMap ∘ₗ
            W₁.projectionOnto _ hJ₁.isCompl_map_sup_normalComplement).dualMap ∘ₗ
          ω₀.toBilinForm)) ∘ₗ
        ((W₀ ⊓ ω₀.orthogonal W₀).map J₀.toLinearMap).projection _
          hJ₀.isCompl_map_self_sup_normalComplement +
      (ω₁.normalComplement J₁ W₁).projection _ hJ₁.isCompl_sup_map_normalComplement.symm ∘ₗ
        L ∘ₗ (ω₀.normalComplement J₀ W₀).projection _
          hJ₀.isCompl_sup_map_normalComplement.symm :=
  (rfl)

/-- The extension is a linear symplectomorphism. -/
theorem Compatible.isSymplectomorphism_extendAlong :
    IsSymplectomorphism ω₀ ω₁ (hJ₀.extendAlong hJ₁ b hb L hL hLω hdim) :=
  isSymplectomorphism_iff.2 (extendAlongMap_apply_apply hJ₀ hJ₁ hb hL hLω)

/-- On `W₀`, the extension is `b`. -/
@[simp]
theorem Compatible.extendAlong_apply_coe (w : W₀) :
    hJ₀.extendAlong hJ₁ b hb L hL hLω hdim w = b w :=
  extendAlongMap_apply_coe hJ₀ hJ₁ (b := b) (L := L) w

/-- On the normal complement `E₀`, the extension is `L` followed by the projection onto `E₁`
along `W₁ ⊕ J₁ K₁`. -/
theorem Compatible.extendAlong_apply_of_mem_normalComplement {e : V₀}
    (he : e ∈ ω₀.normalComplement J₀ W₀) :
    hJ₀.extendAlong hJ₁ b hb L hL hLω hdim e = (ω₁.normalComplement J₁ W₁).projection _
      hJ₁.isCompl_sup_map_normalComplement.symm (L e) :=
  extendAlongMap_apply_of_mem_normalComplement hJ₀ hJ₁ (b := b) (L := L) he

/-- The extension induces the same map as `L` on the reduced spaces: `A v - L v ∈ W₁` for
`v ∈ W₀^ω`. -/
theorem Compatible.extendAlong_sub_mem {v : V₀} (hv : v ∈ ω₀.orthogonal W₀) :
    hJ₀.extendAlong hJ₁ b hb L hL hLω hdim v - L v ∈ W₁ := by
  have hdim' : finrank ℝ (ω₁.ReducedSpace (ω₁.orthogonal W₁)) ≤
      finrank ℝ (ω₀.ReducedSpace (ω₀.orthogonal W₀)) := by
    have h₀ := ω₀.finrank_reducedSpace_orthogonal_add W₀
    have h₁ := ω₁.finrank_reducedSpace_orthogonal_add W₁
    have h₂ := b.finrank_eq
    -- Tau Ceti's lemma is stated with `Submodule.orthogonalBilin`, which `ω.orthogonal` unfolds to
    have h₃ := Submodule.finrank_inf_orthogonalBilin_eq_of_isometry
      (c := LinearMap.id (R := ℝ) (M := ℝ)) Function.injective_id b fun x y => by
        rw [LinearMap.id_apply, toBilinForm_apply, toBilinForm_apply, hb]
    rw [← LinearMap.BilinForm.orthogonal, ← LinearMap.BilinForm.orthogonal, ← orthogonal_def,
      ← orthogonal_def] at h₃
    omega
  obtain ⟨k, hk, e, he, rfl⟩ := Submodule.mem_sup.1 (hJ₀.inf_sup_normalComplement.ge hv)
  have hLk : L k ∈ W₁ := by
    have h := ker_restrict_le_comap_of_forall_apply_eq hL hLω hdim'
      (x := ⟨k, hk.2⟩) ((mem_ker_restrict_iff _ _).2 (by rw [orthogonal_orthogonal]; exact hk.1))
    rw [Submodule.mem_comap, LinearMap.restrict_apply, mem_ker_restrict_iff,
      orthogonal_orthogonal] at h
    exact h
  rw [map_add, map_add, add_sub_add_comm]
  refine W₁.add_mem (W₁.sub_mem ?_ hLk) ?_
  · have h := hJ₀.extendAlong_apply_coe hJ₁ b hb L hL hLω hdim ⟨k, hk.1⟩
    rw [Submodule.coe_mk] at h
    rw [h]
    exact (b _).property
  · rw [hJ₀.extendAlong_apply_of_mem_normalComplement hJ₁ b hb L hL hLω hdim he]
    exact (projection_sub_mem hJ₁ hL he).1

end Extension

end TauCeti.SymplecticForm

end
