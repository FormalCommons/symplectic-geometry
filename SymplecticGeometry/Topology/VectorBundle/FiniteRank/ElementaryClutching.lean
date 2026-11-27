/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.CategoryTheory.Preadditive.IdAdd
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.NearbyClutching
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# Elementary operations do not change a clutching

Let `E` be a finite-rank core over a paracompact R₁ space `X`, with fibres over a complete normed
`ℝ`-algebra `𝕜`, let `f` be an automorphism of its pullback to `X × Circle`, and let `n` be an
endomorphism of that pullback with `n ≫ n = 0`. Then `𝟙 + n` is an automorphism
(`CategoryTheory.Preadditive.idAddIso`), and composing `f` with it on either side does not change
the clutching of `E` up to isomorphism.

The segment from `f` to `(𝟙 + n) ≫ f` has fibre maps `f ∘ (1 + t n)` for `t ∈ [0, 1]`, which are
invertible with inverse `(1 - t n) ∘ f⁻¹`, so it is a homotopy through automorphisms and
`TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic` applies; the same holds on the
other side. This is the step of [Hatcher2017, §2.1] that elementary row and column operations on
a clutching function do not change the clutched bundle, used there to make a polynomial clutching
function linear.

The row case follows from the column case, since `f ≪≫ (𝟙 + n)` is `(𝟙 + f n f⁻¹) ≪≫ f`
(`CategoryTheory.Preadditive.trans_idAddIso`).

For a Whitney sum `A ⊕ D`, the elementary automorphisms are the block unitriangular ones of Tau
Ceti's bicone `whitneyBicone A D`: `(whitneyBicone A D).unipotentUpper c` for `c : A ⟶ D`, which
is `𝟙 + whitneyFst ≫ c ≫ whitneyInr`, and `(whitneyBicone A D).unipotentLower c` for
`c : D ⟶ A`, which is `𝟙 + whitneySnd ≫ c ≫ whitneyInl`
(`CategoryTheory.Limits.BinaryBicone.unipotentUpper` and `unipotentLower`).

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.isUnit_one_add_smul_fiberMap`: for `n ≫ n = 0`, the fibre maps
  of `1 + s n` are invertible;
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_idAddIso_trans` and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_trans_idAddIso`: the clutchings by
  `(𝟙 + n) ≫ f` and by `f ≫ (𝟙 + n)` are isomorphic to the clutching by `f`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (the reduction of polynomial
  clutching functions to linear ones).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Preadditive

namespace TauCeti.FiniteRankBundleCore

/-! ### Elementary operations on clutching functions -/

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  {E : FiniteRankBundleCore 𝕜 X}

/-- For an endomorphism `n` of a finite-rank core with `n ≫ n = 0`, the map `1 + s n` on each fibre
is invertible, for every scalar `s`. -/
theorem isUnit_one_add_smul_fiberMap {B : Type*} [TopologicalSpace B]
    {A : FiniteRankBundleCore 𝕜 B} (n : A ⟶ A) (hn : n ≫ n = 0) (x : B) (s : 𝕜) :
    IsUnit (1 + s • n.fiberMap x) := by
  refine IsNilpotent.isUnit_one_add ⟨2, ?_⟩
  rw [pow_two, smul_mul_smul_comm, ContinuousLinearMap.mul_def, ← fiberMap_comp, hn,
    VectorBundleCore.CoordinateHom.fiberMap_zero, smul_zero]

variable [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]

/-- **Elementary column operations do not change a clutching.** Let `X` be paracompact and R₁,
`f` an automorphism of the pullback of `E` to `X × Circle`, and `n` an endomorphism of it with
`n ≫ n = 0`. Then the clutching of `E` by `(𝟙 + n) ≫ f` is isomorphic to its clutching by
`f`. -/
theorem nonempty_iso_clutching_idAddIso_trans [ParacompactSpace X] [R1Space X]
    (f : E.circlePullback ≅ E.circlePullback) (n : E.circlePullback ⟶ E.circlePullback)
    (hn : n ≫ n = 0) :
    Nonempty (E.clutching (idAddIso n hn ≪≫ f) ≅ E.clutching f) := by
  have : IsIso (segmentHom f.hom (idAddIso n hn ≪≫ f).hom) := by
    refine (isIso_iff_bijective _).2 fun b ↦ ?_
    -- At time `s`, the fibre map is `f ∘ (1 + s n)`.
    have he : (segmentHom f.hom (idAddIso n hn ≪≫ f).hom).fiberMap b =
        (f.hom.fiberMap (b.1.1, b.2)).comp
          (.id 𝕜 _ + algebraMap ℝ 𝕜 b.1.2 • n.fiberMap (b.1.1, b.2)) := by
      rw [fiberMap_segmentHom, Iso.trans_hom, fiberMap_comp, idAddIso_hom, fiberMap_add,
        fiberMap_id]
      ext v : 1
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_add, map_smul]
      module
    rw [he, ContinuousLinearMap.coe_comp, ← toContinuousLinearMap_isoFiberEquiv,
      ← ContinuousLinearMap.one_def]
    exact (isoFiberEquiv f _).bijective.comp (ContinuousLinearEquiv.unitsEquiv 𝕜 _
      (isUnit_one_add_smul_fiberMap n hn _ _).unit).bijective
  exact (E.nonempty_iso_clutching_of_homotopic (asIso (segmentHom f.hom (idAddIso n hn ≪≫ f).hom))
    (fiberMap_segmentHom_zero _ _) (fiberMap_segmentHom_one _ _)).map Iso.symm

/-- **Elementary row operations do not change a clutching.** Let `X` be paracompact and R₁,
`f` an automorphism of the pullback of `E` to `X × Circle`, and `n` an endomorphism of it with
`n ≫ n = 0`. Then the clutching of `E` by `f ≫ (𝟙 + n)` is isomorphic to its clutching by
`f`. -/
theorem nonempty_iso_clutching_trans_idAddIso [ParacompactSpace X] [R1Space X]
    (f : E.circlePullback ≅ E.circlePullback) (n : E.circlePullback ⟶ E.circlePullback)
    (hn : n ≫ n = 0) :
    Nonempty (E.clutching (f ≪≫ idAddIso n hn) ≅ E.clutching f) := by
  rw [trans_idAddIso]
  exact nonempty_iso_clutching_idAddIso_trans _ _ _

end TauCeti.FiniteRankBundleCore

end
