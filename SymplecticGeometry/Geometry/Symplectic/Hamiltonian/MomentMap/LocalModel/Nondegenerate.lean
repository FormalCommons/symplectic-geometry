/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent

import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.LinearNormalForm
import TauCeti.Geometry.Symplectic.Manifold.Flat
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens

/-!
# The local model's descended form is symplectic near the zero section

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `Y = G ×_K (A × V)`, and `ω = D.descendedForm` the descent of `D.form` to `Y`
(`LocalModel/Descent.lean`). This file shows that `ω` is a symplectic form on a `G`-invariant
open neighbourhood of the zero section `{[g, 0] | g ∈ G}`.

* At `[1, 0]`, every tangent vector is `dπ u` for a tangent vector `u` of `G × (A × V)` at
  `(1, 0, 0)`, since `π : (g, p) ↦ [g, p]` is a submersion. If `dπ u` pairs to zero with every
  vector, then `u` lies in the kernel of `D.form` at `(1, 0, 0)`, which is `𝔥 × 0`
  (`SymplecticGeometry.LocalModelData.forall_eval₂_form_one_zero_eq_zero_iff`), and this is the
  kernel of `dπ` there (`SymplecticGeometry.LocalModelData.mem_ker_mfderiv_mk_one_zero_iff`). So
  `ω` is nondegenerate at `[1, 0]`.
* The action of `G` on `Y` is smooth (Tau Ceti's
  `TauCeti.BalancedProduct.contMDiffSMul_rightTranslation`) and preserves `ω`, so `ω` is
  nondegenerate at `k • y` exactly when it is at `y`
  (`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_smul_iff`). Since `[g, 0] = g • [1, 0]`, it is
  nondegenerate along the zero section.
* The set where `ω` is nondegenerate is open
  (`TauCeti.SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt`) and `G`-invariant, and `ω`
  restricts to a symplectic form on it
  (`TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtypeVal`).

The last step follows the proof of Tau Ceti's
`TauCeti.CotangentBundle.exists_opens_isNondegenerate_mpullback_coisotropicModelForm`.

## Main results

* `SymplecticGeometry.LocalModelData.nondegenerate_bilinFormAt_descendedForm_mk_one_zero`: `ω` is
  nondegenerate at `[1, 0]`.
* `SymplecticGeometry.LocalModelData.nondegenerate_bilinFormAt_descendedForm_smul_iff`: `ω` is
  nondegenerate at `k • y` exactly when it is at `y`.
* `SymplecticGeometry.LocalModelData.nondegenerate_bilinFormAt_descendedForm_mk_zero`: `ω` is
  nondegenerate at every point `[g, 0]` of the zero section.
* `SymplecticGeometry.LocalModelData.exists_opens_isSymplectic_mpullback_descendedForm`: `ω`
  restricts to a symplectic form on a `G`-invariant open set containing the zero section.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.Lie TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The descended form is nondegenerate at `[1, 0]`.** The descended form of the local model on
`G ×_K (A × V)` is nondegenerate at the point `[1, 0, 0]` of the zero section. -/
theorem nondegenerate_bilinFormAt_descendedForm_mk_one_zero :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    (D.descendedForm.bilinFormAt
      (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V)))).Nondegenerate := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have hπ := BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  set x : G × (A × V) := ((1 : G), ((0 : A), (0 : V)))
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (SmoothForm.isAlt_bilinFormAt D.descendedForm _).isRefl).2 fun v hv ↦ ?_
  -- `v = dπ u`, and `u` pairs to zero with every vector, so it is vertical.
  obtain ⟨u, rfl⟩ := hπ.surjective_mfderiv (x := x) (by simp) v
  have hu : ∀ u', D.form.eval₂ x u u' = 0 := fun u' ↦ by
    rw [← D.eval₂_descendedForm_mfderiv x u u', ← SmoothForm.bilinFormAt_apply]
    exact hv _
  exact (D.mem_ker_mfderiv_mk_one_zero_iff u).2 ((D.forall_eval₂_form_one_zero_eq_zero_iff u).1 hu)

/-- **`G` moves nondegeneracy of the descended form.** For `k ∈ G`, the descended form of the
local model is nondegenerate at `k • y` exactly when it is nondegenerate at `y`. -/
theorem nondegenerate_bilinFormAt_descendedForm_smul_iff (k : G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ y : BalancedProduct K K.RightTranslation (A × V),
      (D.descendedForm.bilinFormAt (k • y)).Nondegenerate ↔
        (D.descendedForm.bilinFormAt y).Nondegenerate := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := ContMDiffSMul.contMDiffConstSMul I (n := ∞) (G := G)
    (I' := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))))
    (M := BalancedProduct K K.RightTranslation (A × V))
  have hk := ContMDiffConstSMul.contMDiff_const_smul
    (I := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))) (n := ∞)
    (M := BalancedProduct K K.RightTranslation (A × V)) k
  exact SmoothTwoForm.nondegenerate_bilinFormAt_smul_iff (g := k)
    (D.mpullback_smul_descendedForm k hk)

/-- **The descended form is nondegenerate along the zero section**: at every point `[g, 0, 0]`. -/
theorem nondegenerate_bilinFormAt_descendedForm_mk_zero (g : G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    (D.descendedForm.bilinFormAt
      (BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V)))).Nondegenerate := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  rw [← mul_one g, ← BalancedProduct.smul_mk_toRightTranslation,
    D.nondegenerate_bilinFormAt_descendedForm_smul_iff]
  exact D.nondegenerate_bilinFormAt_descendedForm_mk_one_zero

/-- **The descended form is symplectic near the zero section.** There is an open set `U` of
`G ×_K (A × V)` that contains every point `[g, 0, 0]` of the zero section and is invariant under
the action of `G`, on which the descended form of the local model restricts to a symplectic
form. -/
theorem exists_opens_isSymplectic_mpullback_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∃ U : TopologicalSpace.Opens (BalancedProduct K K.RightTranslation (A × V)),
      (∀ g : G, BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V)) ∈ U) ∧
      (∀ (k : G) (y), y ∈ U → k • y ∈ U) ∧
      SmoothTwoForm.IsSymplectic
        (SmoothForm.mpullback (Subtype.val : U → _) contMDiff_subtypeVal D.descendedForm) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  -- `U` is the set of points at which the descended form is nondegenerate.
  exact ⟨⟨_, SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt D.descendedForm⟩,
    D.nondegenerate_bilinFormAt_descendedForm_mk_zero,
    fun k y hy ↦ (D.nondegenerate_bilinFormAt_descendedForm_smul_iff k y).2 hy,
    D.isClosed_descendedForm.isSymplectic_mpullback_subtypeVal fun _ hy ↦ hy⟩

end LocalModelData

end SymplecticGeometry

end
