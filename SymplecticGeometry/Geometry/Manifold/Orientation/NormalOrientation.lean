/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Analysis.Normed.Module.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.LinearAlgebra.Orientation.Exact.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Exact

/-!
# The normal orientation induced by orientations of a submanifold and its ambient manifold

Let `f : Z → X` be a smooth embedding with intrinsic normal bundle `ν` (Tau Ceti's
`TauCeti.SmoothEmbedding.NormalSpace`, with model fibre `P`). At each `z : Z` the differential and
the normal class map form the short exact sequence `0 → T_z Z → T_{f z} X → ν_z → 0`
(`TauCeti.SmoothEmbedding.exact_mfderiv_normalClass`). Orientations `oZ` of `Z` and `oX` of `X`
therefore orient each normal space `ν_z` by Tau Ceti's cokernel orientation
`Orientation.cokerOfExact`: the orientation of `ν_z` which, preceded by that of `T_z Z`, gives that
of `T_{f z} X`. In other words, a positive basis of `T_z Z` followed by lifts of a positive basis
of `ν_z` is a positive basis of `T_{f z} X`, with the tangent directions first and no sign
correction.

These fibre orientations vary continuously, and so form an orientation of the normal bundle,
`TauCeti.SmoothEmbedding.normalOrientation`. In a chart of the normal bundle at `z₀`, which by
Tau Ceti's `TauCeti.SmoothEmbedding.exists_normalSpaceTrivialization_symm_apply` lifts the normal
coordinates through a fixed linear map `B : P →L[ℝ] V`, the sequence at `z` is isomorphic to the
split sequence `E → E × P → P`, by the map `(u, w) ↦ D f(z) u + B w` read in the tangent charts
at `z₀` and `f z₀`. This map depends continuously on `z`, so it transports orientations locally
constantly (`Orientation.eventually_map_eq_map_of_continuousAt`), and Tau Ceti's naturality
`Orientation.map_cokerOfExact` reads the normal orientation in the chart as a cokernel orientation
on the model, which is then locally constant. The structure of the argument, reading a fibrewise
linear-algebra orientation in local frames and trivializations, follows Tau Ceti's
`TauCeti.VectorBundleOrientation.transverse`.

For the diagonal of an oriented manifold, Tau Ceti's
`TauCeti.SmoothEmbedding.diagonalNormalOrientation` also puts the tangent directions first
(`TauCeti.SmoothEmbedding.diagonalTangentNormalEquiv_map_orientation`).

## Main definitions

* `TauCeti.SmoothEmbedding.normalOrientation`: the orientation of the normal bundle of an
  embedding induced by orientations of the source and the target.

## Main results

* `TauCeti.SmoothEmbedding.normalOrientation_apply`: on each fibre it is the cokernel
  orientation of the tangent sequence.
* `TauCeti.SmoothEmbedding.ofExact_normalOrientation`,
  `TauCeti.SmoothEmbedding.normalOrientation_eq_iff`: the orientation of the submanifold followed
  by the normal orientation gives the orientation of the ambient manifold, and this characterizes
  it.
* `TauCeti.SmoothEmbedding.normalOrientation_neg_left`,
  `TauCeti.SmoothEmbedding.normalOrientation_neg_right`: reversing either orientation reverses
  the normal orientation.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V P H G Z X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I 1 Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J 1 X]
  {n : ℕ∞ω} {m : ℕ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [IsManifold I 1 Z] [IsManifold J 1 X] in
/-- The normal fibres have the dimension of the model fibre. -/
private theorem finrank_normalSpace_eq (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (z : Z) :
    finrank ℝ (f.NormalSpace z hn) = finrank ℝ P := by
  rw [f.finrank_normalSpace z hn, hdim, TauCeti.finrank_tangentSpace,
    TauCeti.finrank_tangentSpace]

/-- The orientation of the normal space at `z` induced by `oX` and `oZ`: the cokernel orientation
of `0 → T_z Z → T_{f z} X → ν_z → 0`. -/
private def normalOrientationAt (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (oX : Manifold.Orientation J X (Fin (m + finrank ℝ P))) (oZ : Manifold.Orientation I Z (Fin m))
    (z : Z) : Orientation ℝ (f.NormalSpace z hn) (Fin (finrank ℝ P)) :=
  haveI := f.finiteDimensional_tangentSpace z hn
  Orientation.cokerOfExact (f.isImmersion.mfderiv_injective hn z)
    (f.exact_mfderiv_normalClass z hn) (f.normalClass_surjective z hn) (oZ.orientationAt z)
    (oX.orientationAt (f z)) (by simpa using oZ.finrank_tangentSpace_eq z)
    (finrank_normalSpace_eq f hn hdim z)

/-- In a chart of the normal bundle whose inverse lifts normal coordinates `w` to the tangent
vectors with coordinates `B w` in the chart at `f z₀`, the map `(u, w) ↦ D f(z) u + B w`, read in
the tangent charts at `z₀` and `f z₀`, is a linear equivalence `E × P ≃ T_{f z} X`. -/
private theorem exists_linearEquiv_mfderiv_add (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {z₀ z : Z} (B : P →L[ℝ] V)
    (hz : z ∈ (f.normalSpaceTrivialization hn hdim z₀).baseSet)
    (hzS : z ∈ (trivializationAt E (TangentSpace I) z₀).baseSet)
    (hzT : f z ∈ (trivializationAt V (TangentSpace J) (f z₀)).baseSet)
    (hsymm : ∀ w, (f.normalSpaceTrivialization hn hdim z₀).symm z w =
      f.normalClass z hn ((trivializationAt V (TangentSpace J) (f z₀)).symm (f z) (B w))) :
    ∃ D : (E × P) ≃ₗ[ℝ] TangentSpace J (f z), ∀ p : E × P, D p =
      mfderiv I J (f : Z → X) z
          (((trivializationAt E (TangentSpace I) z₀).linearEquivAt ℝ z hzS).symm p.1) +
        ((trivializationAt V (TangentSpace J) (f z₀)).linearEquivAt ℝ (f z) hzT).symm (B p.2) := by
  set N := f.normalSpaceTrivialization hn hdim z₀
  set S := trivializationAt E (TangentSpace I) z₀
  set T := trivializationAt V (TangentSpace J) (f z₀)
  let D : (E × P) →ₗ[ℝ] TangentSpace J (f z) :=
    LinearMap.coprod ((mfderiv I J (f : Z → X) z).toLinearMap ∘ₗ
        (S.linearEquivAt ℝ z hzS).symm.toLinearMap)
      ((T.linearEquivAt ℝ (f z) hzT).symm.toLinearMap ∘ₗ B.toLinearMap)
  have hDnormal (p : E × P) : f.normalClass z hn (D p) = (N.linearEquivAt ℝ z hz).symm p.2 := by
    simp [D, Trivialization.linearEquivAt_symm_apply, hsymm]
  have hDinj : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hw : w = 0 := (LinearEquiv.map_eq_zero_iff _).1
      ((hDnormal (u, w)).symm.trans (by rw [hp, map_zero]))
    subst hw
    have hu : mfderiv I J (f : Z → X) z ((S.linearEquivAt ℝ z hzS).symm u) = 0 := by
      rw [← hp]
      simp only [D, LinearMap.coprod_apply, LinearMap.comp_apply, map_zero, add_zero]
      rfl
    have := f.isImmersion.mfderiv_injective hn z (hu.trans (map_zero _).symm)
    simpa only [Prod.mk_eq_zero, and_true] using (LinearEquiv.map_eq_zero_iff _).1 this
  have : FiniteDimensional ℝ (TangentSpace J (f z)) := inferInstanceAs (FiniteDimensional ℝ V)
  have hdimV : finrank ℝ (E × P) = finrank ℝ (TangentSpace J (f z)) := by
    have h := f.finrank_normalSpace_add_finrank z hn
    rw [finrank_normalSpace_eq f hn hdim z, TauCeti.finrank_tangentSpace,
      TauCeti.finrank_tangentSpace] at h
    rw [finrank_prod, TauCeti.finrank_tangentSpace]
    omega
  exact ⟨D.linearEquivOfInjective hDinj hdimV, fun p ↦ rfl⟩

/-- **Local constancy of the induced normal orientations.** Read in the chart of the normal bundle
at `z₀`, the orientations `normalOrientationAt f hn hdim oX oZ z` are constant near `z₀`. -/
private theorem eventually_mapOrientation_normalOrientationAt (f : SmoothEmbedding I J n Z X)
    (hn : n ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (oX : Manifold.Orientation J X (Fin (m + finrank ℝ P))) (oZ : Manifold.Orientation I Z (Fin m))
    (z₀ : Z) :
    ∀ᶠ z in 𝓝 z₀, ∀ hz : z ∈ (f.normalSpaceTrivialization hn hdim z₀).baseSet,
      (f.normalSpaceTrivialization hn hdim z₀).mapOrientation (Fin (finrank ℝ P)) hz
          (normalOrientationAt f hn hdim oX oZ z) =
        (f.normalSpaceTrivialization hn hdim z₀).mapOrientation (Fin (finrank ℝ P))
          (f.mem_normalSpaceTrivialization_baseSet hn hdim z₀)
          (normalOrientationAt f hn hdim oX oZ z₀) := by
  classical
  obtain ⟨B, hsub, hsymm⟩ := f.exists_normalSpaceTrivialization_symm_apply hn hdim z₀
  set N := f.normalSpaceTrivialization hn hdim z₀
  set S := trivializationAt E (TangentSpace I) z₀
  set T := trivializationAt V (TangentSpace J) (f z₀)
  have hN₀ : z₀ ∈ N.baseSet := f.mem_normalSpaceTrivialization_baseSet hn hdim z₀
  have hS (z : Z) (hz : z ∈ N.baseSet) : z ∈ S.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hsub hz).1
  have hT (z : Z) (hz : z ∈ N.baseSet) : f z ∈ T.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hsub hz).2
  have hmE : finrank ℝ E = m := by simpa using oZ.card_eq.symm
  -- The derivative in the tangent charts at `z₀` and `f z₀` is continuous at `z₀`.
  let c : Z → E →L[ℝ] V :=
    inTangentCoordinates I J (_root_.id : Z → Z) (f : Z → X) (mfderiv I J (f : Z → X)) z₀
  have hc : ContinuousAt c z₀ :=
    (f.contMDiff.contMDiffAt.mfderiv_const (m := 0)
      (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn)).continuousAt
  have hcz (z : Z) (hz : z ∈ N.baseSet) (u : E) :
      c z u = T.linearEquivAt ℝ (f z) (hT z hz)
        (mfderiv I J (f : Z → X) z ((S.linearEquivAt ℝ z (hS z hz)).symm u)) := by
    simp only [c, inTangentCoordinates, _root_.id_eq]
    rw [ContinuousLinearMap.inCoordinates_eq (hS z hz) (hT z hz)]
    simp [Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_symm_apply]
    rfl
  -- The splitting `(u, w) ↦ D f(z) u + B w` of the tangent sequence at `z`.
  have hsplit (z : Z) (hz : z ∈ N.baseSet) := exists_linearEquiv_mfderiv_add f hn hdim B hz
    (hS z hz) (hT z hz) (hsymm z hz)
  let De (z : Z) (hz : z ∈ N.baseSet) : (E × P) ≃ₗ[ℝ] TangentSpace J (f z) :=
    (hsplit z hz).choose
  have hDe (z : Z) (hz : z ∈ N.baseSet) (p : E × P) : De z hz p =
      mfderiv I J (f : Z → X) z ((S.linearEquivAt ℝ z (hS z hz)).symm p.1) +
        (T.linearEquivAt ℝ (f z) (hT z hz)).symm (B p.2) :=
    (hsplit z hz).choose_spec p
  have hDnormal (z : Z) (hz : z ∈ N.baseSet) (p : E × P) :
      f.normalClass z hn (De z hz p) = (N.linearEquivAt ℝ z hz).symm p.2 := by
    simp [hDe z hz, Trivialization.linearEquivAt_symm_apply, hsymm z hz]
  -- The splitting read in the tangent chart at `f z₀`.
  let G (z : Z) (hz : z ∈ N.baseSet) : (E × P) ≃L[ℝ] V :=
    ((De z hz).trans (T.linearEquivAt ℝ (f z) (hT z hz))).toContinuousLinearEquiv
  let L (z : Z) : (E × P) →L[ℝ] V :=
    (c z).comp (ContinuousLinearMap.fst ℝ E P) + B.comp (ContinuousLinearMap.snd ℝ E P)
  have hL : ContinuousAt L z₀ := (hc.clm_comp continuousAt_const).add continuousAt_const
  have hG (z : Z) (hz : z ∈ N.baseSet) : (G z hz : (E × P) →L[ℝ] V) = L z := by
    refine ContinuousLinearMap.ext fun p ↦ ?_
    obtain ⟨u, w⟩ := p
    simp only [G, L, ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_toContinuousLinearEquiv',
      LinearEquiv.trans_apply, hDe z hz, map_add, LinearEquiv.apply_symm_apply]
    rw [← hcz z hz]
    rfl
  have hP : finrank ℝ P = finrank ℝ P := rfl
  -- The normal orientation read in the chart is a cokernel orientation of the split sequence.
  have hread (z : Z) (hz : z ∈ N.baseSet) (a : Orientation ℝ E (Fin m))
      (b : Orientation ℝ (E × P) (Fin (m + finrank ℝ P)))
      (ha : S.mapOrientation (Fin m) (hS z hz) (oZ.orientationAt z) = a)
      (hb : Orientation.map _ (G z hz).toLinearEquiv b =
        T.mapOrientation _ (hT z hz) (oX.orientationAt (f z))) :
      N.mapOrientation (Fin (finrank ℝ P)) hz (normalOrientationAt f hn hdim oX oZ z) =
        Orientation.cokerOfExact LinearMap.inl_injective Function.Exact.inl_snd
          LinearMap.snd_surjective a b hmE hP := by
    have := f.finiteDimensional_tangentSpace z hn
    have ha' : Orientation.map (Fin m) (S.linearEquivAt ℝ z (hS z hz)).symm a =
        oZ.orientationAt z := by
      rw [← ha, Trivialization.mapOrientation_apply, ← Orientation.map_symm,
        Equiv.symm_apply_apply]
    have hb' : Orientation.map _ (De z hz) b = oX.orientationAt (f z) := by
      apply (T.mapOrientation (Fin (m + finrank ℝ P)) (hT z hz)).injective
      rw [← hb, Trivialization.mapOrientation_apply, ← Orientation.map_trans]
      rfl
    rw [Trivialization.mapOrientation_apply, ← Equiv.eq_symm_apply,
      Orientation.map_symm, Orientation.map_cokerOfExact _ _ _
        (f.isImmersion.mfderiv_injective hn z) (f.exact_mfderiv_normalClass z hn)
        (f.normalClass_surjective z hn)
        (S.linearEquivAt ℝ z (hS z hz)).symm (De z hz) (N.linearEquivAt ℝ z hz).symm
        (fun u ↦ by
          rw [hDe z hz]
          simp only [LinearMap.inl_apply, map_zero, add_zero]
          rfl)
        (fun p ↦ by rw [hDnormal z hz]; rfl), ha', hb']
    rfl
  -- The three readings are locally constant near `z₀`.
  set a₀ := S.mapOrientation (Fin m) (hS z₀ hN₀) (oZ.orientationAt z₀)
  set q₀ := T.mapOrientation (Fin (m + finrank ℝ P)) (hT z₀ hN₀) (oX.orientationAt (f z₀))
  obtain ⟨b₀, hb₀⟩ : ∃ b, Orientation.map _ (G z₀ hN₀).toLinearEquiv b = q₀ :=
    ⟨(Orientation.map _ (G z₀ hN₀).toLinearEquiv).symm q₀, Equiv.apply_symm_apply _ _⟩
  have hZ := oZ.toVectorBundleOrientation.eventually_mapOrientation_eq oZ.card_eq S (hS z₀ hN₀)
  have hX := (f.contMDiff.continuous.tendsto z₀).eventually
    (oX.toVectorBundleOrientation.eventually_mapOrientation_eq oX.card_eq T (hT z₀ hN₀))
  have hGev := Orientation.eventually_map_eq_map_of_continuousAt
    (by rw [Fintype.card_fin, finrank_prod, hmE]) b₀ (fun _ ↦ hL) (hG z₀ hN₀).symm
  filter_upwards [hZ, hX, hGev] with z hzZ hzX hzG hz
  simp only [Manifold.Orientation.toVectorBundleOrientation_apply] at hzZ hzX
  rw [hread z hz a₀ b₀ (hzZ (hS z hz)) ?_, hread z₀ hN₀ a₀ b₀ rfl ?_]
  · exact hb₀
  · rw [hzG (G z hz) (hG z hz), hb₀, hzX (hT z hz)]

/-- **The normal orientation induced by orientations of the ambient manifold and the
submanifold.** For a smooth embedding `f : Z → X`, orientations `oX` of `X` and `oZ` of `Z`
orient the normal bundle of `f`: the normal space at `z` carries the orientation which, preceded by
that of `T_z Z`, gives the orientation of `T_{f z} X` along `0 → T_z Z → T_{f z} X → ν_z → 0`
(`Orientation.cokerOfExact`). So a positive basis of `T_z Z`, followed by lifts of a positive
basis of `ν_z`, is a positive basis of `T_{f z} X`. -/
def normalOrientation (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (oX : Manifold.Orientation J X (Fin (m + finrank ℝ P)))
    (oZ : Manifold.Orientation I Z (Fin m)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    VectorBundleOrientation P (f.NormalSpace · hn) (Fin (finrank ℝ P)) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  haveI (z : Z) : MemTrivializationAtlas (f.normalSpaceTrivialization hn hdim z) :=
    ⟨(f.mem_normalSpaceFiberBundle_trivializationAtlas_iff hn hdim _).2 ⟨z, rfl⟩⟩
  VectorBundleOrientation.ofEventually (Fintype.card_fin _) (normalOrientationAt f hn hdim oX oZ)
    (f.normalSpaceTrivialization hn hdim) (f.mem_normalSpaceTrivialization_baseSet hn hdim)
    (eventually_mapOrientation_normalOrientationAt f hn hdim oX oZ)

variable (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
  (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
  (oX : Manifold.Orientation J X (Fin (m + finrank ℝ P))) (oZ : Manifold.Orientation I Z (Fin m))

/-- On the fibre over `z`, the induced normal orientation is the cokernel orientation of the
tangent sequence `0 → T_z Z → T_{f z} X → ν_z → 0` for the orientations of `T_z Z` and
`T_{f z} X`, with the subspace first and no sign.

The order is the one that the cap product with a fundamental class needs, where the normal
directions come first in local homology. By
`TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`, the homology cross
product of the local orientations of two linear orientations `ω` and `ω'` is
`(-1) ^ (dim · dim')` times the local orientation of `ω.prod ω'`. Exchanging the two blocks of a
basis costs the same sign, so the cross product with the normal factor first is the local
orientation of the linear orientation with the tangent factor first, which is this one. -/
theorem normalOrientation_apply (z : Z) (hm : finrank ℝ (TangentSpace I z) = m)
    (hr : finrank ℝ (f.NormalSpace z hn) = finrank ℝ P) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    normalOrientation f hn hdim oX oZ z =
      Orientation.cokerOfExact (f.isImmersion.mfderiv_injective hn z)
        (f.exact_mfderiv_normalClass z hn) (f.normalClass_surjective z hn) (oZ.orientationAt z)
        (oX.orientationAt (f z)) hm hr := by
  simp only [normalOrientation, VectorBundleOrientation.coe_ofEventually]
  rfl

/-- The orientation of `T_z Z` followed by the induced normal orientation of `ν_z` gives the
orientation of `T_{f z} X`. -/
@[simp]
theorem ofExact_normalOrientation (z : Z) (hm : finrank ℝ (TangentSpace I z) = m)
    (hr : finrank ℝ (f.NormalSpace z hn) = finrank ℝ P) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    Orientation.ofExact (f.isImmersion.mfderiv_injective hn z) (f.exact_mfderiv_normalClass z hn)
        (f.normalClass_surjective z hn) (oZ.orientationAt z)
        (normalOrientation f hn hdim oX oZ z) hm hr =
      oX.orientationAt (f z) := by
  rw [normalOrientation_apply f hn hdim oX oZ z hm hr]
  exact Orientation.ofExact_cokerOfExact _ _ _ _ _ hm hr

/-- **Characterization of the induced normal orientation.** An orientation `p` of `ν_z` is the
induced normal orientation exactly when the orientation of `T_z Z` followed by `p` gives the
orientation of `T_{f z} X`: a positive basis of `T_z Z` followed by lifts of a positive basis
for `p` is a positive basis of `T_{f z} X` (`Orientation.ofExact_orientation`). -/
theorem normalOrientation_eq_iff (z : Z)
    (p : Orientation ℝ (f.NormalSpace z hn) (Fin (finrank ℝ P)))
    (hm : finrank ℝ (TangentSpace I z) = m) (hr : finrank ℝ (f.NormalSpace z hn) = finrank ℝ P) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    normalOrientation f hn hdim oX oZ z = p ↔
      Orientation.ofExact (f.isImmersion.mfderiv_injective hn z)
        (f.exact_mfderiv_normalClass z hn) (f.normalClass_surjective z hn) (oZ.orientationAt z) p
        hm hr = oX.orientationAt (f z) := by
  rw [normalOrientation_apply f hn hdim oX oZ z hm hr]
  exact Orientation.cokerOfExact_eq_iff _ _ _ _ _ _ hm hr

/-- Reversing the orientation of the ambient manifold reverses the induced normal orientation. -/
@[simp]
theorem normalOrientation_neg_left :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    normalOrientation f hn hdim (-oX) oZ = -normalOrientation f hn hdim oX oZ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  ext z
  have hm : finrank ℝ (TangentSpace I z) = m := by simpa using oZ.finrank_tangentSpace_eq z
  have hr := finrank_normalSpace_eq f hn hdim z
  rw [VectorBundleOrientation.neg_apply, normalOrientation_apply f hn hdim _ oZ z hm hr,
    normalOrientation_apply f hn hdim oX oZ z hm hr, Manifold.Orientation.orientationAt_neg,
    Orientation.cokerOfExact_neg_right]

/-- Reversing the orientation of the submanifold reverses the induced normal orientation. -/
@[simp]
theorem normalOrientation_neg_right :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    normalOrientation f hn hdim oX (-oZ) = -normalOrientation f hn hdim oX oZ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  ext z
  have hm : finrank ℝ (TangentSpace I z) = m := by simpa using oZ.finrank_tangentSpace_eq z
  have hr := finrank_normalSpace_eq f hn hdim z
  rw [VectorBundleOrientation.neg_apply, normalOrientation_apply f hn hdim oX _ z hm hr,
    normalOrientation_apply f hn hdim oX oZ z hm hr, Manifold.Orientation.orientationAt_neg,
    Orientation.cokerOfExact_neg_left]

end TauCeti.SmoothEmbedding

end
