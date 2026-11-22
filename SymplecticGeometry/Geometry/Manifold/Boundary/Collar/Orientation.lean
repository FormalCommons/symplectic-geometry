/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Manifold.Orientation.Sign
import Mathlib.GroupTheory.Perm.Fin
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts

/-!
# A smooth collar and the induced boundary orientation

Let `M` be a manifold modelled on the half-space `𝓡∂ (n + 1)`, oriented by `o`, and let
`c : ∂M × [0, 1) → M` be a smooth collar (`TauCeti.SmoothCollar`). Orient `∂M` by Tau Ceti's
induced orientation `boundaryOrientation o`, with the outward vector first, the depth parameter
`[0, 1)` by its standard orientation `TauCeti.EuclideanHalfSpace.normalIioOpensOrientation 1`,
and `∂M × [0, 1)` by their product, with the boundary directions first. This file shows that
`c` has orientation sign `(-1) ^ (n + 1)` at every point: it preserves orientation when `n` is
odd, as for surfaces, and reverses it when `n` is even.

At a point `(y, 0)` of the zero slice, the derivative of `c` restricts on the first factor to
the derivative of the inclusion of the boundary, since `c (y, 0) = y`, and sends the unit vector
`∂ₜ` of the depth parameter to a vector whose normal coordinate is positive, so that `-dc(∂ₜ)`
points outward. The normal coordinate of `c` read in the chart at `y` is nonnegative and vanishes
at `(y, 0)`; Fermat's rule on the positive tangent cone of the model makes its derivative
nonnegative on `∂ₜ` and zero on the boundary directions, and invertibility of the derivative
excludes zero. This adapts the proof of `TauCeti.tangentCoordChange_normal_nonneg` and
`TauCeti.tangentCoordChange_normal_pos` from chart transitions to collars. The ordered image
basis `(dc(b₁), …, dc(bₙ), dc(∂ₜ))` differs from the outward-first basis
`(-dc(∂ₜ), dc(b₁), …, dc(bₙ))` of `boundaryOrientation_spec` by a cyclic permutation of sign
`(-1) ^ n` and one negation. The orientation sign is locally constant where the derivative is
invertible (`TauCeti.Manifold.Orientation.eventually_orientationSign_eq`) and each slice
`{y} × [0, 1)` is connected, so the sign at `(y, 0)` holds on the whole slice.

## Main definitions

* `TauCeti.EuclideanHalfSpace.normalIioOpensOrientation`: the standard orientation of the
  initial segment `[0, ε)` of the one-dimensional half-space model.

## Main results

* `TauCeti.SmoothCollar.mfderiv_comp_inl`: on the zero slice, the derivative of a collar along
  the boundary directions is the derivative of the inclusion of the boundary.
* `TauCeti.SmoothCollar.isOutwardPointing_neg_mfderiv_inr`: on the zero slice, minus the image of
  the depth direction points outward.
* `TauCeti.SmoothCollar.orientationSign_eq_neg_one_pow`: the orientation sign of a collar is
  `(-1) ^ (n + 1)`.
* `TauCeti.SmoothCollar.isOrientationPreservingAt_of_odd`,
  `TauCeti.SmoothCollar.isOrientationReversingAt_of_even`: a collar preserves orientation when
  `n` is odd and reverses it when `n` is even.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 15 (the induced orientation on the boundary, and product orientations).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 4, §6 (collars).
-/

public section

noncomputable section

open Set Function Topology Filter
open scoped Manifold ContDiff

namespace TauCeti

namespace EuclideanHalfSpace

/-- The standard orientation of the initial segment `[0, ε)` of the one-dimensional half-space
model: the restriction of the constant orientation of the standard basis. -/
def normalIioOpensOrientation (ε : ℝ) :
    Manifold.Orientation (𝓡∂ 1) (normalIioOpens ε) (Fin 1) :=
  (Manifold.Orientation.model (I := 𝓡∂ 1)
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation (by simp)).restrict _

theorem normalIioOpensOrientation_def (ε : ℝ) :
    normalIioOpensOrientation ε =
      (Manifold.Orientation.model (I := 𝓡∂ 1)
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation (by simp)).restrict
          (normalIioOpens ε) :=
  (rfl)

/-- At every point, the standard orientation of `[0, ε)` is that of the standard basis. -/
@[simp]
theorem orientationAt_normalIioOpensOrientation {ε : ℝ} (t : normalIioOpens ε) :
    (normalIioOpensOrientation ε).orientationAt t =
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation := by
  have h := (Manifold.Orientation.isOrientationPreservingAt_iff_of_basis
    (o := normalIioOpensOrientation ε) (f := Subtype.val) (x := t)
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
    (fun i ↦ by rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]; rfl)).1
    (Manifold.Orientation.isOrientationPreservingAt_restrict _ _ t)
  rw [normalIioOpensOrientation_def, Manifold.Orientation.orientationAt_model] at h
  exact (h.2 rfl).symm

end EuclideanHalfSpace

namespace SmoothCollar

open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (c : SmoothCollar n k M)

/-- On the zero slice, the derivative of a smooth collar along the boundary directions is the
derivative of the inclusion of the boundary. -/
theorem mfderiv_comp_inl (hk : k ≠ 0) (y : (𝓡∂ (n + 1)).boundary M) :
    (mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c (y, normalIioOpensZero one_pos)).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) =
      mfderiv (𝓡 n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y := by
  let g : (𝓡∂ (n + 1)).boundary M → (𝓡∂ (n + 1)).boundary M × normalIioOpens 1 :=
    fun x ↦ (x, normalIioOpensZero one_pos)
  have hg : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡∂ 1)) g y :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hcg : c ∘ g = Subtype.val := funext c.apply_zero
  rw [← hcg, mfderiv_comp y ((c.contMDiff _).mdifferentiableAt hk) hg]
  congr 1
  -- `inl` is `id.prod 0`, between the model spaces, which are the tangent spaces.
  exact ((hasMFDerivAt_id y).prodMk (hasMFDerivAt_const _ y)).mfderiv.symm

/-- On the zero slice, the image of the depth direction under the derivative of a smooth collar
has positive normal coordinate. -/
private theorem proj_zero_mfderiv_inr_pos (hk : k ≠ 0) (y : (𝓡∂ (n + 1)).boundary M) :
    0 < EuclideanSpace.proj (0 : Fin (n + 1))
      (mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c (y, normalIioOpensZero one_pos)
        (0, EuclideanSpace.single 0 1)) := by
  set I := (𝓡 n).prod (𝓡∂ 1)
  set p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1 := (y, normalIioOpensZero one_pos)
  set z := extChartAt I p p
  obtain ⟨D, hD⟩ := (c.isLocalDiffeomorph p).isInvertible_mfderiv hk
  rw [← hD]
  let π : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0
  -- The normal coordinate of the derivative, on the model space of the product.
  let L : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    π.comp (D : TangentSpace I p →L[ℝ] TangentSpace (𝓡∂ (n + 1)) (c p))
  -- The normal coordinate of `c`, read in the charts at `p` and at `c p = y`.
  let f := π ∘ writtenInExtChartAt I (𝓡∂ (n + 1)) p c
  have hF : HasFDerivWithinAt f L (range I) z := by
    have hc := ((c.contMDiff p).mdifferentiableAt hk).hasMFDerivAt
    rw [← hD] at hc
    exact π.hasFDerivAt.comp_hasFDerivWithinAt z hc.2
  have hnonneg (w) : 0 ≤ f w := by
    simp only [f, writtenInExtChartAt, Function.comp_apply, extChartAt_coe,
      modelWithCornersEuclideanHalfSpace_toFun, π, PiLp.proj_apply]
    exact (chartAt (EuclideanHalfSpace (n + 1)) (c p) _).property
  have hz : f z = 0 := by
    have hcp : c p ∈ (𝓡∂ (n + 1)).boundary M := by
      rw [show c p = y from c.apply_zero y]
      exact y.property
    simpa only [f, z, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv, π,
      PiLp.proj_apply] using extChartAt_self_apply_zero hcp
  have hmin : IsLocalMinOn f (range I) z :=
    Filter.Eventually.of_forall fun w ↦ hz ▸ hnonneg w
  have hzr : z ∈ range I := extChartAt_target_subset_range p (mem_extChartAt_target p)
  have hcone (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) (hv : 0 ≤ v.2 0) :
      v ∈ posTangentConeAt (range I) z := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset hzr
    rw [ModelWithCorners.range_prod] at hzr ⊢
    simp only [modelWithCornersSelf_coe, range_id, range_modelWithCornersEuclideanHalfSpace,
      mem_prod, mem_univ, true_and, mem_ofPred_eq, Prod.snd_add, PiLp.add_apply] at hzr ⊢
    linarith
  have h1 := hmin.hasFDerivWithinAt_nonneg hF (hcone (0, EuclideanSpace.single 0 1) (by simp))
  have h2 (u : EuclideanSpace ℝ (Fin n)) : L (u, 0) = 0 :=
    hmin.hasFDerivWithinAt_eq_zero hF (hcone (u, 0) (by simp)) (hcone (-(u, 0)) (by simp))
  refine lt_of_le_of_ne h1 fun h0 ↦ ?_
  replace h0 : L (0, EuclideanSpace.single 0 1) = 0 := h0.symm
  have hall (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) : L w = 0 := by
    have hw : w = (w.1, 0) + w.2 0 • (0, EuclideanSpace.single 0 1) := by
      ext i <;> [simp; (fin_cases i; simp)]
    rw [hw, map_add, map_smul, h2, h0, smul_zero, add_zero]
  -- `L` is `π ∘ D` on the model space of the product, which is the tangent space at `p`.
  let e : TangentSpace (𝓡∂ (n + 1)) (c p) := EuclideanSpace.single 0 1
  have h3 : π (D (D.symm e)) = 0 := hall _
  rw [D.apply_symm_apply] at h3
  simp [π, e] at h3

variable [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- On the zero slice of a smooth collar, minus the image of the depth direction `∂ₜ` under the
derivative points outward. -/
theorem isOutwardPointing_neg_mfderiv_inr (hk : k ≠ 0) (y : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (y : M)
      (-mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c (y, normalIioOpensZero one_pos)
        (0, EuclideanSpace.single 0 1)) := by
  refine (isOutwardPointing_iff_tangentCoordChange y.property
    (mem_extChartAt_source (y : M)) _).2 ?_
  refine (congrArg (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0)
    (tangentCoordChange_self (I := 𝓡∂ (n + 1)) (mem_extChartAt_source (y : M)))).trans_lt ?_
  exact neg_neg_of_pos (c.proj_zero_mfderiv_inr_pos hk y)

local instance : IsManifold (𝓡 n) 1 ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M

variable (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))

/-- The orientation sign of a smooth collar at a point `(y, 0)` of its zero slice. -/
private theorem orientationSign_mk_normalIioOpensZero (hk : k ≠ 0)
    (y : (𝓡∂ (n + 1)).boundary M) :
    Manifold.Orientation.orientationSign
      ((boundaryOrientation o).prod (normalIioOpensOrientation 1)) o c
        (y, normalIioOpensZero one_pos) = (-1) ^ (n + 1) := by
  set p : ↥((𝓡∂ (n + 1)).boundary M) × normalIioOpens 1 := (y, normalIioOpensZero one_pos)
  have hcp : c p = (y : M) := c.apply_zero y
  have ho : o.orientationAt (c p) = o.orientationAt (y : M) := by rw [hcp]
  obtain ⟨D, hD⟩ := (c.isLocalDiffeomorph p).isInvertible_mfderiv hk
  -- The standard bases of the two factors, and their product basis of the tangent space at `p`.
  let b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let e : Module.Basis (Fin 1) ℝ (TangentSpace (𝓡∂ 1) p.2) :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  have he0 : (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0 =
      EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    simp
  have hlast : ((b.prod e).reindex finSumFinEquiv) (Fin.last n) =
      (0, EuclideanSpace.single 0 1) := by
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_last]
    exact Prod.ext (Module.Basis.prod_apply_inr_fst _ _ _)
      ((Module.Basis.prod_apply_inr_snd _ _ _).trans he0)
  have hcast (j : Fin n) : ((b.prod e).reindex finSumFinEquiv) j.castSucc = (b j, 0) := by
    rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castSucc]
    exact Prod.ext (Module.Basis.prod_apply_inl_fst _ _ _) (Module.Basis.prod_apply_inl_snd _ _ _)
  let B₀ : Module.Basis (Fin (n + 1)) ℝ (TangentSpace ((𝓡 n).prod (𝓡∂ 1)) p) :=
    (b.prod e).reindex finSumFinEquiv
  -- Its image under the derivative, and the outward-first basis of `boundaryOrientation_spec`.
  let B := B₀.map D.toLinearEquiv
  have hB (i) : mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c p (B₀ i) = B i := by
    simp only [B, Module.Basis.map_apply, ← hD, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv]
  let B' := (B.reindex (finRotate (n + 1))).unitsSMul (Function.update 1 0 (-1))
  have hrot0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (Equiv.symm_apply_eq _).2 finRotate_last.symm
  have hrot (j : Fin n) : (finRotate (n + 1)).symm j.succ = j.castSucc :=
    (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))
  have hB'0 : B' 0 =
      -mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c p (0, EuclideanSpace.single 0 1) := by
    have h : B' 0 = -B (Fin.last n) := by
      simp only [B', Module.Basis.unitsSMul_apply, Function.update_self,
        Module.Basis.reindex_apply, hrot0]
      rw [Units.neg_smul, one_smul]
    rw [h, ← hB]
    congr 2
  have hB'succ (j : Fin n) : B' j.succ =
      mfderiv (𝓡 n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y (b j) := by
    have h : B' j.succ = B j.castSucc := by
      simp only [B', Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, hrot,
        Function.update_of_ne (Fin.succ_ne_zero j), Pi.one_apply, one_smul]
    rw [h, ← hB, ← c.mfderiv_comp_inl hk y]
    -- Unfold the composite with `inl` to an application of the derivative.
    change (mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c p) (B₀ j.castSucc) =
      (mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c p) (ContinuousLinearMap.inl ℝ _ _ (b j))
    congr 1
    exact hcast j
  have hB' : ⇑B' = Fin.cons
      (-mfderiv ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) c p (0, EuclideanSpace.single 0 1))
      (fun i ↦ mfderiv (𝓡 n) (𝓡∂ (n + 1)) (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y
        (b i)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    -- `Fin.cons` evaluates on `0` and on successors by definition.
    · exact hB'0
    · exact hB'succ j
  have hspec := boundaryOrientation_spec o y (c.isOutwardPointing_neg_mfderiv_inr hk y) b B' hB'
  have hprod := Manifold.Orientation.orientation_eq_orientationAt_prod_iff
    (boundaryOrientation o) (normalIioOpensOrientation 1) (x := p) b e
  have he : e.orientation = (normalIioOpensOrientation 1).orientationAt p.2 :=
    (orientationAt_normalIioOpensOrientation _).symm
  simp only [he, iff_true] at hprod
  -- Moving the last vector to the front has sign `(-1) ^ n`, and negating it one more sign.
  have hsign : B'.orientation = -(Units.map (Int.castRingHom ℝ).toMonoidHom
      (Equiv.Perm.sign (finRotate (n + 1))) • B.orientation) := by
    rw [Module.Basis.orientation_neg_single, Module.Basis.orientation_reindex,
      Orientation.reindex_perm]
  rw [sign_finRotate, Nat.add_sub_cancel] at hsign
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, map_one, one_smul] at hsign
    rw [Manifold.Orientation.orientationSign_of_isOrientationReversingAt, hn.add_one.neg_one_pow]
    rw [Manifold.Orientation.isOrientationReversingAt_iff_of_basis B₀ B hB, ho]
    have h : B.orientation = -B'.orientation := by
      rw [hsign, neg_neg (G := Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (c p)) (Fin (n + 1)))]
    rw [h]
    exact hprod.trans (hspec.trans
      (neg_inj (G := Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (c p)) (Fin (n + 1)))).symm)
  · have hu : Units.map (Int.castRingHom ℝ).toMonoidHom (-1 : ℤˣ) = -1 := by ext; simp
    rw [hn.neg_one_pow, hu, Module.Ray.neg_units_smul, one_smul,
      neg_neg (G := Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (c p)) (Fin (n + 1)))] at hsign
    rw [Manifold.Orientation.orientationSign_of_isOrientationPreservingAt, hn.add_one.neg_one_pow]
    rw [Manifold.Orientation.isOrientationPreservingAt_iff_of_basis B₀ B hB, ho, ← hsign]
    exact hprod.trans hspec

/-- **The orientation sign of a smooth collar.** Orient `∂M` by the outward-first boundary
orientation of `o`, `[0, 1)` by its standard orientation, and `∂M × [0, 1)` by their product,
with the boundary directions first. Then a `C^k` smooth collar `c`, `k ≠ 0`, has orientation sign
`(-1) ^ (n + 1)` at every point. -/
theorem orientationSign_eq_neg_one_pow (hk : k ≠ 0)
    (q : (𝓡∂ (n + 1)).boundary M × normalIioOpens 1) :
    Manifold.Orientation.orientationSign
      ((boundaryOrientation o).prod (normalIioOpensOrientation 1)) o c q = (-1) ^ (n + 1) := by
  obtain ⟨y, t⟩ := q
  let g : normalIioOpens 1 → ℤ := fun s ↦ Manifold.Orientation.orientationSign
    ((boundaryOrientation o).prod (normalIioOpensOrientation 1)) o c (y, s)
  have hg : IsLocallyConstant g := (IsLocallyConstant.iff_eventually_eq g).2 fun s ↦
    ((continuous_const.prodMk continuous_id).tendsto s).eventually
      (Manifold.Orientation.eventually_orientationSign_eq
        ((c.contMDiff (y, s)).of_le (ENat.one_le_iff_ne_zero_withTop.2 hk))
        ((c.isLocalDiffeomorph (y, s)).isInvertible_mfderiv hk))
  -- The slice `{y} × [0, 1)` is connected, as `[0, 1)` is.
  let h := homeomorphNormalIioOpens 1
  have : PreconnectedSpace (Ico (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ico
  have hgt := (hg.comp_continuous h.symm.continuous).apply_eq_of_preconnectedSpace
    (h t) (h (normalIioOpensZero one_pos))
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at hgt
  exact hgt.trans (c.orientationSign_mk_normalIioOpensZero o hk y)

/-- When `n` is odd, as for surfaces, a smooth collar preserves orientation at every point, from
the product of the boundary orientation and the standard orientation of `[0, 1)`. -/
theorem isOrientationPreservingAt_of_odd (hk : k ≠ 0) (hn : Odd n)
    (q : (𝓡∂ (n + 1)).boundary M × normalIioOpens 1) :
    Manifold.Orientation.IsOrientationPreservingAt
      ((boundaryOrientation o).prod (normalIioOpensOrientation 1)) o c q := by
  rw [← Manifold.Orientation.orientationSign_eq_one_iff,
    c.orientationSign_eq_neg_one_pow o hk, hn.add_one.neg_one_pow]

/-- When `n` is even, a smooth collar reverses orientation at every point, from the product of
the boundary orientation and the standard orientation of `[0, 1)`. -/
theorem isOrientationReversingAt_of_even (hk : k ≠ 0) (hn : Even n)
    (q : (𝓡∂ (n + 1)).boundary M × normalIioOpens 1) :
    Manifold.Orientation.IsOrientationReversingAt
      ((boundaryOrientation o).prod (normalIioOpensOrientation 1)) o c q := by
  rw [← Manifold.Orientation.orientationSign_eq_neg_one_iff,
    c.orientationSign_eq_neg_one_pow o hk, hn.add_one.neg_one_pow]

end SmoothCollar

end TauCeti
