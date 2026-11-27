/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
import SymplecticGeometry.Geometry.Manifold.Instances.HalfLine.Basic
import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Orientation.Glue
import TauCeti.Geometry.Manifold.Orientation.Pullback
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.Orientation.Sign
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Orientation.Glue
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Topology.Algebra.Module.Determinant
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts

/-!
# The orientation of the double

Let `W` be a manifold with boundary over the half-space `𝓡∂ (n + 1)`, `c` a smooth collar of its
boundary, and `o` an orientation of the interior of `W`, as Tau Ceti's charted interior
`(𝓡∂ (n + 1)).interior W` over `ℝⁿ⁺¹`. The double `c.Double` (`Collar/Double/Basic.lean`) has
exactly one orientation, `TauCeti.SmoothCollar.Double.orientation c o`, for which the first copy
`inlInterior c` of the interior preserves orientation from `o` and the second copy
`inrInterior c` preserves orientation from `-o`. The sign changes because the collar coordinate
is reflected from one copy to the other: the point `(s, x)` of the band is `c (x, -s)` in the
first copy and `c (x, s)` in the second. No orientation of `W` or of `∂W` is used, and the
construction holds in every dimension.

The orientation is glued by `TauCeti.Manifold.Orientation.iGlue` from the two copies of the
interior and the band piece `bandIncl c`. The band is oriented by pulling `o` back along the
map `(s, x) ↦ c (x, 1/2 - s/4)` into the interior, a local diffeomorphism since the collar is
one. Where the band meets the first copy, `s < 0`, the band parameters carry into the interior
by `(s, x) ↦ c (x, -s)`. That map is `C¹` with invertible derivative, so its orientation sign
takes one value on the connected slice `(-1, 0) × {x}`
(`IsPreconnected.orientationSign_eq`).
At `s = -2/3` the two maps into the interior differ by `(s, x) ↦ (2 + 4 s, x)`, which fixes the
point with derivative of determinant `4`, so the sign is `1`
(`TauCeti.Manifold.Orientation.orientationSign_of_apply_eq`). On the second copy, `s > 0`, the
same argument at `s = 2/5`, with `(s, x) ↦ (2 - 4 s, x)` of determinant `-4`, gives the sign
`-1`. The two copies cover a dense subset of the double
(`TauCeti.SmoothCollar.Double.dense_range_inlInterior_union_range_inrInterior`), which is why their
two conditions determine the orientation (`TauCeti.Manifold.Orientation.eq_of_dense`).

The gluing follows that of `SymplecticGeometry.capDiscs.orientation` in
`Gluing/CapDiscs/Orientation.lean`.

## Main definitions

* `TauCeti.SmoothCollar.Double.orientation`: the orientation of the double.

## Main results

* `TauCeti.SmoothCollar.Double.isOrientationPreservingAt_inlInterior`,
  `TauCeti.SmoothCollar.Double.isOrientationPreservingAt_inrInterior`: the first copy of the
  interior preserves orientation from `o`, the second from `-o`.
* `TauCeti.SmoothCollar.Double.eq_orientation_iff`: these properties characterize the
  orientation.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §2.7 (the first Chern number of bundles over surfaces).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 15 (orientations and their pullbacks).
-/

public section

open Set Function Topology Manifold TopologicalSpace SymplecticGeometry Filter
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar.Double
open _root_.TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace
  _root_.TauCeti.Manifold.Orientation

universe u

variable {n : ℕ} {W : Type u} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] (c : SmoothCollar n ∞ W)

variable (n W) in
/-- The parameters `(s, x)` of the band, `s ∈ (-1, 1)` and `x ∈ ∂W`. -/
private abbrev BandParam : Type u := bandInterval × (𝓡∂ (n + 1)).boundary W

/-! ### The depth map of the band -/

/-- The depth `1/2 - s/4 ∈ (1/4, 3/4)` of the collar at the parameter `s ∈ (-1, 1)`. -/
private def bandDepth (s : bandInterval) : normalIioOpens 1 :=
  normalIioRay ⟨1 / 2 - s / 4, by rw [mem_Iio]; have := (mem_bandInterval.1 s.property).1; linarith⟩

private theorem bandDepth_coe_apply (s : bandInterval) :
    (bandDepth s : EuclideanHalfSpace 1).val 0 = 1 / 2 - s / 4 :=
  normalIioRay_coe_apply_of_nonneg _
    (by have := (mem_bandInterval.1 s.property).2; linarith)

private theorem bandDepth_pos (s : bandInterval) :
    0 < (bandDepth s : EuclideanHalfSpace 1).val 0 := by
  rw [bandDepth_coe_apply]
  have := (mem_bandInterval.1 s.property).2
  linarith

private theorem bandDepth_eq {s : bandInterval} {r : ℝ} (hr : r < 1) (h : 1 / 2 - s / 4 = r) :
    bandDepth s = normalIioRay ⟨r, hr⟩ :=
  congrArg normalIioRay (Subtype.ext h)

private theorem isLocalDiffeomorph_bandDepth : IsLocalDiffeomorph 𝓘(ℝ) (𝓡∂ 1) ∞ bandDepth := by
  intro s
  have hg : IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : normalIioOpens 1 ↦ (t : EuclideanHalfSpace 1).val 0) (bandDepth s) :=
    isLocalDiffeomorphAt_opens_val_zero (bandDepth_pos s)
  have hcont : Continuous bandDepth :=
    continuous_normalIioRay.comp (Continuous.subtype_mk (by fun_prop) _)
  refine (hg.comp_iff_left hcont.continuousAt).1 ?_
  have he : (fun t : normalIioOpens 1 ↦ (t : EuclideanHalfSpace 1).val 0) ∘ bandDepth =
      Diffeomorph.smulAdd ∞ (-1 / 4 : ℝ) (1 / 2) (by norm_num) ∘ Subtype.val := by
    funext s
    rw [comp_apply, bandDepth_coe_apply, comp_apply, Diffeomorph.smulAdd_apply, smul_eq_mul]
    ring
  rw [he]
  exact (isLocalDiffeomorph_subtype_val s).comp (hg := Diffeomorph.isLocalDiffeomorph _ _)

/-! ### The orientation of the band -/

/-- The collar point `c (x, 1/2 - s/4)` of the interior of `W`, at the parameter `(s, x)` of the
band. -/
private def bandCollar (p : BandParam n W) : (𝓡∂ (n + 1)).interiorOpens W :=
  ⟨c (p.2, bandDepth p.1), by
    rw [← SetLike.mem_coe, ModelWithCorners.coe_interiorOpens, c.apply_mem_interior_iff_pos]
    exact bandDepth_pos p.1⟩

private theorem isLocalDiffeomorph_bandCollar :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) (𝓡∂ (n + 1)) ∞ (bandCollar c) := fun p ↦ by
  refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
  have h : IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡∂ 1)) ∞
      (fun p : BandParam n W ↦ (p.2, bandDepth p.1)) p :=
    ((isLocalDiffeomorph_bandDepth p.1).prodMap (isLocalDiffeomorph_id p.2)).comp
      (hg := (Diffeomorph.prodComm _ _ _ _ ∞).isLocalDiffeomorph _)
  exact h.comp (hg := c.isLocalDiffeomorph _)

/-- The collar point `c (x, 1/2 - s/4)`, read in the copy of the interior of `W` over `ℝⁿ⁺¹`. -/
private def bandInterior (p : BandParam n W) : (𝓡∂ (n + 1)).interior W :=
  (𝓡∂ (n + 1)).interiorOpensDiffeomorph W ∞ (bandCollar c p)

private theorem isLocalDiffeomorph_bandInterior :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (bandInterior c) := fun p ↦
  (isLocalDiffeomorph_bandCollar c p).comp (hg := Diffeomorph.isLocalDiffeomorph _ _)

variable (o : Manifold.Orientation (𝓡 (n + 1)) ((𝓡∂ (n + 1)).interior W) (Fin (n + 1)))

/-- The orientation of the parameters of the band, pulled back from `o` along `bandInterior`. -/
private def bandParamOrientation :
    Manifold.Orientation (𝓘(ℝ).prod (𝓡 n)) (BandParam n W) (Fin (n + 1)) :=
  o.pullback ((isLocalDiffeomorph_bandInterior c).contMDiff.of_le (by simp))
    (fun p ↦ (isLocalDiffeomorph_bandInterior c p).isInvertible_mfderiv (by simp))
    (by simp [Module.finrank_prod, add_comm])

private theorem isOrientationPreservingAt_bandInterior (p : BandParam n W) :
    IsOrientationPreservingAt (bandParamOrientation c o) o (bandInterior c) p :=
  isOrientationPreservingAt_pullback _ _ _ _ p

variable (n W) in
/-- The re-modelling of the parameters of the band as the band piece. -/
private abbrev remodelBand : BandParam n W ≃ₘ^∞⟮𝓘(ℝ).prod (𝓡 n), 𝓡 (n + 1)⟯ BandPiece n W :=
  remodelDiffeomorph (endModelDiffeomorph n) (BandParam n W)

/-- The orientation of the band piece. -/
private def bandOrientation : Manifold.Orientation (𝓡 (n + 1)) (BandPiece n W) (Fin (n + 1)) :=
  (bandParamOrientation c o).map (remodelBand n W) (by simp) (by simp)

private theorem isOrientationPreservingAt_remodelBand (p : BandParam n W) :
    IsOrientationPreservingAt (bandParamOrientation c o) (bandOrientation c o)
      (remodelBand n W) p :=
  isOrientationPreservingAt_map _ _ _ _ p

/-! ### An affine self-map of the band near a fixed point -/

/-- The map `s ↦ a + b s` of `(-1, 1)`, where it stays in `(-1, 1)`; elsewhere the identity. Only
its germ at a fixed point is used. -/
private def bandAffine (a b : ℝ) (s : bandInterval) : bandInterval :=
  if h : a + b * s ∈ Ioo (-1) 1 then ⟨a + b * s, mem_bandInterval.2 h⟩ else s

private theorem bandAffine_apply_of_mem {a b : ℝ} {s : bandInterval}
    (h : a + b * s ∈ Ioo (-1) 1) : (bandAffine a b s : ℝ) = a + b * s := by
  simp [bandAffine, h]

private theorem eventuallyEq_bandAffine {a b : ℝ} {s₀ : bandInterval} (h : a + b * s₀ = s₀) :
    Subtype.val ∘ bandAffine a b =ᶠ[𝓝 s₀] (fun r : ℝ ↦ a + b * r) ∘ Subtype.val := by
  have hmem : (fun s : bandInterval ↦ a + b * s) ⁻¹' Ioo (-1) 1 ∈ 𝓝 s₀ :=
    (isOpen_Ioo.preimage (by fun_prop)).mem_nhds (by
      rw [mem_preimage, h]; exact mem_bandInterval.1 s₀.property)
  filter_upwards [hmem] with s hs using bandAffine_apply_of_mem hs

private theorem bandAffine_of_eq {a b : ℝ} {s₀ : bandInterval} (h : a + b * s₀ = s₀) :
    bandAffine a b s₀ = s₀ :=
  have hm : a + b * s₀ ∈ Ioo (-1) 1 := by rw [h]; exact mem_bandInterval.1 s₀.property
  Subtype.ext ((bandAffine_apply_of_mem hm).trans h)

private theorem isLocalDiffeomorphAt_bandAffine {a b : ℝ} (hb : b ≠ 0) {s₀ : bandInterval}
    (h : a + b * s₀ = s₀) : IsLocalDiffeomorphAt 𝓘(ℝ) 𝓘(ℝ) ∞ (bandAffine a b) s₀ := by
  have he : (fun r : ℝ ↦ a + b * r) = Diffeomorph.smulAdd ∞ b a hb :=
    funext fun r ↦ by rw [Diffeomorph.smulAdd_apply, smul_eq_mul, add_comm]
  have hA : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ∞ fun r : ℝ ↦ a + b * r := by
    rw [he]
    exact (Diffeomorph.smulAdd ∞ b a hb).isLocalDiffeomorph
  exact isLocalDiffeomorphAt_subtypeVal_comp_iff.1
    (((isLocalDiffeomorph_subtype_val s₀).comp (hg := hA _)).congr_of_eventuallyEq
      (eventuallyEq_bandAffine h))

private theorem mfderiv_bandAffine {a b : ℝ} {s₀ : bandInterval} (h : a + b * s₀ = s₀)
    (v : TangentSpace 𝓘(ℝ) s₀) : mfderiv 𝓘(ℝ) 𝓘(ℝ) (bandAffine a b) s₀ v = b • v := by
  have hd : HasFDerivAt (fun r : ℝ ↦ a + b * r) (b • ContinuousLinearMap.id ℝ ℝ) s₀ := by
    simpa [smul_eq_mul] using ((hasFDerivAt_id (s₀ : ℝ)).const_smul b).const_add a
  rw [TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eventuallyEq
    (eventuallyEq_bandAffine h) v, mfderiv_eq_fderiv, hd.fderiv]
  rfl

/-- The map `(s, x) ↦ (a + b s, x)` of the parameters of the band, near a fixed point. -/
private def bandParamAffine (a b : ℝ) : BandParam n W → BandParam n W :=
  Prod.map (bandAffine a b) id

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandParamAffine_snd (a b : ℝ) (p : BandParam n W) :
    (bandParamAffine a b p).2 = p.2 :=
  (rfl)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem det_mfderiv_bandParamAffine {a b : ℝ} (hb : b ≠ 0) {s₀ : bandInterval}
    (h : a + b * s₀ = s₀) (x : (𝓡∂ (n + 1)).boundary W) :
    (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) (bandParamAffine a b) (s₀, x) :
      ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n)).det = b := by
  have hD : (mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) (bandParamAffine a b) (s₀, x) :
      ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n)) =
      (b • ContinuousLinearMap.id ℝ ℝ).prodMap
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [bandParamAffine, mfderiv_prodMap
      ((isLocalDiffeomorphAt_bandAffine hb h).mdifferentiableAt (by simp)) mdifferentiableAt_id,
      mfderiv_id]
    ext v
    · exact mfderiv_bandAffine h v.1
    · rfl
  have hdet : ((b • ContinuousLinearMap.id ℝ ℝ).prodMap
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))).det = b := by simp
  rw [hD]
  exact hdet

/-! ### The band read in the copies of the interior -/

private theorem val_bandInterior (p : BandParam n W) :
    (bandInterior c p).val = c (p.2, bandDepth p.1) :=
  ModelWithCorners.coe_interiorOpensDiffeomorph_apply _

/-- The point `bandMap c (s, x)` of the double, at the parameter `(s, x)` of the band. -/
private def bandPoint (p : BandParam n W) : c.Double := bandIncl c (remodelBand n W p)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandPoint_apply (p : BandParam n W) : bandPoint c p = bandMap c (p.1, p.2) :=
  bandIncl_remodelDiffeomorph c p

private theorem isLocalDiffeomorph_bandPoint :
    IsLocalDiffeomorph (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (bandPoint c) := fun p ↦
  ((remodelBand n W).isLocalDiffeomorph p).comp (hg := isLocalDiffeomorph_bandIncl c _)

private theorem continuous_bandPoint : Continuous (bandPoint c) :=
  (isLocalDiffeomorph_bandPoint c).contMDiff.continuous

section Copy

variable {c} {j : (𝓡∂ (n + 1)).interior W → c.Double} (hj : IsOpenEmbedding j)

/-- The point of the copy `j` of the interior of `W` at the parameter `p` of the band, when the
band point lies on that copy. -/
private def copyParam (p : BandParam n W) : (𝓡∂ (n + 1)).interior W :=
  -- The inverse of `j` needs a point of the interior of `W`; `p` gives one.
  have : Nonempty ((𝓡∂ (n + 1)).interior W) := ⟨bandInterior c p⟩
  (hj.toOpenPartialHomeomorph j).symm (bandPoint c p)

private theorem copyParam_def (p : BandParam n W) :
    have : Nonempty ((𝓡∂ (n + 1)).interior W) := ⟨bandInterior c p⟩
    copyParam hj p = (hj.toOpenPartialHomeomorph j).symm (bandPoint c p) :=
  (rfl)

private theorem apply_copyParam {p : BandParam n W} (hp : bandPoint c p ∈ range j) :
    j (copyParam hj p) = bandPoint c p := by
  have : Nonempty ((𝓡∂ (n + 1)).interior W) := ⟨bandInterior c p⟩
  rw [copyParam_def]
  exact (hj.toOpenPartialHomeomorph j).right_inv (by rwa [hj.toOpenPartialHomeomorph_target])

private theorem copyParam_eq {p : BandParam n W} {q : (𝓡∂ (n + 1)).interior W}
    (h : j q = bandPoint c p) : copyParam hj p = q := by
  have : Nonempty ((𝓡∂ (n + 1)).interior W) := ⟨q⟩
  rw [copyParam_def, ← h]
  exact (hj.toOpenPartialHomeomorph j).left_inv (by simp)

private theorem eventuallyEq_copyParam {p : BandParam n W} (hp : bandPoint c p ∈ range j) :
    j ∘ copyParam hj =ᶠ[𝓝 p] bandPoint c :=
  Filter.eventually_of_mem
    ((continuous_bandPoint c).continuousAt.preimage_mem_nhds (hj.isOpen_range.mem_nhds hp))
    fun _ h ↦ apply_copyParam hj h

private theorem isLocalDiffeomorphAt_copyParam
    (hjd : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ j) {p : BandParam n W}
    (hp : bandPoint c p ∈ range j) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (copyParam hj) p := by
  have : Nonempty ((𝓡∂ (n + 1)).interior W) := ⟨bandInterior c p⟩
  have hcont : ContinuousAt (copyParam hj) p := by
    have he : copyParam hj = (hj.toOpenPartialHomeomorph j).symm ∘ bandPoint c :=
      funext fun p' ↦ copyParam_def hj p'
    rw [he]
    exact ((hj.toOpenPartialHomeomorph j).continuousAt_symm
      (by rwa [hj.toOpenPartialHomeomorph_target])).comp (continuous_bandPoint c).continuousAt
  exact ((hjd _).comp_iff_left hcont).1
    ((isLocalDiffeomorph_bandPoint c p).congr_of_eventuallyEq (eventuallyEq_copyParam hj hp))

/-- **The sign at a reference point.** If near a fixed point `(s₀, x)` of `(s, x) ↦ (a + b s, x)`
the band point is the point of the copy `j` at `bandInterior c (a + b s, x)`, then the band
parameters carry into the copy `j` with the sign of `b`, from the band orientation to `o`. -/
private theorem orientationSign_copyParam_of_eventuallyEq {a b : ℝ} (hb : b ≠ 0)
    {s₀ : bandInterval} (h : a + b * s₀ = s₀) (x : (𝓡∂ (n + 1)).boundary W)
    (hβ : ∀ᶠ p in 𝓝 (s₀, x), j (bandInterior c (bandParamAffine a b p)) = bandPoint c p) :
    orientationSign (bandParamOrientation c o) o (copyParam hj) (s₀, x) = SignType.sign b := by
  have hfix : bandParamAffine a b (s₀, x) = (s₀, x) := Prod.ext (bandAffine_of_eq h) rfl
  have heq : bandInterior c ∘ bandParamAffine a b =ᶠ[𝓝 (s₀, x)] copyParam hj :=
    hβ.mono fun _ hp ↦ (copyParam_eq hj hp).symm
  have hA : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) (𝓘(ℝ).prod (𝓡 n)) (bandParamAffine a b)
      (s₀, x) :=
    ((isLocalDiffeomorphAt_bandAffine hb h).mdifferentiableAt (by simp)).prodMap
      mdifferentiableAt_id
  rw [← heq.orientationSign_eq, orientationSign_comp
      ((isLocalDiffeomorph_bandInterior c _).mdifferentiableAt (by simp)) hA,
    orientationSign_of_isOrientationPreservingAt (isOrientationPreservingAt_bandInterior c o _),
    one_mul, orientationSign_of_apply_eq _ hfix, det_mfderiv_bandParamAffine hb h]

/-- **The sign along a slice.** On a preconnected set `I ⊆ (-1, 1)` of parameters `s` whose band
points lie on the copy `j`, the sign of the map into the copy is constant along each slice
`I × {x}`. -/
private theorem orientationSign_copyParam_eq
    (hjd : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ j) {I : Set ℝ} (hI : IsPreconnected I)
    (hIsub : I ⊆ Ioo (-1) 1) (hmem : ∀ p : BandParam n W, (p.1 : ℝ) ∈ I → bandPoint c p ∈ range j)
    (x : (𝓡∂ (n + 1)).boundary W) {s s' : bandInterval} (hs : (s : ℝ) ∈ I)
    (hs' : (s' : ℝ) ∈ I) :
    orientationSign (bandParamOrientation c o) o (copyParam hj) (s, x) =
      orientationSign (bandParamOrientation c o) o (copyParam hj) (s', x) := by
  have hpre : IsPreconnected (Subtype.val ⁻¹' I : Set bandInterval) := by
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.1
      (Eq.subst (motive := IsPreconnected) ?_ hI)
    ext r
    exact ⟨fun hr ↦ ⟨⟨r, mem_bandInterval.2 (hIsub hr)⟩, hr, rfl⟩, fun ⟨_, ht, h⟩ ↦ h ▸ ht⟩
  have hS := hpre.image (fun s : bandInterval ↦ (s, x)) (by fun_prop)
  refine hS.orientationSign_eq ?_ ?_ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (isLocalDiffeomorphAt_copyParam hj hjd (hmem (t, x) ht)).contMDiffAt.of_le (by simp)
  · rintro _ ⟨t, ht, rfl⟩
    exact (isLocalDiffeomorphAt_copyParam hj hjd (hmem (t, x) ht)).isInvertible_mfderiv (by simp)

end Copy

/-! ### The two copies of the interior -/

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandPoint_mem_range_inlInterior_iff (p : BandParam n W) :
    bandPoint c p ∈ range (inlInterior c) ↔ (p.1 : ℝ) < 0 := by
  rw [bandPoint_apply]
  exact bandMap_mem_range_inlInterior_iff c (mem_bandInterval.1 p.1.property) p.2

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandPoint_mem_range_inrInterior_iff (p : BandParam n W) :
    bandPoint c p ∈ range (inrInterior c) ↔ 0 < (p.1 : ℝ) := by
  rw [bandPoint_apply]
  exact bandMap_mem_range_inrInterior_iff c (mem_bandInterval.1 p.1.property) p.2

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- Near `(s₀, x)`, the parameter `s` lies in an open set `U` and the affine map `s ↦ a + b s`
has the value `a + b s`. -/
private theorem eventually_bandParamAffine {a b : ℝ} {s₀ : bandInterval} (h : a + b * s₀ = s₀)
    {U : Set ℝ} (hU : IsOpen U) (hs₀ : (s₀ : ℝ) ∈ U) (x : (𝓡∂ (n + 1)).boundary W) :
    ∀ᶠ p : BandParam n W in 𝓝 (s₀, x),
      (p.1 : ℝ) ∈ U ∧ ((bandParamAffine a b p).1 : ℝ) = a + b * p.1 := by
  have h₁ : ∀ᶠ s : bandInterval in 𝓝 s₀, (s : ℝ) ∈ U ∧ (bandAffine a b s : ℝ) = a + b * s :=
    (Filter.eventually_of_mem ((hU.preimage continuous_subtypeVal).mem_nhds hs₀)
      fun _ h ↦ h).and (eventuallyEq_bandAffine h)
  exact (continuous_fst.tendsto ((s₀, x) : BandParam n W)).eventually h₁

/-- The point `(-2/3, ·)` of the band, a fixed point of `s ↦ 2 + 4 s`. -/
private def inlRef : bandInterval := ⟨-2 / 3, mem_bandInterval.2 ⟨by norm_num, by norm_num⟩⟩

/-- The point `(2/5, ·)` of the band, a fixed point of `s ↦ 2 - 4 s`. -/
private def inrRef : bandInterval := ⟨2 / 5, mem_bandInterval.2 ⟨by norm_num, by norm_num⟩⟩

/-- Near `(-2/3, x)`, the band point is `c (x, 1/2 - (2 + 4 s)/4) = c (x, -s)` of the first
copy. -/
private theorem eventually_inlInterior_bandInterior (x : (𝓡∂ (n + 1)).boundary W) :
    ∀ᶠ p in 𝓝 (inlRef, x),
      inlInterior c (bandInterior c (bandParamAffine 2 4 p)) = bandPoint c p := by
  filter_upwards [eventually_bandParamAffine (a := 2) (b := 4) (s₀ := inlRef)
    (by norm_num [inlRef]) isOpen_Iio (show (inlRef : ℝ) ∈ Iio 0 by norm_num [inlRef]) x]
    with p ⟨hp, hA⟩
  rw [inlInterior_apply, val_bandInterior, bandParamAffine_snd, bandPoint_apply,
    bandMap_of_nonpos c (le_of_lt hp) (mem_bandInterval.1 p.1.property).1,
    bandDepth_eq (r := -p.1) (by have := (mem_bandInterval.1 p.1.property).1; linarith)
      (by rw [hA]; ring)]

/-- Near `(2/5, x)`, the band point is `c (x, 1/2 - (2 - 4 s)/4) = c (x, s)` of the second
copy. -/
private theorem eventually_inrInterior_bandInterior (x : (𝓡∂ (n + 1)).boundary W) :
    ∀ᶠ p in 𝓝 (inrRef, x),
      inrInterior c (bandInterior c (bandParamAffine 2 (-4) p)) = bandPoint c p := by
  filter_upwards [eventually_bandParamAffine (a := 2) (b := -4) (s₀ := inrRef)
    (by norm_num [inrRef]) isOpen_Ioi (show (inrRef : ℝ) ∈ Ioi 0 by norm_num [inrRef]) x]
    with p ⟨hp, hA⟩
  rw [inrInterior_apply, val_bandInterior, bandParamAffine_snd, bandPoint_apply,
    bandMap_of_nonneg c (le_of_lt hp) (mem_bandInterval.1 p.1.property).2,
    bandDepth_eq (r := p.1) (mem_bandInterval.1 p.1.property).2 (by rw [hA]; ring)]

/-- The parameters `(s, x)` with `s < 0` carry into the first copy preserving orientation, from
the band orientation to `o`. -/
private theorem isOrientationPreservingAt_copyParam_inl {p : BandParam n W} (hp : (p.1 : ℝ) < 0) :
    IsOrientationPreservingAt (bandParamOrientation c o) o
      (copyParam (isOpenEmbedding_inlInterior c)) p := by
  have hsub : Ioo (-1 : ℝ) 0 ⊆ Ioo (-1) 1 := Ioo_subset_Ioo_right zero_le_one
  rw [← orientationSign_eq_one_iff, orientationSign_copyParam_eq o _
      (isLocalDiffeomorph_inlInterior c) isPreconnected_Ioo hsub
      (fun q hq ↦ (bandPoint_mem_range_inlInterior_iff c q).2 hq.2) p.2
      ⟨(mem_bandInterval.1 p.1.property).1, hp⟩
      (show (inlRef : ℝ) ∈ Ioo (-1) 0 by norm_num [inlRef]),
    orientationSign_copyParam_of_eventuallyEq o _ (by norm_num) (by norm_num [inlRef]) p.2
      (eventually_inlInterior_bandInterior c p.2)]
  norm_num

/-- The parameters `(s, x)` with `0 < s` carry into the second copy preserving orientation, from
the band orientation to `-o`. -/
private theorem isOrientationPreservingAt_copyParam_inr {p : BandParam n W} (hp : 0 < (p.1 : ℝ)) :
    IsOrientationPreservingAt (bandParamOrientation c o) (-o)
      (copyParam (isOpenEmbedding_inrInterior c)) p := by
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 := Ioo_subset_Ioo_left (by norm_num)
  rw [← orientationSign_eq_one_iff, orientationSign_neg_right, orientationSign_copyParam_eq o _
      (isLocalDiffeomorph_inrInterior c) isPreconnected_Ioo hsub
      (fun q hq ↦ (bandPoint_mem_range_inrInterior_iff c q).2 hq.1) p.2
      ⟨hp, (mem_bandInterval.1 p.1.property).2⟩
      (show (inrRef : ℝ) ∈ Ioo 0 1 by norm_num [inrRef]),
    orientationSign_copyParam_of_eventuallyEq o _ (by norm_num) (by norm_num [inrRef]) p.2
      (eventually_inrInterior_bandInterior c p.2)]
  norm_num

/-! ### Gluing the orientation -/

/-- A copy `j` of the interior and the band piece carry `oj` and the band orientation to the same
tangent orientation of the double wherever they meet, if the band parameters carry into `j`
preserving orientation, from the band orientation to `oj`. -/
private theorem map_orientationAt_eq_bandIncl
    {j : (𝓡∂ (n + 1)).interior W → c.Double} (hj : IsOpenEmbedding j)
    (hjd : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ j)
    {oj : Manifold.Orientation (𝓡 (n + 1)) ((𝓡∂ (n + 1)).interior W) (Fin (n + 1))}
    (hpres : ∀ p, bandPoint c p ∈ range j →
      IsOrientationPreservingAt (bandParamOrientation c o) oj (copyParam hj) p)
    {x : (𝓡∂ (n + 1)).interior W} {y : BandPiece n W} (h : j x = bandIncl c y) :
    _root_.Orientation.map (Fin (n + 1))
        ((hjd x).mfderivToContinuousLinearEquiv (NeZero.ne _)).toLinearEquiv
        (oj.orientationAt x) =
      _root_.Orientation.map (Fin (n + 1))
        ((isLocalDiffeomorph_bandIncl c y).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((bandOrientation c o).orientationAt y) := by
  obtain ⟨p, rfl⟩ := (remodelBand n W).surjective y
  have hp : bandPoint c p ∈ range j := ⟨x, h⟩
  obtain rfl : copyParam hj p = x := copyParam_eq hj h
  have hρ₁ := hpres p hp
  have hρ₂ := isOrientationPreservingAt_remodelBand c o p
  exact map_orientationAt_eq_of_comp_eventuallyEq hjd (isLocalDiffeomorph_bandIncl c) hρ₁ hρ₂
    (mdifferentiableAt_of_isInvertible_mfderiv hρ₁.isInvertible_mfderiv)
    (mdifferentiableAt_of_isInvertible_mfderiv hρ₂.isInvertible_mfderiv)
    (eventuallyEq_copyParam hj hp)

/-- The orientations of the pieces: `o` on the first copy of the interior, `-o` on the second, and
the band orientation on the band. -/
private def pieceOrientation :
    ∀ k, Manifold.Orientation (𝓡 (n + 1)) (piece n W k) (Fin (n + 1))
  | .inl => o
  | .inr => -o
  | .band => bandOrientation c o

/-- The pieces carry their orientations to the same orientation wherever they meet. -/
private theorem map_orientationAt_pieceMap (k l : Piece) (x : piece n W k) (y : piece n W l)
    (h : pieceMap c k x = pieceMap c l y) :
    _root_.Orientation.map (Fin (n + 1))
        ((isLocalDiffeomorph_pieceMap c k x).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation c o k).orientationAt x) =
      _root_.Orientation.map (Fin (n + 1))
        ((isLocalDiffeomorph_pieceMap c l y).mfderivToContinuousLinearEquiv
          (NeZero.ne _)).toLinearEquiv ((pieceOrientation c o l).orientationAt y) := by
  have hinl : ∀ p, bandPoint c p ∈ range (inlInterior c) →
      IsOrientationPreservingAt (bandParamOrientation c o) o
        (copyParam (isOpenEmbedding_inlInterior c)) p := fun p hp ↦
    isOrientationPreservingAt_copyParam_inl c o ((bandPoint_mem_range_inlInterior_iff c p).1 hp)
  have hinr : ∀ p, bandPoint c p ∈ range (inrInterior c) →
      IsOrientationPreservingAt (bandParamOrientation c o) (-o)
        (copyParam (isOpenEmbedding_inrInterior c)) p := fun p hp ↦
    isOrientationPreservingAt_copyParam_inr c o ((bandPoint_mem_range_inrInterior_iff c p).1 hp)
  cases k <;> cases l
  · obtain rfl : x = y := (isOpenEmbedding_inlInterior c).injective h
    rfl
  · exact absurd h ((disjoint_range_inlInterior_inrInterior c).ne_of_mem ⟨x, rfl⟩ ⟨y, rfl⟩)
  · exact map_orientationAt_eq_bandIncl c o (isOpenEmbedding_inlInterior c)
      (isLocalDiffeomorph_inlInterior c) hinl h
  · exact absurd h.symm ((disjoint_range_inlInterior_inrInterior c).ne_of_mem ⟨y, rfl⟩ ⟨x, rfl⟩)
  · obtain rfl : x = y := (isOpenEmbedding_inrInterior c).injective h
    rfl
  · exact map_orientationAt_eq_bandIncl c o (isOpenEmbedding_inrInterior c)
      (isLocalDiffeomorph_inrInterior c) hinr h
  · exact (map_orientationAt_eq_bandIncl c o (isOpenEmbedding_inlInterior c)
      (isLocalDiffeomorph_inlInterior c) hinl h.symm).symm
  · exact (map_orientationAt_eq_bandIncl c o (isOpenEmbedding_inrInterior c)
      (isLocalDiffeomorph_inrInterior c) hinr h.symm).symm
  · obtain rfl : x = y := (isOpenEmbedding_bandIncl c).injective h
    rfl

/-! ### The orientation of the double -/

/-- **The orientation of the double.** For an orientation `o` of the interior of `W`, re-modelled
on `ℝⁿ⁺¹`, the orientation of the double `c.Double` for which the first copy of the interior
preserves orientation from `o` (`Double.isOrientationPreservingAt_inlInterior`) and the second
copy preserves orientation from `-o` (`Double.isOrientationPreservingAt_inrInterior`). -/
def orientation : Manifold.Orientation (𝓡 (n + 1)) c.Double (Fin (n + 1)) :=
  iGlue (isLocalDiffeomorph_pieceMap c) (iUnion_range_pieceMap c) (o := pieceOrientation c o)
    (map_orientationAt_pieceMap c o)

private theorem orientation_def :
    orientation c o =
      iGlue (isLocalDiffeomorph_pieceMap c) (iUnion_range_pieceMap c) (o := pieceOrientation c o)
        (map_orientationAt_pieceMap c o) :=
  (rfl)

/-- The first copy of the interior of `W` preserves orientation, from `o` to the orientation of
the double. -/
theorem isOrientationPreservingAt_inlInterior (p : (𝓡∂ (n + 1)).interior W) :
    IsOrientationPreservingAt o (orientation c o) (inlInterior c) p := by
  rw [orientation_def]
  exact isOrientationPreservingAt_iGlue (isLocalDiffeomorph_pieceMap c) (iUnion_range_pieceMap c)
    (map_orientationAt_pieceMap c o) .inl p

/-- The second copy of the interior of `W` preserves orientation, from `-o` to the orientation of
the double: the collar coordinate is reflected from one copy to the other. -/
theorem isOrientationPreservingAt_inrInterior (p : (𝓡∂ (n + 1)).interior W) :
    IsOrientationPreservingAt (-o) (orientation c o) (inrInterior c) p := by
  rw [orientation_def]
  exact isOrientationPreservingAt_iGlue (isLocalDiffeomorph_pieceMap c) (iUnion_range_pieceMap c)
    (map_orientationAt_pieceMap c o) .inr p

/-- **The orientation of the double is characterized by the copies.** An orientation of the
double is `Double.orientation c o` exactly when the first copy of the interior of `W` preserves
orientation from `o` and the second from `-o`, at every point. -/
theorem eq_orientation_iff {o' : Manifold.Orientation (𝓡 (n + 1)) c.Double (Fin (n + 1))} :
    o' = orientation c o ↔
      (∀ p, IsOrientationPreservingAt o o' (inlInterior c) p) ∧
        ∀ p, IsOrientationPreservingAt (-o) o' (inrInterior c) p := by
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨isOrientationPreservingAt_inlInterior c o, isOrientationPreservingAt_inrInterior c o⟩
  refine eq_of_dense (dense_range_inlInterior_union_range_inrInterior c) ?_
  rintro _ (⟨p, rfl⟩ | ⟨p, rfl⟩)
  · exact (hl p).orientationAt_eq (isOrientationPreservingAt_inlInterior c o p)
  · exact (hr p).orientationAt_eq (isOrientationPreservingAt_inrInterior c o p)

end TauCeti.SmoothCollar.Double

end
