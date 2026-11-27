/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.TotalSpace.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Topology.FiberBundle.Basic
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# The zero section of a vector bundle as a smooth embedding

For a `C^n` vector bundle `V`, with `1 ≤ n` (`n = ω` included), with finite-dimensional model
fibre `F` over a manifold `B` without boundary, with finite-dimensional model, the zero section
`B → TotalSpace F V` is a `C^n` embedding: the bundle projection is a smooth left inverse of it.
This file bundles it as
`SymplecticGeometry.Bundle.zeroSectionEmbedding`, so that results about submanifolds, such as the
neighbourhood theorems, apply to it, and shows that its image is closed. It also reads the zero
section in the preferred charts of the total space, and computes the differential of a map along
the zero section on horizontal and on vertical vectors, and notes that Tau Ceti's fibrewise
linear diffeomorphisms `TauCeti.bundleDiffeomorph` of total spaces, and their inverses, fix the
zero section. Finally, for a map on the total space that is smooth along the zero section, the
velocities at `0` of the images of the rays `t ↦ t • v` in the fibres form a smooth map on the
total space.

The file has the path of Tau Ceti's `Geometry/Manifold/VectorBundle/ZeroSection.lean`, which
splits the tangent spaces along the zero section. The zero section as an embedding is the
library's own definition, in `SymplecticGeometry.Bundle`. Of the other lemmas,
`isClosed_range_zeroSection`, about Mathlib's notions alone, and
`zeroSectionTangentEquiv_symm_inl`, `mfderiv_zeroSectionTangentEquiv_symm_inl` and
`mfderiv_zeroSectionTangentEquiv_symm_inr`, about Tau Ceti's splitting, are in Tau Ceti's
namespace `TauCeti.Bundle`, `bundleDiffeomorph_zeroSection` and
`bundleDiffeomorph_symm_zeroSection`, about Tau Ceti's `bundleDiffeomorph`, are in its namespace
`TauCeti`, and
`extChartAt_symm_apply_zero_of_mem_baseSet`, about the charts of the total space,
`contMDiff_totalSpaceMk_comp`, about linear maps into one fibre,
`hasMFDerivAt_totalSpaceMk_trivializationAt_symm`, about the inclusion of one fibre,
`contMDiff_subtypeMk_zeroSection` and `subtypeVal_comp_subtypeMk_zeroSection`, about the zero
section as a map into a set that contains it, `contMDiff_of_apply_zeroSection`, about maps
that factor through it, and
`contMDiff_mfderiv_smul_curve`, about maps on the total space, in Mathlib's namespace `Bundle`.

## Main definitions

* `SymplecticGeometry.Bundle.zeroSectionEmbedding`: the zero section, as a `C^n` embedding for
  every `n` with `1 ≤ n`, `n = ω` included.

## Main results

* `SymplecticGeometry.Bundle.coe_zeroSectionEmbedding`: its underlying map is `zeroSection F V`.
* `TauCeti.Bundle.isClosed_range_zeroSection`: the image of the zero section is closed when the
  total space is Hausdorff.
* `TauCeti.bundleDiffeomorph_zeroSection`, `TauCeti.bundleDiffeomorph_symm_zeroSection`: the
  diffeomorphism of total spaces given by a smooth family of fibrewise continuous linear
  equivalences, and its inverse, send the zero vector over `b` to the zero vector over `b`.
* `Bundle.extChartAt_symm_apply_zero_of_mem_baseSet`: the inverse of the preferred chart of the
  total space sends `(y, 0)` to the zero vector over the base point with coordinate `y`.
* `Bundle.contMDiff_totalSpaceMk_comp`: a continuous linear map from a normed space into one
  fibre, followed by the inclusion of that fibre into the total space, is `C^n` for every `n`.
  Its proof follows that of Tau Ceti's `TauCeti.Manifold.contMDiff_totalSpaceMk`, the case of
  the identity of a normed fibre.
* `Bundle.hasMFDerivAt_totalSpaceMk_trivializationAt_symm`: the inclusion of a fibre into the
  total space, read through the preferred trivialization, has derivative `w ↦ (0, w)`.
* `Bundle.contMDiff_subtypeMk_zeroSection`: the zero section, as a map into an open set of the
  total space that contains it, is `C^n` for every `n`.
* `Bundle.contMDiff_of_apply_zeroSection`: a map on the base that agrees on the zero section
  with a `C^n` map from an open set of the total space is `C^n`.
* `TauCeti.Bundle.zeroSectionTangentEquiv_symm_inl`: the inverse of Tau Ceti's splitting sends
  the horizontal vector `(u, 0)` at `b` to the image of `u` under the differential of the zero
  section.
* `TauCeti.Bundle.mfderiv_zeroSectionTangentEquiv_symm_inl`: a map on the total space that agrees
  with a map `g` on the zero section near `b` has, at `0_b`, a differential that sends the
  horizontal vector `(u, 0)` of Tau Ceti's splitting to `dg u`.
* `TauCeti.Bundle.mfderiv_zeroSectionTangentEquiv_symm_inr`: at `0_b`, the differential of a map
  `f` on the total space sends the vertical vector `(0, v)` of Tau Ceti's splitting to the
  velocity at `0` of `t ↦ f (t • v)`.
* `Bundle.contMDiff_mfderiv_smul_curve`: for a map `Φ` on the total space, smooth along the zero
  section, where it restricts to a smooth map `f`, the velocities at `0` of `t ↦ Φ (t • v)` form
  a smooth map into the pull-back along `f` of the tangent bundle.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {B : Type*} [TopologicalSpace B]

namespace TauCeti.Bundle

/-- The image of the zero section of a vector bundle with Hausdorff total space is closed: the
zero section has the projection as a continuous left inverse. -/
theorem isClosed_range_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (V : B → Type*) [∀ b, AddCommMonoid (V b)]
    [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] [T2Space (TotalSpace F V)] :
    IsClosed (range (zeroSection F V)) :=
  Function.LeftInverse.isClosed_range (zeroSection_proj F V) (FiberBundle.continuous_proj F V)
    (Trivialization.continuous_zeroSection 𝕜)

end TauCeti.Bundle

namespace SymplecticGeometry.Bundle

open TauCeti

variable {𝕜 EB HB : Type*} [RCLike 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [IB.Boundaryless]
  {n : WithTop ℕ∞} [ChartedSpace HB B] [IsManifold IB n B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ b, AddCommMonoid (V b)] [∀ b, Module 𝕜 (V b)]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V IB]

variable (IB F V) in
/-- The zero section of a `C^n` vector bundle, `1 ≤ n`, with finite-dimensional model fibre over
a manifold without boundary with finite-dimensional model, as a `C^n` embedding of the base into
the total space. For `n = ω` it is an analytic embedding. -/
def zeroSectionEmbedding (hn : 1 ≤ n) :
    SmoothEmbedding IB (IB.prod 𝓘(𝕜, F)) n B (TotalSpace F V) :=
  SmoothEmbedding.ofIsSmoothEmbedding (zeroSection F V)
    ((contMDiff_zeroSection 𝕜 V).isSmoothEmbedding_of_leftInverse hn
      (contMDiff_proj V) (zeroSection_proj F V))

variable (IB F V) in
/-- The underlying map of `zeroSectionEmbedding` is the zero section. -/
@[simp]
theorem coe_zeroSectionEmbedding (hn : 1 ≤ n) :
    ⇑(zeroSectionEmbedding IB F V hn) = zeroSection F V :=
  SmoothEmbedding.coe_ofIsSmoothEmbedding _ _

end SymplecticGeometry.Bundle

namespace TauCeti

variable {𝕜 F₁ F₂ EB HB : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  (e : ∀ x, E₁ x ≃L[𝕜] E₂ x)
  (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
    (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.snd)))

/-- The diffeomorphism `bundleDiffeomorph e he` of total spaces, being linear on each fibre,
sends the zero vector over `b` to the zero vector over `b`. -/
theorem bundleDiffeomorph_zeroSection (b : B) :
    bundleDiffeomorph e he (zeroSection F₁ E₁ b) = zeroSection F₂ E₂ b := by
  rw [bundleDiffeomorph_apply]
  exact congrArg (TotalSpace.mk b) (map_zero (e b))

/-- The inverse of the diffeomorphism `bundleDiffeomorph e he` of total spaces sends the zero
vector over `b` to the zero vector over `b`. -/
theorem bundleDiffeomorph_symm_zeroSection (b : B) :
    (bundleDiffeomorph e he).symm (zeroSection F₂ E₂ b) = zeroSection F₁ E₁ b := by
  rw [bundleDiffeomorph_symm_apply]
  exact congrArg (TotalSpace.mk b) (map_zero (e b).symm)

end TauCeti

namespace Bundle

variable {𝕜 F EB HB : Type*} [NontriviallyNormedField 𝕜] {V : B → Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The inverse of the preferred chart at `p` sends `(y, 0)`, with `y` over the base set of the
trivialization at `p.proj`, to the zero vector over `(extChartAt IB p.proj).symm y`. -/
theorem extChartAt_symm_apply_zero_of_mem_baseSet (p : TotalSpace F V) {y : EB}
    (hy : (extChartAt IB p.proj).symm y ∈ (trivializationAt F V p.proj).baseSet) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm (y, 0) =
      zeroSection F V ((extChartAt IB p.proj).symm y) := by
  rw [extChartAt_symm_apply_of_mem_baseSet p hy, ← Trivialization.symmₗ_apply (R := 𝕜) _ hy,
    map_zero, zeroSection_def]

/-- A continuous linear map `L` from a normed space into the fibre over `b`, followed by the
inclusion of that fibre into the total space, is `C^n` for every `n`. -/
theorem contMDiff_totalSpaceMk_comp {Q : Type*} [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
    {n : WithTop ℕ∞} (b : B) (L : Q →L[𝕜] V b) :
    ContMDiff 𝓘(𝕜, Q) (IB.prod 𝓘(𝕜, F)) n (fun w ↦ TotalSpace.mk' F b (L w)) := by
  have hb := FiberBundle.mem_baseSet_trivializationAt F V b
  intro w
  refine contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_const, ?_⟩
  exact ((trivializationAt F V b).continuousLinearMapAt 𝕜 b ∘L L).contMDiff.contMDiffAt
    |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' ↦
      ((trivializationAt F V b).continuousLinearMapAt_apply_of_mem 𝕜 hb (L w')).symm)

omit [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V] in
/-- The inclusion of the fibre over `b` into the total space, read through the preferred
trivialization at `b`, `w ↦ (b, e⁻¹ w)`, has at every `w₀` the derivative `w ↦ (0, w)`. -/
theorem hasMFDerivAt_totalSpaceMk_trivializationAt_symm (b : B) (w₀ : F) :
    HasMFDerivAt 𝓘(𝕜, F) (IB.prod 𝓘(𝕜, F))
      (fun w ↦ TotalSpace.mk' F b ((trivializationAt F V b).symm b w)) w₀
      (ContinuousLinearMap.inr 𝕜 EB F) := by
  have hb := FiberBundle.mem_baseSet_trivializationAt F V b
  refine TauCeti.Manifold.hasMFDerivAt_totalSpace_iff.2 ⟨?_, ?_⟩
  · -- The base point is constant; the tangent space of the base is `EB` only up to unfolding
    -- `TangentSpace`, so the first component of `inr` is computed by `rfl`.
    convert hasMFDerivAt_const (I := 𝓘(𝕜, F)) (I' := IB) b w₀ using 1
    ext w
    rfl
  · refine hasMFDerivAt_iff_hasFDerivAt.2 <| ((hasFDerivAt_id w₀).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w ↦
        congrArg Prod.snd ((trivializationAt F V b).apply_mk_symm hb w))).congr_fderiv ?_
    -- As above, the second component of `inr` is the identity only up to unfolding.
    ext w
    rfl

/-- The zero section, as a map into an open set `U` of the total space that contains it, is
`C^n`. -/
theorem contMDiff_subtypeMk_zeroSection {n : WithTop ℕ∞}
    {U : TopologicalSpace.Opens (TotalSpace F V)} (hU : ∀ b, zeroSection F V b ∈ U) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun b ↦ (⟨zeroSection F V b, hU b⟩ : U)) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff U _).1 (contMDiff_zeroSection 𝕜 V)

omit [TopologicalSpace B] [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] in
/-- The zero section, as a map into a set `U` of the total space that contains it, followed by
the inclusion of `U`, is the zero section. -/
theorem subtypeVal_comp_subtypeMk_zeroSection {U : Set (TotalSpace F V)}
    (hU : ∀ b, zeroSection F V b ∈ U) :
    Subtype.val ∘ (fun b ↦ (⟨zeroSection F V b, hU b⟩ : U)) = zeroSection F V :=
  (rfl)

/-- Let `ι : U → W` be a `C^n` map from an open set `U` of the total space to an open set `W` of
a manifold `M`. If the zero vector over each `b` lies in `U` and `ι` sends it to `f b`, then
`f : B → M` is `C^n`, being `ι` composed with the zero section. -/
theorem contMDiff_of_apply_zeroSection {EM HM M : Type*} [NormedAddCommGroup EM]
    [NormedSpace 𝕜 EM] [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M]
    [ChartedSpace HM M] {n : WithTop ℕ∞} {U : TopologicalSpace.Opens (TotalSpace F V)}
    {W : TopologicalSpace.Opens M} {ι : U → W} (hι : ContMDiff (IB.prod 𝓘(𝕜, F)) IM n ι)
    {f : B → M} (hιf : ∀ b, ∃ h : zeroSection F V b ∈ U, (ι ⟨_, h⟩ : M) = f b) :
    ContMDiff IB IM n f :=
  (contMDiff_subtypeVal.comp (hι.comp (contMDiff_subtypeMk_zeroSection fun b ↦ (hιf b).1))).congr
    fun b ↦ (hιf b).2.symm

end Bundle

namespace TauCeti.Bundle

open scoped Topology

variable {𝕜 F EB HB EM HM M : Type*} [NontriviallyNormedField 𝕜] {V : B → Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- The splitting `zeroSectionTangentEquiv b` sends the horizontal vector `(u, 0)` back to the
image of `u` under the differential of the zero section at `b`. -/
theorem zeroSectionTangentEquiv_symm_inl (b : B) (u : TangentSpace IB b) :
    (zeroSectionTangentEquiv (I := IB) b).symm (u, 0) =
      mfderiv IB (IB.prod 𝓘(𝕜, F)) (zeroSection F V) b u := by
  rw [zeroSectionTangentEquiv_symm_eq, Prod.mk_zero_zero, map_zero, add_zero]

/-- Let `f` be a map on the total space, differentiable at the zero vector `0_b`, which agrees with
a map `g` on the zero section near `b`. Then the differential of `f` at `0_b` sends the horizontal
vector `(u, 0)` of the splitting `zeroSectionTangentEquiv b` to `dg u`. -/
theorem mfderiv_zeroSectionTangentEquiv_symm_inl {f : TotalSpace F V → M} {g : B → M} {b : B}
    (hf : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) IM f (zeroSection F V b))
    (hfg : f ∘ zeroSection F V =ᶠ[𝓝 b] g) (u : TangentSpace IB b) :
    mfderiv (IB.prod 𝓘(𝕜, F)) IM f (zeroSection F V b)
        ((zeroSectionTangentEquiv (I := IB) b).symm (u, 0)) = mfderiv IB IM g b u := by
  rw [zeroSectionTangentEquiv_symm_inl,
    ← mfderiv_comp_apply b hf (mdifferentiableAt_zeroSection 𝕜 V), hfg.mfderiv_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  exact eq_of_heq (heq_tangentSpaceCast hfg.eq_of_nhds.symm _)

/-- Let `f` be a map on the total space, differentiable at the zero vector `0_b`. Then the
differential of `f` at `0_b` sends the vertical vector `(0, v)` of the splitting
`zeroSectionTangentEquiv b` to the velocity at `0` of the image `t ↦ f (t • v)` of the line
through `v` in the fibre over `b`. -/
theorem mfderiv_zeroSectionTangentEquiv_symm_inr {f : TotalSpace F V → M} {b : B}
    (hf : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) IM f (zeroSection F V b)) (v : V b) :
    mfderiv (IB.prod 𝓘(𝕜, F)) IM f (zeroSection F V b)
        ((zeroSectionTangentEquiv (I := IB) b).symm (0, v)) =
      mfderiv 𝓘(𝕜) IM (fun t : 𝕜 ↦ f ⟨b, t • v⟩) 0 (1 : 𝕜) := by
  have hl := (TotalSpace.hasMFDerivAt_smul_curve (IB := IB) (⟨b, v⟩ : TotalSpace F V)
    (hasDerivAt_id' (0 : 𝕜))).mdifferentiableAt
  rw [zeroSectionTangentEquiv_symm_inr]
  exact (mfderiv_comp_apply_of_eq (0 : 𝕜) hf hl (by simp [zeroSection_def]) (1 : 𝕜)).symm

end TauCeti.Bundle

namespace Bundle

open scoped Topology

variable {𝕜 F EB HB EN HN N : Type*} [NontriviallyNormedField 𝕜] {V : B → Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] [IsManifold IB ∞ B]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle ∞ F V IB]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {J : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]

/-- Let `Φ` be a map on the total space of a smooth vector bundle, smooth at every zero vector,
which restricts to a smooth map `f` on the zero section. Then the velocities at `0` of the curves
`t ↦ Φ ⟨b, t • v⟩`, which are tangent vectors at `Φ 0_b = f b`, form a smooth map from the total
space into the pull-back along `f` of the tangent bundle. -/
theorem contMDiff_mfderiv_smul_curve {Φ : TotalSpace F V → N} {f : C^∞⟮IB, B; J, N⟯}
    (hΦ : ∀ b, ContMDiffAt (IB.prod 𝓘(𝕜, F)) J ∞ Φ (zeroSection F V b))
    (hfΦ : Φ ∘ zeroSection F V = f) :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, EN)) ∞
      (fun p : TotalSpace F V ↦
        (⟨p.proj, mfderiv 𝓘(𝕜) J (fun t : 𝕜 ↦ Φ ⟨p.proj, t • p.snd⟩) 0 (1 : 𝕜)⟩ :
          TotalSpace EN ((f : B → N) *ᵖ (TangentSpace J)))) := by
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  have h0 (q : TotalSpace F V) : Φ ⟨q.proj, (0 : 𝕜) • q.snd⟩ = f q.proj := by
    rw [zero_smul]
    exact congrFun hfΦ q.proj
  intro p₀
  rw [Pullback.contMDiffAt_iff f (f.contMDiff _), contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, (f.contMDiff _).comp _ (contMDiffAt_proj _), ?_⟩
  -- The curves form a smooth family parametrized by the total space.
  have hF : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜)) J ∞
      (Function.uncurry fun (p : TotalSpace F V) (t : 𝕜) ↦ Φ ⟨p.proj, t • p.snd⟩) (p₀, 0) :=
    (hΦ p₀.proj).comp_of_eq (contMDiffAt_snd.smul_totalSpace contMDiffAt_fst)
      (by simp [zeroSection_def])
  refine ((ContMDiffAt.mfderiv _ (fun _ ↦ (0 : 𝕜)) hF (m := ∞) contMDiffAt_const
    (by simp)).clm_apply (contMDiffAt_const (c := (1 : 𝕜)))).congr_of_eventuallyEq ?_
  let e := trivializationAt EN (TangentSpace J) (f p₀.proj)
  have hb : ∀ᶠ p in 𝓝 p₀, f p.proj ∈ e.baseSet :=
    (f.contMDiff.continuous.comp (FiberBundle.continuous_proj F V)).continuousAt
      |>.eventually_mem_baseSet_trivializationAt EN (TangentSpace J)
  filter_upwards [hb] with p hp
  -- The base point of the coordinate change is `Φ 0_b`, which is `f b`.
  have key (b : N) (w : EN) (hb : b = f p.proj) :
      e.continuousLinearMapAt 𝕜 b w = (e ⟨f p.proj, w⟩).2 := by
    subst hb
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hp w
  simp only [Pullback.lift, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, TangentBundle.symmL_model_space, h0 p₀]
  -- `(D ∘L 1) 1` is `D 1` by definition; the source `TangentSpace 𝓘(𝕜) 0` of `D`, which is `𝕜`
  -- only by definition, keeps `ContinuousLinearMap.comp_apply` from rewriting it.
  exact (key _ _ (h0 p)).symm

end Bundle


end
