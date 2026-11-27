/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# The vertical projection of an Ehresmann connection

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). At every point `x` of `P`, the tangent space splits as the sum
of the horizontal space `D x` and the vertical space `ker (df_x)`. The vertical space is closed and
`D x` is finite-dimensional, so the two are complements as topological vector spaces, and the
projection onto the vertical space along `D x` is a continuous linear map: the vertical
projection `TauCeti.IsEhresmannConnection.verticalProjection`. It sends `v` to `v` minus the
horizontal lift of `df_x v` (Tau Ceti's `TauCeti.IsEhresmannConnection.projection_ker_apply`).

Over `ℝ` or `ℂ`, for a `C^n` connection on a `C^(n+1)` map whose source is modelled on a
finite-dimensional space, the vertical projections form a `C^n` section of the bundle of
endomorphisms of the tangent bundle
(`TauCeti.IsEhresmannConnection.contMDiff_verticalProjection`). The map
`v ↦ v - (horizontal lift of df v)` of the tangent bundle is `C^n` by the library's
`TauCeti.IsEhresmannConnection.contMDiff_horizontalLift`, applied along the projection of the
tangent bundle to the tangent map of `f`, and Tau Ceti's `TauCeti.contMDiff_hom_bundle_iff`
turns this map of total spaces into a section of the endomorphism bundle. Precomposing a family
of alternating maps on the tangent spaces with the vertical projections therefore keeps it as
smooth as it was, up to `C^n`: a `C^m` family stays `C^m` for `m ≤ n`
(`TauCeti.IsEhresmannConnection.contMDiffOn_compContinuousLinearMap_verticalProjection`), by
`SymplecticGeometry.contMDiff_compContinuousLinearMap_totalSpace`.

## Main definitions

* `TauCeti.IsEhresmannConnection.verticalProjection`: the projection of `T_x P` onto
  `ker (df_x)` along `D x`, as a continuous linear map.

## Main results

* `TauCeti.IsEhresmannConnection.verticalProjection_apply_eq_sub`: the vertical part of `v` is
  `v` minus the horizontal lift of `df_x v`.
* `TauCeti.IsEhresmannConnection.contMDiff_verticalProjection`: the vertical projections form a
  `C^n` section of the endomorphism bundle of `TP`.
* `TauCeti.IsEhresmannConnection.contMDiffOn_compContinuousLinearMap_verticalProjection`:
  precomposing a `C^m` family of alternating maps with the vertical projections, for `m ≤ n`,
  gives a `C^m` family.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace IsEhresmannConnection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

include hD in
/-- The vertical space `ker (df_x)` and the horizontal space `D x` of an Ehresmann connection are
complements as topological vector spaces: the projection onto either along the other is
continuous. -/
theorem isTopCompl_ker (x : P) : (mfderiv I J f x).ker.IsTopCompl (D x) :=
  have := hD.finiteDimensional x
  Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional (hD.isCompl_ker x).symm
    (mfderiv I J f x).isClosed_ker

/-- The **vertical projection** of an Ehresmann connection `D` on `f` at `x`: the projection of
`T_x P` onto the vertical space `ker (df_x)` along the horizontal space `D x`, as a continuous
linear map. -/
def verticalProjection (x : P) : TangentSpace I x →L[𝕜] TangentSpace I x :=
  (mfderiv I J f x).ker.projectionL (D x) (hD.isTopCompl_ker x)

theorem verticalProjection_def (x : P) :
    hD.verticalProjection x = (mfderiv I J f x).ker.projectionL (D x) (hD.isTopCompl_ker x) :=
  (rfl)

/-- The vertical projection does not depend on the smoothness index at which the connection is
seen. -/
theorem verticalProjection_of_le {m : ℕ∞ω} (hmn : m ≤ n) (x : P) :
    (hD.of_le hmn).verticalProjection x = hD.verticalProjection x := by
  rw [verticalProjection_def, verticalProjection_def]

/-- The vertical projection is the linear projection onto `ker (df_x)` along `D x`. -/
theorem verticalProjection_apply (x : P) (v : TangentSpace I x) :
    hD.verticalProjection x v =
      (mfderiv I J f x).ker.projection (D x) (hD.isCompl_ker x).symm v := by
  rw [verticalProjection_def, Submodule.coe_projectionL]

/-- The vertical part of `v` is `v` minus the horizontal lift of `df_x v`. -/
theorem verticalProjection_apply_eq_sub (x : P) (v : TangentSpace I x) :
    hD.verticalProjection x v = v - (hD.horizontalLift x (mfderiv I J f x v) : TangentSpace I x) :=
  by rw [verticalProjection_apply, projection_ker_apply]

/-- The vertical projection takes values in the vertical space. -/
theorem verticalProjection_apply_mem (x : P) (v : TangentSpace I x) :
    hD.verticalProjection x v ∈ (mfderiv I J f x).ker :=
  Submodule.projectionL_apply_mem _ v

/-- The derivative of `f` kills the vertical part of every vector. -/
@[simp]
theorem mfderiv_verticalProjection (x : P) (v : TangentSpace I x) :
    mfderiv I J f x (hD.verticalProjection x v) = 0 :=
  hD.verticalProjection_apply_mem x v

/-- The vertical projection fixes vertical vectors. -/
theorem verticalProjection_apply_of_mem_ker {x : P} {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J f x).ker) : hD.verticalProjection x v = v :=
  Submodule.projectionL_apply_left _ ⟨v, hv⟩

/-- The vertical projection kills horizontal vectors. -/
theorem verticalProjection_apply_eq_zero_of_mem {x : P} {v : TangentSpace I x} (hv : v ∈ D x) :
    hD.verticalProjection x v = 0 :=
  Submodule.projectionL_apply_eq_zero_of_mem_right _ hv

/-- A vector has vertical part `0` exactly when it is horizontal. -/
theorem verticalProjection_apply_eq_zero_iff {x : P} {v : TangentSpace I x} :
    hD.verticalProjection x v = 0 ↔ v ∈ D x :=
  Submodule.projectionL_apply_eq_zero_iff _

/-- The kernel of the vertical projection is the horizontal space. -/
@[simp]
theorem ker_verticalProjection (x : P) : (hD.verticalProjection x).ker = D x :=
  Submodule.ker_projectionL _

/-- The range of the vertical projection is the vertical space. -/
@[simp]
theorem range_verticalProjection (x : P) :
    (hD.verticalProjection x).range = (mfderiv I J f x).ker :=
  Submodule.range_projectionL _

/-- The vertical projection is idempotent. -/
@[simp]
theorem verticalProjection_verticalProjection (x : P) (v : TangentSpace I x) :
    hD.verticalProjection x (hD.verticalProjection x v) = hD.verticalProjection x v :=
  hD.verticalProjection_apply_of_mem_ker (hD.verticalProjection_apply_mem x v)

section Smooth

/-! ### Smoothness -/

variable [IsRCLikeNormedField 𝕜] [IsManifold J 1 B]

/-- **The vertical projection is smooth, on the tangent bundle.** For a `C^n` Ehresmann
connection on a `C^(n+1)` map `f`, the map `v ↦ (vertical part of v)` from the tangent bundle of
`P` to itself is `C^n`. -/
theorem contMDiff_totalSpace_verticalProjection (hf : ContMDiff I J (n + 1) f) :
    ContMDiff I.tangent I.tangent n
      (fun v : TangentBundle I P ↦
        (⟨v.proj, hD.verticalProjection v.proj v.snd⟩ : TangentBundle I P)) := by
  have hT : ContMDiff I.tangent J.tangent n (tangentMap I J f) :=
    hf.contMDiff_tangentMap le_rfl
  have hl := hD.contMDiff_horizontalLift (g := TotalSpace.proj) (w := tangentMap I J f)
    (fun _ ↦ rfl) hf (contMDiff_proj _) hT
  have hid : ContMDiff I.tangent I.tangent n (fun v : TangentBundle I P ↦ v) := contMDiff_id
  simpa only [verticalProjection_apply_eq_sub, tangentMap] using hid.sub_sectionAlong hl

/-- **The vertical projection is smooth.** For a `C^n` Ehresmann connection on a `C^(n+1)` map
`f`, the vertical projections form a `C^n` section of the bundle of endomorphisms of the tangent
bundle of `P`. -/
theorem contMDiff_verticalProjection [FiniteDimensional 𝕜 E] (hf : ContMDiff I J (n + 1) f) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x ↦ TangentSpace I x →L[𝕜] TangentSpace I x) x (hD.verticalProjection x)) :=
  (contMDiff_hom_bundle_iff _).2 (hD.contMDiff_totalSpace_verticalProjection hf)

variable {ι : Type*} [Fintype ι] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {W : P → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [TopologicalSpace (TotalSpace F' W)]
  [FiberBundle F' W] [VectorBundle 𝕜 F' W]

/-- **Precomposing with the vertical projection keeps forms smooth.** For a `C^n` Ehresmann
connection on a `C^(n+1)` map `f`, with `P` modelled on a finite-dimensional space, and `m ≤ n`:
if a family `α x` of alternating maps on `T_x P`, with values in the fibres of a vector bundle `W`,
is `C^m` on a set `u`, so is the family of its precompositions with the vertical projections,
`x ↦ (α x).compContinuousLinearMap (verticalProjection x)`. -/
theorem contMDiffOn_compContinuousLinearMap_verticalProjection [FiniteDimensional 𝕜 E]
    (hf : ContMDiff I J (n + 1) f)
    {m : ℕ∞} (hm : (m : ℕ∞ω) ≤ n) {α : Π x : P, TangentSpace I x [⋀^ι]→L[𝕜] W x} {u : Set P}
    (hα : ContMDiffOn I (I.prod 𝓘(𝕜, E [⋀^ι]→L[𝕜] F')) m
      (fun x ↦ TotalSpace.mk' (E [⋀^ι]→L[𝕜] F')
        (E := fun x ↦ TangentSpace I x [⋀^ι]→L[𝕜] W x) x (α x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, E [⋀^ι]→L[𝕜] F')) m
      (fun x ↦ TotalSpace.mk' (E [⋀^ι]→L[𝕜] F')
        (E := fun x ↦ TangentSpace I x [⋀^ι]→L[𝕜] W x) x
        ((α x).compContinuousLinearMap (hD.verticalProjection x))) u :=
  (SymplecticGeometry.contMDiff_compContinuousLinearMap_totalSpace _
    ((hD.contMDiff_verticalProjection hf).of_le hm)).comp_contMDiffOn hα

end Smooth

end IsEhresmannConnection

end TauCeti
