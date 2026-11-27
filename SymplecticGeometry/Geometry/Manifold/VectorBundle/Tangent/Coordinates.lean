/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Topology.VectorBundle.Frame
import TauCeti.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Families of linear maps in tangent coordinates

This file reads families of continuous linear maps into the tangent spaces of a manifold `M`,
modelled on `E`, in the tangent coordinates of a chart.

On the overlap of the charts at `x` and `y`, the tangent coordinate changes from `x` to `y` and
from `y` to `x` are mutually inverse (`tangentCoordChange_comp_tangentCoordChange`,
`isInvertible_tangentCoordChange`, `inverse_tangentCoordChange`), by Tau Ceti's
`TauCeti.tangentCoordChange_tangentCoordChange`.

A continuous linear endomorphism `J₀` of `E` gives the constant family `y ↦ J₀` of endomorphisms
of the tangent spaces `T_x M = E`. Read in the tangent coordinates of the chart at a point `x₀`,
this family is `J₀` at each point `x` of the chart's source at which `J₀` commutes with the
tangent coordinate change from the chart at `x` to the chart at `x₀`
(`inTangentCoordinates_const`). The proof writes the reading by Mathlib's
`inTangentCoordinates_eq` as a conjugate of `J₀` by tangent coordinate changes and cancels them.
It follows that of the private lemma `inTangentCoordinates_I_smul_id` of Tau Ceti's
`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Basic.lean`, the case of multiplication by
`i` on a complex model space.

For a family of maps from a model space into the tangent spaces, the coordinates on the source
play no role (`inTangentCoordinates_model_space_source`): in tangent coordinates the family is
its composite with the tangent coordinate changes of `M`
(`inTangentCoordinates_eq_tangentCoordChange_comp`). For the same reason, reading in tangent
coordinates commutes with composing on the right with linear maps between model spaces
(`inTangentCoordinates_clm_comp`) and with taking the coprod of two families
(`inTangentCoordinates_coprod`), at every point. Hence a family that is `Cⁿ` in tangent
coordinates stays so after composing on the right with a `Cⁿ` family of linear maps between model
spaces (`ContMDiffAt.inTangentCoordinates_clm_comp`, a smooth counterpart of Tau Ceti's
`ContinuousAt.inCoordinates_clm_comp`), and two such families give one on the product
(`ContMDiffAt.inTangentCoordinates_clm_coprod`). Such a family that is
continuous as a map `X × G → TM` is continuous in tangent coordinates
(`continuousAt_inTangentCoordinates_of_continuous`, from
`Bundle.Trivialization.continuousOn_continuousLinearMapAt_comp`). Conversely, a family that is
continuous in tangent coordinates is continuous as a map `X × G → TM`
(`continuous_of_continuousAt_inTangentCoordinates`, from Mathlib's
`ContinuousAt.clm_apply_of_inCoordinates`), and a fixed map read in one
chart and carried to the tangent spaces along a `Cⁿ` map by the tangent coordinate changes is
`Cⁿ` in tangent coordinates (`contMDiffAt_inTangentCoordinates_tangentCoordChange_comp`).

A family of maps `A x : G → T_(g x) M`, `Cᵐ` in tangent coordinates, composed with the
differential of a `Cⁿ` map `φ : M → V` with `m + 1 ≤ n`, is a `Cᵐ` family of linear maps `G → V`
(`contMDiffAt_mvfderiv_comp_of_inTangentCoordinates`), from Mathlib's `ContMDiffAt.mfderiv`.
-/

public section

namespace SymplecticGeometry

open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change from `y` to `x`
undoes that from `x` to `y`. -/
theorem tangentCoordChange_comp_tangentCoordChange {x y z : M}
    (hx : z ∈ (extChartAt I x).source) (hy : z ∈ (extChartAt I y).source) :
    tangentCoordChange I y x z ∘L tangentCoordChange I x y z = .id 𝕜 E :=
  ContinuousLinearMap.ext (TauCeti.tangentCoordChange_tangentCoordChange hx hy)

/-- On the overlap of the charts at `x` and `y`, the tangent coordinate change from `x` to `y` is
invertible. -/
theorem isInvertible_tangentCoordChange {x y z : M} (hx : z ∈ (extChartAt I x).source)
    (hy : z ∈ (extChartAt I y).source) : (tangentCoordChange I x y z).IsInvertible :=
  .of_inverse (tangentCoordChange_comp_tangentCoordChange I hy hx)
    (tangentCoordChange_comp_tangentCoordChange I hx hy)

/-- On the overlap of the charts at `x` and `y`, the inverse of the tangent coordinate change from
`x` to `y` is the tangent coordinate change from `y` to `x`. -/
theorem inverse_tangentCoordChange {x y z : M} (hx : z ∈ (extChartAt I x).source)
    (hy : z ∈ (extChartAt I y).source) :
    (tangentCoordChange I x y z).inverse = tangentCoordChange I y x z :=
  ContinuousLinearMap.inverse_eq (tangentCoordChange_comp_tangentCoordChange I hy hx)
    (tangentCoordChange_comp_tangentCoordChange I hx hy)

/-- Let `x` be in the source of the chart at `x₀`. If a continuous linear endomorphism `J₀` of the
model space commutes with the tangent coordinate change at `x` from the chart at `x` to the chart
at `x₀`, then the constant family `y ↦ J₀` of endomorphisms of the tangent spaces, read in the
tangent coordinates of the chart at `x₀`, is `J₀` at `x`. -/
theorem inTangentCoordinates_const (J₀ : E →L[𝕜] E) {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (h : ∀ v : E, tangentCoordChange I x x₀ x (J₀ v) = J₀ (tangentCoordChange I x x₀ x v)) :
    inTangentCoordinates I I id id
        (fun x : M ↦ (J₀ : TangentSpace I x →L[𝕜] TangentSpace I x)) x₀ x = J₀ := by
  refine (inTangentCoordinates_eq (I := I) (I' := I) id id _ hx hx).trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [ContinuousLinearMap.comp_apply]
  exact (h _).trans
    (congrArg J₀ (TauCeti.tangentCoordChange_tangentCoordChange (by simp [hx]) (by simp) _))

/-- Read in the tangent coordinates at `x₀`, a family of maps `ϕ x` from a model space `G` into
the tangent spaces `T_(g x) M` is, at each `x` with `g x` in the source of the chart at `g x₀`,
the map `ϕ x` followed by the tangent coordinate change from the chart at `g x` to the chart at
`g x₀`. The coordinates on the model space `G` play no role. -/
theorem inTangentCoordinates_eq_tangentCoordChange_comp {G X : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {f : X → G} {g : X → M} (ϕ : ∀ x, G →L[𝕜] TangentSpace I (g x))
    {x₀ x : X} (hx : g x ∈ (chartAt H (g x₀)).source) :
    inTangentCoordinates 𝓘(𝕜, G) I f g ϕ x₀ x =
      tangentCoordChange I (g x) (g x₀) (g x) ∘L ϕ x := by
  rw [inTangentCoordinates_eq f g ϕ (by simp) hx, tangentBundleCore_coordChange_model_space]
  -- The identity on the right is that of `TangentSpace 𝓘(𝕜, G) (f x)`, which is `G` only up to
  -- unfolding, so `ContinuousLinearMap.comp_id` does not rewrite it.
  rfl

/-- Read in tangent coordinates, a family of maps `ϕ x` from a model space `G` into the tangent
spaces `T_(g x) M` does not depend on the map `f : X → G` along which the source is read: the
tangent bundle of a model space is trivialized by the identity. -/
theorem inTangentCoordinates_model_space_source {G X : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f f' : X → G) (g : X → M) (ϕ : ∀ x, G →L[𝕜] TangentSpace I (g x))
    (x₀ : X) :
    inTangentCoordinates 𝓘(𝕜, G) I f g ϕ x₀ = inTangentCoordinates 𝓘(𝕜, G) I f' g ϕ x₀ := by
  ext1 x
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.symmL_model_space]
  -- Both sides compose with the identity of `TangentSpace 𝓘(𝕜, G)` at `f x` and at `f' x`,
  -- which are both `G` only up to unfolding.
  rfl

/-- Read in tangent coordinates, the composite of a family of maps `A x` from a model space `G`
into the tangent spaces `T_(g x) M` with a family of linear maps `U x : G' → G` is the reading of
`A` composed with `U`. -/
theorem inTangentCoordinates_clm_comp {G G' X : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] (f : X → G) (f' : X → G') (g : X → M)
    (A : ∀ x, G →L[𝕜] TangentSpace I (g x)) (U : X → G' →L[𝕜] G) (x₀ : X) :
    inTangentCoordinates 𝓘(𝕜, G') I f' g (fun x ↦ A x ∘L U x) x₀ =
      fun x ↦ inTangentCoordinates 𝓘(𝕜, G) I f g A x₀ x ∘L U x := by
  ext1 x
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.symmL_model_space]
  -- The identities of `TangentSpace 𝓘(𝕜, G')` at `f' x` and of `TangentSpace 𝓘(𝕜, G)` at `f x`
  -- are those of `G'` and `G` only up to unfolding.
  rfl

/-- Read in tangent coordinates, the coprod of two families of maps `A x : G₁ → T_(g x) M` and
`B x : G₂ → T_(g x) M` from model spaces is the coprod of their readings. -/
theorem inTangentCoordinates_coprod {G₁ G₂ X : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁]
    [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] (f₁ : X → G₁) (f₂ : X → G₂) (f : X → G₁ × G₂)
    (g : X → M) (A : ∀ x, G₁ →L[𝕜] TangentSpace I (g x)) (B : ∀ x, G₂ →L[𝕜] TangentSpace I (g x))
    (x₀ : X) :
    inTangentCoordinates 𝓘(𝕜, G₁ × G₂) I f g (fun x ↦ (A x).coprod (B x)) x₀ =
      fun x ↦ (inTangentCoordinates 𝓘(𝕜, G₁) I f₁ g A x₀ x).coprod
        (inTangentCoordinates 𝓘(𝕜, G₂) I f₂ g B x₀ x) := by
  ext1 x
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.symmL_model_space]
  exact ContinuousLinearMap.comp_coprod _ _ _

/-- Let `A x : G → T_(g x) M` be a family of maps along a map `g : X → M`, and `U x : G' → G` a
family of linear maps between model spaces. If `A` read in tangent coordinates and `U` are both
`Cⁿ` at `x₀`, then so is `x ↦ A x ∘ U x` read in tangent coordinates. This is a smooth
counterpart of Tau Ceti's `ContinuousAt.inCoordinates_clm_comp`. -/
theorem _root_.ContMDiffAt.inTangentCoordinates_clm_comp {n : WithTop ℕ∞}
    {G G' X EX HX : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G']
    [NormedSpace 𝕜 G'] [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f : X → G} {f' : X → G'} {g : X → M} {A : ∀ x, G →L[𝕜] TangentSpace I (g x)}
    {U : X → G' →L[𝕜] G} {x₀ : X}
    (hA : ContMDiffAt IX 𝓘(𝕜, G →L[𝕜] E) n (inTangentCoordinates 𝓘(𝕜, G) I f g A x₀) x₀)
    (hU : ContMDiffAt IX 𝓘(𝕜, G' →L[𝕜] G) n U x₀) :
    ContMDiffAt IX 𝓘(𝕜, G' →L[𝕜] E) n
      (inTangentCoordinates 𝓘(𝕜, G') I f' g (fun x ↦ A x ∘L U x) x₀) x₀ := by
  rw [SymplecticGeometry.inTangentCoordinates_clm_comp I f f' g A U x₀]
  exact hA.clm_comp hU

/-- Let `A x : G₁ → T_(g x) M` and `B x : G₂ → T_(g x) M` be families of maps along a map
`g : X → M`. If both are `Cⁿ` at `x₀` when read in tangent coordinates, then so is the family
`x ↦ (A x).coprod (B x)` of maps `G₁ × G₂ → T_(g x) M`. -/
theorem _root_.ContMDiffAt.inTangentCoordinates_clm_coprod {n : WithTop ℕ∞}
    {G₁ G₂ X EX HX : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [NormedAddCommGroup G₂]
    [NormedSpace 𝕜 G₂] [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f₁ : X → G₁} {f₂ : X → G₂} {f : X → G₁ × G₂} {g : X → M}
    {A : ∀ x, G₁ →L[𝕜] TangentSpace I (g x)} {B : ∀ x, G₂ →L[𝕜] TangentSpace I (g x)} {x₀ : X}
    (hA : ContMDiffAt IX 𝓘(𝕜, G₁ →L[𝕜] E) n (inTangentCoordinates 𝓘(𝕜, G₁) I f₁ g A x₀) x₀)
    (hB : ContMDiffAt IX 𝓘(𝕜, G₂ →L[𝕜] E) n (inTangentCoordinates 𝓘(𝕜, G₂) I f₂ g B x₀) x₀) :
    ContMDiffAt IX 𝓘(𝕜, G₁ × G₂ →L[𝕜] E) n
      (inTangentCoordinates 𝓘(𝕜, G₁ × G₂) I f g (fun x ↦ (A x).coprod (B x)) x₀) x₀ := by
  rw [inTangentCoordinates_coprod I f₁ f₂ f g A B x₀]
  exact hA.clm_coprod hB

/-- A family of maps `ϕ x` from a finite-dimensional normed space `G` into the tangent spaces
`T_(g x) M`, continuous as a map `X × G → TM`, is continuous at `x₀` when read in the tangent
coordinates at `x₀`. -/
theorem continuousAt_inTangentCoordinates_of_continuous [CompleteSpace 𝕜] {G X : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G] [TopologicalSpace X]
    {f : X → G} {g : X → M} {ϕ : ∀ x, G →L[𝕜] TangentSpace I (g x)}
    (hϕ : Continuous fun q : X × G ↦ (⟨g q.1, ϕ q.1 q.2⟩ : TangentBundle I M)) (x₀ : X) :
    ContinuousAt (inTangentCoordinates 𝓘(𝕜, G) I f g ϕ x₀) x₀ := by
  have hg : Continuous g :=
    (FiberBundle.continuous_proj E _).comp (hϕ.comp (Continuous.prodMk_left 0))
  let e := trivializationAt E (TangentSpace I) (g x₀)
  have hΩ : g ⁻¹' e.baseSet ∈ 𝓝 x₀ :=
    hg.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (g x₀)))
  refine ((Bundle.Trivialization.continuousOn_continuousLinearMapAt_comp hϕ e).continuousAt
    hΩ).congr_of_eventuallyEq ?_
  filter_upwards [hΩ] with x hx
  have hx' : g x ∈ (chartAt H (g x₀)).source := by simpa [e] using hx
  rw [inTangentCoordinates_eq_tangentCoordChange_comp I ϕ hx',
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx']
  -- Mathlib's `tangentCoordChange` is an abbreviation for this coordinate change of
  -- `tangentBundleCore I M`, with no lemma that states it.
  rfl

/-- Conversely, a family of maps `ϕ x` from a normed space `G` into the tangent spaces
`T_(g x) M`, along a continuous map `g`, that is continuous at each `x₀` when read in the tangent
coordinates at `x₀`, is continuous as a map `X × G → TM`. By
`inTangentCoordinates_model_space_source`, the map `f` along which the source is read plays no
role. -/
theorem continuous_of_continuousAt_inTangentCoordinates {G X : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] [TopologicalSpace X] {f : X → G} {g : X → M}
    {ϕ : ∀ x, G →L[𝕜] TangentSpace I (g x)} (hg : Continuous g)
    (hϕ : ∀ x₀, ContinuousAt (inTangentCoordinates 𝓘(𝕜, G) I f g ϕ x₀) x₀) :
    Continuous fun q : X × G ↦ (⟨g q.1, ϕ q.1 q.2⟩ : TangentBundle I M) :=
  continuous_iff_continuousAt.2 fun q₀ ↦
    ContinuousAt.clm_apply_of_inCoordinates (F₁ := G) (F₂ := E) (E₁ := TangentSpace 𝓘(𝕜, G))
      (E₂ := TangentSpace I) (b₁ := fun _ : X × G ↦ (0 : G)) (b₂ := fun q : X × G ↦ g q.1)
      (v := fun q : X × G ↦ q.2)
      ((inTangentCoordinates_model_space_source I f 0 g ϕ q₀.1 ▸ hϕ q₀.1).comp continuousAt_fst)
      ((FiberBundle.continuousAt_totalSpace G _).2
        ⟨continuousAt_const, by simpa using continuousAt_snd⟩)
      (hg.comp continuous_fst).continuousAt

/-- Carry a fixed map `C : G → E`, read in the chart at `ι x₀`, to the tangent spaces along `ι`:
`y ↦ tangentCoordChange I (ι x₀) (ι y) (ι y) ∘ C`. If `ι` is `Cⁿ` at `y₁` and `ι y₁` lies in the
source of the chart at `ι x₀`, this family is `Cⁿ` at `y₁` in tangent coordinates. -/
theorem contMDiffAt_inTangentCoordinates_tangentCoordChange_comp {n : WithTop ℕ∞}
    [IsManifold I (n + 1) M] {G X EX HX : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
    {f : X → G} {ι : X → M} {x₀ y₁ : X} (hι : ContMDiffAt IX I n ι y₁)
    (hy₁ : ι y₁ ∈ (chartAt H (ι x₀)).source) (C : G →L[𝕜] E) :
    ContMDiffAt IX 𝓘(𝕜, G →L[𝕜] E) n (inTangentCoordinates 𝓘(𝕜, G) I f ι
      (fun y ↦ (tangentCoordChange I (ι x₀) (ι y) (ι y) ∘L C : G →L[𝕜] E)) y₁) y₁ := by
  have hO : (chartAt H (ι x₀)).source ∩ (chartAt H (ι y₁)).source ∈ 𝓝 (ι y₁) :=
    ((chartAt H (ι x₀)).open_source.inter (chartAt H (ι y₁)).open_source).mem_nhds
      ⟨hy₁, mem_chart_source H (ι y₁)⟩
  -- Near `y₁`, the family read at `y₁` is the coordinate change from `ι x₀` to `ι y₁`, after `C`.
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  have hcc := (((tangentBundleCore I M).contMDiffOn_coordChange I (achart H (ι x₀))
    (achart H (ι y₁))).contMDiffAt hO).comp y₁ hι
  refine (hcc.clm_comp (contMDiffAt_const (c := C))).congr_of_eventuallyEq ?_
  filter_upwards [hι.continuousAt.preimage_mem_nhds hO] with y hy
  refine (inTangentCoordinates_eq_tangentCoordChange_comp I (f := f)
    (fun y ↦ (tangentCoordChange I (ι x₀) (ι y) (ι y) ∘L C : G →L[𝕜] E)) hy.2).trans ?_
  ext v
  exact tangentCoordChange_comp (w := ι x₀) (x := ι y) (y := ι y₁)
    ⟨⟨by rw [extChartAt_source]; exact hy.1, mem_extChartAt_source (ι y)⟩,
      by rw [extChartAt_source]; exact hy.2⟩

/-- Let `A x : G → T_(g x) M` be a family of maps along a map `g : X → M`, `Cᵐ` at `x₀` when
read in tangent coordinates, and `φ : M → V` a map `Cⁿ` at `g x₀`, with `m + 1 ≤ n`. Then the
composition `x ↦ dφ (g x) ∘ A x`, a family of linear maps `G → V`, is `Cᵐ` at `x₀`. -/
theorem contMDiffAt_mvfderiv_comp_of_inTangentCoordinates {m n : WithTop ℕ∞}
    {G V X EX HX : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX 1 X]
    {φ : M → V} {g : X → M} {f : X → G} {A : ∀ x, G →L[𝕜] TangentSpace I (g x)} {x₀ : X}
    (hφ : ContMDiffAt I 𝓘(𝕜, V) n φ (g x₀)) (hg : ContMDiffAt IX I m g x₀)
    (hA : ContMDiffAt IX 𝓘(𝕜, G →L[𝕜] E) m (inTangentCoordinates 𝓘(𝕜, G) I f g A x₀) x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt IX 𝓘(𝕜, G →L[𝕜] V) m (fun x ↦ (mvfderiv I φ (g x)).comp (A x)) x₀ := by
  have hdφ := ContMDiffAt.mfderiv (I' := 𝓘(𝕜, V)) (fun _ ↦ φ) g
    (hφ.comp (x₀, g x₀) contMDiffAt_snd) hg hmn
  refine (hdφ.clm_comp hA).congr_of_eventuallyEq ?_
  have hnear : ∀ᶠ x in 𝓝 x₀, g x ∈ (chartAt H (g x₀)).source :=
    hg.continuousAt.preimage_mem_nhds
      ((chartAt H (g x₀)).open_source.mem_nhds (mem_chart_source H (g x₀)))
  filter_upwards [hnear] with x hx
  have e1 := inTangentCoordinates_eq_tangentCoordChange_comp I (f := f) A hx
  have e2 := inTangentCoordinates_eq (I := I) (I' := 𝓘(𝕜, V)) g (fun x ↦ φ (g x))
    (fun x ↦ mfderiv I 𝓘(𝕜, V) φ (g x)) hx (by simp)
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e1, e2]
  simp only [ContinuousLinearMap.comp_apply, tangentBundleCore_coordChange_model_space]
  -- `d% φ` is `mfderiv φ` read in `V`, and the two coordinate changes cancel.
  exact (congrArg (fun w : E ↦ mfderiv I 𝓘(𝕜, V) φ (g x) w)
    (TauCeti.tangentCoordChange_tangentCoordChange (by simp) (by simpa using hx)
      (show E from A x v))).symm

end SymplecticGeometry

end
