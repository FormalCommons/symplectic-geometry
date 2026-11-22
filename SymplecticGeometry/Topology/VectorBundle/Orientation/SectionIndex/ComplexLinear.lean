/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

/-!
# A zero with complex-linear invertible derivative has index one

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, oriented as a real manifold by Tau Ceti's
`TauCeti.complexManifoldOrientation`, and `V → M` a complex vector bundle with model fibre `G`,
oriented as a real bundle by `TauCeti.VectorBundleOrientation.complex`. Let `s` be a continuous
section with a zero `z`, and `e` a complex-linear trivialization of `V` whose base set contains
`z`. Suppose that the section read in the preferred chart `φ` of `M` at `z` and in `e`,
`y ↦ (e (s (φ⁻¹ y))).2`, has at `φ z` a real derivative that is a complex-linear isomorphism
`A : E ≃L[ℂ] G`; in particular the complex rank of `V` is the complex dimension of `M`. Then the
local index `TauCeti.VectorBundleOrientation.sectionIndex` of `s` at `z` is `1`
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_one_of_complexLinear`). This is the case of a
transverse zero of a holomorphic section of a holomorphic bundle.

## Proof

Tau Ceti computes the local index as a sign: that of the determinant of the derivative of the
section, read in `e` and in an oriented chart of `M` with values in the model fibre `G`
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`). Take as chart the
preferred chart at `z` followed by `A`. It carries the local orientation of `M` at `z` to the
local orientation of `G` selected by the image under `A` of the tangent orientation at `z`
(`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph`).
The tangent orientation is the complex orientation of `E`
(`TauCeti.orientationAt_complexManifoldOrientation_eq_complexOrientation`), and `A`, being
complex linear, carries it to the complex orientation of `G`
(`LinearEquiv.map_complexOrientation`), which is how the complex-linear trivialization `e` reads
the orientation of every fibre (`Bundle.Trivialization.mapOrientation_complexOrientation`). In
this chart the section has derivative `A ∘ A⁻¹ = id` at the image of `z`, of determinant `1`.
That `z` is an isolated zero follows from the invertibility of the derivative
(`HasFDerivAt.eventually_ne`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (indices of sections at isolated zeros) and §14 (the canonical
  orientation of a complex vector bundle).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2 (complex manifolds are oriented, and holomorphic maps preserve orientation).
-/

public section

open Bundle Filter Module Set Topology
open scoped Manifold TauCeti.ComplexManifold

namespace TauCeti.VectorBundleOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {V : M → Type} [TopologicalSpace (TotalSpace G V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle G V] [VectorBundle ℂ G V]

local instance : VectorBundle ℝ G V := VectorBundle.restrictScalars ℝ ℂ G V

/-- **A zero with complex-linear invertible derivative has index `1`.** Let `M` be a complex
manifold modelled on `𝓘(ℂ, E)`, of real dimension `n + 1`, with its complex orientation, and `V`
a complex vector bundle over `M` with its complex orientation. Let `s` be a continuous section of
`V` vanishing at `z`, and `e` a complex-linear trivialization of `V` whose base set contains `z`.
If the section read in the preferred chart of `M` at `z` and in `e` has at the image of `z` the
real derivative of a complex-linear isomorphism `A : E ≃L[ℂ] G`, then the local index of `s` at
`z` is `1`. -/
theorem sectionIndex_eq_one_of_complexLinear {n : ℕ} (hE : finrank ℝ E = n + 1)
    {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x)) {z : M} (hz : s z = 0)
    (e : Trivialization G (π G V)) [e.IsLinear ℂ] (hze : z ∈ e.baseSet) (A : E ≃L[ℂ] G)
    (hA : HasFDerivAt
      (fun y ↦ (e (TotalSpace.mk' G ((chartAt E z).symm y) (s ((chartAt E z).symm y)))).2)
      ((A : E →L[ℂ] G).restrictScalars ℝ) (chartAt E z z)) :
    ((complex G V).reindex (finCongr (by
        rw [← A.toLinearEquiv.finrank_eq, ← finrank_real_of_complex, hE]))).sectionIndex
      (by rw [← (A.restrictScalars' ℝ).toLinearEquiv.finrank_eq, hE])
      (((complexManifoldOrientation E M).reindex (finCongr (by
        rw [← finrank_real_of_complex, hE]))).toHomologicalOrientation hE) hs z = 1 := by
  have : e.IsLinear ℝ := Trivialization.isLinear_restrictScalars ℝ ℂ e
  have hG : finrank ℝ G = n + 1 := by rw [← (A.restrictScalars' ℝ).toLinearEquiv.finrank_eq, hE]
  have h₁ : 2 * finrank ℂ G = n + 1 := by
    rw [← A.toLinearEquiv.finrank_eq, ← finrank_real_of_complex, hE]
  have h₂ : 2 * finrank ℂ E = n + 1 := by rw [← finrank_real_of_complex, hE]
  set oV := (complex G V).reindex (finCongr h₁)
  set oM := (complexManifoldOrientation E M).reindex (finCongr h₂)
  set Aℝ : E ≃L[ℝ] G := A.restrictScalars' ℝ
  have hAℝ : (A : E →L[ℂ] G).restrictScalars ℝ = (Aℝ : E →L[ℝ] G) := by
    ext v
    simp [Aℝ]
  rw [hAℝ] at hA
  set ω : Orientation ℝ G (Fin (n + 1)) :=
    Orientation.reindex ℝ G (finCongr h₁) (complexOrientation G)
  -- The chart `φ` of `M` at `z`: the preferred chart followed by `A`.
  set φ : OpenPartialHomeomorph M G :=
    (chartAt E z).transHomeomorph (𝓘(ℝ, E).toHomeomorph.trans Aℝ.toHomeomorph)
  have hzφ : z ∈ φ.source := by simp [φ]
  -- The section read in a chart, as a function of the point of `M`.
  set g : M → G := fun x ↦ (e (TotalSpace.mk' G x (s x))).2 with hg
  have hg0 : ∀ x ∈ e.baseSet, s x = 0 → g x = 0 := fun x hx h0 ↦ by
    simp only [hg, h0]
    exact congrArg Prod.snd (e.zeroSection ℝ hx)
  have hφg : (fun y ↦ (e (TotalSpace.mk' G (φ.symm y) (s (φ.symm y)))).2) =
      (g ∘ (chartAt E z).symm) ∘ Aℝ.symm := by
    ext y
    exact congrArg g (by simp [φ, OpenPartialHomeomorph.transHomeomorph_symm_apply])
  -- By definition of `g`, the function of `hA` is `g ∘ (chartAt E z).symm`.
  replace hA : HasFDerivAt (g ∘ (chartAt E z).symm) (Aℝ : E →L[ℝ] G) (chartAt E z z) := hA
  -- The derivative of the section read in `φ` is the identity.
  have hAφ : HasFDerivAt (fun y ↦ (e (TotalSpace.mk' G (φ.symm y) (s (φ.symm y)))).2)
      (ContinuousLinearMap.id ℝ G) (φ z) := by
    have hφz : φ z = Aℝ (chartAt E z z) := by simp [φ]
    rw [hφg, hφz]
    have h := ((Aℝ.symm_apply_apply (chartAt E z z)).symm ▸ hA).comp (Aℝ (chartAt E z z))
      Aℝ.symm.hasFDerivAt
    rwa [ContinuousLinearEquiv.coe_comp_coe_symm] at h
  -- `z` is an isolated zero of `s`, since the derivative of the section read in the chart is
  -- injective.
  obtain ⟨U, hUz, hUo, hzU⟩ : ∃ U ⊆ {x | s x = 0 → x = z}, IsOpen U ∧ z ∈ U := by
    have hne := hA.eventually_ne (c := 0) ⟨_, Aℝ.antilipschitzWith⟩
    rw [eventually_nhdsWithin_iff] at hne
    refine eventually_nhds_iff.1 ?_
    filter_upwards [(chartAt E z).continuousAt (mem_chart_source E z) |>.eventually hne,
      (chartAt E z).open_source.mem_nhds (mem_chart_source E z),
      e.open_baseSet.mem_nhds hze] with x hx hxs hxe h0
    by_contra hxz
    refine hx (fun h ↦ hxz ((chartAt E z).injOn hxs (mem_chart_source E z) h)) ?_
    rw [Function.comp_apply, (chartAt E z).left_inv hxs]
    exact hg0 x hxe h0
  set U' := U ∩ e.baseSet ∩ φ.source
  have hU'o : IsOpen U' := (hUo.inter e.open_baseSet).inter φ.open_source
  have hzU' : z ∈ U' := ⟨⟨hzU, hze⟩, hzφ⟩
  -- The trivialization `e` reads the orientation of every fibre as `ω`.
  have ho : ∀ x (hx : x ∈ U'), e.mapOrientation (Fin (n + 1)) hx.1.2 (oV x) = ω := by
    intro x hx
    have := VectorBundle.finiteDimensional ℂ G V x
    rw [reindex_apply, Trivialization.mapOrientation_reindex, complex_apply,
      Trivialization.mapOrientation_complexOrientation _ _ _ rfl, ← Orientation.reindex_trans]
    exact congrArg (Orientation.reindex ℝ G · (complexOrientation G)) (Equiv.ext fun _ ↦ by simp)
  -- The chart `φ` carries the local orientation of `M` at `z` to the one selected by `ω`.
  have hoz : (oM.orientationAt z : Orientation ℝ E (Fin (n + 1))) =
      Orientation.reindex ℝ E (finCongr h₂) (complexOrientation E) := by
    rw [Manifold.Orientation.orientationAt_reindex,
      orientationAt_complexManifoldOrientation_eq_complexOrientation]
    -- The two sides differ only in reading the tangent space at `z` as `E`.
    rfl
  have hω : (oM.orientationAt z).map (Fin (n + 1)) Aℝ.toLinearEquiv = ω := by
    refine (congrArg (Orientation.map (Fin (n + 1)) Aℝ.toLinearEquiv) hoz).trans ?_
    rw [Orientation.map_reindex, ContinuousLinearEquiv.restrictScalars'_toLinearEquiv,
      LinearEquiv.map_complexOrientation, ← Orientation.reindex_trans]
    exact congrArg (Orientation.reindex ℝ G · (complexOrientation G)) (Equiv.ext fun _ ↦ by simp)
  have hφl := Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph
    hE oM hG Aℝ z
  rw [hω] at hφl
  have hdet : (ContinuousLinearMap.id ℝ G).det = 1 := LinearMap.det_id
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt oV hG _ hs e φ hU'o hzU'
    (fun x hx h0 ↦ hUz hx.1.1 h0) hz (fun x hx ↦ hx.1.2) (fun x hx ↦ hx.2) ho hφl hAφ
    (hdet ▸ one_ne_zero), hdet, sign_one, SignType.coe_one]

end TauCeti.VectorBundleOrientation

end
