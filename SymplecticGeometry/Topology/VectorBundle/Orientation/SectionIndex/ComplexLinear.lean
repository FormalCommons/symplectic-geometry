/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Basic
import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Derivative
import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# A zero with complex-linear invertible derivative has index one

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, oriented as a real manifold by Tau Ceti's
`TauCeti.complexManifoldOrientation` (as a homological orientation,
`SymplecticGeometry.complexManifoldHomologicalOrientation`), and `V → M` a complex vector
bundle with model fibre `G`, oriented as a real bundle by `TauCeti.VectorBundleOrientation.complex`.
Let `s` be a continuous section with a zero `z`, and `e` a complex-linear trivialization of `V`
whose base set contains `z`. Suppose that the section read in the preferred chart `φ` of `M` at
`z` and in `e`, `y ↦ (e (s (φ⁻¹ y))).2`, has at `φ z` a real derivative that is a
complex-linear isomorphism `A : E ≃L[ℂ] G`; in particular the complex rank of `V` is the complex
dimension of `M`. Then the local index `TauCeti.VectorBundleOrientation.sectionIndex`
of `s` at `z` is `1` (`SymplecticGeometry.sectionIndex_eq_one_of_complexLinear`). This
is the case of a transverse zero of a holomorphic section of a holomorphic bundle.

## Proof

Tau Ceti computes the local index as a sign: that of the determinant of the derivative of the
section, read in `e` and in an oriented chart of `M` with values in the model fibre `G`
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`). Since the derivative
is invertible, `z` is an isolated zero, and the form of that computation used here finds the
isolating neighbourhood itself
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually`). Take
as chart the preferred chart at `z` followed by `A`. It carries the local orientation of `M` at
`z` to the local orientation of `G` selected by the image under `A` of the tangent orientation at
`z` (`TauCeti.Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph`).
The tangent orientation is the complex orientation of `E`
(`TauCeti.orientationAt_complexManifoldOrientation_eq_complexOrientation`), and `A`, being
complex linear, carries it to the complex orientation of `G`
(`LinearEquiv.map_complexOrientation`; the two steps together are
`TauCeti.map_orientationAt_reindex_complexManifoldOrientation`). That is how the complex-linear
trivialization `e` reads the orientation of every fibre
(`TauCeti.VectorBundleOrientation.mapOrientation_complex_of_isLinear`, a form of
`Bundle.Trivialization.mapOrientation_complexOrientation`). In this chart the section has
derivative `A ∘ A⁻¹ = id` at the image of `z`, of determinant `1`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (indices of sections at isolated zeros) and §14 (the canonical
  orientation of a complex vector bundle).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §2 (complex manifolds are oriented, and holomorphic maps preserve orientation).
-/

public section

open Bundle Filter Module Set Topology TauCeti TauCeti.VectorBundleOrientation
open scoped Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]

variable [T2Space M]
  {V : M → Type} [TopologicalSpace (TotalSpace G V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle G V] [VectorBundle ℂ G V]

open scoped VectorBundle.ComplexToReal

/-- **A zero with complex-linear invertible derivative has index `1`.** Let `M` be a complex
manifold modelled on `𝓘(ℂ, E)`, of complex dimension `r + 1`, with its complex orientation
`complexManifoldHomologicalOrientation E M hE`, and `V` a complex vector bundle
over `M` with its complex orientation. Let `s` be a continuous section of `V` vanishing at `z`,
and `e` a complex-linear trivialization of `V` whose base set contains `z`. If the section read in
the preferred chart of `M` at `z` and in `e` has at the image of `z` the real derivative of a
complex-linear isomorphism `A : E ≃L[ℂ] G`, then the local index of `s` at `z` is `1`. -/
theorem sectionIndex_eq_one_of_complexLinear {r : ℕ} (hE : finrank ℂ E = r + 1)
    {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x)) {z : M} (hz : s z = 0)
    (e : Trivialization G (π G V)) [e.IsLinear ℂ] (hze : z ∈ e.baseSet) (A : E ≃L[ℂ] G)
    (hA : HasFDerivAt
      (fun y ↦ (e (TotalSpace.mk' G ((chartAt E z).symm y) (s ((chartAt E z).symm y)))).2)
      ((A : E →L[ℂ] G).restrictScalars ℝ) (chartAt E z z)) :
    ((complex G V).reindex (finCongr (by
        rw [← A.toLinearEquiv.finrank_eq, hE]; ring))).sectionIndex
      (by rw [← (A.restrictScalars' ℝ).toLinearEquiv.finrank_eq,
        finrank_real_of_finrank_complex_eq_add_one hE])
      (complexManifoldHomologicalOrientation E M hE) hs z = 1 := by
  have hEℝ : finrank ℝ E = 2 * r + 1 + 1 := finrank_real_of_finrank_complex_eq_add_one hE
  have : e.IsLinear ℝ := Trivialization.isLinear_restrictScalars ℝ ℂ e
  have hG : finrank ℝ G = 2 * r + 1 + 1 := by
    rw [← (A.restrictScalars' ℝ).toLinearEquiv.finrank_eq, hEℝ]
  have h₁ : 2 * finrank ℂ G = 2 * r + 1 + 1 := by rw [← A.toLinearEquiv.finrank_eq, hE]; ring
  rw [complexManifoldHomologicalOrientation_def]
  set oV := (complex G V).reindex (finCongr h₁)
  set oM := complexManifoldOrientationOfFinrank E M hE
  set Aℝ : E ≃L[ℝ] G := A.restrictScalars' ℝ
  have hAℝ : (A : E →L[ℂ] G).restrictScalars ℝ = (Aℝ : E →L[ℝ] G) := by
    ext v
    simp [Aℝ]
  rw [hAℝ] at hA
  set ω : Orientation ℝ G (Fin (2 * r + 1 + 1)) :=
    Orientation.reindex ℝ G (finCongr h₁) (complexOrientation G)
  -- The chart `φ` of `M` at `z`: the preferred chart followed by `A`.
  set φ : OpenPartialHomeomorph M G :=
    (chartAt E z).transHomeomorph (𝓘(ℝ, E).toHomeomorph.trans Aℝ.toHomeomorph)
  have hzφ : z ∈ φ.source := by simp [φ]
  -- The section read in a chart, as a function of the point of `M`.
  set g : M → G := fun x ↦ (e (TotalSpace.mk' G x (s x))).2
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
  -- The trivialization `e` reads the orientation of every fibre as `ω`.
  have ho : ∀ x (hx : x ∈ e.baseSet), e.mapOrientation (Fin (2 * r + 1 + 1)) hx (oV x) = ω := by
    intro x hx
    rw [reindex_apply, Trivialization.mapOrientation_reindex, mapOrientation_complex_of_isLinear]
  -- The chart `φ` carries the local orientation of `M` at `z` to the one selected by `ω`.
  have hω := map_orientationAt_complexManifoldOrientationOfFinrank hE
    (by rw [← A.toLinearEquiv.finrank_eq, hE]) A z
  have hφl := Manifold.Orientation.localHomologyMap_sub_toHomologicalOrientation_transHomeomorph
    hEℝ oM hG Aℝ z
  rw [hω] at hφl
  rw [sectionIndex_eq_sign_det_of_hasFDerivAt_of_eventually oV hG _ hs e φ hz hze hzφ
    (Eventually.of_forall ho) hφl hAφ (by simp), ContinuousLinearMap.det_id, sign_one,
    SignType.coe_one]

end SymplecticGeometry

end
