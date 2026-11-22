/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Topology.VectorBundle.LineBundle
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.FiberwiseEquiv
public import SymplecticGeometry.Topology.VectorBundle.Orientation.SectionIndex.Trivial
public import TauCeti.Geometry.Manifold.ModelTransport.Finrank
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import TauCeti.Topology.VectorBundle.Smul

/-!
# Local indices of sections of a complex line bundle read in a frame over a coordinate disc

Let `M` be a surface with a homological orientation `o`, `ψ` a coordinate disc of `M`
(`SymplecticGeometry.CoordinateDisc`), and `L` a complex line bundle over `M`, oriented as a
complex line. Let `σ` be a frame of `L` along `ψ`: a section `w ↦ σ w ∈ L (ψ w)` over the ball,
nowhere zero and continuous on total spaces. A section `s` of `L` reads `s (ψ w) = g w • σ w` in
the frame, for a map `g` from the ball to `ℂ`. Then the local index of `s` at `ψ z`, for an
isolated zero `z` of `g`, is the local index of `g` at `z` for the canonical orientations of the
ball and of `ℂ` (`SymplecticGeometry.CoordinateDisc.sectionIndex_eq_localIndex_of_eq_smul`).

The statement reads `ψ` through any map `j` equal to it. A composite disc such as
`SymplecticGeometry.CoordinateDisc.comp φ f` agrees with `φ ∘ f` only up to a proof, not by
definition, so this lets a frame along it be given as one along `φ ∘ f`.

## Proof

The frame gives at each point `w` of the ball the complex-linear equivalence `c ↦ c • σ w` from
`ℂ` onto the fibre of `L` at `ψ w` (`VectorBundle.toSpanSingletonEquiv`), so an isomorphism of
the trivial bundle `ball × ℂ` with the pull-back of `L` along `ψ` that carries the orientation of
`ℂ` to the complex orientation of `L` (`TauCeti.VectorBundleOrientation.map_complex`) and the
section `g` to `s`. The two sections have the same local index
(`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`), with the ball charted on
the model of `M` through `ChartedSpace.ofFinrankEq`, and in the trivial bundle the local index of
`g` is its local index as a map
(`TauCeti.VectorBundleOrientation.sectionIndex_trivial_eq_localIndex`), since `ψ` carries the
canonical orientation of the ball to `o`.

## Main results

* `SymplecticGeometry.CoordinateDisc.sectionIndex_eq_localIndex_of_eq_smul`: the local index of a
  section of a complex line bundle is that of its coefficient in a frame over a coordinate disc.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class and indices of sections at isolated zeros).
-/

public section

noncomputable section

open Bundle Module Set Topology TauCeti

namespace SymplecticGeometry

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

local instance : VectorBundle ℝ G L := VectorBundle.restrictScalars ℝ ℂ G L

/-- **Local indices in a frame over a coordinate disc.** Let `ψ` be a coordinate disc of a surface
`M` with homological orientation `o`, read through any map `j` equal to it (so that a frame along a
composite disc may be given along the composite map). Let `L` be a complex line bundle over `M`,
and `σ` a frame of `L` along `j`: a section `w ↦ σ w ∈ L (j w)` over the ball, nowhere zero and
continuous on total spaces. Let `s` be a continuous section of `L` with `s (j w) = g w • σ w` for a
continuous `g : ball → ℂ`, and `z` a zero of `g` with an open neighbourhood `U` containing no
other zero. Then the local index of `s` at `j z`, for the orientation of `L` as a complex line, is
the local index of `g` at `z`, for the canonical orientations of the ball and of `ℂ`. -/
theorem sectionIndex_eq_localIndex_of_eq_smul (hn : finrank ℝ E = 2) (hG : finrank ℂ G = 1)
    (ψ : CoordinateDisc o) {j : ball → M} (hψj : ⇑ψ = j) {σ : ∀ w : ball, L (j w)}
    (hσ : Continuous fun w ↦ TotalSpace.mk' G (j w) (σ w)) (hσ0 : ∀ w, σ w ≠ 0)
    (g : C(ball, ℂ)) {s : ∀ x, L x} (hs : Continuous fun x ↦ TotalSpace.mk' G x (s x))
    (hsg : ∀ w, s (j w) = g w • σ w) {z : ball} (hgz : g z = 0) {U : Set ball} (hU : IsOpen U)
    (hzU : z ∈ U) (hUz : ∀ w ∈ U, g w = 0 → w = z) :
    (VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L)).sectionIndex
        (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) o hs (j z) =
      (complexHomologicalOrientation ball).localIndex (complexHomologicalOrientation ℂ) g z := by
  subst hψj
  let _ : ChartedSpace E ball :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := ℂ) (E' := E) ball
      (Complex.finrank_real_complex.trans hn.symm)
  -- The frame `σ`, as an isomorphism of the trivial bundle `ball × ℂ` with `ψ^* L`.
  let Φ : ∀ w : ball, Bundle.Trivial ball ℂ w ≃L[ℝ] L (ψ w) := fun w ↦
    (VectorBundle.toSpanSingletonEquiv G hG (σ w) (hσ0 w)).restrictScalars' ℝ
  have hΦ : ∀ w c, Φ w c = c • σ w := fun w c ↦
    (congrFun (ContinuousLinearEquiv.coe_restrictScalars' ℝ _) c).trans
      (VectorBundle.toSpanSingletonEquiv_apply G hG _ _ c)
  have hΦc : Continuous fun v : TotalSpace ℂ (Bundle.Trivial ball ℂ) ↦
      TotalSpace.mk' G (ψ v.proj) (Φ v.proj v.snd) := by
    simp only [hΦ]
    exact Continuous.smul_totalSpace (c := fun v : TotalSpace ℂ (Bundle.Trivial ball ℂ) ↦ v.snd)
      (continuous_snd.comp (Bundle.Trivial.isInducing_toProd ball ℂ).continuous)
      (hσ.comp (FiberBundle.continuous_proj ℂ _))
  have ho : ∀ w, Orientation.map (Fin 2) (Φ w).toLinearEquiv
      (VectorBundleOrientation.trivial ball Complex.orientation w) =
      VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L) (ψ w) := by
    intro w
    -- `Φ w` is complex-linear, so it carries the canonical orientation of `ℂ` to that of `L`.
    have h := VectorBundleOrientation.map_complex (F := G) (E := L) (F' := ℂ)
      (E' := Bundle.Trivial ball ℂ) (b' := w) (b := ψ w)
      (VectorBundle.toSpanSingletonEquiv G hG (σ w) (hσ0 w)).toLinearEquiv
    rw [VectorBundleOrientation.complex_trivial, VectorBundleOrientation.trivial_apply] at h
    rw [VectorBundleOrientation.trivial_apply, ← reindex_complexOrientation_complex,
      ContinuousLinearEquiv.restrictScalars'_toLinearEquiv, Orientation.map_reindex, h,
      VectorBundleOrientation.reindex_apply, Orientation.reindex_finCongr_reindex_finCongr]
  have hs₁ : Continuous fun w ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ball ℂ) w (g w) :=
    (Bundle.Trivial.isInducing_toProd ball ℂ).continuous_iff.2 (continuous_id.prodMk g.continuous)
  have h1 := VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise
    (VectorBundleOrientation.reindex (finCongr (by rw [hG])) (VectorBundleOrientation.complex G L))
    (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) o
    (VectorBundleOrientation.trivial ball Complex.orientation) Complex.finrank_real_complex
    (j := ⟨ψ, ψ.continuous⟩) ψ.isOpenEmbedding hΦc ho hs₁ hs (fun w ↦ (hΦ w _).trans (hsg w).symm) z
  simp only [ContinuousMap.coe_mk] at h1
  rw [← h1]
  -- `ψ` carries the canonical orientation of the ball to `o`.
  have hor : (o.comap ψ.isOpenEmbedding) z = complexHomologicalOrientation ball z := by
    rw [HomologicalOrientation.comap_apply, ψ.complexHomologicalOrientation_apply]
  exact VectorBundleOrientation.sectionIndex_trivial_eq_localIndex _ _ hor g hs₁ hgz hU hzU hUz

end CoordinateDisc

end SymplecticGeometry
