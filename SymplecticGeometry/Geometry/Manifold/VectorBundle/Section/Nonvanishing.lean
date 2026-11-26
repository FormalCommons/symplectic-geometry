/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Discrete
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Push
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Generic
import TauCeti.Geometry.Manifold.Boundary.Collar.Topological
import TauCeti.Geometry.Manifold.Boundary.Interior
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import TauCeti.Geometry.Manifold.VectorBundle.Section.Nonvanishing
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.VectorBundle.HomotopyInvariance

/-!
# Smooth nowhere-zero sections

Over a compact connected manifold `M` of dimension `d ≥ 2` with nonempty boundary, every smooth
real bundle of rank at least `d` has a smooth nowhere-zero section
(`SymplecticGeometry.exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty`); for surfaces,
every bundle of rank at least two. The argument replaces the book's cutting of the surface:

1. Pulled back to the interior `M°`, a generic section in the span of finitely many spanning
   sections has no zeros if the rank exceeds `d` (Tau Ceti's
   `ContMDiffSection.mem_residual_setOf_affineFamily_ne_zero`), and a discrete set of zeros if
   the rank is `d` (`ContMDiffSection.mem_residual_setOf_isDiscrete_zero_affineFamily`).
2. A collar of the boundary gives a map `g : M → M` homotopic to the identity with image in a
   compact subset `K` of `M°` that misses a nonempty open subset of `M°`
   (`TauCeti.IsCollar.exists_homotopy_push`).
3. `M°` is connected, and stays connected after removing a closed discrete set, so some
   diffeotopy of `M°` has a final map that sends no point of `K` to a zero of `σ`
   (`TauCeti.exists_diffeotopy_apply_one_notMem`); its inverse carries the finitely many zeros in
   `K` out of `K` and fixes the other zeros. Following `g` by this final map gives a map `h`
   homotopic to the identity along which the section `σ` has no zero.
4. Homotopy invariance of bundles (Tau Ceti's
   `ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`) identifies `h^* V` with `V`,
   so `σ ∘ h` gives a continuous nowhere-zero section of `V`, which is then smoothed by Tau Ceti's
   `TauCeti.exists_contMDiffSection_forall_ne_zero_of_continuous`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.6
  (where nowhere-zero sections of bundles over surfaces are used to build unitary frames)
-/

public section

open Bundle
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

open Set Module TauCeti

section Generic

open ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

/-- Over a compact second-countable manifold modelled on `E`, a bundle of rank at least `dim E` has
a smooth section whose zeros in the interior form a discrete set: the generic section of the
bundle pulled back to the interior, which has no zeros if the rank is larger than `dim E`. -/
private theorem exists_contMDiffSection_isDiscrete_interior [SecondCountableTopology M]
    (hF : finrank ℝ E ≤ finrank ℝ F) :
    ∃ σ : ContMDiffSection I F ∞ V, IsDiscrete {x : I.interior M | σ x = 0} := by
  let N := I.interior M
  let j : C^∞⟮𝓘(ℝ, E), N; I, M⟯ := ⟨Subtype.val, I.contMDiff_subtypeVal_interior⟩
  obtain ⟨k, s, hspan⟩ :=
    exists_fin_spanning_contMDiffSection (I := I) (F := F) (V := V) (n := ∞)
  let t i := (s i).pullback j
  have ht (i) (y : N) : t i y = s i (j y) := pullback_apply (s i) j y
  have hspan' (y : N) : Submodule.span ℝ (range fun i ↦ t i y) = ⊤ := by
    rw [funext (ht · y)]
    exact hspan (j y)
  have key (a : Fin k → ℝ) (y : N) : affineFamily 0 t a y = affineFamily 0 s a (j y) := by
    simp only [affineFamily_apply, ht, coe_zero, Pi.zero_apply]
    rfl
  have hres : {a : Fin k → ℝ | IsDiscrete {y : N | affineFamily 0 t a y = 0}} ∈ residual _ := by
    rcases hF.lt_or_eq with h | h
    · filter_upwards [mem_residual_setOf_affineFamily_ne_zero 0 t hspan' h] with a ha
      exact Set.Subsingleton.isDiscrete fun x hx ↦ (ha x hx).elim
    · exact mem_residual_setOf_isDiscrete_zero_affineFamily h 0 t hspan'
  obtain ⟨a, ha⟩ := (dense_of_mem_residual hres).nonempty
  simp only [mem_ofPred_eq, key] at ha
  exact ⟨affineFamily 0 s a, ha⟩

omit [CompactSpace M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
/-- In the interior of a connected manifold of dimension at least two, let `σ` be a section whose
zeros in the interior are isolated, and `K` a compact subset of the interior whose complement in the
interior is nonempty. Some homotopy of the interior, starting at the identity, ends at a map that
sends no point of `K` to a zero of `σ`. -/
private theorem exists_homotopy_interior_ne_zero [ConnectedSpace M] (hdim : 1 < finrank ℝ E)
    (σ : ContMDiffSection I F ∞ V) (hσ : IsDiscrete {x : I.interior M | σ x = 0})
    {K : Set (I.interior M)} (hK : IsCompact K) (hKc : Kᶜ.Nonempty) :
    ∃ G : unitInterval × I.interior M → I.interior M, Continuous G ∧
      (∀ y, G (0, y) = y) ∧ ∀ y ∈ K, σ (G (1, y)) ≠ 0 := by
  have hZ : IsClosed {x : I.interior M | σ x = 0} :=
    σ.isClosed_setOf_eq_zero.preimage continuous_subtypeVal
  obtain ⟨Ψ, hΨ, -⟩ := exists_diffeotopy_apply_one_notMem (E := E) (N := I.interior M) (n := ∞)
    (m := 1) (by rw [← Module.finrank_eq_rank]; exact_mod_cast hdim) le_rfl (by norm_num) hZ hσ
    hK hKc
  exact ⟨fun p ↦ Ψ p, Ψ.contMDiff.continuous, Ψ.apply_zero, hΨ⟩

end Generic

section Surface

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 2)) M]
  [IsManifold (𝓡∂ (n + 2)) ∞ M] [CompactSpace M] [ConnectedSpace M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V (𝓡∂ (n + 2))]

/-- Let `M` be a compact connected manifold of dimension `d = n + 2 ≥ 2` whose boundary is not
empty. Then each smooth real vector bundle on `M` whose rank is at least `d` admits a smooth section
vanishing nowhere. The case `n = 0` covers bundles of rank two or more on surfaces with boundary. -/
theorem exists_contMDiffSection_forall_ne_zero_of_boundary_nonempty
    (hM : ((𝓡∂ (n + 2)).boundary M).Nonempty) (hF : n + 2 ≤ finrank ℝ F) :
    ∃ t : ContMDiffSection (𝓡∂ (n + 2)) F ∞ V, ∀ x, t x ≠ 0 := by
  have := (𝓡∂ (n + 2)).secondCountableTopology_of_sigmaCompact M
  -- A section whose zeros in the interior form a discrete set.
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_isDiscrete_interior (I := 𝓡∂ (n + 2)) (V := V)
    (by simpa using hF)
  -- Push `M` into a compact subset `K` of its interior, missing a nonempty open set `O`.
  obtain ⟨c, hc⟩ := isCollared_iff.1
    (isCollared_subtypeVal_boundary_of_compactSpace (n := n + 1) (M := M))
  obtain ⟨K, O, g, hK, hKi, -, hOi, hOK, hO, hgK, hg⟩ := hc.exists_homotopy_push
  -- Move the zeros of `σ` off `K`, inside the interior.
  let U := (𝓡∂ (n + 2)).interior M
  have hKU : IsCompact ((↑) ⁻¹' K : Set U) :=
    (((𝓡∂ (n + 2)).isOpen_interior (n := ∞) (by simp)).isOpenEmbedding_subtypeVal.isInducing
      |>.isCompact_preimage_iff (by simpa using hKi)).2 hK
  obtain ⟨x₀, hx₀⟩ := hO hM
  obtain ⟨G, hGc, hG0, hG1⟩ := exists_homotopy_interior_ne_zero (I := 𝓡∂ (n + 2)) (by simp) σ hσ
    hKU ⟨⟨x₀, hOi hx₀⟩, fun h ↦ disjoint_left.1 hOK hx₀ h⟩
  -- The map `h = G₁ ∘ g` is homotopic to the identity and avoids the zeros of `σ`.
  let g' : M → U := fun x ↦ ⟨g x, hKi (hgK ⟨x, rfl⟩)⟩
  have hg' : Continuous g' := g.continuous.subtype_mk _
  let h : C(M, M) := ⟨fun x ↦ G (1, g' x), continuous_subtypeVal.comp (hGc.comp
    (continuous_const.prodMk hg'))⟩
  let G' : ContinuousMap.Homotopy g h :=
    { toFun := fun p ↦ G (p.1, g' p.2)
      continuous_toFun := continuous_subtypeVal.comp (hGc.comp
        (continuous_fst.prodMk (hg'.comp continuous_snd)))
      map_zero_left := fun x ↦ by simp [hG0, g']
      map_one_left := fun x ↦ rfl }
  have hh0 (x : M) : σ (h x) ≠ 0 := hG1 (g' x) (hgK ⟨x, rfl⟩)
  -- Transport `σ ∘ h` along an isomorphism `h^* V ≅ V`, and smooth the result.
  obtain ⟨Φ, hΦ, -⟩ := (hg.trans ⟨G'⟩).symm.exists_continuousLinearEquiv_pullback
    (𝕜 := ℝ) (F := F) (E := V)
  have h1 : Continuous fun x ↦ TotalSpace.mk' F (E := (h : M → M) *ᵖ V) x (σ (h x)) :=
    Pullback.continuous_iff.2 ⟨continuous_id, σ.contMDiff.continuous.comp h.continuous⟩
  exact TauCeti.exists_contMDiffSection_forall_ne_zero_of_continuous (n := ⊤)
    (s := fun x ↦ Φ x (σ (h x))) ((Pullback.continuous_lift F V _).comp (hΦ.comp h1))
    fun x hx ↦ hh0 x ((Φ x).map_eq_zero_iff.1 hx)

end Surface

end SymplecticGeometry

end
