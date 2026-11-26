/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Surface
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel.Basic
import SymplecticGeometry.Geometry.Manifold.RegularValue.StrictSublevel
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Pullback

/-!
# Symplectic frames over strict sublevel sets in a surface

Let `ω` be a nondegenerate smooth two-form on a smooth real vector bundle `V` of rank `2 |κ|` over
a boundaryless smooth surface `M`, and let `a` be a regular value of a smooth function
`f : M → ℝ` whose sublevel set `{f ≤ a}` is compact and connected and whose level set `{f = a}`
is nonempty. This file shows that `ω` has a smooth symplectic frame for `stdForm κ` over the
open set `{f < a}`.

## Main results

* `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_setOf_lt`: the frame over
  `{f < a}`.

## Implementation notes

Tau Ceti makes the sublevel set `S = {f ≤ a}` a compact connected surface with boundary
(`TauCeti.isManifold_scalarRegularSublevel`), whose boundary is the level set
(`TauCeti.boundary_scalarRegularSublevel`), and its inclusion into `M` is smooth
(`TauCeti.contMDiff_subtypeVal_scalarRegularSublevel`). The pull-back of `ω` to `S` has a global
frame by `ContMDiffTwoForm.IsNondegenerate.exists_isSymplecticFrameOn_univ_of_boundary_nonempty`.
On `{f < a}` the frame is read through the inclusion of `{f < a}` into `S`, which is smooth by
`TauCeti.contMDiff_codRestrict_scalarRegularSublevel`, and
`IsSymplecticFrameOn.of_pullback_subtypeVal` makes it a frame of `ω` there.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are manifolds with boundary).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.1.3 and Proposition 2.6.7
-/

public noncomputable section

open _root_.Bundle Module Set TopologicalSpace
open scoped Manifold

namespace SymplecticGeometry

open StdSpace

namespace Bundle.ContMDiffTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ((⊤ : ℕ∞) : WithTop ℕ∞) F V I]
  {ω : ContMDiffTwoForm I ⊤ F V}

/-- **Symplectic frames over a regular strict sublevel set.** Let `ω` be a nondegenerate smooth
two-form on a smooth real vector bundle `V` of rank `2 |κ|` over a boundaryless smooth surface
`M`. Let `a` be a regular value of a smooth function `f : M → ℝ` such that the sublevel set
`{f ≤ a}` is compact and connected and the level set `{f = a}` is nonempty. Then `ω` has a
smooth symplectic frame for `stdForm κ` over the open set `{f < a}`. -/
theorem IsNondegenerate.exists_isSymplecticFrameOn_setOf_lt (hω : ω.IsNondegenerate)
    (hE : finrank ℝ E = 2) {f : M → ℝ} {a : ℝ} (hf : ContMDiff I 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : TauCeti.IsRegularValue I 𝓘(ℝ) f a) (hc : IsCompact {x | f x ≤ a})
    (hconn : IsConnected {x | f x ≤ a}) (hne : {x | f x = a}.Nonempty)
    {κ : Type*} [Fintype κ] (hκ : finrank ℝ F = 2 * Fintype.card κ) :
    ∃ Φ : ∀ x, StdSpace κ ≃L[ℝ] V x, ω.IsSymplecticFrameOn (stdForm κ) {x | f x < a} Φ := by
  have hn : finrank ℝ E = 1 + 1 := hE
  have hm : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- The sublevel set `S = {f ≤ a}` as a compact connected surface with nonempty boundary.
  let S := {x | f x ≤ a}
  let := TauCeti.scalarRegularSublevelChartedSpace (hf.of_le hm) hreg hn
  have := TauCeti.isManifold_scalarRegularSublevel hreg hn hm hf
  have : CompactSpace S := isCompact_iff_compactSpace.1 hc
  have : ConnectedSpace S := isConnected_iff_connectedSpace.1 hconn
  have hS : ((𝓡∂ 2).boundary S).Nonempty := by
    rw [TauCeti.boundary_scalarRegularSublevel hreg hn hm hf]
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, le_of_eq hx⟩, hx⟩
  -- Pull `ω` back to `S` and take a global frame there.
  let ι : C(S, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hι : ContMDiff (𝓡∂ 2) I ((⊤ : ℕ∞) : WithTop ℕ∞) ι :=
    TauCeti.contMDiff_subtypeVal_scalarRegularSublevel hreg hn hm hf
  have := Pullback.contMDiffVectorBundle (E := V) (F := F) hι
  obtain ⟨Ψ, hΨ⟩ := (hω.pullback ι hι).exists_isSymplecticFrameOn_univ_of_boundary_nonempty hS hκ
  -- A frame of `V` over all of `M`, used off `S`, where its values play no role.
  have hdim : finrank ℝ (StdSpace κ) = finrank ℝ F := by rw [finrank_stdSpace, hκ]
  let Φ₀ (x : M) : StdSpace κ ≃L[ℝ] V x :=
    (ContinuousLinearEquiv.ofFinrankEq hdim).trans
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (FiberBundle.mem_baseSet_trivializationAt' x)).symm
  let Φ (x : M) : StdSpace κ ≃L[ℝ] V x := if h : f x ≤ a then Ψ ⟨x, h⟩ else Φ₀ x
  -- On `{f < a}`, `Φ` is `Ψ`, read through the inclusion of `{f < a}` into `S`.
  let U : Opens M := ⟨f ⁻¹' Iio a, isOpen_Iio.preimage hf.continuous⟩
  have hUS : (U : Set M) ⊆ S := fun _ hx ↦ le_of_lt hx
  exact ⟨Φ, hΨ.of_pullback_subtypeVal hUS
    (TauCeti.contMDiff_codRestrict_scalarRegularSublevel hreg hn hm hf subset_rfl)
    fun x hx ↦ dite_eq_left hx.le⟩

end Bundle.ContMDiffTwoForm

end SymplecticGeometry

end
