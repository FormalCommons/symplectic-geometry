/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.VectorBundlePoincare
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Normalized
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Correcting a family of one-forms to vanish along a submanifold

Let `f : Q → M` be a smooth embedding of a compact manifold, and let `γ_t`, `t ∈ ℝ`, be a
smooth family of one-forms on `M`, given as a one-form `γ` on `ℝ × M` with slices
`γ_t = ι_t^* γ`, `ι_t x = (t, x)`. This file constructs a smooth function `φ` on `ℝ × M`,
supported in `ℝ × K` for a compact `K` inside any given neighbourhood of `f(Q)`, that vanishes
on `ℝ × f(Q)` and whose slices `φ_t` satisfy `dφ_t = γ_t` at every point `f q` with
`(f^* γ_t)_q = 0` (`TauCeti.SmoothEmbedding.exists_contMDiff_mextDeriv_eq_mpullback_prodMk`).
So `γ_t - dφ_t` vanishes at `f q` as a covector on `T_{f q} M`, and not only on the tangent
vectors of `Q`. This is the correction of the primitive in the relative Moser theorem along a
family (compare [McDuffSalamon2017], §3.2).

## Construction

Take a tubular neighbourhood `Φ` from the total space of the normal bundle of `f` onto an open
set `W ⊇ f(Q)` (Tau Ceti's `TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`).
On the total space of a vector bundle, the relative Poincaré operator gives fibre-scaling
primitives of a family of one-forms, jointly smooth in `(t, v)`
(`TauCeti.exists_contMDiff_mextDeriv_ofFunction_eq_of_mpullback_zeroSection`). Apply this to the
pullback of `γ` along `id × Φ`, transport the result back by `Φ⁻¹`, and multiply it by a
cutoff equal to `1` near `f(Q)` with compact support in `W`. The argument for a single form is
that of Tau Ceti's `Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`, without the
closedness of the form, since the extra term it removes vanishes along the zero section. The
inverse of the tube, as a map on `M` smooth on `W`, is built as in Tau Ceti's
`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`.

## Main results

* `TauCeti.SmoothEmbedding.exists_contMDiff_mextDeriv_eq_mpullback_prodMk`: the correction
  function along a compact embedded submanifold.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], §6.2
-/

public section

noncomputable section

open Bundle Manifold Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Correcting a family of one-forms along a compact submanifold.** Let `f : Q → M` be a smooth
embedding of a compact manifold, and let `γ` be a smooth one-form on `ℝ × M`, with slices
`γ_t = ι_t^* γ`. For every open set `O ⊇ f(Q)` there is a smooth function `φ` on `ℝ × M`,
vanishing outside `ℝ × K` for a compact set `K ⊆ O` and on `ℝ × f(Q)`, such that its slice
`φ_t = φ (t, ·)` satisfies `d φ_t = γ_t` at every point `f q` where `f^* γ_t` vanishes. -/
theorem exists_contMDiff_mextDeriv_eq_mpullback_prodMk [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F 1) {O : Set M}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ φ : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ φ ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ O ∧ ∀ t, ∀ x ∉ K, φ (t, x) = 0) ∧
      (∀ t q, φ (t, f q) = 0) ∧
      ∀ t q, (SmoothForm.mpullback f f.contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ)).val q = 0 →
        mextDeriv (RoughForm.ofFunction I fun x ↦ φ (t, x)) (f q) =
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ).val
            (f q) := by
  classical
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · exact ⟨0, contMDiff_const, ⟨∅, isCompact_empty, empty_subset _, by simp⟩,
      fun _ q ↦ isEmptyElim q, fun _ q ↦ isEmptyElim q⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  -- A tubular neighbourhood `Φ` of `f`, onto an open set `W ⊆ O`.
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ E'))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ E - Module.finrank ℝ E' := by simp [P]
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let N := fun q ↦ f.isImmersion.NormalSpace q hn
  have hfW : range f ⊆ W := range_subset_of_apply_zeroSection f hn hdim Φ hΦ
  -- The tube as a map into `M`, and its inverse `ψ`, smooth on `W`.
  let Φ' : TotalSpace P N → M := fun v ↦ (Φ v : M)
  have hΦ' : ContMDiff (J.prod 𝓘(ℝ, P)) I ∞ Φ' := contMDiff_subtypeVal.comp Φ.contMDiff
  let ψ : M → TotalSpace P N := fun x ↦
    if h : x ∈ W then Φ.symm ⟨x, h⟩ else zeroSection P N (Classical.arbitrary Q)
  have hψW (w : W) : ψ w = Φ.symm w := by simp [ψ, w.property]
  have hψ {x : M} (hx : x ∈ W) : ContMDiffAt I (J.prod 𝓘(ℝ, P)) ∞ ψ x := by
    have hsmooth : ContMDiff I (J.prod 𝓘(ℝ, P)) ∞ fun w : W ↦ ψ w := by
      simp only [hψW]
      exact Φ.symm.contMDiff
    exact (contMDiff_subtype_iff.1 hsmooth).contMDiffAt (W.isOpen.mem_nhds hx)
  have hΦψ {x : M} (hx : x ∈ W) : Φ' (ψ x) = x := by
    simp [Φ', ψ, hx]
  have hψf (q : Q) : ψ (f q) = zeroSection P N q := by
    rw [hψW ⟨f q, hfW (mem_range_self q)⟩]
    exact symm_apply_eq_zeroSection_of_apply_zeroSection f hn hdim Φ hΦ q _
  -- The fibre-scaling primitives of the pullback of `γ` to the tube.
  have hΦ'' : ContMDiff (𝓘(ℝ, ℝ).prod (J.prod 𝓘(ℝ, P))) (𝓘(ℝ, ℝ).prod I) ∞
      (Prod.map _root_.id Φ') :=
    (contMDiff_id (I := 𝓘(ℝ, ℝ)) (M := ℝ)).prodMap hΦ'
  obtain ⟨G, hG, hG0, hdG⟩ :=
    exists_contMDiff_mextDeriv_ofFunction_eq_of_mpullback_zeroSection
      (SmoothForm.mpullback (Prod.map _root_.id Φ') hΦ'' γ)
  -- A cutoff `χ`, equal to `1` near `f(Q)` and vanishing outside a compact `K ⊆ W`.
  have hfc : IsCompact (range f) := isCompact_range f.contMDiff.continuous
  obtain ⟨K, hK, hfK, hKW⟩ := exists_compact_between hfc W.isOpen hfW
  obtain ⟨χ, hχ1, hχ0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior I (n := ⊤) hfc.isClosed hfK
  refine ⟨fun p ↦ χ p.2 • G (p.1, ψ p.2), ?_, ⟨K, hK, hKW.trans hWO, fun t x hx ↦ ?_⟩,
    fun t q ↦ ?_, fun t q hq ↦ ?_⟩
  · rintro ⟨t, x⟩
    by_cases hx : x ∈ W
    · exact (χ.contMDiff.comp contMDiff_snd).contMDiffAt.smul
        (hG.contMDiffAt.comp (t, x)
          (contMDiffAt_fst.prodMk (ContMDiffAt.comp (t, x) (hψ hx) contMDiffAt_snd)))
    · refine contMDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      have hxK : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds fun h ↦ hx (hKW h)
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hxK] with p hp
      simp [hχ0 p.2 hp]
  · simp [hχ0 x hx]
  · simp [hψf, hG0]
  · -- Near `f q`, the slice is `G_t ∘ ψ`.
    have hloc : (fun x ↦ χ x • G (t, ψ x)) =ᶠ[𝓝 (f q)] (fun v ↦ G (t, v)) ∘ ψ := by
      filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet (mem_range_self q))] with x hx
      simp [hx]
    have hψq := (hψ (hfW (mem_range_self q))).mdifferentiableAt (by simp)
    have hGq : MDifferentiableAt (J.prod 𝓘(ℝ, P)) 𝓘(ℝ, F) (fun v ↦ G (t, v)) (ψ (f q)) :=
      ((hG.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp)) _
    have hΦq : MDifferentiableAt (J.prod 𝓘(ℝ, P)) I Φ' (ψ (f q)) :=
      (hΦ'.mdifferentiable (by simp)) _
    have hid : Φ' ∘ ψ =ᶠ[𝓝 (f q)] _root_.id := by
      filter_upwards [W.isOpen.mem_nhds (hfW (mem_range_self q))] with x hx
      exact hΦψ hx
    have hd := hdG t q (by
      rw [SmoothForm.mpullback_prodMk_mpullback_prodMap Φ' hΦ' γ t,
        SmoothForm.mpullback_mpullback]
      rw [SmoothForm.coe_mpullback, show Φ' ∘ zeroSection P N = f from funext hΦ,
        ← SmoothForm.coe_mpullback _ f.contMDiff]
      exact hq)
    rw [SmoothForm.mpullback_prodMk_mpullback_prodMap Φ' hΦ' γ t] at hd
    rw [mextDeriv_congr_of_eventuallyEq
        (η := RoughForm.ofFunction I ((fun v ↦ G (t, v)) ∘ ψ)) (hloc.mono fun x hx ↦ by
        rw [RoughForm.ofFunction_apply_eq_constOfIsEmpty,
          RoughForm.ofFunction_apply_eq_constOfIsEmpty]
        exact congrArg _ hx),
      ← mpullback_mextDeriv_ofFunction_apply hψq hGq]
    rw [← hψf q] at hd
    have hcomp := mpullback_comp_at (F := F) (k := 1) hψq hΦq
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ).val
    rw [mpullback_apply_congr hd, SmoothForm.coe_mpullback, ← hcomp, hid.mpullback_eq,
      mpullback_id]

end SmoothEmbedding

end TauCeti

end
