/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Gluing two local frames of a vector bundle

Let `s` and `s'` be `C^n` local frames of a vector bundle `V` with finite-dimensional fibre on
open sets `U` and `U'` of a manifold, indexed by the same finite type. On `U ∩ U'` each `s i` is a
combination `∑ j, A i j • s' j` with `C^n` coefficients `A i j`, by Tau Ceti's
`IsLocalFrameOn.contMDiffOn_coeff`. Given a `C^n` map `φ` that sends an open set `W' ⊆ U'` into
`U ∩ U'`, the sections `x ↦ ∑ j, A i j (φ x) • s' j x` form a frame on `W'`: at each point they
are the image of the basis `s · (φ x)` under the linear map that sends `s' j (φ x)` to `s' j x`.
Where `φ` is the identity, they agree with `s`. So, if `φ` is the identity on `W ∩ W'` for an open
`W ⊆ U`, they glue with `s` to a frame on `W ∪ W'` that is `s` on `W`.

## Main results

* `IsLocalFrameOn.exists_isLocalFrameOn_union`: two local frames glued along a map `φ` into their
  overlap.
* `IsLocalFrameOn.exists_isLocalFrameOn_iUnion`: the limit of a sequence of local frames on an
  increasing sequence of open sets, each agreeing with the previous one.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace IsLocalFrameOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]
  {ι : Type*} [Finite ι] {s s' : ι → Π x, V x} {U U' : Set B}

/-- Two `C^n` local frames `s` on `U` and `s'` on `U'`, indexed by the same finite type, glue to a
`C^n` local frame on `W ∪ W'` that is `s` on `W`, for open sets `W ⊆ U` and `W' ⊆ U'` that admit
a `C^n` map `φ` from `W'` into `U ∩ U'` that is the identity on `W ∩ W'`. -/
theorem exists_isLocalFrameOn_union (hs : IsLocalFrameOn IB F n s U)
    (hs' : IsLocalFrameOn IB F n s' U') (hU : IsOpen U) (hU' : IsOpen U') {W W' : Set B}
    (hW : IsOpen W) (hW' : IsOpen W') (hWU : W ⊆ U) (hW'U' : W' ⊆ U') {φ : B → B}
    (hφ : ContMDiffOn IB IB n φ W') (hφW' : MapsTo φ W' (U ∩ U'))
    (hφid : ∀ x ∈ W ∩ W', φ x = x) :
    ∃ t : ι → Π x, V x, IsLocalFrameOn IB F n t (W ∪ W') ∧ ∀ i, ∀ x ∈ W, t i x = s i x := by
  classical
  let := Fintype.ofFinite ι
  -- The coefficients are taken in `s'` restricted to the overlap, where they are `C^n`.
  have hs'' : IsLocalFrameOn IB F n s' (U ∩ U') := hs'.mono inter_subset_right
  -- The frame `s` rewritten in `s'` at the point `φ x`.
  set g : ι → Π x, V x := fun i x ↦ ∑ j, hs''.coeff j (φ x) (s i (φ x)) • s' j x with hg
  -- At a point of `W'`, `g · x` is the image of the basis `s · (φ x)` under the linear map
  -- sending `s' j (φ x)` to `s' j x`.
  have hbasis {x : B} (hx : x ∈ W') : ∃ b : Module.Basis ι 𝕜 (V x), ⇑b = (g · x) := by
    have hy := hφW' hx
    refine ⟨(hs.toBasisAt hy.1).map ((hs''.toBasisAt hy).equiv
      (hs'.toBasisAt (hW'U' hx)) (Equiv.refl ι)), funext fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, toBasisAt_coe, hs''.coeff_sum_eq (s i) hy, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, ← toBasisAt_coe hs'' hy, Module.Basis.equiv_apply, Equiv.refl_apply,
      toBasisAt_coe]
  have hgs {x : B} (hx : x ∈ W ∩ W') (i : ι) : g i x = s i x := by
    simp only [hg]
    rw [hφid x hx]
    exact (hs''.coeff_sum_eq (s i) ⟨hWU hx.1, hW'U' hx.2⟩).symm
  have hgsmooth (i : ι) : ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (T% (g i)) W' := by
    have hA (j : ι) : ContMDiffOn IB 𝓘(𝕜) n (fun y ↦ hs''.coeff j y (s i y)) (U ∩ U') :=
      hs''.contMDiffOn_coeff (hU.inter hU') le_rfl ((hs.contMDiffOn i).mono inter_subset_left) j
    exact ContMDiffOn.sum_section fun j _ ↦
      ((hA j).comp hφ hφW').smul_section ((hs'.contMDiffOn j).mono hW'U')
  -- Off `W`, the glued family at a point of `W'` is the basis given by `hbasis`.
  have hfam {x : B} (hxW : x ∉ W) (hx : x ∈ W') : ∃ b : Module.Basis ι 𝕜 (V x),
      (fun i ↦ if x ∈ W then s i x else g i x) = ⇑b := by
    obtain ⟨b, hb⟩ := hbasis hx
    exact ⟨b, by simp [hxW, hb]⟩
  refine ⟨fun i x ↦ if x ∈ W then s i x else g i x, ⟨fun {x} hx ↦ ?_, fun {x} hx ↦ ?_, fun i ↦ ?_⟩,
    fun i x hx ↦ by simp [hx]⟩
  · by_cases hxW : x ∈ W
    · simpa [hxW] using hs.linearIndependent (hWU hxW)
    · obtain ⟨b, hb⟩ := hfam hxW (hx.resolve_left hxW)
      rw [hb]
      exact b.linearIndependent
  · by_cases hxW : x ∈ W
    · simpa [hxW] using hs.generating (hWU hxW)
    · obtain ⟨b, hb⟩ := hfam hxW (hx.resolve_left hxW)
      rw [hb]
      exact b.span_eq.ge
  · refine ContMDiffOn.union_of_isOpen ?_ ?_ hW hW'
    · exact ((hs.contMDiffOn i).mono hWU).congr fun x hx ↦ by simp [hx]
    · refine (hgsmooth i).congr fun x hx ↦ ?_
      by_cases hxW : x ∈ W
      · simp [hxW, hgs ⟨hxW, hx⟩ i]
      · simp [hxW]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V IB] [Finite ι] in
/-- A sequence of `C^n` local frames `t k` on an increasing sequence of open sets `W k`, each
agreeing with the previous one on its open set, has a limit: a `C^n` local frame on `⋃ k, W k` that
is `t k` on `W k`. -/
theorem exists_isLocalFrameOn_iUnion {W : ℕ → Set B} (hW : Monotone W) (hWo : ∀ k, IsOpen (W k))
    {t : ℕ → ι → Π x, V x} (ht : ∀ k, IsLocalFrameOn IB F n (t k) (W k))
    (htt : ∀ k i, ∀ x ∈ W k, t (k + 1) i x = t k i x) :
    ∃ s : ι → Π x, V x, IsLocalFrameOn IB F n s (⋃ k, W k) ∧
      ∀ k i, ∀ x ∈ W k, s i x = t k i x := by
  classical
  -- Once a point lies in `W k`, the frames from `t k` on agree at that point.
  have hle {k m : ℕ} (hkm : k ≤ m) (i : ι) {x : B} (hx : x ∈ W k) : t m i x = t k i x := by
    induction m, hkm using Nat.le_induction with
    | base => rfl
    | succ m hkm ih => rw [htt m i x (hW hkm hx), ih]
  let s : ι → Π x, V x := fun i x ↦ if h : ∃ k, x ∈ W k then t (Nat.find h) i x else 0
  have hs (k : ℕ) (i : ι) {x : B} (hx : x ∈ W k) : s i x = t k i x := by
    have h : ∃ k, x ∈ W k := ⟨k, hx⟩
    simp only [s, h, ↓reduceDIte]
    exact (hle (Nat.find_min' h hx) i (Nat.find_spec h)).symm
  refine ⟨s, ⟨fun {x} hx ↦ ?_, fun {x} hx ↦ ?_, fun i ↦ ?_⟩, fun k i x hx ↦ hs k i hx⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    simpa [hs k _ hk] using (ht k).linearIndependent hk
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    simpa [hs k _ hk] using (ht k).generating hk
  · refine contMDiffOn_of_locally_contMDiffOn fun x hx ↦ ?_
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    refine ⟨W k, hWo k, hk, (((ht k).contMDiffOn i).mono inter_subset_right).congr ?_⟩
    intro y hy
    simp [hs k i hy.2]

end IsLocalFrameOn

end
