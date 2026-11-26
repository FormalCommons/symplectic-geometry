/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

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

The file also gives the general steps of such gluings. A family of `C^n` sections whose
values at each point of `U` are the vectors of a basis is a frame on `U`
(`IsLocalFrameOn.of_forall_exists_basis`); Tau Ceti's
`IsLocalFrameOn.of_linearIndependent_of_card_eq_finrank` gives one from linear independence.
A frame on each open set of a family is a frame on their union (`IsLocalFrameOn.iUnion_of_isOpen`),
and frames on open sets `U` and `U'` that agree on `U ∩ U'` glue to the piecewise frame on `U ∪ U'`
(`IsLocalFrameOn.piecewise`, from `IsLocalFrameOn.union_of_isOpen`).

A frame on all of the base gives, by Tau Ceti's
`ContMDiffVectorBundle.exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn`, a
trivialization over the whole base in the maximal atlas. It and its inverse are `C^n`, so
`Bundle.Trivialization.toDiffeomorphOfBaseSetEqUniv` makes it a diffeomorphism of the total space
with `B × F`.

## Main results

* `IsLocalFrameOn.of_forall_exists_basis`: a frame from pointwise bases.
* `IsLocalFrameOn.iUnion_of_isOpen`: a family that is a frame on each of a family of open sets is
  a frame on their union.
* `IsLocalFrameOn.piecewise`: two frames that agree on the overlap of their open sets glue.
* `IsLocalFrameOn.exists_isLocalFrameOn_union`: two local frames glued along a map `φ` into their
  overlap.
* `IsLocalFrameOn.exists_isLocalFrameOn_iUnion`: the limit of a sequence of local frames on an
  increasing sequence of open sets, each agreeing with the previous one.
* `Bundle.exists_diffeomorph_prod_of_isLocalFrameOn_univ`: a bundle with a global frame is
  diffeomorphic to the product bundle, by a map over the base that is linear on each fibre.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

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

namespace IsLocalFrameOn

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V IB] [Finite ι] in
/-- A family of sections that is `C^n` on `U`, and whose vectors at each point of `U` are those of
a basis of the fibre, is a `C^n` local frame on `U`. -/
theorem of_forall_exists_basis (hb : ∀ x ∈ U, ∃ b : Module.Basis ι 𝕜 (V x), ⇑b = (s · x))
    (hs : ∀ i, ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (T% (s i)) U) :
    IsLocalFrameOn IB F n s U where
  linearIndependent {x} hx := by
    obtain ⟨b, hb⟩ := hb x hx
    exact hb ▸ b.linearIndependent
  generating {x} hx := by
    obtain ⟨b, hb⟩ := hb x hx
    exact hb ▸ b.span_eq.ge
  contMDiffOn := hs

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V IB] [Finite ι] in
/-- A family of sections that is a `C^n` local frame on each of two open sets is a `C^n` local
frame on their union. -/
theorem union_of_isOpen (hs : IsLocalFrameOn IB F n s U) (hs' : IsLocalFrameOn IB F n s U')
    (hU : IsOpen U) (hU' : IsOpen U') : IsLocalFrameOn IB F n s (U ∪ U') where
  linearIndependent hx := hx.elim hs.linearIndependent hs'.linearIndependent
  generating hx := hx.elim hs.generating hs'.generating
  contMDiffOn i := (hs.contMDiffOn i).union_of_isOpen (hs'.contMDiffOn i) hU hU'

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V IB] [Finite ι] in
/-- A family of sections that is a `C^n` local frame on each open set of a family is a `C^n` local
frame on their union. -/
theorem iUnion_of_isOpen {κ : Type*} {W : κ → Set B} (hs : ∀ k, IsLocalFrameOn IB F n s (W k))
    (hW : ∀ k, IsOpen (W k)) : IsLocalFrameOn IB F n s (⋃ k, W k) where
  linearIndependent hx := by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact (hs k).linearIndependent hk
  generating hx := by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact (hs k).generating hk
  contMDiffOn i := .iUnion_of_isOpen (fun k ↦ (hs k).contMDiffOn i) hW

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V IB] [Finite ι] in
/-- `C^n` local frames `s` on an open set `U` and `s'` on an open set `U'` that agree on `U ∩ U'`
glue to a `C^n` local frame on `U ∪ U'`: the family that is `s` on `U` and `s'` off `U`. -/
theorem piecewise [∀ x, Decidable (x ∈ U)] (hs : IsLocalFrameOn IB F n s U)
    (hs' : IsLocalFrameOn IB F n s' U') (hU : IsOpen U) (hU' : IsOpen U')
    (hss' : ∀ i, ∀ x ∈ U ∩ U', s i x = s' i x) :
    IsLocalFrameOn IB F n (fun i ↦ U.piecewise (s i) (s' i)) (U ∪ U') := by
  refine (hs.congr fun i x hx ↦ ?_).union_of_isOpen (hs'.congr fun i x hx ↦ ?_) hU hU'
  · rw [piecewise_eq_of_mem _ _ _ hx]
  · by_cases hxU : x ∈ U
    · rw [piecewise_eq_of_mem _ _ _ hxU, hss' i x ⟨hxU, hx⟩]
    · rw [piecewise_eq_of_notMem _ _ _ hxU]

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
  exact ⟨_, (hs.mono hWU).piecewise (of_forall_exists_basis (fun _ ↦ hbasis) hgsmooth) hW hW'
    fun i x hx ↦ (hgs hx i).symm, fun i x hx ↦ piecewise_eq_of_mem _ _ _ hx⟩

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
  exact ⟨s, iUnion_of_isOpen (fun k ↦ (ht k).congr fun i x hx ↦ (hs k i hx).symm) hWo,
    fun k i x hx ↦ hs k i hx⟩

end IsLocalFrameOn

namespace Bundle

omit [FiniteDimensional 𝕜 F] in
/-- A `C^n` vector bundle with a global `C^n` frame, indexed by a type that indexes a basis of the
model fibre `F`, is `C^n` trivial: its total space is `C^n`-diffeomorphic to `B × F` by a map that
covers the identity of `B` and is a continuous linear isomorphism on each fibre. -/
theorem exists_diffeomorph_prod_of_isLocalFrameOn_univ (b : Module.Basis ι 𝕜 F)
    (hs : IsLocalFrameOn IB F n s univ) :
    ∃ (h : TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯ B × F)
      (L : ∀ x, V x ≃L[𝕜] F), ∀ (x : B) (v : V x), h ⟨x, v⟩ = (x, L x v) := by
  obtain ⟨e, _, hem, he⟩ :=
    (ContMDiffVectorBundle.exists_trivialization_baseSet_eq_iff_exists_isLocalFrameOn
      isOpen_univ b).2 ⟨s, hs⟩
  have hmem (x : B) : x ∈ e.baseSet := he ▸ mem_univ x
  have hsrc : e.source = univ := by rw [e.source_eq, he, preimage_univ]
  have h₁ : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n e := by
    rw [← contMDiffOn_univ, ← hsrc]
    exact Trivialization.contMDiffOn_of_mem_maximalAtlas hem
  have h₂ : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      e.toOpenPartialHomeomorph.symm := by
    intro q
    rw [Trivialization.contMDiffAt_iff_of_mem_maximalAtlas hem (hsrc ▸ mem_univ _)]
    refine ⟨contMDiffAt_fst.congr_of_eventuallyEq (.of_forall fun q' ↦ ?_),
      contMDiffAt_snd.congr_of_eventuallyEq (.of_forall fun q' ↦ ?_)⟩
    · exact e.proj_symm_apply' (hmem q'.1)
    · exact congrArg Prod.snd (e.apply_symm_apply' (hmem q'.1))
  refine ⟨e.toDiffeomorphOfBaseSetEqUniv he h₁ h₂, fun x ↦ e.continuousLinearEquivAt 𝕜 x (hmem x),
    fun x v ↦ ?_⟩
  rw [Trivialization.coe_toDiffeomorphOfBaseSetEqUniv]
  exact e.apply_eq_prod_continuousLinearEquivAt 𝕜 x (hmem x) v

end Bundle

end
