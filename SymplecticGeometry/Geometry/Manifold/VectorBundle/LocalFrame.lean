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

The file also gives the two general steps of such a gluing. A family of `C^n` sections whose
values at each point of `U` are the vectors of a basis is a frame on `U`
(`IsLocalFrameOn.of_forall_exists_basis`), and frames on open sets `U` and `U'` that agree on
`U ∩ U'` glue to the piecewise frame on `U ∪ U'` (`IsLocalFrameOn.piecewise`, from
`IsLocalFrameOn.union_of_isOpen`).

## Main results

* `IsLocalFrameOn.of_forall_exists_basis`: a frame from pointwise bases.
* `IsLocalFrameOn.piecewise`: two frames that agree on the overlap of their open sets glue.
* `IsLocalFrameOn.exists_isLocalFrameOn_union`: two local frames glued along a map `φ` into their
  overlap.

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

end IsLocalFrameOn

end
