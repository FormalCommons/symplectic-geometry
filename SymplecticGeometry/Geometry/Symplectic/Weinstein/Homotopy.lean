/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Weinstein homotopies

A *Weinstein homotopy* on a boundaryless manifold `M` is a family `t ↦ (ω t, X t, f t)` of
Weinstein structures (`SymplecticGeometry.IsWeinsteinStructure`) indexed by `t : unitInterval`,
smooth in `(t, x)` on `unitInterval × M`, whose functions satisfy a condition at infinity: there
are smooth functions `c₀ < c₁ < c₂ < ⋯` on `[0, 1]`, tending to infinity uniformly, such that
`c k t` is a regular value of `f t` for all `k` and `t`. Such a sequence is a *regular barrier*
of the functions. The condition keeps critical points of `f t` from escaping to infinity as `t`
moves; on a compact manifold it always holds.

Two Weinstein homotopies, the second starting where the first ends, concatenate to a Weinstein
homotopy when they have regular barriers that agree at the seam. Without that hypothesis the
concatenation can fail to have any regular barrier: a pair of critical points born in the first
homotopy, or dying in the second, blocks the values between its critical values at the seam, and
such pairs can block every regular value there. Two Weinstein structures are *Weinstein
homotopic* when one Weinstein homotopy joins them, as in Cieliebak–Eliashberg's Theorem 1.1; this
relation is reflexive and symmetric, and it is not claimed here to be transitive.

## Main declarations

* `SymplecticGeometry.IsRegularBarrier E f c`: `c` is a regular barrier of the family `f`, with
  `SymplecticGeometry.IsRegularBarrier.comp`, `.symm` and `.trans`.
* `SymplecticGeometry.IsWeinsteinHomotopy`: the predicate on a family `(ω, X, f)`, with
  `SymplecticGeometry.isWeinsteinHomotopy_iff`.
* `SymplecticGeometry.IsWeinsteinHomotopy.exists_isRegularBarrier`: the functions of a Weinstein
  homotopy have a regular barrier.
* `SymplecticGeometry.IsWeinsteinHomotopy.refl`: the constant family of a Weinstein structure.
* `SymplecticGeometry.IsWeinsteinHomotopy.comp`: a Weinstein homotopy reparametrized by a smooth
  map `[0, 1] → [0, 1]`.
* `SymplecticGeometry.IsWeinsteinHomotopy.symm`: a Weinstein homotopy run backwards, by
  `unitInterval.symm`.
* `SymplecticGeometry.IsWeinsteinHomotopy.trans`: the concatenation
  `SymplecticGeometry.collaredConcat` of two Weinstein homotopies with regular barriers that agree
  at the seam.
* `SymplecticGeometry.IsWeinsteinHomotopy.pullback`: the pull-back of a Weinstein homotopy along a
  diffeomorphism.
* `SymplecticGeometry.IsWeinsteinHomotopy.of_isCompact`: on a compact manifold, every smooth
  family of Weinstein structures is a Weinstein homotopy.
* `SymplecticGeometry.AreWeinsteinHomotopic`: two Weinstein structures joined by a Weinstein
  homotopy, with `SymplecticGeometry.AreWeinsteinHomotopic.refl` and `.symm`, and
  `SymplecticGeometry.IsWeinsteinHomotopy.areWeinsteinHomotopic_trans`: the start of one Weinstein
  homotopy and the end of the next are joined by their concatenation.

## Implementation notes

The forms are a smooth family in the sense of `SymplecticGeometry.IsSmoothFamily`, over
`unitInterval` with the model `𝓡∂ 1`. The fields are jointly smooth as sections of the tangent
bundle along the projection `unitInterval × M → M`, in the form of the hypothesis of
`SymplecticGeometry.isSmoothFamily_interiorₗ`. The functions are jointly smooth on
`unitInterval × M`.

The functions `c k` are smooth on `[0, 1]`, with the model `𝓡∂ 1`, as Cieliebak and Eliashberg
ask, so that a statement that a Weinstein homotopy exists says as much as theirs. They ask for
`c k t → ∞` at each `t`; since the `c k` are continuous and increasing in `k`, the convergence
is then uniform, as `[0, 1]` is compact, and the predicate asks for the uniform form.

For a single Weinstein structure, the regular values `c k ∈ (k, k + 1)` exist because a proper
generalized Morse function has finitely many critical values in each compact interval
(`TauCeti.IsGeneralizedMorse.exists_isRegularValue_mem_Ioo`). On a compact manifold the functions
`f t` are bounded above, uniformly in `t`, by some `B`, and the constants `B + k + 1` are values
outside their ranges, so they are regular values (`TauCeti.isRegularValue_of_notMem_range`). The
field pulled back along a diffeomorphism `Φ` is the image of `X t` under the tangent map of `Φ⁻¹`
(`Diffeomorph.tangentMap_symm_mk`), so it stays jointly smooth.

The concatenation `SymplecticGeometry.collaredConcat` follows Tau Ceti's
`TauCeti.Diffeotopy.IsHomotopy.trans`: each piece is reparametrized by `TauCeti.collaredFirstHalf`
or `TauCeti.collaredSecondHalf`, which are stationary near the seam, and the pieces glue smoothly
by `ContMDiff.glue_collaredHalves_left` (for the fields and the functions),
`ContMDiff.collaredConcat` (for the barriers) and
`SymplecticGeometry.IsSmoothFamily.glue_collaredHalves` (for the forms). Its values at `t = 0` and
`t = 1` are `SymplecticGeometry.collaredConcat_zero` and `collaredConcat_one`, so the glued barrier
can be glued again at the next seam.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.6, Definition 11.19 and the definition of Morse homotopies after it, and Theorem 1.1
-/

public section

open Bundle Filter Set TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable (E) in
/-- A **regular barrier** of a family `f t`, `t ∈ [0, 1]`, of functions on `M` is a sequence of
smooth functions `c₀ < c₁ < ⋯` on `[0, 1]`, tending to infinity uniformly, with `c k t` a regular
value of `f t` for all `k` and `t`. The model `E` is explicit, since `f` does not determine it. -/
structure IsRegularBarrier (f : unitInterval → M → ℝ) (c : ℕ → unitInterval → ℝ) : Prop where
  /-- Each `c k` is smooth on `[0, 1]`. -/
  contMDiff (k : ℕ) : ContMDiff (𝓡∂ 1) 𝓘(ℝ) (⊤ : ℕ∞) (c k)
  /-- At each time, the `c k` increase strictly with `k`. -/
  strictMono (t : unitInterval) : StrictMono fun k ↦ c k t
  /-- The `c k` tend to infinity, uniformly in time. -/
  eventually_le (C : ℝ) : ∀ᶠ k in atTop, ∀ t, C ≤ c k t
  /-- Each `c k t` is a regular value of `f t`. -/
  isRegularValue (k : ℕ) (t : unitInterval) : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (f t) (c k t)

variable {f : unitInterval → M → ℝ}

namespace IsRegularBarrier

variable {c : ℕ → unitInterval → ℝ}

/-- **Reparametrizing a regular barrier.** Composing with a smooth map `φ : [0, 1] → [0, 1]`
turns a regular barrier of `f` into one of `t ↦ f (φ t)`. -/
protected theorem comp (hc : IsRegularBarrier E f c) (φ : unitInterval → unitInterval)
    (hφ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) (⊤ : ℕ∞) φ) :
    IsRegularBarrier E (fun t ↦ f (φ t)) fun k t ↦ c k (φ t) where
  contMDiff k := (hc.contMDiff k).comp hφ
  strictMono t := hc.strictMono (φ t)
  eventually_le C := by filter_upwards [hc.eventually_le C] with k hk t using hk _
  isRegularValue k t := hc.isRegularValue k (φ t)

/-- A regular barrier run backwards, by `unitInterval.symm`, is a regular barrier of the family
run backwards. -/
protected theorem symm (hc : IsRegularBarrier E f c) :
    IsRegularBarrier E (fun t ↦ f (unitInterval.symm t)) fun k t ↦ c k (unitInterval.symm t) :=
  hc.comp _ unitInterval.contMDiff_symm

/-- **Concatenation of regular barriers.** Regular barriers `c` of `f` and `c'` of `f'` that agree
at the seam, `c k 1 = c' k 0` for every `k`, concatenate to a regular barrier
`k ↦ collaredConcat (c k) (c' k)` of the concatenated family `collaredConcat f f'`. -/
protected theorem trans {f' : unitInterval → M → ℝ} {c' : ℕ → unitInterval → ℝ}
    (hc : IsRegularBarrier E f c) (hc' : IsRegularBarrier E f' c')
    (hcc' : ∀ k, c k 1 = c' k 0) :
    IsRegularBarrier E (collaredConcat f f') fun k ↦ collaredConcat (c k) (c' k) where
  contMDiff k := (hc.contMDiff k).collaredConcat (hc'.contMDiff k) (hcc' k) le_rfl
  strictMono t := by
    simp only [collaredConcat_def]
    split_ifs
    exacts [hc.strictMono _, hc'.strictMono _]
  eventually_le C := by
    filter_upwards [hc.eventually_le C, hc'.eventually_le C] with k hk hk' t
    rw [collaredConcat_def]
    split_ifs
    exacts [hk _, hk' _]
  isRegularValue k t := by
    simp only [collaredConcat_def]
    split_ifs
    exacts [hc.isRegularValue k _, hc'.isRegularValue k _]
end IsRegularBarrier

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]

/-- A **Weinstein homotopy** on `M` is a family `t ↦ (ω t, X t, f t)`, `t ∈ [0, 1]`, of Weinstein
structures that depends smoothly on `(t, x) ∈ [0, 1] × M`, together with smooth functions
`c₀ < c₁ < ⋯` on `[0, 1]`, tending to infinity uniformly, with `c k t` a regular value of `f t`
for all `k` and `t` (a `SymplecticGeometry.IsRegularBarrier` of the functions). -/
structure IsWeinsteinHomotopy (ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M)
    (X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : unitInterval → M → ℝ) :
    Prop where
  /-- The forms are a smooth family. -/
  isSmoothFamily : IsSmoothFamily (𝓡∂ 1) ω
  /-- The fields are jointly smooth in the parameter and the point. -/
  contMDiff_field : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
    fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M)
  /-- The functions are jointly smooth in the parameter and the point. -/
  contMDiff_function : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞)
    fun p : unitInterval × M ↦ f p.1 p.2
  /-- Each member of the family is a Weinstein structure. -/
  isWeinsteinStructure (t : unitInterval) : IsWeinsteinStructure (ω t) (X t) (f t)
  /-- The condition at infinity: the functions have a regular barrier. -/
  exists_isRegularBarrier : ∃ c : ℕ → unitInterval → ℝ, IsRegularBarrier E f c

variable {ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M}
  {X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The conditions of `SymplecticGeometry.IsWeinsteinHomotopy`, as a conjunction. -/
theorem isWeinsteinHomotopy_iff :
    IsWeinsteinHomotopy ω X f ↔
      IsSmoothFamily (𝓡∂ 1) ω ∧
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
        (fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) (fun p : unitInterval × M ↦ f p.1 p.2) ∧
      (∀ t, IsWeinsteinStructure (ω t) (X t) (f t)) ∧
      ∃ c : ℕ → unitInterval → ℝ, IsRegularBarrier E f c :=
  ⟨fun h ↦ ⟨h.isSmoothFamily, h.contMDiff_field, h.contMDiff_function, h.isWeinsteinStructure,
      h.exists_isRegularBarrier⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩


namespace IsWeinsteinHomotopy

/-- **The constant Weinstein homotopy.** The constant family of a Weinstein structure is a
Weinstein homotopy. -/
protected theorem refl {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {f : M → ℝ} (hW : IsWeinsteinStructure ω X f) :
    IsWeinsteinHomotopy (fun _ ↦ ω) (fun _ ↦ X) (fun _ ↦ f) := by
  -- A regular value of `f` in each interval `(k, k + 1)`.
  have hex (k : ℕ) : ∃ c ∈ Ioo (k : ℝ) (k + 1), IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c :=
    hW.isGeneralizedMorse.exists_isRegularValue_mem_Ioo (by linarith)
      (hW.isProperMap.isCompact_preimage isCompact_Icc)
  choose c hc hreg using hex
  refine ⟨isSmoothFamily_const ω, hW.contMDiff_field.comp contMDiff_snd,
    hW.isGeneralizedMorse.contMDiff.comp contMDiff_snd, fun _ ↦ hW,
    ⟨fun k _ ↦ c k, fun _ ↦ contMDiff_const, fun _ ↦ ?_, fun C ↦ ?_, fun k _ ↦ hreg k⟩⟩
  · exact strictMono_nat_of_lt_succ fun k ↦ (hc k).2.trans (by simpa using (hc (k + 1)).1)
  · filter_upwards [eventually_ge_atTop ⌈C⌉₊] with k hk _
    exact (Nat.ceil_le.1 hk).trans (hc k).1.le

/-- **Reparametrizing a Weinstein homotopy.** Composing the parameter of a Weinstein homotopy with
a smooth map `φ : [0, 1] → [0, 1]` gives a Weinstein homotopy. -/
protected theorem comp (h : IsWeinsteinHomotopy ω X f) (φ : unitInterval → unitInterval)
    (hφ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) (⊤ : ℕ∞) φ) :
    IsWeinsteinHomotopy (fun t ↦ ω (φ t)) (fun t ↦ X (φ t)) (fun t ↦ f (φ t)) := by
  obtain ⟨c, hc⟩ := h.exists_isRegularBarrier
  have hσ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      fun p : unitInterval × M ↦ (φ p.1, p.2) :=
    (hφ.comp contMDiff_fst).prodMk contMDiff_snd
  exact ⟨h.isSmoothFamily.comp φ hφ, h.contMDiff_field.comp hσ,
    h.contMDiff_function.comp hσ, fun t ↦ h.isWeinsteinStructure _, ⟨_, hc.comp φ hφ⟩⟩

/-- **A Weinstein homotopy run backwards** is a Weinstein homotopy: reparametrize the family by
`t ↦ 1 - t`. -/
protected theorem symm (h : IsWeinsteinHomotopy ω X f) :
    IsWeinsteinHomotopy (fun t ↦ ω (unitInterval.symm t)) (fun t ↦ X (unitInterval.symm t))
      (fun t ↦ f (unitInterval.symm t)) :=
  h.comp _ unitInterval.contMDiff_symm

/-- **Concatenation of Weinstein homotopies.** Two Weinstein homotopies, the second starting where
the first ends, concatenate to a Weinstein homotopy `t ↦ (collaredConcat ω ω' t,
collaredConcat X X' t, collaredConcat f f' t)`, provided that the two families have regular
barriers `c` and `c'` that agree at the seam, `c k 1 = c' k 0` for every `k`. The concatenated
barrier is `SymplecticGeometry.IsRegularBarrier.trans`. -/
protected theorem trans {ω' : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M}
    {X' : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x} {f' : unitInterval → M → ℝ}
    (h : IsWeinsteinHomotopy ω X f) (h' : IsWeinsteinHomotopy ω' X' f')
    (hω : ω 1 = ω' 0) (hX : X 1 = X' 0) (hf : f 1 = f' 0) {c c' : ℕ → unitInterval → ℝ}
    (hc : IsRegularBarrier E f c) (hc' : IsRegularBarrier E f' c')
    (hcc' : ∀ k, c k 1 = c' k 0) :
    IsWeinsteinHomotopy (collaredConcat ω ω') (collaredConcat X X') (collaredConcat f f') where
  isSmoothFamily := h.isSmoothFamily.glue_collaredHalves h'.isSmoothFamily hω
  contMDiff_field := by
    refine (h.contMDiff_field.glue_collaredHalves_left h'.contMDiff_field
      (fun x ↦ by rw [hX]) le_rfl).congr fun p ↦ ?_
    exact apply_collaredConcat (fun Y ↦ (⟨p.2, Y p.2⟩ : TangentBundle 𝓘(ℝ, E) M)) X X'
      p.1
  contMDiff_function := by
    refine (h.contMDiff_function.glue_collaredHalves_left h'.contMDiff_function
      (fun x ↦ by rw [hf]) le_rfl).congr fun p ↦ ?_
    exact apply_collaredConcat (fun g ↦ g p.2) f f' p.1
  isWeinsteinStructure t := by
    simp only [collaredConcat_def]
    split_ifs
    exacts [h.isWeinsteinStructure _, h'.isWeinsteinStructure _]
  exists_isRegularBarrier := ⟨_, hc.trans hc' hcc'⟩

/-- **Weinstein homotopies pull back along diffeomorphisms.** If `t ↦ (ω t, X t, f t)` is a
Weinstein homotopy on `M` and `Φ : M' → M` is a diffeomorphism, then the family of pulled-back
Weinstein structures `t ↦ (Φ^* ω t, Φ^* X t, f t ∘ Φ)` is a Weinstein homotopy on `M'`. -/
theorem pullback (h : IsWeinsteinHomotopy ω X f) {M' : Type*} [TopologicalSpace M']
    [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M']
    (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M' M (⊤ : ℕ∞)) :
    IsWeinsteinHomotopy (fun t ↦ SmoothForm.mpullback Φ Φ.contMDiff (ω t))
      (fun t ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (X t)) (fun t ↦ f t ∘ Φ) := by
  obtain ⟨c, hc⟩ := h.exists_isRegularBarrier
  have hΦ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      fun p : unitInterval × M' ↦ (p.1, Φ p.2) :=
    contMDiff_fst.prodMk (Φ.contMDiff.comp contMDiff_snd)
  -- The pulled-back field is the image of `X t` under the tangent map of `Φ⁻¹`.
  have hfield : (fun p : unitInterval × M' ↦ (⟨p.2, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ
      (X p.1) p.2⟩ : TangentBundle 𝓘(ℝ, E) M')) =
      tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) Φ.symm ∘
        fun p : unitInterval × M' ↦ (⟨Φ p.2, X p.1 (Φ p.2)⟩ : TangentBundle 𝓘(ℝ, E) M) :=
    funext fun p ↦ by
      rw [Function.comp_apply,Φ.tangentMap_symm_mk (by simp), VectorField.mpullback_apply]
  refine ⟨h.isSmoothFamily.mpullback Φ Φ.contMDiff, ?_, h.contMDiff_function.comp hΦ,
    fun t ↦ (h.isWeinsteinStructure t).pullback Φ,
    ⟨c, hc.contMDiff, hc.strictMono, hc.eventually_le,
      fun k t ↦ (Φ.isRegularValue_comp_iff (by simp)).2 (hc.isRegularValue k t)⟩⟩
  rw [hfield]
  exact (Φ.symm.contMDiff.contMDiff_tangentMap le_rfl).comp (h.contMDiff_field.comp hΦ)

/-- **Weinstein homotopies on a compact manifold.** On a compact manifold, a family of Weinstein
structures whose forms, fields and functions depend smoothly on the parameter and the point is a
Weinstein homotopy: the condition at infinity holds automatically. -/
theorem of_isCompact [CompactSpace M] (hω : IsSmoothFamily (𝓡∂ 1) ω)
    (hX : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
      fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hf : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦ f p.1 p.2)
    (hW : ∀ t, IsWeinsteinStructure (ω t) (X t) (f t)) : IsWeinsteinHomotopy ω X f := by
  -- A bound `B` for all the functions; the levels `B + k + 1` are empty.
  obtain ⟨B, hB⟩ := (isCompact_range hf.continuous).bddAbove
  have hlt (k : ℕ) (t : unitInterval) (x : M) : f t x < B + k + 1 := by
    have := hB (mem_range_self (t, x))
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    dsimp only at *
    linarith
  refine ⟨hω, hX, hf, hW, ⟨fun k _ ↦ B + k + 1, fun _ ↦ contMDiff_const,
    fun _ ↦ strictMono_nat_of_lt_succ fun k ↦ by push_cast; linarith, fun C ↦ ?_,
    fun k t ↦ isRegularValue_of_notMem_range fun ⟨x, hx⟩ ↦ (hlt k t x).ne hx⟩⟩
  filter_upwards [eventually_ge_atTop ⌈C - B⌉₊] with k hk _
  have := Nat.ceil_le.1 hk
  linarith

end IsWeinsteinHomotopy

/-- Two Weinstein structures `(ω₀, X₀, f₀)` and `(ω₁, X₁, f₁)` on `M` are **Weinstein homotopic**
when one Weinstein homotopy `t ↦ (ω t, X t, f t)` joins them: it is `(ω₀, X₀, f₀)` at `t = 0` and
`(ω₁, X₁, f₁)` at `t = 1`. -/
def AreWeinsteinHomotopic (ω₀ : SmoothTwoForm 𝓘(ℝ, E) M) (X₀ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (f₀ : M → ℝ) (ω₁ : SmoothTwoForm 𝓘(ℝ, E) M) (X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (f₁ : M → ℝ) : Prop :=
  ∃ (ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M)
    (X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : unitInterval → M → ℝ),
    IsWeinsteinHomotopy ω X f ∧ ω 0 = ω₀ ∧ X 0 = X₀ ∧ f 0 = f₀ ∧ ω 1 = ω₁ ∧ X 1 = X₁ ∧ f 1 = f₁

section AreWeinsteinHomotopic

variable {ω₀ ω₁ : SmoothTwoForm 𝓘(ℝ, E) M} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {f₀ f₁ : M → ℝ}

/-- The defining property of `SymplecticGeometry.AreWeinsteinHomotopic`. -/
theorem areWeinsteinHomotopic_def :
    AreWeinsteinHomotopic ω₀ X₀ f₀ ω₁ X₁ f₁ ↔
      ∃ (ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M)
        (X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : unitInterval → M → ℝ),
        IsWeinsteinHomotopy ω X f ∧ ω 0 = ω₀ ∧ X 0 = X₀ ∧ f 0 = f₀ ∧ ω 1 = ω₁ ∧ X 1 = X₁ ∧
          f 1 = f₁ :=
  Iff.rfl

/-- A Weinstein homotopy joins its structures at `t = 0` and at `t = 1`. -/
theorem IsWeinsteinHomotopy.areWeinsteinHomotopic (h : IsWeinsteinHomotopy ω X f) :
    AreWeinsteinHomotopic (ω 0) (X 0) (f 0) (ω 1) (X 1) (f 1) :=
  ⟨ω, X, f, h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A Weinstein structure is Weinstein homotopic to itself, by the constant homotopy. -/
protected theorem AreWeinsteinHomotopic.refl (hW : IsWeinsteinStructure ω₀ X₀ f₀) :
    AreWeinsteinHomotopic ω₀ X₀ f₀ ω₀ X₀ f₀ :=
  (IsWeinsteinHomotopy.refl hW).areWeinsteinHomotopic

/-- Being Weinstein homotopic is symmetric: run the homotopy backwards. -/
protected theorem AreWeinsteinHomotopic.symm (h : AreWeinsteinHomotopic ω₀ X₀ f₀ ω₁ X₁ f₁) :
    AreWeinsteinHomotopic ω₁ X₁ f₁ ω₀ X₀ f₀ := by
  obtain ⟨ω, X, f, h, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  simpa only [unitInterval.symm_zero, unitInterval.symm_one] using h.symm.areWeinsteinHomotopic

/-- Two Weinstein homotopies, the second starting where the first ends, with regular barriers that
agree at the seam, join the start of the first to the end of the second, by their concatenation
`SymplecticGeometry.IsWeinsteinHomotopy.trans`. -/
theorem IsWeinsteinHomotopy.areWeinsteinHomotopic_trans
    {ω' : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M}
    {X' : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x} {f' : unitInterval → M → ℝ}
    (h : IsWeinsteinHomotopy ω X f) (h' : IsWeinsteinHomotopy ω' X' f')
    (hω : ω 1 = ω' 0) (hX : X 1 = X' 0) (hf : f 1 = f' 0) {c c' : ℕ → unitInterval → ℝ}
    (hc : IsRegularBarrier E f c) (hc' : IsRegularBarrier E f' c')
    (hcc' : ∀ k, c k 1 = c' k 0) :
    AreWeinsteinHomotopic (ω 0) (X 0) (f 0) (ω' 1) (X' 1) (f' 1) := by
  simpa only [collaredConcat_zero, collaredConcat_one] using
    (h.trans h' hω hX hf hc hc' hcc').areWeinsteinHomotopic

end AreWeinsteinHomotopic

end SymplecticGeometry

end
