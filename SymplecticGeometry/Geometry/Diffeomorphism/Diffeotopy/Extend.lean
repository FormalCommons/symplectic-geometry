/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.UnitInterval
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph

/-!
# Moving compactly supported diffeomorphisms and diffeotopies along embeddings

Let `G` be a smooth isotopy of maps `W → M` whose slices `G_t` are local diffeomorphisms, and let
`Λ` be a diffeomorphism of `W` that fixes every point outside a compact set `K`. Transplanting
`Λ` along each `G_t` gives a diffeomorphism `Λ_t` of `M`: it acts on `G_t w` as `G_t (Λ w)`, and
fixes every point outside `G_t '' K`. The family `Λ_t` is smooth in `t`, so
`Φ_t = Λ_t ∘ Λ₀⁻¹` is a diffeotopy of `M`
(`TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend`).

If moreover each `G_t` pulls a form `σ` on `M` back to a form `τ` on `W`, and `Λ` preserves `τ`,
then `Λ₀` and every `Φ_t` preserve `σ`
(`TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend_of_isSymplectic`).

A diffeotopy of `N` also extends along one smooth open embedding `χ : N → M` when the points it
moves map into a closed subset of `range χ`, which need not be compact
(`TauCeti.Diffeotopy.exists_extend`). For a diffeotopy `h` of `S × N` that moves only points
over a compact `C ⊆ N`, extending along `id × φ` gives the diffeotopy
`TauCeti.extendDiffeotopyAlong` of `S × M`: it reads `h` through `φ` and fixes every point
`(q, y)` with `y ∉ φ '' C`. The parameter space `S` need not be compact.

## Main results

* `TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend`: a diffeomorphism `Λ₀` of `M` and a
  diffeotopy `Φ` of `M` with `Φ_t (Λ₀ (G_t w)) = G_t (Λ w)`, where `Λ₀` transplants `Λ` along
  `G_0` and `Φ` fixes every point outside the image of `univ ×ˢ K` under `G`.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_timeSlice_comp_eq_extend`: the same, with the
  transplant `Φ_t ∘ Λ₀` of `Λ` along `G_t` fixing every point outside `G_t '' K` for each `t`.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend_of_isSymplectic`: for a symplectic
  isotopy `G` and a diffeomorphism `Λ` preserving the form on `W`, `Λ₀` and every `Φ_t` preserve
  the form on `M`.
* `TauCeti.Diffeotopy.exists_extend`: a diffeotopy of `N` that fixes every `z` with `χ z` outside
  a closed `C ⊆ range χ` extends along `χ` to a diffeotopy of `M` fixing every point outside `C`.
* `TauCeti.extendDiffeotopyAlong`: the extension along `id × φ` of a diffeotopy of `S × N` that
  moves only points over a compact subset of `N`, with
  `TauCeti.extendDiffeotopyAlong_apply_prodMk`, `TauCeti.extendDiffeotopyAlong_apply_of_notMem`
  and `TauCeti.fst_extendDiffeotopyAlong_apply`.

## Implementation notes

The map `χ (t, w) = (t, G_t w)` is a local diffeomorphism of the cylinders
`unitInterval × W → unitInterval × M`, also at the end times
(`ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`), and it is injective since every slice of
`G` is an embedding, so it is an open embedding. Tau Ceti's
`IsLocalDiffeomorph.exists_diffeomorph_extend_of_isCompact` extends the diffeomorphism
`(t, w) ↦ (t, Λ w)` of `unitInterval × W` along `χ` to a diffeomorphism `Ψ` of
`unitInterval × M` that fixes every point outside `χ '' (univ ×ˢ K)`, and `Ψ` preserves the time
coordinate. Then `Λ₀` is the time-zero slice of `Ψ` (`Diffeomorph.slice`), and `Φ` is
`TauCeti.Diffeotopy.ofFstEq Ψ`, whose total diffeomorphism is `Ψ ∘ (id × Λ₀⁻¹)`. This adapts the
proof of Tau Ceti's `TauCeti.Diffeotopy.exists_extend_of_isCompact`, which moves a diffeotopy
along one fixed embedding, to an embedding that moves with time.

That `Φ_t ∘ Λ₀` preserves `σ` follows from the lemma on transplants along the local diffeomorphism
`G_t` (`TauCeti.SmoothForm.mem_diffeomorphStabilizer_of_semiconj`, in
`Pullback/LocalDiffeomorph.lean`, with the closed set
`G_t '' K`); the slice `Φ_t` is then `(Φ_t ∘ Λ₀) ∘ Λ₀⁻¹`.

The proof of `TauCeti.Diffeotopy.exists_extend` is that of Tau Ceti's
`TauCeti.Diffeotopy.exists_extend_of_isCompact`, with the closed set `univ ×ˢ C` in place of the
image of a compact set, so that it calls `IsLocalDiffeomorph.exists_diffeomorph_extend` rather
than its compact form.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for
  diffeotopies with compact support.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I' : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'}
  {W : Type*} [TopologicalSpace W] [ChartedSpace H W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold I' ∞ W] [BoundarylessManifold I' W] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- Let `G` be a smooth isotopy from `g₀` to `g₁` of maps `W → M` whose slices are local
diffeomorphisms, and `Λ` a diffeomorphism of `W` fixing every point outside a compact set `K`.
Then there are a diffeomorphism `Λ₀` of `M` and a diffeotopy `Φ` of `M` such that
`Φ_t (Λ₀ (G_t w)) = G_t (Λ w)` for all `t` and `w`, `Φ` fixes at all times every point outside
the image of `univ ×ˢ K` under `G`, and, for each `t`, `Φ_t ∘ Λ₀` fixes every point outside
`G_t '' K`. -/
theorem exists_diffeotopy_timeSlice_comp_eq_extend [T2Space M] {g₀ g₁ : C^∞⟮I', W; I, M⟯}
    (G : SmoothIsotopy g₀ g₁) (hGd : ∀ t, IsLocalDiffeomorph I' I ∞ (fun w ↦ G (t, w)))
    (Λ : W ≃ₘ⟮I', I'⟯ W) {K : Set W} (hK : IsCompact K) (hΛ : ∀ w ∉ K, Λ w = w) :
    ∃ (Λ₀ : M ≃ₘ⟮I, I⟯ M) (Φ : Diffeotopy I ∞ M),
      (∀ t w, Φ.timeSlice t (Λ₀ (G (t, w))) = G (t, Λ w)) ∧
      (∀ t x, x ∉ (fun p ↦ G p) '' (univ ×ˢ K) → Φ (t, x) = x) ∧
      ∀ t, ∀ x ∉ (fun w ↦ G (t, w)) '' K, Φ.timeSlice t (Λ₀ x) = x := by
  let χ : unitInterval × W → unitInterval × M := fun p ↦ (p.1, G p)
  have hχ : IsLocalDiffeomorph ((𝓡∂ 1).prod I') ((𝓡∂ 1).prod I) ∞ χ :=
    G.contMDiff.isLocalDiffeomorph_prodMk_unitInterval hGd
  have hχo : IsOpenEmbedding χ := by
    refine .of_continuous_injective_isOpenMap hχ.isLocalHomeomorph.continuous
      (fun ⟨s, v⟩ ⟨t, w⟩ h ↦ ?_) hχ.isOpenMap
    simp only [χ, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [(G.isSmoothEmbedding s).isEmbedding.injective h]
  have hχK (t : unitInterval) (x : M) : (t, x) ∈ χ '' (univ ×ˢ K) ↔ ∃ w ∈ K, G (t, w) = x := by
    simp only [χ, mem_image, mem_prod, mem_univ, true_and, Prod.mk.injEq]
    exact ⟨fun ⟨p, hp, h₁, h₂⟩ ↦ ⟨p.2, hp, h₁ ▸ h₂⟩, fun ⟨w, hw, h⟩ ↦ ⟨(t, w), hw, rfl, h⟩⟩
  obtain ⟨Ψ, hΨχ, hΨK⟩ := hχ.exists_diffeomorph_extend_of_isCompact hχo
    ((Diffeomorph.refl (𝓡∂ 1) unitInterval ∞).prodCongr Λ) (isCompact_univ.prod hK) fun p hp ↦ by
      rw [Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl]
      exact Prod.ext rfl (hΛ p.2 fun h ↦ hp ⟨mem_univ _, h⟩)
  have hΨχ' (t : unitInterval) (w : W) : Ψ (t, G (t, w)) = (t, G (t, Λ w)) := by
    simpa [χ, Diffeomorph.coe_prodCongr] using hΨχ (t, w)
  -- `Ψ` is the identity off `χ '' (univ ×ˢ K)` and agrees with `χ ∘ (id × Λ) ∘ χ⁻¹` on it, so it
  -- preserves the time coordinate.
  have hΨ (p : unitInterval × M) : (Ψ p).1 = p.1 := by
    by_cases hp : p ∈ χ '' (univ ×ˢ K)
    · obtain ⟨⟨t, w⟩, -, rfl⟩ := hp
      rw [hΨχ']
    · rw [hΨK p hp]
  have hfix (t : unitInterval) (x : M) (hx : ∀ w ∈ K, G (t, w) ≠ x) : Ψ (t, x) = (t, x) :=
    hΨK _ fun h ↦ by obtain ⟨w, hw, h⟩ := (hχK t x).1 h; exact hx w hw h
  let Λ₀ := Ψ.slice hΨ 0
  have hΛ₀ (x : M) : Λ₀ x = (Ψ (0, x)).2 := Ψ.slice_apply hΨ 0 x
  have hΛ₀K (x : M) (hx : x ∉ g₀ '' K) : Λ₀ x = x := by
    rw [hΛ₀, hfix 0 x fun w hw h ↦ hx ⟨w, hw, by rw [← h, apply_zero]⟩]
  let Φ : Diffeotopy I ∞ M := Diffeotopy.ofFstEq Ψ hΨ
  have hΦ (t : unitInterval) (x : M) : Φ (t, x) = (Ψ (t, Λ₀.symm x)).2 := by
    rw [Diffeotopy.ofFstEq_apply, Diffeomorph.slice_apply]
  refine ⟨Λ₀, Φ, fun t w ↦ ?_, fun t x hx ↦ ?_, fun t x hx ↦ ?_⟩
  · rw [Diffeotopy.timeSlice_apply, hΦ, Λ₀.symm_apply_apply, hΨχ']
  · have hx₀ : x ∉ g₀ '' K := fun ⟨w, hw, h⟩ ↦
      hx ⟨(0, w), ⟨mem_univ _, hw⟩, by rw [← h]; exact G.apply_zero w⟩
    have hsymm : Λ₀.symm x = x := by
      conv_lhs => rw [← hΛ₀K x hx₀]
      exact Λ₀.symm_apply_apply x
    rw [hΦ, hsymm, hfix t x fun w hw h ↦ hx ⟨(t, w), ⟨mem_univ _, hw⟩, h⟩]
  · rw [Diffeotopy.timeSlice_apply, hΦ, Λ₀.symm_apply_apply,
      hfix t x fun w hw h ↦ hx ⟨w, hw, h⟩]

/-- Let `G` be a smooth isotopy from `g₀` to `g₁` of maps `W → M` whose slices are local
diffeomorphisms, and `Λ` a diffeomorphism of `W` fixing every point outside a compact set `K`.
Then there are a diffeomorphism `Λ₀` of `M` and a diffeotopy `Φ` of `M` such that
`Φ_t (Λ₀ (G_t w)) = G_t (Λ w)` for all `t` and `w`, `Φ` fixes at all times every point outside
the image of `univ ×ˢ K` under `G`, `Λ₀ ∘ g₀ = g₀ ∘ Λ`, and `Λ₀` fixes every point outside
`g₀ '' K`. -/
theorem exists_diffeotopy_comp_eq_extend [T2Space M] {g₀ g₁ : C^∞⟮I', W; I, M⟯}
    (G : SmoothIsotopy g₀ g₁) (hGd : ∀ t, IsLocalDiffeomorph I' I ∞ (fun w ↦ G (t, w)))
    (Λ : W ≃ₘ⟮I', I'⟯ W) {K : Set W} (hK : IsCompact K) (hΛ : ∀ w ∉ K, Λ w = w) :
    ∃ (Λ₀ : M ≃ₘ⟮I, I⟯ M) (Φ : Diffeotopy I ∞ M),
      (∀ t w, Φ.timeSlice t (Λ₀ (G (t, w))) = G (t, Λ w)) ∧
      (∀ t x, x ∉ (fun p ↦ G p) '' (univ ×ˢ K) → Φ (t, x) = x) ∧
      (∀ w, Λ₀ (g₀ w) = g₀ (Λ w)) ∧ ∀ x ∉ g₀ '' K, Λ₀ x = x := by
  obtain ⟨Λ₀, Φ, h₁, h₂, h₃⟩ := G.exists_diffeotopy_timeSlice_comp_eq_extend hGd Λ hK hΛ
  refine ⟨Λ₀, Φ, h₁, h₂, fun w ↦ ?_, fun x hx ↦ ?_⟩
  · simpa [Φ.timeSlice_zero] using h₁ 0 w
  · simpa [Φ.timeSlice_zero] using h₃ 0 x (by simpa using hx)

/-- **Moving a symplectomorphism along a symplectic family of embeddings.** Let `G` be a smooth
isotopy from `g₀` to `g₁` of maps `W → M` whose slices are local diffeomorphisms pulling `σ` back
to `τ`, and `Λ` a diffeomorphism of `W` preserving `τ` and fixing every point outside a compact
set `K`. Then there are a diffeomorphism `Λ₀` of `M` and a diffeotopy `Φ` of `M` as in
`TauCeti.SmoothIsotopy.exists_diffeotopy_comp_eq_extend`, such that `Φ_t ∘ Λ₀` fixes every point
outside `G_t '' K` for each `t`, and moreover `Λ₀` and every slice `Φ_t` preserve `σ`. -/
theorem exists_diffeotopy_comp_eq_extend_of_isSymplectic [T2Space M] {g₀ g₁ : C^∞⟮I', W; I, M⟯}
    (G : SmoothIsotopy g₀ g₁) (hGd : ∀ t, IsLocalDiffeomorph I' I ∞ (fun w ↦ G (t, w)))
    {τ : SmoothTwoForm I' W} {σ : SmoothTwoForm I M} (hG : G.IsSymplectic τ σ)
    (Λ : W ≃ₘ⟮I', I'⟯ W) (hΛτ : Λ ∈ SmoothForm.diffeomorphStabilizer τ) {K : Set W}
    (hK : IsCompact K) (hΛ : ∀ w ∉ K, Λ w = w) :
    ∃ (Λ₀ : M ≃ₘ⟮I, I⟯ M) (Φ : Diffeotopy I ∞ M),
      (∀ t w, Φ.timeSlice t (Λ₀ (G (t, w))) = G (t, Λ w)) ∧
      (∀ t x, x ∉ (fun p ↦ G p) '' (univ ×ˢ K) → Φ (t, x) = x) ∧
      (∀ w, Λ₀ (g₀ w) = g₀ (Λ w)) ∧ (∀ x ∉ g₀ '' K, Λ₀ x = x) ∧
      Λ₀ ∈ SmoothForm.diffeomorphStabilizer σ ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      ∀ t, ∀ x ∉ (fun w ↦ G (t, w)) '' K, Φ.timeSlice t (Λ₀ x) = x := by
  obtain ⟨Λ₀, Φ, h₁, h₂, h₃⟩ := G.exists_diffeotopy_timeSlice_comp_eq_extend hGd Λ hK hΛ
  -- `Φ_t * Λ₀ = Φ_t ∘ Λ₀` is the transplant of `Λ` along `G_t`, so it preserves `σ`.
  have hΛt (t : unitInterval) :
      Φ.timeSlice t * Λ₀ ∈ SmoothForm.diffeomorphStabilizer σ :=
    SmoothForm.mem_diffeomorphStabilizer_of_semiconj (hGd t)
      (by rw [← Subtype.coe_inj, SmoothForm.coe_mpullback, isSymplectic_def.1 hG t]) hΛτ
      (fun w ↦ by rw [Diffeomorph.mul_def, Diffeomorph.coe_trans, Function.comp_apply, h₁])
      (hK.image (hGd t).contMDiff.continuous).isClosed (image_subset_range _ _)
      fun x hx ↦ by
        rw [Diffeomorph.mul_def, Diffeomorph.coe_trans, Function.comp_apply, h₃ t x hx]
  have hΛ₀ : Λ₀ ∈ SmoothForm.diffeomorphStabilizer σ := by
    simpa [Φ.timeSlice_zero] using hΛt 0
  refine ⟨Λ₀, Φ, h₁, h₂, fun w ↦ ?_, fun x hx ↦ ?_, hΛ₀, fun t ↦ ?_, h₃⟩
  · simpa [Φ.timeSlice_zero] using h₁ 0 w
  · simpa [Φ.timeSlice_zero] using h₃ 0 x (by simpa using hx)
  · exact (Subgroup.mul_mem_cancel_right _ hΛ₀).1 (hΛt t)

end TauCeti.SmoothIsotopy

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] {n : ℕ∞ω}

/-- A diffeotopy `Λ` of `N` extends along a smooth open embedding `χ : N → M` by the identity if,
at all times, it fixes every point `z` with `χ z` outside a closed set `C ⊆ range χ`. The
extension moves `χ z` as `Λ` moves `z`, and fixes every point outside `C` at all times. -/
theorem Diffeotopy.exists_extend {χ : N → M} (hχ : IsLocalDiffeomorph J J' n χ)
    (hχo : IsOpenEmbedding χ) (Λ : Diffeotopy J n N) {C : Set M} (hC : IsClosed C)
    (hCχ : C ⊆ range χ) (hΛ : ∀ t z, χ z ∉ C → Λ (t, z) = z) :
    ∃ Φ : Diffeotopy J' n M, (∀ t z, Φ (t, χ z) = χ (Λ (t, z))) ∧
      ∀ t, ∀ y ∉ C, Φ (t, y) = y := by
  let χ' : unitInterval × N → unitInterval × M := Prod.map id χ
  have hχ' : IsLocalDiffeomorph ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J') n χ' :=
    (Diffeomorph.refl (𝓡∂ 1) unitInterval n).isLocalDiffeomorph.prodMap hχ
  have hC' : univ ×ˢ C ⊆ range χ' := by
    rintro ⟨t, y⟩ ⟨-, hy⟩
    obtain ⟨z, rfl⟩ := hCχ hy
    exact ⟨(t, z), rfl⟩
  obtain ⟨Ψ, hΨχ, hΨC⟩ := hχ'.exists_diffeomorph_extend (IsOpenEmbedding.id.prodMap hχo)
    Λ.toDiffeomorph (isClosed_univ.prod hC) hC' fun z hz ↦ by
      rw [Diffeotopy.toDiffeomorph_apply, hΛ z.1 z.2 fun h ↦ hz ⟨mem_univ _, h⟩]
  -- Off `univ ×ˢ C` the extension is the identity; on it, it is the motion read through `χ'`.
  have hΨ (p : unitInterval × M) :
      Ψ p = p ∨ ∃ z : unitInterval × N, p = χ' z ∧ Ψ p = χ' (Λ.toDiffeomorph z) := by
    by_cases hp : p ∈ univ ×ˢ C
    · obtain ⟨z, rfl⟩ := hC' hp
      exact .inr ⟨z, rfl, hΨχ z⟩
    · exact .inl (hΨC p hp)
  refine ⟨⟨Ψ, fun p ↦ ?_, fun x ↦ ?_⟩, fun t z ↦ ?_, fun t y hy ↦ ?_⟩
  · rcases hΨ p with h | ⟨z, rfl, h⟩
    · rw [h]
    · simp [h, χ']
  · rcases hΨ (0, x) with h | ⟨⟨t, w⟩, hz, h⟩
    · rw [h]
    · simp only [χ', Prod.map, id, Prod.mk.injEq] at hz
      obtain ⟨rfl, rfl⟩ := hz
      simp [h, χ']
  · rw [Diffeotopy.coe_apply, Diffeotopy.coe_apply]
    exact congrArg Prod.snd (hΨχ (t, z))
  · rw [Diffeotopy.coe_apply]
    exact congrArg Prod.snd (hΨC (t, y) fun h ↦ hy h.2)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {I : ModelWithCorners ℝ F G}
  {S : Type*} [TopologicalSpace S] [ChartedSpace G S]
  [T2Space M] {φ : N → M} (hφ : IsLocalDiffeomorph J J' n φ) (hφo : IsOpenEmbedding φ)
  (h : Diffeotopy (I.prod J) n (S × N)) {C : Set N} (hC : IsCompact C)
  (hh : ∀ t p, p.2 ∉ C → h (t, p) = p)
include hφ hφo hC hh

/-- The diffeotopy that `extendDiffeotopyAlong` chooses. -/
private theorem exists_extendDiffeotopyAlong :
    ∃ Φ : Diffeotopy (I.prod J') n (S × M),
      (∀ t p, Φ (t, Prod.map id φ p) = Prod.map id φ (h (t, p))) ∧
      ∀ t, ∀ p ∉ univ ×ˢ (φ '' C), Φ (t, p) = p :=
  Diffeotopy.exists_extend ((Diffeomorph.refl I S n).isLocalDiffeomorph.prodMap hφ)
    (IsOpenEmbedding.id.prodMap hφo) h (isClosed_univ.prod (hC.image hφo.continuous).isClosed)
    (fun _ ⟨_, ⟨z, _, hz⟩⟩ ↦ ⟨(_, z), Prod.ext rfl hz⟩)
    fun t p hp ↦ hh t p fun hpC ↦ hp ⟨mem_univ _, p.2, hpC, rfl⟩

/-- The extension of a family of diffeotopies along a smooth open embedding. Let `φ : N → M` be
a smooth open embedding into a Hausdorff manifold, and `h` a diffeotopy of `S × N` that fixes
at all times every point `(q, z)` with `z` outside a compact set `C`. Then
`extendDiffeotopyAlong hφ hφo h hC hh` is a diffeotopy of `S × M` that moves `(q, φ z)` as `h`
moves `(q, z)` (`extendDiffeotopyAlong_apply_prodMk`) and fixes every `(q, y)` with
`y ∉ φ '' C` (`extendDiffeotopyAlong_apply_of_notMem`). If `h` keeps the parameter `q`, so does
the extension (`fst_extendDiffeotopyAlong_apply`): then at the parameter `q` and time `t` it is
`φ ∘ h_(q,t) ∘ φ⁻¹` on the range of `φ` and the identity elsewhere. -/
def extendDiffeotopyAlong : Diffeotopy (I.prod J') n (S × M) :=
  (exists_extendDiffeotopyAlong hφ hφo h hC hh).choose

/-- The extension of `h` along `φ` moves `(q, φ z)` as `h` moves `(q, z)`. -/
@[simp]
theorem extendDiffeotopyAlong_apply_prodMk (t : unitInterval) (q : S) (z : N) :
    extendDiffeotopyAlong hφ hφo h hC hh (t, (q, φ z)) =
      ((h (t, (q, z))).1, φ (h (t, (q, z))).2) :=
  (exists_extendDiffeotopyAlong hφ hφo h hC hh).choose_spec.1 t (q, z)

/-- The extension of `h` along `φ` fixes at all times every `(q, y)` with `y ∉ φ '' C`. -/
theorem extendDiffeotopyAlong_apply_of_notMem (t : unitInterval) (q : S) {y : M}
    (hy : y ∉ φ '' C) : extendDiffeotopyAlong hφ hφo h hC hh (t, (q, y)) = (q, y) :=
  (exists_extendDiffeotopyAlong hφ hφo h hC hh).choose_spec.2 t (q, y) fun h ↦ hy h.2

/-- If `h` keeps the parameter, so does its extension along `φ`. -/
theorem fst_extendDiffeotopyAlong_apply (hfst : ∀ t p, (h (t, p)).1 = p.1) (t : unitInterval)
    (p : S × M) : (extendDiffeotopyAlong hφ hφo h hC hh (t, p)).1 = p.1 := by
  obtain ⟨q, y⟩ := p
  by_cases hy : y ∈ φ '' C
  · obtain ⟨z, -, rfl⟩ := hy
    rw [extendDiffeotopyAlong_apply_prodMk, hfst]
  · rw [extendDiffeotopyAlong_apply_of_notMem hφ hφo h hC hh t q hy]

end TauCeti

end
