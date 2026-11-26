/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.SmoothApprox.Basic

/-!
# Smooth null-homotopies of smooth loops

Let `M` be a simply connected Hausdorff manifold without boundary, modelled on a
finite-dimensional real space, and let `c : I → M` be a `C^n` loop based at `p₀`. Then `c` is the
bottom edge of a `C^n` map `H : I × I → M` that is constant equal to `p₀` on the three other edges
of the square. If moreover `c` is constant equal to `p₀` outside an interval `(a, b)`, then `H`
can be chosen constant equal to `p₀` on `{t ∉ (a, b)} × I`.

The proof builds a continuous null-homotopy that is already `C^n` near the closed set where `H` is
prescribed, and smooths it relative to that set by Tau Ceti's relative Whitney approximation
theorem `ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`, as in
`ContMDiffOn.exists_contMDiffOn_ball_eq_of_nullhomotopic` (`ContMDiff/ExtendOverDisc.lean`). Let
`ρ : I → I` be a `C^n` map onto `[a, b]` that equals `a` near `a` and `b` near `b`. On the lower
half of the square, the map is the `C^n` homotopy `(t, s) ↦ c ((1 - β s) t + β s ρ t)`, for a
smooth cutoff `β` that vanishes at `0` and equals `1` from `1 / 4` on (Tau Ceti's
`ContMDiff.convexComb`); it runs from `c` to `c ∘ ρ`. On the upper half, it is a continuous
homotopy, rel endpoints, from the loop `c` on `[a, b]` to the constant path (Mathlib's
`SimplyConnectedSpace.paths_homotopic`), reparametrized like `ρ` in space and by a cutoff in
time, so that it is constant near the edges of the square other than the bottom one.

This construction is adapted from Tau Ceti's proof of `TauCeti.exists_contMDiff_periodic_homotopic`
(`TauCeti/Geometry/Manifold/SmoothApprox/PeriodicLoop.lean`): there too the loop is precomposed
near an edge with a ramped interpolation between the identity and a collared step, the continuous
homotopy is precomposed with `TauCeti.collaredSmoothTransitionUnit` in the loop direction, the
pieces are glued into a map which, on some open set, agrees with a smooth piece or is constant,
and that map is smoothed relative to this set.

## Main results

* `ContMDiff.exists_contMDiff_nullhomotopy`: a `C^n` loop in a simply connected manifold bounds a
  `C^n` map on the square, constant on the three other edges.
* `ContMDiff.exists_contMDiff_nullhomotopy_of_notMem_Ioo`: the same, constant on
  `{t ∉ (a, b)} × I` when the loop is constant outside `(a, b)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (the relative Whitney approximation theorem).
-/

public section

open Set Topology
open scoped Manifold ContDiff unitInterval

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]

/-- The `C^n` homotopy `(t, s) ↦ c ((1 - β s) t + β s ρ t)`, for `ρ t = (1 - θ t) a + θ t b` and
a smooth cutoff `β` with `β 0 = 0`, from `c` to `c ∘ ρ`, which it reaches at `s = 1 / 4`. It
is constant equal to `p₀` where `t ≤ a` or `b ≤ t`, if `c` is constant equal to `p₀` outside
`(a, b)` and `θ` is `0` up to `a` and `1` from `b` on. -/
private theorem exists_contMDiff_homotopy_reparam {n : ℕ∞} {c : I → M}
    (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} {a b : I}
    (hcp : ∀ t : I, (t : ℝ) ∉ Ioo (a : ℝ) b → c t = p₀) {θ : I → I}
    (hθ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n θ) (hθa : ∀ t : I, (t : ℝ) ≤ a → θ t = 0)
    (hθb : ∀ t : I, (b : ℝ) ≤ t → θ t = 1) :
    ∃ G : I × I → M, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n G ∧ (∀ t, G (t, 0) = c t) ∧
      (∀ x : I × I, (x.1 : ℝ) ≤ a ∨ (b : ℝ) ≤ x.1 → G x = p₀) ∧
      ∀ x : I × I, 1 / 4 ≤ (x.2 : ℝ) → G x = c (Set.Icc.convexComb a b (θ x.1)) := by
  let β : I → I := fun s ↦ unitInterval.smoothTransition (4 * s)
  have hβ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n β := by
    convert ((by fun_prop : ContDiff ℝ n fun r : ℝ ↦ 4 * r).comp_contMDiff
      contMDiff_subtypeVal_Icc).smoothTransition (WithTop.coe_le_coe.2 le_top) using 2
    exact Subtype.ext (unitInterval.coe_smoothTransition _)
  have hβ0 : β 0 = 0 := unitInterval.smoothTransition_of_nonpos (by simp)
  have hβ1 {s : I} (hs : 1 / 4 ≤ (s : ℝ)) : β s = 1 :=
    unitInterval.smoothTransition_of_one_le (by linarith)
  refine ⟨fun x ↦ c (Set.Icc.convexComb x.1 (Set.Icc.convexComb a b (θ x.1)) (β x.2)),
    hc.comp (contMDiff_fst.convexComb ((contMDiff_const.convexComb contMDiff_const hθ).comp
      contMDiff_fst) (hβ.comp contMDiff_snd)),
    fun t ↦ by simp only [hβ0, Set.Icc.convexComb_zero], fun x hx ↦ hcp _ ?_,
    fun x hx ↦ by simp only [hβ1 hx, Set.Icc.convexComb_one]⟩
  -- the point `(1 - β s) t + β s ρ t` lies between `t` and `ρ t`, which is `a` for `t ≤ a` and
  -- `b` for `b ≤ t`
  rintro ⟨h₁, h₂⟩
  have h₃ := (β x.2).property.1
  have h₄ := (β x.2).property.2
  rcases hx with h | h
  · rw [hθa _ h, Set.Icc.convexComb_zero, Set.Icc.coe_convexComb] at h₁
    nlinarith
  · rw [hθb _ h, Set.Icc.convexComb_one, Set.Icc.coe_convexComb] at h₂
    nlinarith

/-- A continuous null-homotopy of `c`, constant equal to `p₀` on `{t ∉ (a, b)} × I`, that is `C^n`
on an open neighbourhood of the closed set where the null-homotopy of
`ContMDiff.exists_contMDiff_nullhomotopy_of_notMem_Ioo` is prescribed. -/
private theorem exists_continuous_nullhomotopy [SimplyConnectedSpace M] {n : ℕ∞} {c : I → M}
    (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hcp : ∀ t : I, (t : ℝ) ∉ Ioo a b → c t = p₀) :
    ∃ F : C(I × I, M), ∃ V : Set (I × I), IsOpen V ∧
      {x | x.2 = 0 ∨ x.2 = 1 ∨ (x.1 : ℝ) ≤ a ∨ b ≤ x.1} ⊆ V ∧
      ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 1)) J n F V ∧ (∀ t, F (t, 0) = c t) ∧
      (∀ t, F (t, 1) = p₀) ∧ ∀ x : I × I, (x.1 : ℝ) ≤ a ∨ b ≤ x.1 → F x = p₀ := by
  set a' : I := ⟨a, ha, hab.le.trans hb⟩
  set b' : I := ⟨b, ha.trans hab.le, hb⟩
  have ha' : c a' = p₀ := hcp a' fun h ↦ lt_irrefl a h.1
  have hb' : c b' = p₀ := hcp b' fun h ↦ lt_irrefl b h.2
  have hba : 0 < b - a := sub_pos.2 hab
  -- a `C^n` step `θ`, equal to `0` near `a` and to `1` near `b`
  set θ : I → I := fun t ↦ TauCeti.collaredSmoothTransitionUnit (((t : ℝ) - a) / (b - a))
  have hθ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n θ :=
    (TauCeti.contMDiff_collaredSmoothTransitionUnit (WithTop.coe_le_coe.2 le_top)).comp
      ((by fun_prop : ContDiff ℝ n fun r : ℝ ↦ (r - a) / (b - a)).comp_contMDiff
        contMDiff_subtypeVal_Icc)
  have hθ₀ (t : I) (ht : (t : ℝ) ≤ a + (b - a) / 4) : θ t = 0 :=
    TauCeti.collaredSmoothTransitionUnit_eq_zero_of_le (by rw [div_le_iff₀ hba]; linarith)
  have hθ₁ (t : I) (ht : b - (b - a) / 4 ≤ (t : ℝ)) : θ t = 1 :=
    TauCeti.collaredSmoothTransitionUnit_eq_one_of_ge (by rw [le_div_iff₀ hba]; linarith)
  obtain ⟨G, hG, hG₀, hGp, hGθ⟩ := exists_contMDiff_homotopy_reparam hc (a := a') (b := b') hcp
    hθ (fun t ht ↦ hθ₀ t (by simp only [a'] at ht; linarith))
    (fun t ht ↦ hθ₁ t (by simp only [b'] at ht; linarith))
  -- a continuous null-homotopy `L`, rel endpoints, of the loop `c` restricted to `[a, b]`
  let γ : Path p₀ p₀ :=
    { toFun := fun u ↦ c (Set.Icc.convexComb a' b' u)
      continuous_toFun := hc.continuous.comp (Set.Icc.continuous_convexComb _ _)
      source' := by simp only [Set.Icc.convexComb_zero, ha']
      target' := by simp only [Set.Icc.convexComb_one, hb'] }
  obtain ⟨L⟩ := SimplyConnectedSpace.paths_homotopic γ (Path.refl p₀)
  -- `L` run at speed `κ s = smoothTransition (4 s - 2)`, along the loop `c` reparametrized by `θ`
  let K : I × I → M := fun x ↦ L (unitInterval.smoothTransition (4 * x.2 - 2), θ x.1)
  have hK : Continuous K := L.continuous.comp <|
    (unitInterval.continuous_smoothTransition.comp (by fun_prop)).prodMk
      (hθ.continuous.comp continuous_fst)
  have hKθ (x : I × I) (h : (x.2 : ℝ) ≤ 1 / 2) : K x = c (Set.Icc.convexComb a' b' (θ x.1)) := by
    simp only [K, unitInterval.smoothTransition_of_nonpos (by linarith : 4 * (x.2 : ℝ) - 2 ≤ 0),
      ContinuousMap.HomotopyWith.apply_zero, Path.coe_toContinuousMap]
    rfl
  have hKp {x : I × I}
      (h : (x.1 : ℝ) < a + (b - a) / 4 ∨ b - (b - a) / 4 < x.1 ∨ 3 / 4 < (x.2 : ℝ)) :
      K x = p₀ := by
    rcases h with h | h | h
    · simp only [K, hθ₀ _ h.le, Path.Homotopy.source]
    · simp only [K, hθ₁ _ h.le, Path.Homotopy.target]
    · simp only [K, unitInterval.smoothTransition_of_one_le (by linarith : 1 ≤ 4 * (x.2 : ℝ) - 2),
        ContinuousMap.HomotopyWith.apply_one, Path.coe_toContinuousMap, Path.refl_apply]
  -- `G` on the lower half of the square, `K` on the upper half
  let F₀ : I × I → M := fun x ↦ if (x.2 : ℝ) ≤ 1 / 2 then G x else K x
  have hF₀ : Continuous F₀ := Continuous.if_le hG.continuous hK (by fun_prop) continuous_const
    fun x hx ↦ (hGθ x (by linarith)).trans (hKθ x hx.le).symm
  have hc₁ : Continuous fun x : I × I ↦ (x.1 : ℝ) := by fun_prop
  have hc₂ : Continuous fun x : I × I ↦ (x.2 : ℝ) := by fun_prop
  set V₁ : Set (I × I) := {x | (x.2 : ℝ) < 1 / 2}
  set V₂ : Set (I × I) := {x | 1 / 4 < (x.2 : ℝ) ∧
    ((x.1 : ℝ) < a + (b - a) / 4 ∨ b - (b - a) / 4 < x.1 ∨ 3 / 4 < (x.2 : ℝ))}
  have hV₁ : IsOpen V₁ := isOpen_lt hc₂ continuous_const
  have hV₂ : IsOpen V₂ := (isOpen_lt continuous_const hc₂).inter
    ((isOpen_lt hc₁ continuous_const).union ((isOpen_lt continuous_const hc₁).union
      (isOpen_lt continuous_const hc₂)))
  have hF₀V₁ {x : I × I} (hx : x ∈ V₁) : F₀ x = G x := ite_eq_left hx.le
  have hF₀V₂ {x : I × I} (hx : x ∈ V₂) : F₀ x = p₀ := by
    by_cases h : (x.2 : ℝ) ≤ 1 / 2
    · rw [show F₀ x = G x from ite_eq_left h, hGθ x hx.1.le]
      rcases hx.2 with h' | h' | h'
      · rw [hθ₀ _ h'.le, Set.Icc.convexComb_zero, ha']
      · rw [hθ₁ _ h'.le, Set.Icc.convexComb_one, hb']
      · linarith
    · rw [show F₀ x = K x from ite_eq_right h]; exact hKp hx.2
  refine ⟨⟨F₀, hF₀⟩, V₁ ∪ V₂, hV₁.union hV₂, ?_, ?_, fun t ↦ ?_, fun t ↦ ?_, fun x hx ↦ ?_⟩
  · rintro x (h | h | h | h)
    · left; simp [V₁, h]
    · right; simp [V₂, h]; norm_num
    all_goals
      rcases lt_or_ge (x.2 : ℝ) (1 / 2) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by linarith, by first | (left; linarith) | (right; left; linarith)⟩
  · rintro x (hx | hx)
    · exact ((hG x).congr_of_eventuallyEq (Filter.eventually_of_mem (hV₁.mem_nhds hx)
        fun y hy ↦ hF₀V₁ hy)).contMDiffWithinAt
    · exact ((contMDiffAt_const (c := p₀)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hV₂.mem_nhds hx) fun y hy ↦ hF₀V₂ hy)).contMDiffWithinAt
  · exact (ite_eq_left (by simp)).trans (hG₀ t)
  · exact (ite_eq_right (by norm_num)).trans (hKp (Or.inr (Or.inr (by norm_num))))
  · by_cases h : (x.2 : ℝ) ≤ 1 / 2
    · exact (ite_eq_left h).trans (hGp x hx)
    · exact (ite_eq_right h).trans
        (hKp (hx.imp (fun h ↦ by linarith) fun h ↦ Or.inl (by linarith)))

variable [FiniteDimensional ℝ F] [BoundarylessManifold J M] [IsManifold J ∞ M] [T2Space M]

/-- **Smooth null-homotopy of a smooth loop, constant outside an interval.** Let `M` be a simply
connected Hausdorff manifold without boundary, modelled on a finite-dimensional real space, let
`0 ≤ a < b ≤ 1`, and let `c : I → M` be `C^n` with `c t = p₀` for every `t ∉ (a, b)`. Then some
`C^n` map `H : I × I → M` has `H (t, 0) = c t` and `H (t, 1) = p₀` for every `t`, and
`H (t, s) = p₀` for every `s` and every `t ∉ (a, b)`. -/
theorem ContMDiff.exists_contMDiff_nullhomotopy_of_notMem_Ioo [SimplyConnectedSpace M]
    {n : ℕ∞} {c : I → M} (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (hcp : ∀ t : I, (t : ℝ) ∉ Ioo a b → c t = p₀) :
    ∃ H : I × I → M, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n H ∧ (∀ t, H (t, 0) = c t) ∧
      (∀ t, H (t, 1) = p₀) ∧ ∀ t s : I, (t : ℝ) ∉ Ioo a b → H (t, s) = p₀ := by
  obtain ⟨F, V, hV, hSV, hFV, hF₀, hF₁, hFp⟩ := exists_continuous_nullhomotopy hc ha hab hb hcp
  have hc₁ : Continuous fun x : I × I ↦ (x.1 : ℝ) := by fun_prop
  have hS : IsClosed {x : I × I | x.2 = 0 ∨ x.2 = 1 ∨ (x.1 : ℝ) ≤ a ∨ b ≤ x.1} :=
    (isClosed_eq continuous_snd continuous_const).union
      ((isClosed_eq continuous_snd continuous_const).union
        ((isClosed_le hc₁ continuous_const).union (isClosed_le continuous_const hc₁)))
  -- the relative Whitney approximation, relative to the closed set where `H` is prescribed
  obtain ⟨H, hH, hFH⟩ := F.exists_contMDiff_homotopicRel_of_isCompact_closure_range n
    (isCompact_range F.continuous).closure hS (hV.mem_nhdsSet.2 hSV) hFV
  have hHF {x : I × I} (hx : x.2 = 0 ∨ x.2 = 1 ∨ (x.1 : ℝ) ≤ a ∨ b ≤ x.1) : H x = F x :=
    (hFH.fst_eq_snd hx).symm
  refine ⟨H, hH, fun t ↦ (hHF (Or.inl rfl)).trans (hF₀ t),
    fun t ↦ (hHF (Or.inr (Or.inl rfl))).trans (hF₁ t), fun t s ht ↦ ?_⟩
  have ht' : (t : ℝ) ≤ a ∨ b ≤ t := (not_and_or.1 ht).imp not_lt.1 not_lt.1
  exact (hHF (Or.inr (Or.inr ht'))).trans (hFp (t, s) ht')

/-- **Smooth null-homotopy of a smooth loop.** In a simply connected Hausdorff manifold without
boundary, modelled on a finite-dimensional real space, a `C^n` loop `c : I → M` based at `p₀` is
the bottom edge of a `C^n` map `H : I × I → M` that is constant equal to `p₀` on the three other
edges of the square. -/
theorem ContMDiff.exists_contMDiff_nullhomotopy [SimplyConnectedSpace M] {n : ℕ∞} {c : I → M}
    (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} (hc₀ : c 0 = p₀) (hc₁ : c 1 = p₀) :
    ∃ H : I × I → M, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n H ∧ (∀ t, H (t, 0) = c t) ∧
      (∀ t, H (t, 1) = p₀) ∧ (∀ s, H (0, s) = p₀) ∧ ∀ s, H (1, s) = p₀ := by
  have hcp (t : I) (ht : (t : ℝ) ∉ Ioo 0 1) : c t = p₀ := by
    rcases (not_and_or.1 ht).imp not_lt.1 not_lt.1 with h | h
    · rwa [show t = 0 from Subtype.ext (le_antisymm h t.property.1)]
    · rwa [show t = 1 from Subtype.ext (le_antisymm t.property.2 h)]
  obtain ⟨H, hH, h₀, h₁, hp⟩ :=
    hc.exists_contMDiff_nullhomotopy_of_notMem_Ioo le_rfl zero_lt_one le_rfl hcp
  exact ⟨H, hH, h₀, h₁, fun s ↦ hp 0 s (by simp), fun s ↦ hp 1 s (by simp)⟩

end
