/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneConvergence
import SymplecticGeometry.Logic.Equiv.PartialEquiv

/-!
# The map `univBall` onto a ball, and on the real line

Mathlib's `OpenPartialHomeomorph.univBall c r` maps a real normed space `E` onto the ball
`ball c r` if `0 < r`, and is the translation by `c` if `r ≤ 0`. This file gives its range and its
formula in the second case (Tau Ceti's `OpenPartialHomeomorph.univBall_apply` gives the first),
and, on the real line, its order and its limits: there it is a strictly increasing map of `ℝ`
onto the open interval `(c - r, c + r)` when `0 < r`.

As a consequence, a map `g` from `ℝ` to a topological space, continuous on `[c - r, c + r]`,
precomposed with `univBall c r`, runs through `g` on `(c - r, c + r)` and tends to `g (c - r)` at
`-∞`; the closure of the image of each half-line `Iic T` is that image together with
`g (c - r)`, and if `g` is injective on `[c - r, c + r]` it never takes the value `g (c - r)`.

## Main results

* `OpenPartialHomeomorph.range_univBall`: the range of `univBall c r` is `ball c r`, for `0 < r`.
* `OpenPartialHomeomorph.univBall_apply_of_nonpos`,
  `OpenPartialHomeomorph.univBall_symm_apply_of_nonpos`: for `r ≤ 0`, `univBall c r` is the
  translation by `c`, and its inverse subtracts `c`.
* `OpenPartialHomeomorph.exists_univBall_zero_apply_eq_smul`,
  `OpenPartialHomeomorph.exists_univBall_zero_symm_apply_eq_smul`: `univBall 0 r` and its
  inverse send each vector to a real multiple of it.
* `OpenPartialHomeomorph.strictMono_univBall_real`, `tendsto_univBall_real_atBot` and
  `image_univBall_real_Iic`: on the real line, `univBall c r` is strictly increasing, and for
  `0 < r` it tends to `c - r` at `-∞` and sends `Iic T` onto `Ioc (c - r) (univBall c r T)`.
* `ContinuousOn.tendsto_comp_univBall_atBot`, `ContinuousOn.closure_image_comp_univBall_Iic` and
  `Set.InjOn.notMem_range_comp_univBall`: the behaviour of `g ∘ univBall c r` at `-∞`.
-/

public section

open Set Metric Filter Topology

namespace OpenPartialHomeomorph

section Range

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- For `0 < r`, Mathlib's map `univBall c r : E → P` has as range the ball `ball c r`. -/
theorem range_univBall (c : P) {r : ℝ} (hr : 0 < r) :
    range (univBall (E := E) c r) = ball c r := by
  rw [← univBall_target c hr, ← coe_toPartialEquiv,
    (univBall c r).toPartialEquiv.range_eq_target_of_source_eq_univ (univBall_source c r)]

/-- For `r ≤ 0`, Mathlib's map `univBall c r : E → P` is the translation by `c`. -/
theorem univBall_apply_of_nonpos (c : P) {r : ℝ} (hr : r ≤ 0) (x : E) :
    univBall c r x = x +ᵥ c := by
  simp [univBall, not_lt.2 hr]

/-- For `r ≤ 0`, the inverse of Mathlib's map `univBall c r : E → P` is the subtraction of `c`. -/
theorem univBall_symm_apply_of_nonpos (c : P) {r : ℝ} (hr : r ≤ 0) (y : P) :
    (univBall (E := E) c r).symm y = y -ᵥ c := by
  simp [univBall, not_lt.2 hr]

/-- Mathlib's map `univBall 0 r` of `E` sends each vector to a real multiple of it. -/
theorem exists_univBall_zero_apply_eq_smul (r : ℝ) (x : E) :
    ∃ a : ℝ, univBall (0 : E) r x = a • x := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨1, by rw [univBall_apply_of_nonpos _ hr, vadd_eq_add, add_zero, one_smul]⟩
  · exact ⟨r / √(1 + ‖x‖ ^ 2), by rw [univBall_apply hr, vadd_eq_add, add_zero]⟩

/-- The inverse of Mathlib's map `univBall 0 r` of `E` sends each vector to a real multiple of
it. -/
theorem exists_univBall_zero_symm_apply_eq_smul (r : ℝ) (y : E) :
    ∃ a : ℝ, (univBall (0 : E) r).symm y = a • y := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨1, by rw [univBall_symm_apply_of_nonpos _ hr, vsub_eq_sub, sub_zero, one_smul]⟩
  · exact ⟨(√(r ^ 2 - dist y 0 ^ 2))⁻¹, by rw [univBall_symm_apply hr, vsub_eq_sub, sub_zero]⟩

end Range

section Real

variable {r : ℝ}

/-- For `0 < r`, Mathlib's map `univBall c r : ℝ → ℝ` has as range the open interval
`(c - r, c + r)`. -/
theorem range_univBall_real (c : ℝ) (hr : 0 < r) :
    range (univBall (E := ℝ) c r) = Ioo (c - r) (c + r) := by
  rw [range_univBall c hr, Real.ball_eq_Ioo]

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` is
`x ↦ c + r * (x / √(1 + x ^ 2))`. -/
theorem univBall_real_apply (c : ℝ) (hr : 0 < r) (x : ℝ) :
    univBall c r x = c + r * (x / √(1 + x ^ 2)) := by
  rw [univBall_apply hr, vadd_eq_add, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  ring

/-- On the real line, Mathlib's map `univBall c r` is strictly increasing. -/
theorem strictMono_univBall_real (c r : ℝ) : StrictMono (univBall c r) := by
  rcases le_or_gt r 0 with hr | hr
  · intro x y h
    simpa [univBall_apply_of_nonpos c hr] using h
  refine ((continuous_univBall c r).strictMono_of_inj
    fun x y h ↦ (univBall c r).injOn (by simp) (by simp) h).resolve_right fun h ↦ ?_
  have h1 := h zero_lt_one
  rw [univBall_real_apply c hr, univBall_real_apply c hr, zero_div, mul_zero, add_zero] at h1
  have : 0 < r * (1 / √(1 + 1 ^ 2)) := by positivity
  linarith

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` tends to the left end `c - r` of
its range at `-∞`. -/
theorem tendsto_univBall_real_atBot (c : ℝ) (hr : 0 < r) :
    Tendsto (univBall c r) atBot (𝓝 (c - r)) := by
  have := tendsto_atBot_ciInf (strictMono_univBall_real c r).monotone
    (range_univBall_real c hr ▸ bddBelow_Ioo)
  rwa [iInf, range_univBall_real c hr, csInf_Ioo (by linarith)] at this

/-- On the real line, for `0 < r`, Mathlib's map `univBall c r` sends the half-line `Iic T` onto
the interval `Ioc (c - r) (univBall c r T)`. -/
theorem image_univBall_real_Iic (c : ℝ) (hr : 0 < r) (T : ℝ) :
    univBall c r '' Iic T = Ioc (c - r) (univBall c r T) := by
  refine Subset.antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨((range_univBall_real c hr).subset (mem_range_self t)).1,
      (strictMono_univBall_real c r).monotone ht⟩
  · obtain ⟨t₀, ht₀T, ht₀⟩ := ((eventually_le_atBot T).and
      ((tendsto_univBall_real_atBot c hr).eventually (eventually_lt_nhds hy.1))).exists
    obtain ⟨t, ht, rfl⟩ := intermediate_value_Icc ht₀T (continuous_univBall c r).continuousOn
      ⟨ht₀.le, hy.2⟩
    exact ⟨t, ht.2, rfl⟩

end Real

end OpenPartialHomeomorph

open OpenPartialHomeomorph

variable {X : Type*} {g : ℝ → X} {c r : ℝ}

/-- For `0 < r`, if `g : ℝ → X` is injective on `[c - r, c + r]`, then `g` precomposed with
Mathlib's map `univBall c r` of `ℝ` onto `(c - r, c + r)` never takes the value `g (c - r)`. -/
theorem Set.InjOn.notMem_range_comp_univBall (hg : InjOn g (Icc (c - r) (c + r))) (hr : 0 < r) :
    g (c - r) ∉ range (g ∘ univBall c r) := by
  rintro ⟨t, ht⟩
  have h := (range_univBall_real c hr).subset (mem_range_self t)
  exact h.1.ne' (hg (Ioo_subset_Icc_self h) (left_mem_Icc.2 (by linarith)) ht)

variable [TopologicalSpace X]

/-- For `0 < r`, a map `g : ℝ → X` continuous on `[c - r, c + r]`, precomposed with Mathlib's map
`univBall c r` of `ℝ` onto `(c - r, c + r)`, tends to `g (c - r)` at `-∞`. -/
theorem ContinuousOn.tendsto_comp_univBall_atBot (hg : ContinuousOn g (Icc (c - r) (c + r)))
    (hr : 0 < r) : Tendsto (g ∘ univBall c r) atBot (𝓝 (g (c - r))) :=
  (hg _ (left_mem_Icc.2 (by linarith))).tendsto.comp <|
    tendsto_nhdsWithin_iff.2 ⟨tendsto_univBall_real_atBot c hr, .of_forall fun t ↦
      Ioo_subset_Icc_self ((range_univBall_real c hr).subset (mem_range_self t))⟩

/-- For `0 < r`, the closure of the range of a map `g : ℝ → X` continuous on `[c - r, c + r]`,
precomposed with Mathlib's map `univBall c r` of `ℝ` onto `(c - r, c + r)`, lies in
`g '' Icc (c - r) (c + r)`. -/
theorem ContinuousOn.closure_range_comp_univBall_subset [T2Space X]
    (hg : ContinuousOn g (Icc (c - r) (c + r))) (hr : 0 < r) :
    closure (range (g ∘ univBall c r)) ⊆ g '' Icc (c - r) (c + r) := by
  refine closure_minimal ?_ (isCompact_Icc.image_of_continuousOn hg).isClosed
  rw [range_comp, range_univBall_real c hr]
  exact image_mono Ioo_subset_Icc_self

/-- For `0 < r`, let `g : ℝ → X` be continuous on `[c - r, c + r]`, and precompose it with
Mathlib's map `univBall c r` of `ℝ` onto `(c - r, c + r)`. The closure of the image of each
half-line `Iic T` is that image together with `g (c - r)`. -/
theorem ContinuousOn.closure_image_comp_univBall_Iic [T2Space X]
    (hg : ContinuousOn g (Icc (c - r) (c + r))) (hr : 0 < r) (T : ℝ) :
    closure ((g ∘ univBall c r) '' Iic T) = insert (g (c - r)) ((g ∘ univBall c r) '' Iic T) := by
  have hT := (range_univBall_real c hr).subset (mem_range_self T)
  refine (closure_minimal (subset_insert _ _) ?_).antisymm
    (insert_subset (mem_closure_of_tendsto (hg.tendsto_comp_univBall_atBot hr)
      ((eventually_le_atBot T).mono fun t ht ↦ mem_image_of_mem _ ht)) subset_closure)
  rw [image_comp, image_univBall_real_Iic c hr, ← image_insert_eq, insert_left_Ioc hT.1.le]
  exact (isCompact_Icc.image_of_continuousOn (hg.mono (Icc_subset_Icc le_rfl hT.2.le))).isClosed

end
