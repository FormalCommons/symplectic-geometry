/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.SmoothApprox.Basic

/-!
# Smooth null-homotopies of smooth loops

test
-/

public section

open Set Topology
open scoped Manifold ContDiff unitInterval

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

theorem ContMDiff.exists_contMDiff_nullhomotopy_of_notMem_Ioo [SimplyConnectedSpace M]
    {n : ℕ∞} {c : I → M} (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) (hcp : ∀ t : I, (t : ℝ) ∉ Ioo a b → c t = p₀) :
    ∃ H : I × I → M, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n H ∧ (∀ t, H (t, 0) = c t) ∧
      (∀ t, H (t, 1) = p₀) ∧ ∀ t s : I, (t : ℝ) ∉ Ioo a b → H (t, s) = p₀ := by
  have hba : 0 < b - a := sub_pos.2 hab
  -- the real functions of the construction
  set τ : ℝ → ℝ := Real.smoothTransition
  set θ : ℝ → ℝ := fun t ↦ τ (2 * (t - a) / (b - a) - 1 / 2) with hθ_def
  set ρ : ℝ → ℝ := fun t ↦ a + (b - a) * θ t with hρ_def
  set β : ℝ → ℝ := fun s ↦ τ (4 * s) with hβ_def
  set φ : ℝ → ℝ → ℝ := fun t s ↦ (1 - β s) * t + β s * ρ t with hφ_def
  set κ : ℝ → ℝ := fun s ↦ τ (4 * s - 2) with hκ_def
  have hτ0 (x : ℝ) : 0 ≤ τ x := Real.smoothTransition.nonneg x
  have hτ1 (x : ℝ) : τ x ≤ 1 := Real.smoothTransition.le_one x
  have hθ₀ {t : ℝ} (ht : t ≤ a + (b - a) / 4) : θ t = 0 := by
    refine Real.smoothTransition.zero_of_nonpos ?_
    have : 2 * (t - a) / (b - a) ≤ 1 / 2 := by
      rw [div_le_iff₀ hba]; linarith
    linarith
  have hθ₁ {t : ℝ} (ht : b - (b - a) / 4 ≤ t) : θ t = 1 := by
    refine Real.smoothTransition.one_of_one_le ?_
    have : 3 / 2 ≤ 2 * (t - a) / (b - a) := by
      rw [le_div_iff₀ hba]; linarith
    linarith
  have hρa {t : ℝ} (ht : t ≤ a + (b - a) / 4) : ρ t = a := by simp [hρ_def, hθ₀ ht]
  have hρb {t : ℝ} (ht : b - (b - a) / 4 ≤ t) : ρ t = b := by simp [hρ_def, hθ₁ ht]
  have hρ₀ (t : ℝ) : a ≤ ρ t := by
    have := mul_nonneg hba.le (hτ0 (2 * (t - a) / (b - a) - 1 / 2)); simp only [hρ_def]; linarith
  have hρ₁ (t : ℝ) : ρ t ≤ b := by
    have := mul_le_mul_of_nonneg_left (hτ1 (2 * (t - a) / (b - a) - 1 / 2)) hba.le
    simp only [hρ_def]; linarith
  have hφI {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : φ t s ∈ Icc (0 : ℝ) 1 := by
    have h1 := hτ0 (4 * s); have h2 := hτ1 (4 * s)
    have h3 := hρ₀ t; have h4 := hρ₁ t
    simp only [hφ_def, hβ_def]
    constructor <;> nlinarith [ht.1, ht.2]
  have hτc : ContDiff ℝ n τ := Real.smoothTransition.contDiff
  have hφc : ContDiff ℝ n fun p : ℝ × ℝ ↦ φ p.1 p.2 := by
    have hβc : ContDiff ℝ n fun p : ℝ × ℝ ↦ β p.2 := hτc.comp (by fun_prop)
    have hθc : ContDiff ℝ n fun p : ℝ × ℝ ↦ θ p.1 := hτc.comp (by fun_prop)
    simp only [hφ_def, hρ_def]
    fun_prop
  have hβ0 : β 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hβ1 {s : ℝ} (hs : 1 / 4 ≤ s) : β s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  have hκ0 {s : ℝ} (hs : s ≤ 1 / 2) : κ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hκ1 {s : ℝ} (hs : 3 / 4 ≤ s) : κ s = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  -- the smooth homotopy from `c` to its reparametrization `c ∘ ρ`
  let g₀ : I × I → I := fun x ↦ ⟨φ x.1 x.2, hφI x.1.2⟩
  let G : I × I → M := fun x ↦ c (g₀ x)
  have hG : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n G := by
    refine hc.comp (contMDiff_iff_comp_subtypeVal_Icc.2 ⟨?_, ?_⟩)
    · exact Continuous.subtype_mk (hφc.continuous.comp (f := fun x : I × I ↦ ((x.1 : ℝ), (x.2 : ℝ)))
        (by fun_prop)) _
    · exact hφc.comp_contMDiff ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  have hGφ (x : I × I) : G x = c ⟨φ x.1 x.2, hφI x.1.2⟩ := rfl
  -- a continuous null-homotopy of the loop `c` restricted to `[a, b]`
  have hmem (u : I) : a + (b - a) * u ∈ Icc (0 : ℝ) 1 := by
    have := mul_nonneg hba.le u.2.1; have := mul_le_mul_of_nonneg_left u.2.2 hba.le
    constructor <;> nlinarith
  have hcab {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (h : r ≤ a ∨ b ≤ r) : c ⟨r, hr⟩ = p₀ :=
    hcp _ fun h' ↦ h.elim (fun h ↦ h'.1.not_ge h) fun h ↦ h'.2.not_ge h
  let γ : Path p₀ p₀ :=
    { toFun := fun u ↦ c ⟨a + (b - a) * u, hmem u⟩
      continuous_toFun := hc.continuous.comp (Continuous.subtype_mk (by fun_prop) _)
      source' := hcab _ (Or.inl (by simp))
      target' := hcab _ (Or.inr (by simp)) }
  obtain ⟨L⟩ := SimplyConnectedSpace.paths_homotopic γ (Path.refl p₀)
  have hθI (t : ℝ) : θ t ∈ Icc (0 : ℝ) 1 := ⟨hτ0 _, hτ1 _⟩
  have hκI (s : ℝ) : κ s ∈ Icc (0 : ℝ) 1 := ⟨hτ0 _, hτ1 _⟩
  let K : I × I → M := fun x ↦ L (⟨κ x.2, hκI _⟩, ⟨θ x.1, hθI _⟩)
  have hK : Continuous K := L.continuous.comp (by
    refine (Continuous.subtype_mk ?_ _).prodMk (Continuous.subtype_mk ?_ _)
    · exact Real.smoothTransition.continuous.comp (by fun_prop)
    · exact Real.smoothTransition.continuous.comp (by fun_prop))
  have hγθ (t : ℝ) : γ ⟨θ t, hθI t⟩ = c ⟨ρ t, by simpa [hρ_def] using hmem ⟨θ t, hθI t⟩⟩ := rfl
  -- `G` and `K` agree where both describe the loop `c ∘ ρ`
  have hGρ (x : I × I) (h : 1 / 4 ≤ (x.2 : ℝ)) : G x = γ ⟨θ x.1, hθI _⟩ := by
    rw [hGφ, hγθ]; exact congrArg c (Subtype.ext (by simp [hφ_def, hβ1 h]))
  have hKρ (x : I × I) (h : (x.2 : ℝ) ≤ 1 / 2) : K x = γ ⟨θ x.1, hθI _⟩ := by
    have : (⟨κ x.2, hκI _⟩ : I) = 0 := Subtype.ext (hκ0 h)
    simp only [K, this, ContinuousMap.HomotopyWith.apply_zero, Path.coe_toContinuousMap]
  -- where `G` and `K` are constant
  have hGp {x : I × I} (h : (x.1 : ℝ) ≤ a ∨ b ≤ x.1) : G x = p₀ := by
    refine hcab _ (h.imp (fun h ↦ ?_) fun h ↦ ?_) <;>
      have h1 := hτ0 (4 * (x.2 : ℝ)) <;> have h2 := hτ1 (4 * (x.2 : ℝ))
    · rw [show φ x.1 x.2 = (1 - β x.2) * x.1 + β x.2 * a by simp [hφ_def, hρa (t := x.1) (by linarith)]]
      nlinarith
    · rw [show φ x.1 x.2 = (1 - β x.2) * x.1 + β x.2 * b by simp [hφ_def, hρb (t := x.1) (by linarith)]]
      nlinarith
  have hKp {x : I × I} (h : (x.1 : ℝ) < a + (b - a) / 4 ∨ b - (b - a) / 4 < x.1 ∨ 3 / 4 < (x.2 : ℝ)) :
      K x = p₀ := by
    rcases h with h | h | h
    · have : (⟨θ x.1, hθI _⟩ : I) = 0 := Subtype.ext (hθ₀ h.le)
      simp only [K, this, Path.Homotopy.source]
    · have : (⟨θ x.1, hθI _⟩ : I) = 1 := Subtype.ext (hθ₁ h.le)
      simp only [K, this, Path.Homotopy.target]
    · have : (⟨κ x.2, hκI _⟩ : I) = 1 := Subtype.ext (hκ1 h.le)
      simp only [K, this, ContinuousMap.HomotopyWith.apply_one, Path.coe_toContinuousMap,
        Path.refl_apply]
  -- the continuous null-homotopy, smooth near the boundary of the square
  let F₀ : I × I → M := fun x ↦ if (x.2 : ℝ) ≤ 1 / 2 then G x else K x
  have hF₀ : Continuous F₀ := Continuous.if_le hG.continuous hK (by fun_prop) continuous_const
    fun x hx ↦ (hGρ x (by linarith)).trans (hKρ x hx.le).symm
  set V₁ : Set (I × I) := {x | (x.2 : ℝ) < 1 / 2}
  set V₂ : Set (I × I) := {x | 1 / 4 < (x.2 : ℝ) ∧
    ((x.1 : ℝ) < a + (b - a) / 4 ∨ b - (b - a) / 4 < x.1 ∨ 3 / 4 < (x.2 : ℝ))}
  set S : Set (I × I) := {x | x.2 = 0 ∨ x.2 = 1 ∨ (x.1 : ℝ) ≤ a ∨ b ≤ x.1}
  have hc₁ : Continuous fun x : I × I ↦ (x.1 : ℝ) := by fun_prop
  have hc₂ : Continuous fun x : I × I ↦ (x.2 : ℝ) := by fun_prop
  have hV₁ : IsOpen V₁ := isOpen_lt hc₂ continuous_const
  have hV₂ : IsOpen V₂ := (isOpen_lt continuous_const hc₂).inter
    ((isOpen_lt hc₁ continuous_const).union ((isOpen_lt continuous_const hc₁).union
      (isOpen_lt continuous_const hc₂)))
  have hS : IsClosed S := (isClosed_eq continuous_snd continuous_const).union
    ((isClosed_eq continuous_snd continuous_const).union
      ((isClosed_le hc₁ continuous_const).union (isClosed_le continuous_const hc₁)))
  have hSU : S ⊆ V₁ ∪ V₂ := by
    rintro x (h | h | h | h)
    · left; simp [V₁, h]
    · right; simp [V₂, h]; norm_num
    all_goals
      rcases lt_or_ge (x.2 : ℝ) (1 / 2) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by linarith, by first | (left; linarith) | (right; left; linarith)⟩
  have hF₀V₁ {x : I × I} (hx : x ∈ V₁) : F₀ x = G x := ite_eq_left (le_of_lt hx)
  have hF₀V₂ {x : I × I} (hx : x ∈ V₂) : F₀ x = p₀ := by
    by_cases h : (x.2 : ℝ) ≤ 1 / 2
    · rw [show F₀ x = G x from ite_eq_left h, hGρ x hx.1.le]
      rcases hx.2 with h' | h' | h'
      · rw [hγθ]; exact hcab _ (Or.inl (by simp [hρa h'.le]))
      · rw [hγθ]; exact hcab _ (Or.inr (by simp [hρb h'.le]))
      · linarith
    · rw [show F₀ x = K x from ite_eq_right h]; exact hKp hx.2
  have hF₀U : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 1)) J n F₀ (V₁ ∪ V₂) := by
    rintro x (hx | hx)
    · exact ((hG x).congr_of_eventuallyEq (Filter.eventually_of_mem (hV₁.mem_nhds hx)
        fun y hy ↦ hF₀V₁ hy)).contMDiffWithinAt
    · exact ((contMDiffAt_const (c := p₀)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hV₂.mem_nhds hx) fun y hy ↦ hF₀V₂ hy)).contMDiffWithinAt
  -- the relative Whitney approximation
  let F : C(I × I, M) := ⟨F₀, hF₀⟩
  obtain ⟨H, hH, hFH⟩ := F.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    n (isCompact_range hF₀).closure hS
    ((hV₁.union hV₂).mem_nhdsSet.2 hSU) hF₀U
  have hHF {x : I × I} (hx : x ∈ S) : H x = F₀ x := (hFH.fst_eq_snd hx).symm
  refine ⟨H, hH, fun t ↦ ?_, fun t ↦ ?_, fun t s ht ↦ ?_⟩
  · rw [hHF (Or.inl rfl), show F₀ (t, 0) = G (t, 0) from ite_eq_left (by simp), hGφ]
    exact congrArg c (Subtype.ext (by simp [hφ_def, hβ0]))
  · rw [hHF (Or.inr (Or.inl rfl)), show F₀ (t, 1) = K (t, 1) from ite_eq_right (by norm_num)]
    exact hKp (Or.inr (Or.inr (by norm_num)))
  · have ht' : (t : ℝ) ≤ a ∨ b ≤ t := (not_and_or.1 ht).imp not_lt.1 not_lt.1
    rw [hHF (Or.inr (Or.inr ht'))]
    by_cases h : ((t, s).2 : ℝ) ≤ 1 / 2
    · rw [show F₀ (t, s) = G (t, s) from ite_eq_left h]; exact hGp ht'
    · rw [show F₀ (t, s) = K (t, s) from ite_eq_right h]
      exact hKp (ht'.imp (fun h ↦ by linarith) fun h ↦ Or.inl (by linarith))

/-- **Smooth null-homotopy of a smooth loop.** In a simply connected Hausdorff manifold without
boundary, modelled on a finite-dimensional real space, a `C^n` loop `c : I → M` based at `p₀` is
the bottom edge of a `C^n` map `H` on the square `I × I` that is constant equal to `p₀` on the
other three edges. -/
theorem ContMDiff.exists_contMDiff_nullhomotopy [SimplyConnectedSpace M] {n : ℕ∞} {c : I → M}
    (hc : ContMDiff (𝓡∂ 1) J n c) {p₀ : M} (hc₀ : c 0 = p₀) (hc₁ : c 1 = p₀) :
    ∃ H : I × I → M, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) J n H ∧ (∀ t, H (t, 0) = c t) ∧
      (∀ t, H (t, 1) = p₀) ∧ (∀ s, H (0, s) = p₀) ∧ ∀ s, H (1, s) = p₀ := by
  have hcp (t : I) (ht : (t : ℝ) ∉ Ioo 0 1) : c t = p₀ := by
    rcases (not_and_or.1 ht).imp not_lt.1 not_lt.1 with h | h
    · rwa [show t = 0 from Subtype.ext (le_antisymm h t.2.1)]
    · rwa [show t = 1 from Subtype.ext (le_antisymm t.2.2 h)]
  obtain ⟨H, hH, h₀, h₁, hp⟩ :=
    hc.exists_contMDiff_nullhomotopy_of_notMem_Ioo le_rfl zero_lt_one le_rfl hcp
  exact ⟨H, hH, h₀, h₁, fun s ↦ hp 0 s (by simp), fun s ↦ hp 1 s (by simp)⟩

end
