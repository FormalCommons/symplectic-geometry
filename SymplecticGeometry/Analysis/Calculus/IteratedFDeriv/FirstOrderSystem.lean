/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Derivative bounds for solutions of first- and second-order systems

Let `h : E → F` satisfy the first-order system `fderiv 𝕜 h w = Φ (w, h w)` near a point `w₀`,
where `Φ : E × F → (E →L[𝕜] F)` is `C^r` at `(w₀, h w₀)`. Differentiating the system expresses
each derivative of `h` of order `j ≥ 1` at `w₀` through the derivatives of `Φ` of order `< j`
at `(w₀, h w₀)` and the derivatives of `h` of lower order. This file turns that into an explicit
pointwise bound: if the derivatives of `Φ` of order `< j` at `(w₀, h w₀)` have norm at most `A`,
then `‖iteratedFDeriv 𝕜 j h w₀‖ ≤ firstOrderSystemConst j * (1 + A) ^ j`, with a natural number
`firstOrderSystemConst j` that depends only on `j`. The bound is uniform in `h`, `Φ`, `w₀` and
the spaces, so it applies to families of solutions.

From this the file derives bounds that hold for a whole family of systems at once: for systems
`fderiv 𝕜 h w = Ψ (γ (w, h w))` with one fixed `C^r` map `Ψ`, the derivatives of `h` at `w₀` are
bounded by a constant that depends only on `Ψ`, a compact set containing `γ (w₀, h w₀)` and a
bound on the derivatives of `γ` there. A second-order system `D²τ(w) = Ψ (a w, b (τ w), Dτ(w))`
is a first-order system for the pair `(τ, Dτ)`, so the same holds for it.

## Main definitions

* `SymplecticGeometry.firstOrderSystemConst`: the constants of the bound, defined by the
  recursion `K 0 = 1`, `K (n + 1) = n ! * (1 + K n) ^ n`.

## Main results

* `SymplecticGeometry.firstOrderSystemConst_mono`: the constants are nondecreasing.
* `SymplecticGeometry.norm_iteratedFDeriv_le_of_eventually_fderiv_eq`: the bound above, for
  `1 ≤ j ≤ r + 1`.
* `SymplecticGeometry.jetNormAt_le_of_eventually_fderiv_eq`: the same bound for the `r`-jet
  norm of `h` at `w₀`, through the `r`-jet norm of `Φ` at `(w₀, h w₀)`.
* `SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le_of_fderiv_eq_comp`: a bound of the
  derivatives of `h` that depends only on `Ψ`, `r`, a compact set and bounds on the jet of `γ`,
  for systems `fderiv 𝕜 h w = Ψ (γ (w, h w))` with a fixed `C^r` map `Ψ`; the derivatives of `Ψ`
  are bounded on the compact set (Tau Ceti's
  `ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen`) and Faà di Bruno bounds those of
  `Ψ ∘ γ`.
* `SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le_of_fderiv_fderiv_eq`: the same for
  second-order systems `D²τ(w) = Ψ (a w, b (τ w), Dτ(w))`, applied to the pair `(τ, Dτ)`.

## Implementation notes

The proof is an induction on `j`. Since `‖iteratedFDeriv 𝕜 (n + 1) h w₀‖` is the norm of the
`n`-th derivative of `fderiv 𝕜 h`, which near `w₀` is `Φ ∘ (fun w ↦ (w, h w))`, Tau Ceti's
pointwise Faà di Bruno bound `TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt` applies, with the
derivatives of `fun w ↦ (w, h w)` bounded by the induction hypothesis. Tau Ceti's
`HasUniformJetBoundsOn.succ_of_fderiv` (in `TauCeti/Analysis/Calculus/UniformJets.lean`) runs the
same bootstrap for families on sets, with constants that are not explicit.
-/

public section

open scoped Nat

namespace SymplecticGeometry

/-- The constants of the derivative bound for first-order systems
(`norm_iteratedFDeriv_le_of_eventually_fderiv_eq`): `K 0 = 1` and
`K (n + 1) = n ! * (1 + K n) ^ n`. -/
def firstOrderSystemConst : ℕ → ℕ
  | 0 => 1
  | n + 1 => n ! * (1 + firstOrderSystemConst n) ^ n

theorem firstOrderSystemConst_zero : firstOrderSystemConst 0 = 1 := (rfl)

theorem firstOrderSystemConst_succ (n : ℕ) :
    firstOrderSystemConst (n + 1) = n ! * (1 + firstOrderSystemConst n) ^ n := (rfl)

/-- The constants of the derivative bound for first-order systems are nondecreasing. -/
theorem firstOrderSystemConst_mono : Monotone firstOrderSystemConst := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [firstOrderSystemConst_succ]
  rcases n with _ | n
  · simp [firstOrderSystemConst_zero]
  · calc firstOrderSystemConst (n + 1) ≤ (1 + firstOrderSystemConst (n + 1)) ^ 1 := by
          rw [pow_one]; omega
      _ ≤ (1 + firstOrderSystemConst (n + 1)) ^ (n + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Derivative bounds for first-order systems.** Let `h : E → F` be `C^r` at `w₀` and solve
`fderiv 𝕜 h w = Φ (w, h w)` for `w` near `w₀`, where `Φ` is `C^r` at `(w₀, h w₀)`. If the
derivatives of `Φ` at `(w₀, h w₀)` of order `< j` have norm at most `A`, then for `1 ≤ j ≤ r + 1`
the `j`-th derivative of `h` at `w₀` has norm at most `firstOrderSystemConst j * (1 + A) ^ j`. -/
theorem norm_iteratedFDeriv_le_of_eventually_fderiv_eq {h : E → F}
    {Φ : E × F → E →L[𝕜] F} {w₀ : E} {r j : ℕ} {A : ℝ}
    (hh : ContDiffAt 𝕜 r h w₀) (hΦ : ContDiffAt 𝕜 r Φ (w₀, h w₀))
    (heq : ∀ᶠ w in nhds w₀, fderiv 𝕜 h w = Φ (w, h w))
    (hA : ∀ i < j, ‖iteratedFDeriv 𝕜 i Φ (w₀, h w₀)‖ ≤ A) (hj₁ : 1 ≤ j) (hj : j ≤ r + 1) :
    ‖iteratedFDeriv 𝕜 j h w₀‖ ≤ firstOrderSystemConst j * (1 + A) ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj₁
  have hnr : n ≤ r := by omega
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by omega))
  set M : ℝ := 1 + firstOrderSystemConst n
  have hM : 1 ≤ M := by simp [M]
  -- the `n`-th derivative of `fderiv 𝕜 h` at `w₀` is that of `Φ ∘ (fun w ↦ (w, h w))`
  have hcomp : iteratedFDeriv 𝕜 n (fderiv 𝕜 h) w₀ =
      iteratedFDeriv 𝕜 n (Φ ∘ fun w ↦ (w, h w)) w₀ :=
    (Filter.EventuallyEq.iteratedFDeriv 𝕜 (f₂ := Φ ∘ fun w ↦ (w, h w)) heq n).eq_of_nhds
  have hhn : ContDiffAt 𝕜 n h w₀ := hh.of_le (by exact_mod_cast hnr)
  -- the derivatives of `fun w ↦ (w, h w)` of positive order `i ≤ n` are at most `(M (1 + A)) ^ i`
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv 𝕜 i (fun w ↦ (w, h w)) w₀‖ ≤ (M * (1 + A)) ^ i := by
    intro i hi₁ hin
    have hid := TauCeti.norm_iteratedFDeriv_id_le_one (𝕜 := 𝕜) (E := E) hi₁ w₀
    have hhi := ih i (by omega) (fun l hl ↦ hA l (by omega)) hi₁ (by omega)
    have hKi : (firstOrderSystemConst i : ℝ) ≤ firstOrderSystemConst n := by
      exact_mod_cast firstOrderSystemConst_mono hin
    have hprod : iteratedFDeriv 𝕜 i (fun w ↦ (w, h w)) w₀ =
        (iteratedFDeriv 𝕜 i id w₀).prod (iteratedFDeriv 𝕜 i h w₀) :=
      iteratedFDeriv_prodMk contDiffAt_id hhn (by exact_mod_cast hin)
    rw [hprod, ContinuousMultilinearMap.opNorm_prod, mul_pow]
    have h1A : 1 ≤ (1 + A) ^ i := one_le_pow₀ (by linarith)
    have hMi : M ≤ M ^ i := le_self_pow₀ hM (by omega)
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  rw [← norm_iteratedFDeriv_fderiv, hcomp]
  refine (TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt (f := fun w ↦ (w, h w))
    (hΦ.of_le (by exact_mod_cast hnr)) (contDiffAt_id.prodMk hhn) (fun i hi ↦ hA i (by omega))
    hD).trans ?_
  rw [firstOrderSystemConst_succ, mul_pow, pow_succ (1 + A)]
  push_cast
  calc (n ! : ℝ) * A * (M ^ n * (1 + A) ^ n) ≤ n ! * (1 + A) * (M ^ n * (1 + A) ^ n) := by
        gcongr; linarith
    _ = n ! * M ^ n * ((1 + A) ^ n * (1 + A)) := by ring

/-- **Jet norm bounds for first-order systems.** Let `h : E → F` be `C^r` at `w₀` and solve
`fderiv 𝕜 h w = Φ (w, h w)` for `w` near `w₀`, where `Φ` is `C^r` at `(w₀, h w₀)`. Then the
`r`-jet norm of `h` at `w₀` is at most
`‖h w₀‖ + r * firstOrderSystemConst r * (1 + A) ^ r`, where `A` is the `r`-jet norm of `Φ` at
`(w₀, h w₀)`. -/
theorem jetNormAt_le_of_eventually_fderiv_eq {h : E → F} {Φ : E × F → E →L[𝕜] F} {w₀ : E}
    {r : ℕ} (hh : ContDiffAt 𝕜 r h w₀) (hΦ : ContDiffAt 𝕜 r Φ (w₀, h w₀))
    (heq : ∀ᶠ w in nhds w₀, fderiv 𝕜 h w = Φ (w, h w)) :
    jetNormAt 𝕜 r h w₀ ≤
      ‖h w₀‖ + r * firstOrderSystemConst r * (1 + jetNormAt 𝕜 r Φ (w₀, h w₀)) ^ r := by
  set A := jetNormAt 𝕜 r Φ (w₀, h w₀)
  have hA : 1 ≤ 1 + A := le_add_of_nonneg_right (jetNormAt_nonneg _ _ _)
  refine (jetNormAt_le_of_norm_iteratedFDeriv_succ_le
    (C := firstOrderSystemConst r * (1 + A) ^ r) fun j hj ↦ ?_).trans_eq (by ring)
  exact (norm_iteratedFDeriv_le_of_eventually_fderiv_eq (j := j + 1) hh hΦ heq
    (fun i hi ↦ norm_iteratedFDeriv_le_jetNormAt (r := r) (by omega) Φ _) (by omega)
    (by omega)).trans (mul_le_mul (by exact_mod_cast firstOrderSystemConst_mono hj)
    (pow_le_pow_right₀ hA (by omega)) (by positivity) (by positivity))

section SecondOrder

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B]
  [NormedSpace 𝕜 B]

open ContinuousLinearMap
open scoped ContDiff Topology

/-- **Uniform derivative bounds for a family of first-order systems.** Let `Ψ : X → (E →L[𝕜] F)`
be `C^r`, let `S ⊆ X` be compact and let `D` be a real number. There is a constant `K ≥ 0` such
that for every `h : E → F` that is `C^r` at `w₀` and solves `fderiv 𝕜 h w = Ψ (γ (w, h w))` near
`w₀`,
where `γ : E × F → X` is `C^r` at `(w₀, h w₀)` with `γ (w₀, h w₀) ∈ S` and
`‖iteratedFDeriv 𝕜 i γ (w₀, h w₀)‖ ≤ D ^ i` for `1 ≤ i ≤ r`, the derivatives of `h` at `w₀` of
order `1 ≤ j ≤ r + 1` have norm at most `K`. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_fderiv_eq_comp {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] {Ψ : X → E →L[𝕜] F} {r : ℕ}
    (hΨ : ContDiff 𝕜 r Ψ) {S : Set X} (hS : IsCompact S) (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : E → F} {γ : E × F → X} {w₀ : E},
      ContDiffAt 𝕜 r h w₀ → ContDiffAt 𝕜 r γ (w₀, h w₀) →
      (∀ᶠ w in 𝓝 w₀, fderiv 𝕜 h w = Ψ (γ (w, h w))) → γ (w₀, h w₀) ∈ S →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv 𝕜 i γ (w₀, h w₀)‖ ≤ D ^ i) →
      ∀ j, 1 ≤ j → j ≤ r + 1 → ‖iteratedFDeriv 𝕜 j h w₀‖ ≤ K := by
  obtain ⟨M, hM0, hM⟩ := hΨ.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ
    hS (Set.subset_univ _)
  set D' := max |D| 1
  refine ⟨firstOrderSystemConst (r + 1) * (1 + r ! * M * D' ^ r) ^ (r + 1),
    by positivity, fun {h γ w₀} hh hγ heq hγS hD j hj₁ hj ↦ ?_⟩
  have hD' : 1 ≤ D' := le_max_right _ _
  have hA (i : ℕ) (hi : i < j) :
      ‖iteratedFDeriv 𝕜 i (Ψ ∘ γ) (w₀, h w₀)‖ ≤ r ! * M * D' ^ r := by
    refine (TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt (D := D')
      (hΨ.contDiffAt.of_le (by exact_mod_cast (show i ≤ r by omega))) (hγ.of_le
        (by exact_mod_cast (show i ≤ r by omega)))
      (fun l hl ↦ hM l (by omega) _ hγS)
      fun l hl₁ hl ↦ (hD l hl₁ (by omega)).trans ((le_abs_self _).trans ((abs_pow D l).le.trans
        (pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) l)))).trans ?_
    gcongr
    all_goals omega
  have := norm_iteratedFDeriv_le_of_eventually_fderiv_eq (Φ := fun p ↦ Ψ (γ p)) hh
    (hΨ.contDiffAt.comp _ hγ) heq hA hj₁ hj
  refine this.trans ?_
  gcongr
  · exact_mod_cast firstOrderSystemConst_mono hj
  · have : 0 ≤ r ! * M * D' ^ r := by positivity
    linarith

/-- **Uniform derivative bounds for a family of second-order systems.** Let
`Ψ : A × B × (E →L[𝕜] F) → (E →L[𝕜] E →L[𝕜] F)` be `C^r`, let `S ⊆ A × B × (E →L[𝕜] F)` be
compact and let `C` be a real number. There is a constant `K ≥ 0` such that for every `τ : E → F`
that is `C^(r+2)` at `w₀` and solves `D²τ(w) = Ψ (a w, b (τ w), Dτ(w))` near `w₀`, where
`a : E → A` is `C^r` at `w₀` and `b : F → B` is `C^r` at `τ w₀`, with derivatives of order
`1 ≤ i ≤ r` of norm at most `C` there, and `(a w₀, b (τ w₀), Dτ(w₀)) ∈ S`, the derivatives of `τ`
at `w₀` of order `1 ≤ j ≤ r + 1` have norm at most `K`. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_fderiv_fderiv_eq
    {Ψ : A × B × (E →L[𝕜] F) → E →L[𝕜] E →L[𝕜] F} {r : ℕ} (hΨ : ContDiff 𝕜 r Ψ)
    {S : Set (A × B × (E →L[𝕜] F))} (hS : IsCompact S) (C : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {τ : E → F} {a : E → A} {b : F → B} {w₀ : E},
      ContDiffAt 𝕜 (r + 2) τ w₀ → ContDiffAt 𝕜 r a w₀ → ContDiffAt 𝕜 r b (τ w₀) →
      (∀ᶠ w in 𝓝 w₀, fderiv 𝕜 (fderiv 𝕜 τ) w = Ψ (a w, b (τ w), fderiv 𝕜 τ w)) →
      (a w₀, b (τ w₀), fderiv 𝕜 τ w₀) ∈ S →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv 𝕜 i a w₀‖ ≤ C) →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv 𝕜 i b (τ w₀)‖ ≤ C) →
      ∀ j, 1 ≤ j → j ≤ r + 1 → ‖iteratedFDeriv 𝕜 j τ w₀‖ ≤ K := by
  -- The first-order system for `(τ, Dτ)`.
  set Ψ' : A × B × (E →L[𝕜] F) → E →L[𝕜] F × (E →L[𝕜] F) := fun q ↦
    (inl 𝕜 F (E →L[𝕜] F)).comp q.2.2 + (inr 𝕜 F (E →L[𝕜] F)).comp (Ψ q)
  have hΨ' : ContDiff 𝕜 r Ψ' := by
    have h1 : ContDiff 𝕜 r fun q : A × B × (E →L[𝕜] F) ↦ q.2.2 := contDiff_snd.snd
    exact (contDiff_const.clm_comp h1).add (contDiff_const.clm_comp hΨ)
  set D := max C 1
  obtain ⟨K, hK0, hK⟩ := exists_forall_norm_iteratedFDeriv_le_of_fderiv_eq_comp hΨ' hS D
  refine ⟨K, hK0, fun {τ a b w₀} hτ ha hb heq hS₀ haC hbC j hj₁ hj ↦ ?_⟩
  set h : E → F × (E →L[𝕜] F) := fun w ↦ (τ w, fderiv 𝕜 τ w)
  -- `γ` is written with `Function.comp` so that Tau Ceti's lemmas on `f ∘ Prod.fst` and
  -- `f ∘ Prod.snd` apply to its components.
  set γ : E × (F × (E →L[𝕜] F)) → A × B × (E →L[𝕜] F) := fun p ↦
    ((a ∘ Prod.fst) p, ((b ∘ Prod.fst) ∘ Prod.snd) p, (Prod.snd ∘ Prod.snd) p)
  have hτ1 : ContDiffAt 𝕜 (r + 1) τ w₀ := hτ.of_le (by norm_cast; omega)
  have hDτ : ContDiffAt 𝕜 (r + 1) (fderiv 𝕜 τ) w₀ := hτ.fderiv_right (by norm_cast)
  have hh : ContDiffAt 𝕜 (r + 1) h w₀ := hτ1.prodMk hDτ
  set p₀ : E × (F × (E →L[𝕜] F)) := (w₀, h w₀)
  have ha' : ContDiffAt 𝕜 r (a ∘ Prod.fst) p₀ := ha.comp p₀ contDiffAt_fst
  have hb' : ContDiffAt 𝕜 r ((b ∘ Prod.fst) ∘ Prod.snd) p₀ :=
    (hb.comp (τ w₀, fderiv 𝕜 τ w₀) contDiffAt_fst).comp p₀ contDiffAt_snd
  have hs' : ContDiffAt 𝕜 r (Prod.snd ∘ Prod.snd) p₀ := contDiff_snd.snd.contDiffAt
  have hγ : ContDiffAt 𝕜 r γ p₀ := ha'.prodMk (hb'.prodMk hs')
  have hD (i : ℕ) (hi₁ : 1 ≤ i) (hi : i ≤ r) : ‖iteratedFDeriv 𝕜 i γ p₀‖ ≤ D ^ i := by
    refine le_trans ?_ (le_self_pow₀ (le_max_right C 1) (by omega))
    rw [iteratedFDeriv_prodMk ha' (hb'.prodMk hs') (by exact_mod_cast hi),
      iteratedFDeriv_prodMk hb' hs' (by exact_mod_cast hi),
      ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod,
      Prod.norm_iteratedFDeriv_comp_fst, Prod.norm_iteratedFDeriv_comp_snd,
      Prod.norm_iteratedFDeriv_comp_fst, Prod.norm_iteratedFDeriv_comp_snd]
    refine max_le ((haC i hi₁ hi).trans (le_max_left _ _))
      (max_le ((hbC i hi₁ hi).trans (le_max_left _ _)) ?_)
    exact (TauCeti.norm_iteratedFDeriv_snd_le_one hi₁ _).trans (le_max_right _ _)
  have heqh : ∀ᶠ w in 𝓝 w₀, fderiv 𝕜 h w = Ψ' (γ (w, h w)) := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = r + 2 := ⟨_, rfl⟩
    have hτ' : ContDiffAt 𝕜 m τ w₀ := by rw [hm]; exact_mod_cast hτ
    filter_upwards [hτ'.eventually (by simp), heq] with w hw heqw
    rw [DifferentiableAt.fderiv_prodMk (hw.differentiableAt (by simp [hm]))
      ((hw.fderiv_right (m := 1) (by rw [hm]; norm_cast; omega)).differentiableAt one_ne_zero)]
    ext u <;> simp [Ψ', γ, h, heqw]
  have hprod := iteratedFDeriv_prodMk hτ1 hDτ (i := j) (by exact_mod_cast hj)
  calc ‖iteratedFDeriv 𝕜 j τ w₀‖
      ≤ max ‖iteratedFDeriv 𝕜 j τ w₀‖ ‖iteratedFDeriv 𝕜 j (fderiv 𝕜 τ) w₀‖ := le_max_left _ _
    _ = ‖iteratedFDeriv 𝕜 j h w₀‖ := by
        rw [show h = fun w ↦ (τ w, fderiv 𝕜 τ w) from rfl, hprod,
          ContinuousMultilinearMap.opNorm_prod]
    _ ≤ K := hK (hh.of_le (by norm_cast; omega)) hγ heqh hS₀ hD j hj₁ hj

end SecondOrder

end SymplecticGeometry

end
