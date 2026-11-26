/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Connected
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Loop
import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Fibration

/-!
# The Maslov index of paths: naturality, values, homotopy and the reference Lagrangian

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)` and
`μ(γ, V)` for the Robbin–Salamon index `SymplecticGeometry.LagrangianGrassmannian.pathMaslovIndex`
of a path `γ` in `ℒ ι` relative to a Lagrangian `V`.

## Main results

* `pathMaslovIndex_eq_of_homotopy`: a homotopy of paths whose ends move inside the sets where the
  dimension of the intersection with `V` is constant does not change `μ(·, V)`.
* `pathMaslovIndex_smul`: **naturality**, `μ(Ψ γ, Ψ V) = μ(γ, V)` for every symplectic matrix
  `Ψ`.
* `pathMaslovIndex_add_half_sub_mem`: **the values property**, `μ(γ, V)` is congruent modulo `ℤ`
  to half the change of `dim (γ t ∩ V)` between the ends; so `2 μ(γ, V)` is an integer
  (`two_mul_pathMaslovIndex_mem`).
* `pathMaslovIndex_eq_iff_homotopic`: two paths with the same ends are homotopic with fixed ends
  exactly when they have the same index, relative to any Lagrangian.
* `pathMaslovIndex_sub_pathMaslovIndex`: the difference `μ(γ, V') - μ(γ, V)` depends only on the
  ends of `γ` (it is the Hörmander index of the four Lagrangians).

## Implementation notes

Naturality is proved by moving the reference Lagrangian. Join `1` to `Ψ` by a path `s ↦ P s` in
`Sp(2n)`, which is path connected, and lift the path `s ↦ P s V` to a path `s ↦ U s` of unitary
frames. The square `(s, t) ↦ (U s)⁻¹ P s γ(t)` compares `U₀⁻¹ γ` with `U₁⁻¹ Ψ γ` relative to the
fixed Lagrangian `{y = 0}`, and along its two sides the dimension of the intersection with
`{y = 0}` is that of `γ 0 ∩ V`, respectively `γ 1 ∩ V`, so the zero axiom and homotopy invariance
give the equality (`pathMaslovIndex_eq_of_homotopy`, through Mathlib's
`Path.Homotopic.map_trans_evalAt`).

The proofs of `pathMaslovIndex_eq_of_homotopy` and `pathMaslovIndex_smul` adapt Tau Ceti's proof
of `TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`: a path from `1` in the symplectic group, a
square built from it and packaged as a homotopy, the square lemma, catenation, and the zero axiom
on both edges through the invariance of a dimension under the group. The lift to unitary frames
is the new step.

The values property compares the formula of `μ` with Tau Ceti's
`Matrix.det_eq_neg_one_pow_mul_exp_spectralAngleSum`, in which the multiplicity of the eigenvalue
`1` of the Souriau map is the dimension of the intersection with `{y = 0}`
(`rootMultiplicity_one_charpoly_souriau`). This angle-and-determinant calculation follows the one
in Tau Ceti's `Matrix.UnitaryGroup.maslovIndex_eq_zero_of_rootMultiplicity_eq`.

## References

* [J. Robbin, D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2 (Theorems 2.3
  and 2.4) and §3 (Theorem 3.5).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Homotopies with moving ends -/

/-- **Homotopy invariance with moving ends.** Let `F` be a homotopy from the path `γ₀` to the path
`γ₁` whose ends `F (s, 0)` and `F (s, 1)` move inside the sets where the dimension of the
intersection with `V` is constant. Then `γ₀` and `γ₁` have the same index relative to `V`. -/
theorem pathMaslovIndex_eq_of_homotopy {Λ₀ Λ₁ Λ₀' Λ₁' : ℒ ι} (γ₀ : Path Λ₀ Λ₁)
    (γ₁ : Path Λ₀' Λ₁') (V : ℒ ι) (F : C(I × I, ℒ ι)) (h₀ : ∀ t, F (0, t) = γ₀ t)
    (h₁ : ∀ t, F (1, t) = γ₁ t) {k k' : ℕ}
    (hF₀ : ∀ s, Module.finrank ℝ
      ↥((F (s, 0) : Submodule ℝ (StdSpace ι)) ⊓ (V : Submodule ℝ (StdSpace ι))) = k)
    (hF₁ : ∀ s, Module.finrank ℝ
      ↥((F (s, 1) : Submodule ℝ (StdSpace ι)) ⊓ (V : Submodule ℝ (StdSpace ι))) = k') :
    pathMaslovIndex γ₀ V = pathMaslovIndex γ₁ V := by
  let H : ContinuousMap.Homotopy (γ₀ : C(I, ℒ ι)) (γ₁ : C(I, ℒ ι)) :=
    { toContinuousMap := F
      map_zero_left := h₀
      map_one_left := h₁ }
  have h := pathMaslovIndex_eq_of_homotopic (Path.Homotopic.map_trans_evalAt H Path.id) V
  rw [pathMaslovIndex_trans, pathMaslovIndex_trans,
    pathMaslovIndex_eq_zero_of_finrank_eq (H.evalAt 0) V (k := k) hF₀,
    pathMaslovIndex_eq_zero_of_finrank_eq (H.evalAt 1) V (k := k') hF₁, add_zero,
    zero_add] at h
  refine ((pathMaslovIndex_congr γ₀ _ (fun t ↦ ?_) V).trans h).trans
    (pathMaslovIndex_congr _ γ₁ (fun t ↦ ?_) V) <;> simp

/-! ### Naturality -/

/-- **Naturality.** A symplectic matrix `Ψ` does not change the index when it moves both the path
and the reference Lagrangian: `μ(Ψ γ, Ψ V) = μ(γ, V)`. -/
theorem pathMaslovIndex_smul (Ψ : GLSymplectic ι ℝ) {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    pathMaslovIndex (γ.map (continuous_const_smul Ψ)) (Ψ • V) = pathMaslovIndex γ V := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective V
  -- A path `P` from `1` to `Ψ`, and a path `δ` of unitary frames of `s ↦ P s • V`.
  let P : Path (1 : GLSymplectic ι ℝ) Ψ := PathConnectedSpace.somePath 1 Ψ
  obtain ⟨U', δ, hδ⟩ := exists_path_lift_unitaryFrame
    (P.map (f := fun g : GLSymplectic ι ℝ ↦ g • unitaryFrame U)
      (continuous_id.smul continuous_const)) (one_smul _ (unitaryFrame U)).symm
  have hδ' (s : I) : unitaryFrame (δ s) = P s • unitaryFrame U := by simpa using hδ s
  have hU' : unitaryFrame U' = Ψ • unitaryFrame U := by simpa using hδ' 1
  let F : C(I × I, ℒ ι) :=
    ⟨fun p ↦ (δ p.1)⁻¹ • (P p.1 • γ p.2),
      ((δ.continuous.comp continuous_fst).inv).smul
        ((P.continuous.comp continuous_fst).smul (γ.continuous.comp continuous_snd))⟩
  -- Along the sides of the square, the intersections with `{y = 0}` keep their dimension.
  have hside (s t : I) : Module.finrank ℝ
      ↥((F (s, t) : Submodule ℝ (StdSpace ι)) ⊓ (horizontal ι : Submodule ℝ (StdSpace ι))) =
      Module.finrank ℝ
        ↥((γ t : Submodule ℝ (StdSpace ι)) ⊓ (unitaryFrame U : Submodule ℝ (StdSpace ι))) := by
    rw [ContinuousMap.coe_mk, ← finrank_inf_unitaryFrame, hδ', finrank_smul_inf_smul]
  rw [← hU', pathMaslovIndex_unitaryFrame, pathMaslovIndex_unitaryFrame]
  refine (pathMaslovIndex_eq_of_homotopy _ _ (horizontal ι) F (fun t ↦ ?_) (fun t ↦ ?_)
    (fun s ↦ by rw [hside, γ.source]) (fun s ↦ by rw [hside, γ.target])).symm
  · simp [F]
  · simp [F]

/-! ### The values property -/

/-- The values property relative to `{y = 0}`, read off Souriau's formula. -/
private theorem pathMaslovIndex_horizontal_sub_half_sub_mem {Λ Λ' : ℒ ι} (γ : Path Λ Λ') :
    pathMaslovIndex γ (horizontal ι) -
        ((Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι) : ℝ) -
          Module.finrank ℝ ↥((Λ' : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι)) / 2 ∈
      Set.range (Int.cast : ℤ → ℝ) := by
  set n := Fintype.card ι
  -- `det (W Λ) = (-1) ^ (n - k) e^{2πi s(W Λ)}`, where `k = dim (Λ ∩ {y = 0})`.
  have hdet (Λ₀ : ℒ ι) :
      ((souriau Λ₀ : Matrix ι ι ℂ).det : ℂ) =
        Complex.exp (((Real.pi * (n - Module.finrank ℝ
          ↥((Λ₀ : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι) : ℝ) +
            2 * Real.pi * spectralAngleSum (souriau Λ₀ : Matrix ι ι ℂ) : ℝ) : ℂ) *
          Complex.I) := by
    have hle : (souriau Λ₀ : Matrix ι ι ℂ).charpoly.rootMultiplicity 1 ≤ n :=
      (Polynomial.count_roots _).symm.le.trans ((Multiset.count_le_card _ _).trans
        ((Polynomial.card_roots' _).trans (charpoly_natDegree_eq_dim _).le))
    rw [det_eq_neg_one_pow_mul_exp_spectralAngleSum (souriau Λ₀).property,
      ← rootMultiplicity_one_charpoly_souriau, ← Nat.cast_sub hle, ← Complex.exp_pi_mul_I,
      ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- `e^{iθ} det (W Λ) = det (W Λ')` for the angle `θ` swept by the Maslov phase.
  have hθ : Complex.exp (Circle.angleChange (γ.map continuous_maslovPhase) * Complex.I) *
      (souriau Λ : Matrix ι ι ℂ).det = (souriau Λ' : Matrix ι ι ℂ).det := by
    have h := congrArg ((↑) : Circle → ℂ) (Circle.exp_angleChange (γ.map continuous_maslovPhase))
    have hρ (Λ₀ : ℒ ι) : (maslovPhase Λ₀ : ℂ) = (souriau Λ₀ : Matrix ι ι ℂ).det := by
      rw [maslovPhase_def, UnitaryGroup.coe_detCircle]
    rw [Circle.coe_exp, Circle.coe_div, hρ, hρ] at h
    rw [h, div_mul_cancel₀ _ (hρ Λ ▸ Circle.coe_ne_zero _)]
  rw [hdet, hdet, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at hθ
  obtain ⟨m, hm⟩ := hθ
  have hm' := congrArg Complex.im hm
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat] at hm'
  refine ⟨m, ?_⟩
  rw [pathMaslovIndex_horizontal, eq_comm, sub_eq_iff_eq_add, sub_eq_iff_eq_add,
    div_eq_iff (by positivity)]
  linear_combination hm'

/-- **The values property.** The index of a path `γ` from `Λ` to `Λ'` relative to `V`, plus half
the change `dim (Λ ∩ V) - dim (Λ' ∩ V)`, is an integer. -/
theorem pathMaslovIndex_add_half_sub_mem {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    pathMaslovIndex γ V +
        ((Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ V) : ℝ) -
          Module.finrank ℝ ↥((Λ' : Submodule ℝ (StdSpace ι)) ⊓ V)) / 2 ∈
      Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective V
  obtain ⟨m, hm⟩ := pathMaslovIndex_horizontal_sub_half_sub_mem
    (γ.map (continuous_const_smul U⁻¹))
  refine ⟨m + Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ unitaryFrame U) -
    Module.finrank ℝ ↥((Λ' : Submodule ℝ (StdSpace ι)) ⊓ unitaryFrame U), ?_⟩
  rw [pathMaslovIndex_unitaryFrame, finrank_inf_unitaryFrame Λ, finrank_inf_unitaryFrame Λ']
  push_cast
  linear_combination hm

/-- Twice the index of a path is an integer. -/
theorem two_mul_pathMaslovIndex_mem {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι) :
    2 * pathMaslovIndex γ V ∈ Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨m, hm⟩ := pathMaslovIndex_add_half_sub_mem γ V
  refine ⟨2 * m - Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ V) +
    Module.finrank ℝ ↥((Λ' : Submodule ℝ (StdSpace ι)) ⊓ V), ?_⟩
  push_cast
  linear_combination 2 * hm

/-! ### Homotopy and the reference Lagrangian -/

/-- **Homotopy classification of paths.** Two paths of Lagrangians with the same ends are homotopic
with fixed ends exactly when they have the same index relative to `V`, whatever `V` is. -/
theorem pathMaslovIndex_eq_iff_homotopic {Λ Λ' : ℒ ι} {γ γ' : Path Λ Λ'} (V : ℒ ι) :
    pathMaslovIndex γ V = pathMaslovIndex γ' V ↔ γ.Homotopic γ' := by
  refine ⟨fun h ↦ ?_, fun h ↦ pathMaslovIndex_eq_of_homotopic h V⟩
  have hloop : maslovIndex (γ.trans γ'.symm) = maslovIndex (γ'.trans γ'.symm) := by
    have h₁ := pathMaslovIndex_eq_maslovIndex (γ.trans γ'.symm) V
    have h₂ := pathMaslovIndex_eq_maslovIndex (γ'.trans γ'.symm) V
    rw [pathMaslovIndex_trans, pathMaslovIndex_symm, h] at h₁
    rw [pathMaslovIndex_trans, pathMaslovIndex_symm] at h₂
    exact_mod_cast h₁.symm.trans h₂
  have hq := congrArg (fun q ↦ q.trans (Path.Homotopic.Quotient.mk γ'))
    (Path.Homotopic.Quotient.eq.2 (maslovIndex_eq_iff_homotopic.1 hloop))
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at hq
  exact Path.Homotopic.Quotient.eq.1 hq

/-- **The difference of the indices relative to two Lagrangians depends only on the ends.** For two
paths `γ`, `γ'` from `Λ` to `Λ'` and two Lagrangians `V`, `V'`,
`μ(γ, V') - μ(γ, V) = μ(γ', V') - μ(γ', V)`. -/
theorem pathMaslovIndex_sub_pathMaslovIndex {Λ Λ' : ℒ ι} (γ γ' : Path Λ Λ') (V V' : ℒ ι) :
    pathMaslovIndex γ V' - pathMaslovIndex γ V = pathMaslovIndex γ' V' - pathMaslovIndex γ' V := by
  have h := (pathMaslovIndex_eq_maslovIndex (γ.trans γ'.symm) V).trans
    (pathMaslovIndex_eq_maslovIndex (γ.trans γ'.symm) V').symm
  simp only [pathMaslovIndex_trans, pathMaslovIndex_symm] at h
  linarith

end LagrangianGrassmannian

end SymplecticGeometry

end
