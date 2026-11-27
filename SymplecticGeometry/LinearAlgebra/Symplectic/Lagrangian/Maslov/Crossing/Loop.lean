/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Form
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Basic
public import TauCeti.Analysis.Matrix.SymplecticGroup.Maslov
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Path
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Product
import SymplecticGeometry.Analysis.Calculus.Deriv.Matrix

/-!
# The crossing-form formula for loops

Two formulas compute a Maslov index of a loop as a sum of signatures of crossing forms, the
crossings being the times where the loop meets a fixed Lagrangian nontransversally.

* For a loop `γ` of Lagrangian subspaces of `(StdSpace ι, ω₀)`, framed by `Z = fromRows X Y`, the
  crossings with the vertical Lagrangian `{x = 0}` are the times where `X` is singular, and the
  crossing form there is `u ↦ -⟪Y u, X' u⟫` on `ker X` (`lagrangianCrossingForm_vertical`). If
  every crossing is regular, the Maslov index of `γ` is the sum of their signatures over one
  period.
* For a loop `Ψ = (A B; C D)` of symplectic matrices, the crossings are the times where `B` is
  singular, the crossing form is `y ↦ -⟪D y, B' y⟫` on `ker B`, and the Maslov index of `Ψ` is
  half the sum of the signatures.

The frame of the Lagrangian loop need not be periodic: it may close up to a constant invertible
change of frame, `Z (t + 1) = Z t * g`. This cannot be avoided, since a loop of odd index has no
periodic real frame, and it contains the case of unitary frames `X + i Y`, which close up to a
real orthogonal matrix.

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.maslovIndex_eq_crossing_sum`: the formula for loops
  of Lagrangian subspaces.
* `TauCeti.GLSymplectic.maslovIndex_eq_half_crossing_sum`: the formula for loops of symplectic
  matrices.
* `SymplecticGeometry.maslovIndex_eq_crossing_sum_and_half_crossing_sum`: both formulas together.

## Implementation notes

The Lagrangian formula is the formula for paths in the form `pathMaslovIndex_eq_crossing_sum_Ico`,
relative to `{x = 0}`, together with `pathMaslovIndex_eq_maslovIndex`. At time `1` the frame is
`Z 0 * g` with derivative `Z' 0 * g`, so the crossing forms at `0` and at `1` are equivalent
(`lagrangianCrossingForm_mul_equivalent`), and the correction term of the path formula, half the
difference of their signatures, vanishes. The symplectic formula applies the Lagrangian one to the
loop `t ↦ Ψ t {x = 0}`, framed by `fromRows B D`, whose Maslov index is twice that of `Ψ`
(`maslovIndex_smul_const`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3
  (the crossing forms of loops, pp. 49 and 53–54).
* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2 (the crossing
  forms and the formula for paths with regular crossings).
-/

public section

open Matrix TauCeti Set
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => SymplecticGeometry.LagrangianGrassmannian (SymplecticGeometry.stdForm ι)

namespace SymplecticGeometry

namespace LagrangianGrassmannian

/-- A Lagrangian frame `Z` spans a subspace meeting `{x = 0}` nontrivially exactly when its upper
block is singular. -/
private theorem inf_vertical_ne_bot_iff {Λ : ℒ ι} {Z : Matrix (ι ⊕ ι) ι ℝ}
    (hZ : LinearMap.range (toEuclideanLin Z) = Λ) :
    (Λ : Submodule ℝ (StdSpace ι)) ⊓ vertical ι ≠ ⊥ ↔ Z.toRows₁.det = 0 := by
  have hL : (stdForm ι).IsLagrangian
      (LinearMap.range (toEuclideanLin (fromRows Z.toRows₁ Z.toRows₂))) := by
    rw [fromRows_toRows, hZ]; exact Λ.isLagrangian
  rw [ne_eq, ← disjoint_iff, ← hZ, coe_vertical]
  conv_lhs => rw [← fromRows_toRows Z]
  rw [StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian hL,
    isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]

/-- For a frame that closes up as `Z 1 = Z 0 * g`, the crossing form at time `1`, with the
derivative `Z' 0 * g`, is equivalent to the crossing form at time `0`. -/
private theorem lagrangianCrossingForm_equivalent_of_eq_mul {Λ : ℒ ι}
    {Z₀ Z₁ Z' : Matrix (ι ⊕ ι) ι ℝ} {g : Matrix ι ι ℝ}
    (h₀ : LinearMap.range (toEuclideanLin Z₀) = Λ) (h₁ : LinearMap.range (toEuclideanLin Z₁) = Λ)
    (hg : Z₁ = Z₀ * g) (V : Submodule ℝ (StdSpace ι)) :
    (lagrangianCrossingForm Z₀ Z' V).Equivalent (lagrangianCrossingForm Z₁ (Z' * g) V) := by
  have hgU := isUnit_of_range_mul_eq (hg ▸ h₁)
  have hiso : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin Z₀)) := by
    rw [h₀]; exact Λ.isLagrangian.isIsotropic
  have h := lagrangianCrossingForm_mul_equivalent hiso Z' V hgU.unit 0
  rwa [IsUnit.unit_spec, Matrix.mul_zero, add_zero, ← hg] at h

/-- **The crossing-form formula for loops of Lagrangian subspaces.** Let `γ` be a loop of
Lagrangians and `Z = fromRows X Y : ℝ → Matrix (ι ⊕ ι) ι ℝ` a frame of it (the columns of `Z t`
span `γ t` for `t ∈ [0, 1]`) that closes up to a constant change of frame:
`Z (t + 1) = Z t * g` for all `t`. Suppose that at each crossing `t ∈ [0, 1)` with `{x = 0}`,
where `X t` is singular, `Z` has derivative `Z' t` and the crossing form
`u ↦ -⟪Y t u, X' t u⟫` on `ker X t` (`lagrangianCrossingForm_vertical`) is nondegenerate. Then
the Maslov index of `γ` is the sum of the signatures of these crossing forms over `[0, 1)`. -/
theorem maslovIndex_eq_crossing_sum {Λ : ℒ ι} (γ : Path Λ Λ) {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    {g : Matrix ι ι ℝ} (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hg : ∀ t, Z (t + 1) = Z t * g)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, (Z t).toRows₁.det = 0 → HasDerivAt Z (Z' t) t)
    (hreg : ∀ t ∈ Ico (0 : ℝ) 1, (Z t).toRows₁.det = 0 →
      (lagrangianCrossingForm (Z t) (Z' t) (vertical ι)).Nondegenerate) :
    maslovIndex γ =
      ∑ᶠ t ∈ Ico (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) (vertical ι)).signature := by
  have h1 : Z 1 = Z 0 * g := by simpa using hg 0
  have hcross (t : I) :
      (γ t : Submodule ℝ (StdSpace ι)) ⊓ vertical ι ≠ ⊥ ↔ (Z t).toRows₁.det = 0 :=
    inf_vertical_ne_bot_iff (hZ t)
  -- The time `1` is a crossing exactly when `0` is; there the frame is `Z 0 * g`, and we take
  -- `Z' 0 * g` as its derivative.
  have hc10 : (Z (1 : I)).toRows₁.det = 0 ↔ (Z (0 : I)).toRows₁.det = 0 := by
    rw [← hcross, ← hcross, Path.source, Path.target]
  set Z'' : ℝ → Matrix (ι ⊕ ι) ι ℝ := Function.update Z' 1 (Z' 0 * g)
  have hZ''1 : Z'' 1 = Z' 0 * g := Function.update_self _ _ _
  have hZ''t {t : ℝ} (ht : t ≠ 1) : Z'' t = Z' t := Function.update_of_ne ht _ _
  have heq1 : (lagrangianCrossingForm (Z 0) (Z' 0) (vertical ι)).Equivalent
      (lagrangianCrossingForm (Z 1) (Z'' 1) (vertical ι)) := by
    rw [hZ''1]
    exact lagrangianCrossingForm_equivalent_of_eq_mul (by simpa using hZ 0) (by simpa using hZ 1)
      h1 _
  have hd' (t : I) (h : (γ t : Submodule ℝ (StdSpace ι)) ⊓ vertical ι ≠ ⊥) :
      HasDerivWithinAt Z (Z'' t) (Icc 0 1) t := by
    rw [hcross] at h
    rcases eq_or_ne t 1 with rfl | ht
    · rw [Icc.coe_one, hZ''1, ← zero_add (1 : ℝ)]
      exact ((hd 0 ⟨le_rfl, zero_lt_one⟩ (hc10.1 h)).matrix_of_forall_add_eq_mul
        hg).matrix_hasDerivWithinAt
    · have ht' : (t : ℝ) ≠ 1 := fun h ↦ ht (Subtype.ext h)
      rw [hZ''t ht']
      exact (hd t ⟨t.property.1, lt_of_le_of_ne t.property.2 ht'⟩ h).matrix_hasDerivWithinAt
  have hreg' (t : I) (h : (γ t : Submodule ℝ (StdSpace ι)) ⊓ vertical ι ≠ ⊥) :
      (lagrangianCrossingForm (Z t) (Z'' t) (vertical ι)).Nondegenerate := by
    rw [hcross] at h
    rcases eq_or_ne t 1 with rfl | ht
    · rw [Icc.coe_one]
      exact (Classical.choice heq1).nondegenerate_iff.1 (hreg 0 ⟨le_rfl, zero_lt_one⟩ (hc10.1 h))
    · have ht' : (t : ℝ) ≠ 1 := fun h ↦ ht (Subtype.ext h)
      rw [hZ''t ht']
      exact hreg t ⟨t.property.1, lt_of_le_of_ne t.property.2 ht'⟩ h
  have key := pathMaslovIndex_eq_crossing_sum_Ico γ (vertical ι) hZ hd' hreg'
  rw [pathMaslovIndex_eq_maslovIndex] at key
  -- With the derivative `Z' 0 * g` at `1`, the signatures at `0` and `1` agree, and the sum over
  -- `[0, 1)` does not see the change of derivative at `1`.
  have hσ1 : (lagrangianCrossingForm (Z 1) (Z'' 1) (vertical ι)).signature =
      (lagrangianCrossingForm (Z 0) (Z' 0) (vertical ι)).signature :=
    heq1.signature_eq.symm
  have hIco : ∑ᶠ t ∈ Ico (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z'' t) (vertical ι)).signature =
      ∑ᶠ t ∈ Ico (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) (vertical ι)).signature :=
    finsum_mem_congr rfl fun t ht ↦ by rw [hZ''t ht.2.ne]
  rw [hσ1, hIco, hZ''t zero_ne_one, sub_self, Int.cast_zero, zero_div, add_zero] at key
  exact_mod_cast key

end LagrangianGrassmannian

end SymplecticGeometry

namespace TauCeti.GLSymplectic

open SymplecticGeometry SymplecticGeometry.LagrangianGrassmannian

/-- **The crossing-form formula for loops of symplectic matrices.** Let `γ` be a loop of
symplectic matrices, given by a `1`-periodic `Ψ = fromBlocks A B C D : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ`
(`γ t = Ψ t` for `t ∈ [0, 1]`). Suppose that at each crossing `t ∈ [0, 1)`, where `B t` is
singular, `Ψ` has derivative `Ψ' t` and the crossing form `y ↦ -⟪D t y, B' t y⟫` on `ker B t`
(the crossing form of the frame `fromRows B D` relative to `{x = 0}`,
`lagrangianCrossingForm_vertical`) is nondegenerate. Then the Maslov index of `γ` is half the sum
of the signatures of these crossing forms over `[0, 1)`. -/
theorem maslovIndex_eq_half_crossing_sum {A : GLSymplectic ι ℝ} (γ : Path A A)
    {Ψ Ψ' : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hγ : ∀ t : I, ((γ t : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = Ψ t)
    (hΨ : Function.Periodic Ψ 1)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, (Ψ t).toBlocks₁₂.det = 0 → HasDerivAt Ψ (Ψ' t) t)
    (hreg : ∀ t ∈ Ico (0 : ℝ) 1, (Ψ t).toBlocks₁₂.det = 0 →
      (lagrangianCrossingForm (fromRows (Ψ t).toBlocks₁₂ (Ψ t).toBlocks₂₂)
        (fromRows (Ψ' t).toBlocks₁₂ (Ψ' t).toBlocks₂₂) (vertical ι)).Nondegenerate) :
    (maslovIndex γ : ℝ) =
      ((∑ᶠ t ∈ Ico (0 : ℝ) 1,
        (lagrangianCrossingForm (fromRows (Ψ t).toBlocks₁₂ (Ψ t).toBlocks₂₂)
          (fromRows (Ψ' t).toBlocks₁₂ (Ψ' t).toBlocks₂₂) (vertical ι)).signature : ℤ) : ℝ) / 2 := by
  have hV : (vertical ι : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows (0 : Matrix ι ι ℝ) 1)) := by
    rw [StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY, StdSpace.graphY_zero, coe_vertical]
  have h := LagrangianGrassmannian.maslovIndex_eq_crossing_sum
    (γ.map (continuous_id.smul continuous_const : Continuous fun B ↦ B • vertical ι))
    (Z := fun t ↦ fromRows (Ψ t).toBlocks₁₂ (Ψ t).toBlocks₂₂)
    (Z' := fun t ↦ fromRows (Ψ' t).toBlocks₁₂ (Ψ' t).toBlocks₂₂) (g := 1)
    (fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, coe_smul_of_coe_eq _ hV, hγ]
      conv_rhs => rw [← fromBlocks_toBlocks (Ψ t), fromBlocks_mul_fromRows]
      simp)
    (fun t ↦ by simp only [hΨ t, Matrix.mul_one])
    (fun t ht h ↦ hasDerivAt_matrix.2 fun i j ↦ by
      have hΨd := hasDerivAt_matrix.1 (hd t ht (by simpa using h))
      rcases i with i | i
      · simpa [toBlocks₁₂] using hΨd (Sum.inl i) (Sum.inr j)
      · simpa [toBlocks₂₂] using hΨd (Sum.inr i) (Sum.inr j))
    (fun t ht h ↦ hreg t ht (by simpa using h))
  rw [maslovIndex_smul_const] at h
  rw [← h]
  push_cast
  ring

end TauCeti.GLSymplectic

namespace SymplecticGeometry

open LagrangianGrassmannian

/-- **The crossing-form formula for the Maslov index.** Both crossing-form formulas for loops:
for a loop `γ` of Lagrangians with a frame `Z = fromRows X Y` that closes up to a constant change
of frame, whose crossings with `{x = 0}` are regular, the Maslov index of `γ` is the sum of the
signatures of the crossing forms `u ↦ -⟪Y u, X' u⟫` on `ker X` over `[0, 1)`
(`LagrangianGrassmannian.maslovIndex_eq_crossing_sum`); and for a loop of symplectic matrices
`Ψ = fromBlocks A B C D` whose crossings are regular, the Maslov index of `Ψ` is half the sum of
the signatures of the crossing forms `y ↦ -⟪D y, B' y⟫` on `ker B` over `[0, 1)`
(`TauCeti.GLSymplectic.maslovIndex_eq_half_crossing_sum`).

Milestone: *Crossing-form formula for the Maslov index*. -/
theorem maslovIndex_eq_crossing_sum_and_half_crossing_sum :
    (∀ {Λ : ℒ ι} (γ : Path Λ Λ) {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ} {g : Matrix ι ι ℝ},
      (∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t) →
      (∀ t, Z (t + 1) = Z t * g) →
      (∀ t ∈ Ico (0 : ℝ) 1, (Z t).toRows₁.det = 0 → HasDerivAt Z (Z' t) t) →
      (∀ t ∈ Ico (0 : ℝ) 1, (Z t).toRows₁.det = 0 →
        (lagrangianCrossingForm (Z t) (Z' t) (vertical ι)).Nondegenerate) →
      maslovIndex γ =
        ∑ᶠ t ∈ Ico (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) (vertical ι)).signature) ∧
    (∀ {A : GLSymplectic ι ℝ} (γ : Path A A) {Ψ Ψ' : ℝ → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ},
      (∀ t : I, ((γ t : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) = Ψ t) →
      Function.Periodic Ψ 1 →
      (∀ t ∈ Ico (0 : ℝ) 1, (Ψ t).toBlocks₁₂.det = 0 → HasDerivAt Ψ (Ψ' t) t) →
      (∀ t ∈ Ico (0 : ℝ) 1, (Ψ t).toBlocks₁₂.det = 0 →
        (lagrangianCrossingForm (fromRows (Ψ t).toBlocks₁₂ (Ψ t).toBlocks₂₂)
          (fromRows (Ψ' t).toBlocks₁₂ (Ψ' t).toBlocks₂₂) (vertical ι)).Nondegenerate) →
      (GLSymplectic.maslovIndex γ : ℝ) =
        ((∑ᶠ t ∈ Ico (0 : ℝ) 1,
          (lagrangianCrossingForm (fromRows (Ψ t).toBlocks₁₂ (Ψ t).toBlocks₂₂)
            (fromRows (Ψ' t).toBlocks₁₂ (Ψ' t).toBlocks₂₂) (vertical ι)).signature : ℤ) : ℝ) / 2) :=
  ⟨fun γ _ _ _ hZ hg hd hreg ↦ maslovIndex_eq_crossing_sum γ hZ hg hd hreg,
    fun γ _ _ hγ hΨ hd hreg ↦ GLSymplectic.maslovIndex_eq_half_crossing_sum γ hγ hΨ hd hreg⟩

end SymplecticGeometry

end
