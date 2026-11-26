/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.DiscreteSubset
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Crossing.Form
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Maslov.Path.Naturality
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Graph
public import TauCeti.Analysis.Matrix.UnitaryGroup.Maslov.Crossing
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The crossing-form formula for paths of Lagrangian subspaces

Let `γ` be a path of Lagrangian subspaces of `(StdSpace ι, ω₀)` with a frame `Z`, so that the
columns of `Z t` span `γ t`, and let `V` be a Lagrangian. Suppose that at each crossing `t`, where
`γ t ∩ V ≠ 0`, the frame has a derivative `Z' t` within `[0, 1]` and the crossing form
`Γ(t) = lagrangianCrossingForm (Z t) (Z' t) V` is nondegenerate. Then the Robbin–Salamon index
`μ(γ, V)` is the sum of the signatures of the crossing forms, the crossings at `0` and `1`
counting one half:

`μ(γ, V) = (sign Γ(0) + sign Γ(1)) / 2 + ∑ᶠ t ∈ (0, 1), sign Γ(t)`.

Away from the crossings `Γ(t)` is zero (`lagrangianCrossingForm_eq_zero_of_inf_eq_bot`), so the
sum runs over the finitely many crossings (`finite_setOfPred_inf_ne_bot_of_regular`).

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.pathMaslovIndex_graph_eq_crossing_sum`: the formula
  when each `γ t` is the graph `{(x, A t x)}`, relative to `{y = 0}`, with Tau Ceti's crossing forms
  `Matrix.crossingForm (A t) (A' t)`.
* `SymplecticGeometry.LagrangianGrassmannian.finite_setOfPred_inf_ne_bot_of_regular`: a path with
  regular crossings has finitely many.
* `SymplecticGeometry.LagrangianGrassmannian.finite_Icc_inter_support_signature_of_regular`: the
  signatures of the crossing forms of such a path are nonzero at finitely many times.
* `SymplecticGeometry.LagrangianGrassmannian.pathMaslovIndex_eq_crossing_sum`: the formula for
  every path with a frame whose crossings are regular, relative to every Lagrangian.
* `SymplecticGeometry.LagrangianGrassmannian.pathMaslovIndex_eq_crossing_sum_Ico`: the same
  formula with the crossing at `0` counted fully and at `1` not at all, plus half the difference
  of the signatures at `1` and at `0`.

## Implementation notes

The graph case is Tau Ceti's
`Matrix.UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley`, read through a
path of unitary frames (`exists_souriau_eq_cayley_and_pathMaslovIndex_eq_maslovIndex`). For a
general path, near each time `t₀` some Lagrangian `W` is transverse to `V` and to `γ t₀`
(`exists_isCompl_isCompl`), and a symplectic matrix carries `V` to `{y = 0}` and `W` to
`{x = 0}` (`exists_smul_eq_horizontal_vertical`). On the open set of times where `γ t` is
transverse to `W`, each moved value `γ t` is the graph `{(x, A t x)}`, with `A = Y X⁻¹` for the
blocks of the moved frame, and `A` is continuous since it is read in the chart `graphChart`
(`continuous_of_coe_eq_graph`). The naturality of the index (`pathMaslovIndex_smul`) and of the
crossing form (`lagrangianCrossingForm_symplectic_mul_equivalent`), and the change of frame from
`fromRows X Y` to `fromRows 1 A` (`lagrangianCrossingForm_mul_equivalent`,
`lagrangianCrossingForm_graph`), carry the formula over. A partition of `[0, 1]` subordinate to
these open sets (`exists_monotone_Icc_subset_open_cover_unitInterval`) cuts `γ` into subpaths,
each reparametrized by `[0, 1]`, and the index adds up over them (`pathMaslovIndex_trans`).

## References

* [J. Robbin and D. Salamon, *The Maslov index for paths*][RobbinSalamon1993], §2 (the
  formula for paths with regular crossings; the reduction to graphs follows the proof of
  Theorem 2.3).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3
  (crossing forms of paths of Lagrangian subspaces).
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set Filter Topology
open scoped unitInterval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Paths of graphs -/

/-- **The crossing-form formula for paths of graphs.** Let `γ` be a path of Lagrangians that are
the graphs `{(x, A t x)}` of matrices `A t`. Suppose that at each `t ∈ [0, 1]` where `A t` is
singular, that is, where `γ t` meets `{y = 0}`, `A` has derivative `A' t` within `[0, 1]` and
Tau Ceti's crossing form `Matrix.crossingForm (A t) (A' t)` is nondegenerate. Then the index of
`γ` relative to `{y = 0}` is the sum of the signatures of the crossing forms, those at `0` and
`1` counting one half. -/
theorem pathMaslovIndex_graph_eq_crossing_sum {Λ Λ' : ℒ ι} (γ : Path Λ Λ')
    {A A' : ℝ → Matrix ι ι ℝ}
    (hγ : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 → HasDerivWithinAt A (A' t) (Icc 0 1) t)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det = 0 → (crossingForm (A t) (A' t)).Nondegenerate) :
    pathMaslovIndex γ (horizontal ι) =
      (((crossingForm (A 0) (A' 0)).signature + (crossingForm (A 1) (A' 1)).signature :
          ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, (crossingForm (A t) (A' t)).signature : ℤ) : ℝ) := by
  have hAc : ContinuousOn A (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_of_coe_eq_graph γ.continuous hγ
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).IsHermitian :=
    isHermitian_of_coe_eq_graph (hγ ⟨t, ht⟩)
  obtain ⟨_, _, δ, hδ, h⟩ := exists_souriau_eq_cayley_and_pathMaslovIndex_eq_maslovIndex γ
    (A := fun t : I ↦ A t) hγ
  rw [h]
  simpa only [QuadraticForm.signature_def] using
    UnitaryGroup.maslovIndex_eq_crossingForm_add_finsum_of_souriau_eq_cayley δ hAc hA hδ
      (fun t ht h ↦ (hd t ht h).matrix_elem) hreg

/-- Two integer weightings of `[0, 1]` that agree there give the same crossing sum. -/
private theorem crossing_sum_congr {f g : ℝ → ℤ} (h : ∀ t ∈ Icc (0 : ℝ) 1, f t = g t) :
    ((f 0 + f 1 : ℤ) : ℝ) / 2 + ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, f t : ℤ) : ℝ) =
      ((g 0 + g 1 : ℤ) : ℝ) / 2 + ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, g t : ℤ) : ℝ) := by
  rw [h 0 (left_mem_Icc.2 zero_le_one), h 1 (right_mem_Icc.2 zero_le_one),
    finsum_mem_congr rfl fun t ht ↦ h t (Ioo_subset_Icc_self ht)]

/-- The crossing-form formula relative to `{y = 0}` for a path transverse to `{x = 0}`: it is the
path of graphs of `A = Y X⁻¹`, for the blocks `fromRows X Y` of its frame. -/
private theorem crossing_sum_of_isCompl_vertical {Λ Λ' : ℒ ι} (γ : Path Λ Λ')
    {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hW : ∀ t : I, IsCompl (γ t : Submodule ℝ (StdSpace ι)) (vertical ι))
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) (horizontal ι)).Nondegenerate) :
    pathMaslovIndex γ (horizontal ι) =
      (((lagrangianCrossingForm (Z 0) (Z' 0) (horizontal ι)).signature +
          (lagrangianCrossingForm (Z 1) (Z' 1) (horizontal ι)).signature : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1,
          (lagrangianCrossingForm (Z t) (Z' t) (horizontal ι)).signature : ℤ) : ℝ) := by
  -- The blocks `Z t = fromRows (X t) (Y t)`; `X t` is invertible since `γ t` is transverse to
  -- `{x = 0}`, and `γ t` is the graph of `A t = Y t (X t)⁻¹`.
  set X : ℝ → Matrix ι ι ℝ := fun r ↦ (Z r).toRows₁
  set Y : ℝ → Matrix ι ι ℝ := fun r ↦ (Z r).toRows₂
  have hZXY (r : ℝ) : Z r = fromRows (X r) (Y r) := (fromRows_toRows _).symm
  have hX (t : I) : IsUnit (X t) :=
    (mem_graphChart_source_iff_isUnit (by rw [← hZXY, hZ t])).1
      (by rw [graphChart_source, mem_ofPred_eq]; exact hW t)
  set A : ℝ → Matrix ι ι ℝ := fun r ↦ Y r * (X r)⁻¹
  have hZA (t : I) : Z t * (X t)⁻¹ = fromRows 1 (A t) := by
    rw [hZXY, fromRows_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (hX t))]
  have hγA (t : I) : (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t) := by
    rw [← hZ t, hZXY, StdSpace.range_toEuclideanLin_fromRows_eq_graph (hX t)]
  -- The derivative of `A`, from those of the blocks, and the frame `fromRows 1 A` with it.
  set h' : ℝ → Matrix ι ι ℝ := fun r ↦ -((X r)⁻¹ * (Z' r).toRows₁ * (X r)⁻¹)
  set A' : ℝ → Matrix ι ι ℝ := fun r ↦ (Z' r).toRows₂ * (X r)⁻¹ + Y r * h' r
  have hZ' (r : ℝ) : Z' r * (X r)⁻¹ + Z r * h' r =
      fromRows ((Z' r).toRows₁ * (X r)⁻¹ + X r * h' r) (A' r) := by
    conv_lhs => rw [hZXY r, ← fromRows_toRows (Z' r)]
    rw [fromRows_mul, fromRows_mul]
    ext (i | i) j <;> simp [A']
  -- Where `A t` is singular, `γ t` meets `{y = 0}`.
  have hcross (t : I) (h : (A t).det = 0) :
      (γ t : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι ≠ ⊥ := by
    have h' := (mem_graphYChart_source_iff_isUnit
      ((hγA t).trans (StdSpace.range_toEuclideanLin_fromRows_one_eq_graph _).symm)).not
    rw [graphYChart_source, mem_ofPred_eq, isCompl_iff_disjoint, disjoint_iff,
      isUnit_iff_isUnit_det, h] at h'
    exact h'.2 not_isUnit_zero
  have hdA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (h : (A t).det = 0) :
      HasDerivWithinAt A (A' t) (Icc 0 1) t := by
    have hZd := hd ⟨t, ht⟩ (hcross ⟨t, ht⟩ h)
    have hXd : HasDerivWithinAt X (Z' t).toRows₁ (Icc 0 1) t :=
      hasDerivWithinAt_matrix.2 fun i j ↦ hZd.matrix_elem (Sum.inl i) j
    have hYd : HasDerivWithinAt Y (Z' t).toRows₂ (Icc 0 1) t :=
      hasDerivWithinAt_matrix.2 fun i j ↦ hZd.matrix_elem (Sum.inr i) j
    exact hYd.matrix_mul (hXd.matrix_inv (hX ⟨t, ht⟩))
  -- The crossing forms of `Z` and of `A` agree up to isometry.
  have heq (t : I) : (lagrangianCrossingForm (Z t) (Z' t) (horizontal ι)).Equivalent
      (crossingForm (A t) (A' t)) := by
    have hiso : (stdForm ι).IsIsotropic (LinearMap.range (toEuclideanLin (Z t))) := by
      rw [hZ t]; exact (γ t).isLagrangian.isIsotropic
    have h := lagrangianCrossingForm_mul_equivalent hiso (Z' t) (horizontal ι)
      (isUnit_nonsing_inv_iff.2 (hX t)).unit (h' t)
    rw [IsUnit.unit_spec, hZ', hZA] at h
    exact h.trans (lagrangianCrossingForm_graph _ _ _)
  have hregA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (h : (A t).det = 0) :
      (crossingForm (A t) (A' t)).Nondegenerate :=
    (Classical.choice (heq ⟨t, ht⟩)).nondegenerate_iff.1 (hreg ⟨t, ht⟩ (hcross ⟨t, ht⟩ h))
  have hσ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (crossingForm (A t) (A' t)).signature =
      (lagrangianCrossingForm (Z t) (Z' t) (horizontal ι)).signature :=
    (heq ⟨t, ht⟩).symm.signature_eq
  have hsum := crossing_sum_congr hσ
  exact (pathMaslovIndex_graph_eq_crossing_sum γ hγA hdA hregA).trans hsum

/-! ### Paths in one chart, and subpaths -/

/-- The crossing-form formula for a path whose values are all transverse to a Lagrangian `W`
transverse to `V`: move `V` to `{y = 0}` and `W` to `{x = 0}` by a symplectic matrix. -/
private theorem crossing_sum_of_isCompl {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {V W : ℒ ι}
    (hVW : IsCompl (V : Submodule ℝ (StdSpace ι)) W) {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hW : ∀ t : I, IsCompl (γ t : Submodule ℝ (StdSpace ι)) W)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) :
    pathMaslovIndex γ V =
      (((lagrangianCrossingForm (Z 0) (Z' 0) V).signature +
          (lagrangianCrossingForm (Z 1) (Z' 1) V).signature : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) V).signature : ℤ) : ℝ) := by
  obtain ⟨g, hgV, hgW⟩ := exists_smul_eq_horizontal_vertical hVW
  have hΨV : g⁻¹ • V = horizontal ι := by rw [← hgV, inv_smul_smul]
  have hΨW : g⁻¹ • W = vertical ι := by rw [← hgW, inv_smul_smul]
  set M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
    (((g⁻¹ : GLSymplectic ι ℝ) : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
  have hM : M ∈ symplecticGroup ι ℝ := GLSymplectic.mem_iff_mem_symplecticGroup.1 g⁻¹.property
  have hMV : (V : Submodule ℝ (StdSpace ι)).map (toEuclideanLin M) = horizontal ι := by
    rw [← hΨV, coe_smul]
  have hcross (t : I) : ((g⁻¹ • γ t : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι ≠ ⊥ ↔
      (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ := by
    rw [Ne, Ne, ← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, ← hΨV,
      finrank_smul_inf_smul]
  have heq (t : ℝ) : (lagrangianCrossingForm (Z t) (Z' t) V).Equivalent
      (lagrangianCrossingForm (M * Z t) (M * Z' t) (horizontal ι)) := by
    rw [← hMV]
    exact lagrangianCrossingForm_symplectic_mul_equivalent hM (Z t) (Z' t) V
  have key := crossing_sum_of_isCompl_vertical (γ.map (continuous_const_smul g⁻¹))
    (Z := fun r ↦ M * Z r) (Z' := fun r ↦ M * Z' r)
    (fun t ↦ (coe_smul_of_coe_eq g⁻¹ (hZ t).symm).symm)
    (fun t ↦ by rw [Path.map_coe, Function.comp_apply, ← hΨW, isCompl_smul_iff]; exact hW t)
    (fun t h ↦ by
      simpa using (hasDerivWithinAt_matrix_const M _ _).matrix_mul (hd t ((hcross t).1 h)))
    (fun t h ↦ (Classical.choice (heq t)).nondegenerate_iff.1 (hreg t ((hcross t).1 h)))
  have hσ (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      (lagrangianCrossingForm (M * Z t) (M * Z' t) (horizontal ι)).signature =
        (lagrangianCrossingForm (Z t) (Z' t) V).signature :=
    (heq t).symm.signature_eq
  have hsum := crossing_sum_congr hσ
  rw [← pathMaslovIndex_smul g⁻¹ γ V, hΨV]
  exact key.trans hsum

/-- The crossing-form formula on the subpath `γ|[a, b]`, for `a < b`, when `γ` is transverse on
`[a, b]` to a Lagrangian `W` transverse to `V`: reparametrize `[a, b]` by `[0, 1]`, which scales
the derivative, and so the crossing forms, by `b - a > 0`. -/
private theorem crossing_sum_subpath {Λ Λ' : ℒ ι} (γ : Path Λ Λ') {V W : ℒ ι}
    (hVW : IsCompl (V : Submodule ℝ (StdSpace ι)) W) {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate)
    {a b : I} (hab : a < b) (hW : ∀ t ∈ Icc a b, IsCompl (γ t : Submodule ℝ (StdSpace ι)) W) :
    pathMaslovIndex (γ.subpath a b) V =
      (((lagrangianCrossingForm (Z a) (Z' a) V).signature +
          (lagrangianCrossingForm (Z b) (Z' b) V).signature : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (a : ℝ) b, (lagrangianCrossingForm (Z t) (Z' t) V).signature : ℤ) : ℝ) := by
  have hba : (0 : ℝ) < b - a := sub_pos.2 (Subtype.coe_lt_coe.2 hab)
  -- The affine reparametrization `φ` of `[a, b]` by `[0, 1]`, which `Path.subpath` uses.
  set φ : ℝ → ℝ := fun r ↦ (1 - r) * a + r * b
  have hφ (s : I) : φ s = (Icc.convexComb a b s : ℝ) := (Icc.coe_convexComb a b s).symm
  have hsub (s : I) : γ.subpath a b s = γ (Icc.convexComb a b s) := by simp [Path.subpath]
  have hmem (s : I) : Icc.convexComb a b s ∈ Icc a b := by
    constructor <;> rw [← Subtype.coe_le_coe, ← hφ] <;> simp only [φ] <;>
      nlinarith [s.property.1, s.property.2]
  have hφd (r : ℝ) : HasDerivAt φ (b - a) r := by
    have h := ((hasDerivAt_id r).mul_const ((b : ℝ) - a)).const_add (a : ℝ)
    convert h using 1
    · funext r; simp only [φ, id]; ring
    · simp
  have hmaps : MapsTo φ (Icc 0 1) (Icc 0 1) := fun r hr ↦ by
    constructor <;> simp only [φ] <;>
      nlinarith [a.property.1, a.property.2, b.property.1, b.property.2, hr.1, hr.2]
  have hcross (s : I) (h : ((γ.subpath a b s : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥) :
      (γ (Icc.convexComb a b s) : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ := by
    rwa [hsub] at h
  have key := crossing_sum_of_isCompl (γ.subpath a b) hVW (Z := fun r ↦ Z (φ r))
    (Z' := fun r ↦ ((b : ℝ) - a) • Z' (φ r))
    (fun s ↦ by rw [hsub, hφ]; exact hZ _)
    (fun s ↦ by rw [hsub]; exact hW _ (hmem s))
    (fun s h ↦ by
      have hd' := hd _ (hcross s h)
      rw [← hφ] at hd'
      exact hasDerivWithinAt_matrix.2 fun i j ↦
        (hd'.matrix_elem i j).scomp (s : ℝ) (hφd s).hasDerivWithinAt hmaps)
    (fun s h ↦ by
      rw [lagrangianCrossingForm_smul, QuadraticMap.nondegenerate_smul_iff hba.ne'.isUnit, hφ]
      exact hreg _ (hcross s h))
  have hσ (r : ℝ) : (lagrangianCrossingForm (Z (φ r)) (((b : ℝ) - a) • Z' (φ r)) V).signature =
      (lagrangianCrossingForm (Z (φ r)) (Z' (φ r)) V).signature := by
    rw [lagrangianCrossingForm_smul, QuadraticForm.signature_smul_of_pos _ hba]
  have hbij : BijOn φ (Ioo 0 1) (Ioo (a : ℝ) b) := by
    refine ⟨fun r hr ↦ ?_, fun r _ r' _ h ↦ ?_, fun t ht ↦ ?_⟩
    · constructor <;> simp only [φ] <;> nlinarith [hr.1, hr.2]
    · have h' : r * (b - a) = r' * (b - a) := by simp only [φ] at h; linear_combination h
      exact mul_right_cancel₀ hba.ne' h'
    · refine ⟨(t - a) / (b - a), ⟨div_pos (sub_pos.2 ht.1) hba,
        (div_lt_one hba).2 (by linarith [ht.2])⟩, ?_⟩
      simp only [φ]
      field_simp
      ring
  have h0 : φ 0 = a := by simp [φ]
  have h1 : φ 1 = b := by simp [φ]
  rw [key, hσ, hσ, finsum_mem_congr rfl fun r _ ↦ hσ r,
    finsum_mem_eq_of_bijOn φ hbij (g := fun t ↦ (lagrangianCrossingForm (Z t) (Z' t) V).signature)
      fun _ _ ↦ rfl, h0, h1]

/-! ### The crossing-form formula -/

/-- **Regular crossings are finitely many.** Let `Z` be a frame of a path `γ` of Lagrangians,
differentiable within `[0, 1]` at each crossing with a Lagrangian `V`, with nondegenerate crossing
forms there. Then `γ` meets `V` at only finitely many times. -/
theorem finite_setOfPred_inf_ne_bot_of_regular {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι)
    {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) :
    {t : I | (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥}.Finite := by
  -- The times transverse to `V` are open, and every time has a punctured neighbourhood of them.
  have hopen : IsOpen {t : I | (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥} := by
    have h : {t : I | (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥} =
        γ ⁻¹' {Λ | IsCompl (Λ : Submodule ℝ (StdSpace ι)) V} := by
      ext t
      rw [mem_preimage, mem_ofPred_eq, mem_ofPred_eq, isCompl_iff_disjoint, disjoint_iff]
    rw [h]
    exact (isOpen_setOfPred_isCompl V).preimage γ.continuous
  have h : ∀ᶠ t in codiscrete I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥ := by
    rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro t₀
    by_cases h₀ : (γ t₀ : Submodule ℝ (StdSpace ι)) ⊓ V = ⊥
    · exact eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds h₀)
    · exact eventually_not_crossing_of_regular γ V hZ (hd t₀ h₀) (hreg t₀ h₀)
  rw [codiscrete_eq_cofinite] at h
  exact Filter.eventually_cofinite.1 h

/-- **Regular crossings have finitely many nonzero signatures.** Under the hypotheses of
`finite_setOfPred_inf_ne_bot_of_regular`, the signature of the crossing form
`lagrangianCrossingForm (Z t) (Z' t) V` is nonzero at only finitely many times `t ∈ [0, 1]`. -/
theorem finite_Icc_inter_support_signature_of_regular {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι)
    {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) :
    (Icc (0 : ℝ) 1 ∩
      Function.support fun t ↦ (lagrangianCrossingForm (Z t) (Z' t) V).signature).Finite :=
  ((finite_setOfPred_inf_ne_bot_of_regular γ V hZ hd hreg).image ((↑) : I → ℝ)).subset
    fun t ⟨ht, hst⟩ ↦ ⟨⟨t, ht⟩, fun h ↦
      hst ((congrArg QuadraticForm.signature
        (lagrangianCrossingForm_eq_zero_of_inf_eq_bot (by rwa [hZ ⟨t, ht⟩]) _)).trans
          QuadraticForm.signature_zero), rfl⟩

/-- **The crossing-form formula for paths, with the crossing at `0` counted fully.** Under the
hypotheses of `pathMaslovIndex_eq_crossing_sum`, the index of `γ` relative to `V` is the sum of
the signatures of the crossing forms over `[0, 1)`, plus half the difference of the signatures
at `1` and at `0`. -/
theorem pathMaslovIndex_eq_crossing_sum_Ico {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι)
    {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) :
    pathMaslovIndex γ V =
      ((∑ᶠ t ∈ Ico (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) V).signature : ℤ) : ℝ) +
        (((lagrangianCrossingForm (Z 1) (Z' 1) V).signature -
            (lagrangianCrossingForm (Z 0) (Z' 0) V).signature : ℤ) : ℝ) / 2 := by
  set sgn : ℝ → ℤ := fun t ↦ (lagrangianCrossingForm (Z t) (Z' t) V).signature with hsgn
  have hsupp {s : Set ℝ} (hs : s ⊆ Icc 0 1) : (s ∩ Function.support sgn).Finite :=
    (finite_Icc_inter_support_signature_of_regular γ V hZ hd hreg).subset
      (inter_subset_inter_left _ hs)
  -- The crossing sum of `[a, b]` with weight one at `a` and none at `b`, corrected to half
  -- weights at both ends; unlike the sum with half weights, it is additive over adjacent
  -- intervals, also empty ones.
  let F (a b : I) : ℝ := ((∑ᶠ t ∈ Ico (a : ℝ) b, sgn t : ℤ) : ℝ) + ((sgn b - sgn a : ℤ) : ℝ) / 2
  have hF {a b c : I} (hab : a ≤ b) (hbc : b ≤ c) : F a b + F b c = F a c := by
    have hs (x y : I) : Ico (x : ℝ) y ⊆ Icc 0 1 :=
      Ico_subset_Icc_self.trans (Icc_subset_Icc x.property.1 y.property.2)
    simp only [F]
    rw [← Ico_union_Ico_eq_Ico (Subtype.coe_le_coe.2 hab) (Subtype.coe_le_coe.2 hbc),
      finsum_mem_union' Ico_disjoint_Ico_same (hsupp (hs a b)) (hsupp (hs b c))]
    push_cast
    ring
  have hF0 (a : I) : F a a = 0 := by
    simp only [F, Ico_self, finsum_mem_empty, Int.cast_zero, sub_self, zero_div, add_zero]
  -- On an interval where `γ` is transverse to one Lagrangian transverse to `V`, the index of
  -- the subpath is `F`.
  have hloc {a b : I} (hab : a ≤ b) {W : ℒ ι} (hVW : IsCompl (V : Submodule ℝ (StdSpace ι)) W)
      (hW : ∀ t ∈ Icc a b, IsCompl (γ t : Submodule ℝ (StdSpace ι)) W) :
      pathMaslovIndex (γ.subpath a b) V = F a b := by
    rcases hab.eq_or_lt with rfl | hab
    · rw [Path.subpath_self, pathMaslovIndex_refl, hF0]
    · simp only [F]
      rw [crossing_sum_subpath γ hVW hZ hd hreg hab hW,
        ← insert_left_Ioo (Subtype.coe_lt_coe.2 hab),
        finsum_mem_insert' sgn left_notMem_Ioo
          (hsupp (Ioo_subset_Icc_self.trans (Icc_subset_Icc a.property.1 b.property.2)))]
      simp only [hsgn]
      push_cast
      ring
  -- Cut `[0, 1]` into pieces on each of which `γ` is transverse to one Lagrangian `W t₀`, and add
  -- up the pieces.
  choose W hWV hWγ using fun t : I ↦ exists_isCompl_isCompl V (γ t)
  obtain ⟨T, hT0, hTm, ⟨m, hm⟩, hTc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun t₀ : I ↦ {t : I | IsCompl (γ t : Submodule ℝ (StdSpace ι)) (W t₀)})
    (fun t₀ ↦ (isOpen_setOfPred_isCompl (W t₀)).preimage γ.continuous)
    (fun t _ ↦ mem_iUnion.2 ⟨t, (hWγ t).symm⟩)
  have hind (n : ℕ) : pathMaslovIndex (γ.subpath 0 (T n)) V = F 0 (T n) := by
    induction n with
    | zero => rw [hT0, Path.subpath_self, pathMaslovIndex_refl, hF0]
    | succ n ih =>
      obtain ⟨i, hi⟩ := hTc n
      rw [← pathMaslovIndex_eq_of_homotopic
          (Path.Homotopic.subpath_trans_subpath γ 0 (T n) (T (n + 1))) V,
        pathMaslovIndex_trans, ih, hloc (hTm n.le_succ) (hWV i).symm fun t ht ↦ hi ht,
        hF (T n).property.1 (hTm n.le_succ)]
  have h1 := hind m
  rw [hm m le_rfl, Path.subpath_zero_one, pathMaslovIndex_congr _ γ (fun t ↦ by simp) V] at h1
  rw [h1]
  simp only [F, Icc.coe_zero, Icc.coe_one, hsgn]

/-- **The crossing-form formula for paths.** Let `γ` be a path of Lagrangians and `Z` a frame of
it: the columns of `Z t` span `γ t`, for `t ∈ [0, 1]`. Suppose that at each crossing `t` with a
Lagrangian `V`, where `γ t ∩ V ≠ 0`, `Z` has derivative `Z' t` within `[0, 1]` and the crossing
form `lagrangianCrossingForm (Z t) (Z' t) V` is nondegenerate. Then the index of `γ` relative to
`V` is the sum of the signatures of the crossing forms, those at `0` and `1` counting one half.
Away from the crossings the forms are zero (`lagrangianCrossingForm_eq_zero_of_inf_eq_bot`), and
the crossings are finitely many (`finite_setOfPred_inf_ne_bot_of_regular`). -/
theorem pathMaslovIndex_eq_crossing_sum {Λ Λ' : ℒ ι} (γ : Path Λ Λ') (V : ℒ ι)
    {Z Z' : ℝ → Matrix (ι ⊕ ι) ι ℝ}
    (hZ : ∀ t : I, LinearMap.range (toEuclideanLin (Z t)) = γ t)
    (hd : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      HasDerivWithinAt Z (Z' t) (Icc 0 1) t)
    (hreg : ∀ t : I, (γ t : Submodule ℝ (StdSpace ι)) ⊓ V ≠ ⊥ →
      (lagrangianCrossingForm (Z t) (Z' t) V).Nondegenerate) :
    pathMaslovIndex γ V =
      (((lagrangianCrossingForm (Z 0) (Z' 0) V).signature +
          (lagrangianCrossingForm (Z 1) (Z' 1) V).signature : ℤ) : ℝ) / 2 +
        ((∑ᶠ t ∈ Ioo (0 : ℝ) 1, (lagrangianCrossingForm (Z t) (Z' t) V).signature : ℤ) : ℝ) := by
  rw [pathMaslovIndex_eq_crossing_sum_Ico γ V hZ hd hreg, ← insert_left_Ioo zero_lt_one,
    finsum_mem_insert' _ left_notMem_Ioo
      ((finite_Icc_inter_support_signature_of_regular γ V hZ hd hreg).subset
        (inter_subset_inter_left _ Ioo_subset_Icc_self))]
  push_cast
  ring


end LagrangianGrassmannian

end SymplecticGeometry

end
