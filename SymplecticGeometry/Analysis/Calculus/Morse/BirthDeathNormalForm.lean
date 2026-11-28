/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import SymplecticGeometry.Analysis.Calculus.Morse.CubicNormalForm
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Slice
import TauCeti.Analysis.Calculus.Morse.Cerf.Splitting

/-!
# The birth–death normal form in a chart of a normed space

Let `F : E → ℝ` be smooth near a critical point `u` of a finite-dimensional real normed space,
let the kernel of its Hessian at `u` be the line `ℝ ∙ e`, and let the cubic term
`D³F(u)(e, e, e)` be nonzero. Then, in a smooth chart `Φ` of `E` centred at `u`, with values in
`ℝ × ℝᵐ` where `m + 1 = dim E`,

`F y = F u + (Φ y).1 ^ 3 / 3 + ∑ i, σ i * (Φ y).2 i ^ 2`

with signs `σ i = ±1`
(`ContDiffOn.exists_openPartialHomeomorph_eq_add_pow_three_div_three_add_sum_sq`). This is the
normal form of a function at a birth–death point of Cerf, without the parameter of the family.

The proof has three steps.

1. Tau Ceti's splitting lemma for families,
   `TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton`, applied to the constant
   family `fun _ ↦ F`, gives a chart in which `F (u + a • e + w)` is `g a` plus a sum of squares
   with signs, for a reduced function `g` of one variable and `w` in the kernel of a functional
   `ℓ` with `ℓ e = 1`. The function `g` has vanishing first and second derivatives at `0`, and
   its third derivative there is the cubic term of `F` along `e`.
2. The one-variable normal form `ContDiffOn.exists_openPartialHomeomorph_eq_pow_three_div_three`
   writes `g - g 0` as `φ ^ 3 / 3` for a local diffeomorphism `φ` of `ℝ`.
3. The chart `Φ` is the composite of the affine coordinates `y ↦ (ℓ (y - u), (y - u) -
   ℓ (y - u) • e)` of `E`, the slice of the splitting chart at the parameter `0`
   (`OpenPartialHomeomorph.exists_slice_prod_of_fst_eq`), and `φ` on the first coordinate.

## Main results

* `ContDiffOn.exists_openPartialHomeomorph_eq_add_pow_three_div_three_add_sum_sq`: the
  birth–death normal form of `F` near `u`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
-/

public section

open Set Topology Module
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Steps 1 and 2: the splitting chart of the constant family `fun _ ↦ F`, and the cubic normal
form `φ` of its reduced function, combined on the slice of parameter `0`. -/
private theorem exists_splitting_chart_and_cubic {F : E → ℝ} {u e : E} {W : Set E}
    {ℓ : StrongDual ℝ E} (hF : ContDiffOn ℝ ∞ F W) (hW : W ∈ 𝓝 u) (hc : fderiv ℝ F u = 0)
    (hker : (fderiv ℝ (fderiv ℝ F) u).ker = ℝ ∙ e) (hℓ : ℓ e = 1)
    (h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ F)) u e e e ≠ 0) :
    ∃ (ψ : OpenPartialHomeomorph ((ℝ × ℝ) × ℓ.ker)
        ((ℝ × ℝ) × EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker)))) (φ : OpenPartialHomeomorph ℝ ℝ),
      ((0, 0), 0) ∈ ψ.source ∧ ψ ((0, 0), 0) = ((0, 0), 0) ∧
      (∀ z, (ψ z).1 = z.1) ∧ (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      0 ∈ φ.source ∧ φ 0 = 0 ∧ ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ∀ a w, ((0, a), w) ∈ ψ.source → a ∈ φ.source →
        F (u + a • e + w) = F u + φ a ^ 3 / 3 + ∑ i,
          (if i.val < TauCeti.morseIndex F u then -1 else 1) * (ψ ((0, a), w)).2 i ^ 2 := by
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) + 3 = ∞ := by
    rw [← WithTop.coe_ofNat, ← WithTop.coe_add, top_add]
  obtain ⟨g, ψ, hψ0, hψ00, hψ1, hψ1', hψ, hψsymm, hψF, -, hg1, hg2, hg3, -⟩ :=
    TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton (f := fun _ ↦ F) (t := 0)
      (n := ⊤) (W := univ ×ˢ W) (prod_mem_nhds Filter.univ_mem hW)
      (by rw [hinf]; exact hF.comp contDiffOn_snd fun p hp ↦ hp.2) hc hker hℓ (by simp)
  simp only at hψF hg3
  -- The value of the reduced function at `0`.
  have hg00 : g 0 0 = F u := by
    have := hψF _ hψ0
    simp only [hψ00, zero_smul, add_zero] at this
    simpa using this.symm
  -- The reduced function is smooth near `0`, since it differs from `a ↦ F (u + a • e)` by a
  -- smooth function there.
  set S : Set ℝ := {a | ((0, a), (0 : ℓ.ker)) ∈ ψ.source ∧ u + a • e ∈ interior W}
  have hSo : IsOpen S :=
    (ψ.open_source.preimage (by fun_prop)).inter (isOpen_interior.preimage (by fun_prop))
  have hS0 : (0 : ℝ) ∈ S := ⟨hψ0, by simpa using mem_interior_iff_mem_nhds.2 hW⟩
  have hgS : ContDiffOn ℝ ∞ (g 0) S := by
    have hG : ContDiffOn ℝ ∞ (fun a : ℝ ↦ F (u + a • e) - ∑ i,
        (if i.val < TauCeti.morseIndex F u then -1 else 1) *
          (ψ ((0, a), (0 : ℓ.ker))).2 i ^ 2) S := by
      refine ContDiffOn.sub ((hF.mono interior_subset).comp (f := fun a : ℝ ↦ u + a • e)
        (by fun_prop) fun a ha ↦ ha.2) ?_
      refine ContDiffOn.sum fun i _ ↦ contDiffOn_const.mul (ContDiffOn.pow ?_ 2)
      exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn
        (contDiffOn_snd.comp (hψ.comp (s := S) (f := fun a : ℝ ↦ ((0, a), (0 : ℓ.ker)))
          (by fun_prop) fun a ha ↦ ha.1) (mapsTo_univ _ _))
    refine hG.congr fun a ha ↦ ?_
    have := hψF _ ha.1
    simp only [ZeroMemClass.coe_zero, add_zero] at this
    rw [this]
    ring
  -- The cubic normal form of the reduced function.
  have hD : fderiv ℝ (fun a ↦ g 0 a - g 0 0) = fderiv ℝ (g 0) :=
    funext fun _ ↦ fderiv_sub_const _
  obtain ⟨φ, hφ0, -, hφ00, hφ, hφsymm, hφg⟩ :=
    ContDiffOn.exists_openPartialHomeomorph_eq_pow_three_div_three (n := ⊤)
      (g := fun a ↦ g 0 a - g 0 0) (by rw [WithTop.coe_add, ← hinf]; exact hgS.sub contDiffOn_const)
      (hSo.mem_nhds hS0) (by simp) (sub_self _) (by rw [hD, hg1]) (by rw [hD, hg2])
      (by rw [hD, hg3]; exact h3)
  refine ⟨ψ, φ, hψ0, hψ00, hψ1, hψ1', hψ, hψsymm, hφ0, hφ00, hφ, hφsymm, fun a w hz ha ↦ ?_⟩
  rw [hψF _ hz, ← sub_add_cancel (g 0 a) (g 0 0), hφg a ha, hg00]
  ring

/-- **The birth–death normal form in a chart.** Let `F : E → ℝ` be smooth on a neighbourhood of
a critical point `u` of a finite-dimensional real normed space `E`, such that the kernel of the
Hessian `D²F(u)` is the line spanned by `e` and the cubic term `D³F(u)(e, e, e)` is nonzero. Then
there are a smooth chart `Φ` of `E` with values in `ℝ × ℝᵐ`, where `m + 1 = dim E`, with
`Φ u = 0` and a smooth inverse, and signs `σ i = ±1`, such that on the source of `Φ`

`F y = F u + (Φ y).1 ^ 3 / 3 + ∑ i, σ i * (Φ y).2 i ^ 2`. -/
theorem ContDiffOn.exists_openPartialHomeomorph_eq_add_pow_three_div_three_add_sum_sq
    {F : E → ℝ} {u e : E} {W : Set E} (hF : ContDiffOn ℝ ∞ F W) (hW : W ∈ 𝓝 u)
    (hc : fderiv ℝ F u = 0) (hker : (fderiv ℝ (fderiv ℝ F) u).ker = ℝ ∙ e)
    (h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ F)) u e e e ≠ 0) :
    ∃ (m : ℕ) (σ : Fin m → ℝ) (Φ : OpenPartialHomeomorph E (ℝ × EuclideanSpace ℝ (Fin m))),
      m + 1 = finrank ℝ E ∧ (∀ i, σ i = -1 ∨ σ i = 1) ∧ u ∈ Φ.source ∧ Φ u = 0 ∧
      ContDiffOn ℝ ∞ Φ Φ.source ∧ ContDiffOn ℝ ∞ Φ.symm Φ.target ∧
      ∀ y ∈ Φ.source, F y = F u + (Φ y).1 ^ 3 / 3 + ∑ i, σ i * (Φ y).2 i ^ 2 := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) he
  obtain ⟨ψ, φ, hψ0, hψ00, hψ1, hψ1', hψ, hψsymm, hφ0, hφ00, hφ, hφsymm, hFψ⟩ :=
    exists_splitting_chart_and_cubic hF hW hc hker hℓ h3
  -- The slice of the splitting chart at the parameter `0`.
  obtain ⟨ψ₀, hψ₀s, hψ₀t, hψ₀, hψ₀symm⟩ := ψ.exists_slice_prod_of_fst_eq (fun z _ ↦ hψ1 z) hψ1' 0
  -- Linear coordinates `y ↦ (ℓ y, y - ℓ y • e)` on `E`.
  let P₀ : E ≃ₗ[ℝ] ℝ × ℓ.ker :=
    { toFun y := (ℓ y, ⟨y - ℓ y • e, by simp [hℓ]⟩)
      map_add' y z := by ext <;> simp [add_smul]; abel
      map_smul' c y := by ext <;> simp [smul_sub, smul_smul]
      invFun p := p.1 • e + p.2
      left_inv y := by simp
      right_inv p := by
        have hp : ℓ p.2 = 0 := p.2.property
        ext <;> simp [hℓ, hp] }
  set P := P₀.toContinuousLinearEquiv
  have hP (y : E) : P y = (ℓ y, ⟨y - ℓ y • e, by simp [hℓ]⟩) := by simp [P, P₀]
  have hPsymm (p : ℝ × ℓ.ker) : P.symm p = p.1 • e + p.2 := by simp [P, P₀]
  -- The chart, and formulas for it, its inverse, its source and its target.
  set Φ := (((Homeomorph.subRight u).trans P.toHomeomorph).toOpenPartialHomeomorph.trans ψ₀).trans
    (φ.prod (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker)))))
  have hΦ (y : E) : Φ y = (φ (ℓ (y - u)), (ψ ((0, ℓ (y - u)), (P (y - u)).2)).2) := by
    simp [Φ, hψ₀, hψ1, hP]
  have hΦs (y : E) : y ∈ Φ.source ↔
      ((0, ℓ (y - u)), (P (y - u)).2) ∈ ψ.source ∧ ℓ (y - u) ∈ φ.source := by
    simp [Φ, hψ₀, hψ₀s, hψ1, hP]
  have hΦsymm (q : ℝ × EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker))) : Φ.symm q =
      u + (ψ.symm ((0, φ.symm q.1), q.2)).1.2 • e + (ψ.symm ((0, φ.symm q.1), q.2)).2 := by
    simp [Φ, hψ₀symm, hPsymm]
    abel
  have hΦt (q : ℝ × EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker))) :
      q ∈ Φ.target ↔ q.1 ∈ φ.target ∧ ((0, φ.symm q.1), q.2) ∈ ψ.target := by
    simp [Φ, hψ₀t]
  have hsub : ContDiff ℝ ∞ fun y : E ↦ y - u := contDiff_id.sub contDiff_const
  refine ⟨finrank ℝ ℓ.ker, fun i ↦ if i.val < TauCeti.morseIndex F u then -1 else 1, Φ, ?_,
    fun i ↦ ?_,
    (hΦs u).2 ⟨by simpa using hψ0, by simpa using hφ0⟩, by simp [hΦ, hφ00, hψ00], ?_, ?_,
    fun y hy ↦ ?_⟩
  · have := P₀.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self] at this
    omega
  · dsimp only
    split_ifs <;> simp
  · refine ContDiffOn.congr ?_ fun y _ ↦ hΦ y
    refine (hφ.comp (ℓ.contDiff.comp hsub).contDiffOn fun y hy ↦ ((hΦs y).1 hy).2).prodMk ?_
    refine contDiffOn_snd.comp (hψ.comp (f := fun y ↦ ((0, ℓ (y - u)), (P (y - u)).2))
      ((contDiff_const.prodMk (ℓ.contDiff.comp hsub)).prodMk
        (contDiff_snd.comp (P.contDiff.comp hsub))).contDiffOn
      fun y hy ↦ ((hΦs y).1 hy).1) (mapsTo_univ _ _)
  · refine ContDiffOn.congr ?_ fun q _ ↦ hΦsymm q
    have hz : ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin (finrank ℝ ℓ.ker)) ↦
        ψ.symm ((0, φ.symm q.1), q.2)) Φ.target :=
      hψsymm.comp ((contDiffOn_const.prodMk (hφsymm.comp contDiffOn_fst
        fun q hq ↦ ((hΦt q).1 hq).1)).prodMk contDiffOn_snd) fun q hq ↦ ((hΦt q).1 hq).2
    refine (contDiffOn_const.add ((contDiffOn_snd.comp (contDiffOn_fst.comp hz (mapsTo_univ _ _))
      (mapsTo_univ _ _)).smul contDiffOn_const)).add ?_
    exact ℓ.ker.subtypeL.contDiff.comp_contDiffOn (contDiffOn_snd.comp hz (mapsTo_univ _ _))
  · obtain ⟨h1, h2⟩ := (hΦs y).1 hy
    have hu : u + ℓ (y - u) • e + ((P (y - u)).2 : E) = y := by
      simp [hP]
    rw [hΦ]
    dsimp only
    rw [← hFψ _ _ h1 h2, hu]
