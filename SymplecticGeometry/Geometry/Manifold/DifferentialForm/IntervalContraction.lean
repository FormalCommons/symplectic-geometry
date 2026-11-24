/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# The contraction of `M × [a, b]` onto its bottom level

For a manifold `M` and an interval `[a, b]`, `a < b`, the map
`c ((x, t), u) = (x, (1 - u) a + u t)` (`SymplecticGeometry.prodIccContraction`) is a smooth
homotopy, over the unit interval, from the projection `(x, t) ↦ (x, a)` to the bottom level
`M × {a}` to the identity. Its derivative sends `((w, r), q)`, with `r` and `q` multiples of the
unit tangent vectors, to `(w, u r + (t - a) q)`
(`SymplecticGeometry.mfderiv_prodIccContraction`).

The homotopy operator of `c^* η` (`SymplecticGeometry.prodIccHomotopyOperator`) is a form `K η`
on `M × [a, b]` with

* `d (K η) = η - pr^* η`, for a closed `η`, where `pr (x, t) = (x, a)`
  (`SymplecticGeometry.mextDerivₗ_prodIccHomotopyOperator`);
* `f^* (K η) = K (f^* η)` for a smooth `f : M → M` acting on the first factor
  (`SymplecticGeometry.mpullback_prodMap_prodIccHomotopyOperator`);
* for a two-form `η`, `K η` vanishes on the direction of the interval
  (`SymplecticGeometry.prodIccHomotopyOperator_apply_inr`).

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator).
-/

public section

noncomputable section

open Set TauCeti
open scoped Manifold ContDiff Fact.Manifold

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} {a b : ℝ} [Fact (a < b)]

/-! ### The contraction -/

variable (M a b) in
/-- The contraction `((x, t), u) ↦ (x, (1 - u) a + u t)` of `M × [a, b]` onto its bottom level
`M × {a}`, along the unit interval: the identity at `u = 1`, and the projection `(x, t) ↦ (x, a)`
at `u = 0`. -/
def prodIccContraction (x : (M × Icc a b) × unitInterval) : M × Icc a b :=
  (x.1.1, Icc.convexComb ⊥ x.1.2 x.2)

theorem prodIccContraction_def (x : (M × Icc a b) × unitInterval) :
    prodIccContraction M a b x = (x.1.1, Icc.convexComb ⊥ x.1.2 x.2) :=
  (rfl)

/-- The contraction does not move the point of `M`. -/
@[simp]
theorem prodIccContraction_fst (x : (M × Icc a b) × unitInterval) :
    (prodIccContraction M a b x).1 = x.1.1 :=
  (rfl)

/-- The point of the interval moves along the segment from `a` to `t`. -/
@[simp]
theorem prodIccContraction_snd (x : (M × Icc a b) × unitInterval) :
    (prodIccContraction M a b x).2 = Icc.convexComb ⊥ x.1.2 x.2 :=
  (rfl)

/-- At time `1` the contraction is the identity. -/
@[simp]
theorem prodIccContraction_one (x : M × Icc a b) : prodIccContraction M a b (x, 1) = x := by
  simp [prodIccContraction_def]

/-- At time `0` the contraction is the projection to the bottom level. -/
@[simp]
theorem prodIccContraction_zero (x : M × Icc a b) :
    prodIccContraction M a b (x, 0) = (x.1, ⊥) := by
  simp [prodIccContraction_def]

/-- The contraction commutes with every map `f × id` of `M × [a, b]`. -/
theorem prodIccContraction_comp_prodMap {N : Type*} (f : N → M) :
    prodIccContraction M a b ∘ Prod.map (Prod.map f id) id =
      Prod.map f id ∘ prodIccContraction N a b :=
  (rfl)

variable [TopologicalSpace M] [ChartedSpace H M]

variable (I M a b) in
/-- The contraction of `M × [a, b]` onto its bottom level is smooth, up to the boundary. -/
theorem contMDiff_prodIccContraction :
    ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) ∞ (prodIccContraction M a b) :=
  (contMDiff_fst.comp contMDiff_fst).prodMk
    (contMDiff_const.convexComb (contMDiff_snd.comp contMDiff_fst) contMDiff_snd)

/-- **The derivative of the contraction.** At `((x, t), u)`, the derivative of the contraction
sends `((w, r • 1), q • 1)` to `(w, (u r + (t - a) q) • 1)`, where `1` denotes the unit tangent
vectors of the intervals. -/
theorem mfderiv_prodIccContraction (x : (M × Icc a b) × unitInterval) (w : TangentSpace I x.1.1)
    (r q : ℝ) :
    mfderiv ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (prodIccContraction M a b) x
        ((w, r • (1 : TangentSpace (𝓡∂ 1) x.1.2)), q • (1 : TangentSpace (𝓡∂ 1) x.2)) =
      (w, ((x.2 : ℝ) * r + ((x.1.2 : ℝ) - a) * q) •
        (1 : TangentSpace (𝓡∂ 1) (prodIccContraction M a b x).2)) := by
  have hc := ((contMDiff_prodIccContraction I M a b).mdifferentiable (by simp)) x
  refine Prod.ext ?_ ?_
  · refine (hc.mfderiv_fst_apply _).symm.trans ?_
    have h := mfderiv_comp_fst (I := I.prod (𝓡∂ 1)) (J := 𝓡∂ 1) (I'' := I)
      (Prod.fst : M × Icc a b → M) x
    rw [mfderiv_fst] at h
    -- the first component of the contraction is `Prod.fst ∘ Prod.fst`, by definition
    exact DFunLike.congr_fun h _
  · refine (hc.mfderiv_snd_apply _).symm.trans ?_
    refine mfderiv_apply_eq_smul_one_Icc hc.snd ?_
    -- the second component, as a real function, is `a + u (t - a)`
    have hval : (Subtype.val ∘ fun y ↦ (prodIccContraction M a b y).2) =
        (fun _ ↦ a) + (Subtype.val ∘ Prod.snd) *
          (Subtype.val ∘ Prod.snd ∘ Prod.fst - fun _ ↦ a) := by
      funext y
      simp only [Function.comp_apply, prodIccContraction_def, Icc.coe_convexComb, Icc.coe_bot,
        Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    have hT := (mdifferentiableAt_subtypeVal_Icc x.1.2).hasMFDerivAt.comp x
      ((hasMFDerivAt_snd (I := I) (I' := 𝓡∂ 1) x.1).comp x
        (hasMFDerivAt_fst (I := I.prod (𝓡∂ 1)) (I' := 𝓡∂ 1) x))
    have hU := (mdifferentiableAt_subtypeVal_Icc x.2).hasMFDerivAt.comp x
      (hasMFDerivAt_snd (I := I.prod (𝓡∂ 1)) (I' := 𝓡∂ 1) x)
    have hA := hasMFDerivAt_const (I := (I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I' := 𝓘(ℝ)) a x
    rw [hval, (hA.add (hU.mul (hT.sub hA))).mfderiv]
    -- The sums and composites of linear maps, applied to the vector, are those of the values.
    -- `simp` does not apply `add_apply` here: the summands have the tangent spaces of `ℝ` as
    -- codomains, and the sum has `ℝ`.
    change (0 : ℝ) + ((x.2 : ℝ) *
        ((show ℝ from mfderiv (𝓡∂ 1) 𝓘(ℝ) Subtype.val x.1.2 (r • 1)) - 0) +
      ((x.1.2 : ℝ) - a) * (show ℝ from mfderiv (𝓡∂ 1) 𝓘(ℝ) Subtype.val x.2 (q • 1))) = _
    rw [map_smul, map_smul, mfderiv_subtypeVal_Icc_one, mfderiv_subtypeVal_Icc_one]
    -- the tangent spaces of `ℝ` are `ℝ`, with its multiplication as scalar multiplication
    change (0 : ℝ) + ((x.2 : ℝ) * (r * 1 - 0) + ((x.1.2 : ℝ) - a) * (q * 1)) = _
    ring

/-! ### The homotopy operator of the contraction -/

section Homotopy

variable [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable (I M a b F k) in
/-- The homotopy operator `K` of the contraction of `M × [a, b]` onto its bottom level: the
`k`-form `K η = h (c^* η)` built from a `(k + 1)`-form `η`, where `c` is
`SymplecticGeometry.prodIccContraction` and `h` is the homotopy operator
`TauCeti.SmoothForm.homotopyOperator`. -/
def prodIccHomotopyOperator :
    SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1) →ₗ[ℝ]
      SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F k :=
  SmoothForm.homotopyOperator ∘ₗ
    SmoothForm.mpullback (prodIccContraction M a b) (contMDiff_prodIccContraction I M a b)

theorem prodIccHomotopyOperator_apply (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)) :
    prodIccHomotopyOperator I M a b F k η = SmoothForm.homotopyOperator
      (SmoothForm.mpullback (prodIccContraction M a b) (contMDiff_prodIccContraction I M a b) η) :=
  (rfl)

/-- **The homotopy formula of the contraction.** For a closed form `η` on `M × [a, b]`,
`d (K η) = η - pr^* η`, where `pr (x, t) = (x, a)` is the projection to the bottom level. -/
theorem mextDerivₗ_prodIccHomotopyOperator [CompleteSpace F]
    {η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)}
    (hη : mextDerivₗ (I.prod (𝓡∂ 1)) (k + 1) η = 0) :
    mextDerivₗ (I.prod (𝓡∂ 1)) k (prodIccHomotopyOperator I M a b F k η) =
      η - SmoothForm.mpullback (fun x : M × Icc a b ↦ (x.1, ⊥))
        (contMDiff_fst.prodMk contMDiff_const) η :=
  SmoothForm.mextDerivₗ_homotopyOperator_mpullback _ _ prodIccContraction_zero
    prodIccContraction_one hη

/-- **Naturality of `K`.** For a smooth map `f : N → M`, pulling `K η` back along `f × id` gives
`K` of the pull-back of `η`. -/
theorem mpullback_prodMap_prodIccHomotopyOperator [CompleteSpace F] {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] {f : N → M}
    (hf : ContMDiff I' I ∞ f) (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F (k + 1)) :
    SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id)
        (prodIccHomotopyOperator I M a b F k η) =
      prodIccHomotopyOperator I' N a b F k
        (SmoothForm.mpullback (Prod.map f id) (hf.prodMap contMDiff_id) η) := by
  rw [prodIccHomotopyOperator_apply, prodIccHomotopyOperator_apply,
    SmoothForm.mpullback_homotopyOperator, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  simp only [prodIccContraction_comp_prodMap]

/-- The value of `K η` on a tangent vector `w`, for a two-form `η`: the integral over the unit
interval of `η` at `c (x, u)` on the images under the derivative of the contraction of the unit
time vector and of `w`. -/
theorem prodIccHomotopyOperator_apply_apply [CompleteSpace F]
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 2) (x : M × Icc a b)
    (w : TangentSpace (I.prod (𝓡∂ 1)) x) :
    (prodIccHomotopyOperator I M a b F 1 η).val x ![w] = ∫ r in (0 : ℝ)..1,
      η.val (prodIccContraction M a b (x, projIcc 0 1 zero_le_one r))
        ![mfderiv ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1))
            (prodIccContraction M a b) (x, projIcc 0 1 zero_le_one r)
            ((0 : TangentSpace (I.prod (𝓡∂ 1)) x),
              (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one r))),
          mfderiv ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1))
            (prodIccContraction M a b) (x, projIcc 0 1 zero_le_one r)
            (w, (0 : EuclideanSpace ℝ (Fin 1)))] := by
  rw [prodIccHomotopyOperator_apply, SmoothForm.coe_homotopyOperator]
  refine (homotopyOperator_apply_apply ((SmoothForm.mpullback (prodIccContraction M a b)
    (contMDiff_prodIccContraction I M a b) η).isSmoothForm.of_le (by simp)) x ![w]).trans ?_
  refine intervalIntegral.integral_congr fun r _ ↦ ?_
  rw [SmoothForm.mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`K η` has no component along the interval.** For a two-form `η` on `M × [a, b]`, the
one-form `K η` vanishes on every vector `(0, v)` tangent to `[a, b]`. -/
theorem prodIccHomotopyOperator_apply_inr [CompleteSpace F]
    (η : SmoothForm (I.prod (𝓡∂ 1)) (M × Icc a b) F 2) (x : M × Icc a b)
    (v : TangentSpace (𝓡∂ 1) x.2) :
    (prodIccHomotopyOperator I M a b F 1 η).val x ![((0 : TangentSpace I x.1), v)] = 0 := by
  refine (prodIccHomotopyOperator_apply_apply η x _).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : F)) fun r _ ↦ ?_).trans
    intervalIntegral.integral_zero
  dsimp only
  generalize projIcc 0 1 zero_le_one r = u
  obtain ⟨s, hs⟩ : ∃ s : ℝ, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) x.2 v = s := ⟨_, rfl⟩
  -- both images are multiples of the unit vector `e` along `[a, b]`
  set e : TangentSpace (I.prod (𝓡∂ 1)) (prodIccContraction M a b (x, u)) :=
    ((0 : TangentSpace I x.1), (1 : TangentSpace (𝓡∂ 1) (prodIccContraction M a b (x, u)).2))
  have he : ∀ c : ℝ, ((0 : TangentSpace I x.1),
      c • (1 : TangentSpace (𝓡∂ 1) (prodIccContraction M a b (x, u)).2)) = c • e :=
    fun c ↦ Prod.ext (smul_zero c).symm (Prod.smul_snd c e).symm
  have h₁ : mfderiv ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (prodIccContraction M a b)
      (x, u) ((0 : TangentSpace (I.prod (𝓡∂ 1)) x), (1 : TangentSpace (𝓡∂ 1) u)) =
      ((u : ℝ) * 0 + ((x.2 : ℝ) - a) * 1) • e := by
    have h := mfderiv_prodIccContraction (x, u) (0 : TangentSpace I x.1) 0 1
    rw [zero_smul, one_smul, he] at h
    -- `0 : TangentSpace (I.prod (𝓡∂ 1)) x` is the pair of zeros, by definition
    exact h
  have h₂ : mfderiv ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (prodIccContraction M a b)
      (x, u) (((0 : TangentSpace I x.1), v), (0 : EuclideanSpace ℝ (Fin 1))) =
      ((u : ℝ) * s + ((x.2 : ℝ) - a) * 0) • e := by
    have h := mfderiv_prodIccContraction (x, u) (0 : TangentSpace I x.1) s 0
    rw [zero_smul, ← eq_smul_one_of_mfderiv_subtypeVal_Icc hs, he] at h
    -- the model space of the tangent spaces of the unit interval is `EuclideanSpace ℝ (Fin 1)`
    exact h
  rw [h₁, h₂, ContinuousAlternatingMap.vecCons_smul,
    ContinuousAlternatingMap.apply_vecCons_swap, ContinuousAlternatingMap.vecCons_smul,
    (η.val (prodIccContraction M a b (x, u))).map_eq_zero_of_eq ![e, e] (i := 0) (j := 1) rfl
      zero_ne_one, smul_zero, neg_zero, smul_zero]

end Homotopy

end SymplecticGeometry

end
