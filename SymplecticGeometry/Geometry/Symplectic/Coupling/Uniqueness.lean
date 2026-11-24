/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import SymplecticGeometry.Geometry.Symplectic.Coupling.Basic
public import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# Uniqueness of coupling forms

Two coupling forms `ω₀` and `ω₁` on `P × [a, b]` for the same family `τ` of nondegenerate forms
on the base are related by an equivariant diffeomorphism of `P × [a, b]` that preserves the
coordinate `t` of the interval (McDuff–Salamon, Proposition 5.1.9). The proof is Moser's
argument along the segment `ω₀ + s • (ω₁ - ω₀)`, with a primitive of `ω₁ - ω₀` that is invariant
under the circle action and makes the Moser field tangent to the levels `t = const`.

This file builds that primitive. The contraction `c ((p, t), u) = (p, a + u (t - a))` of
`P × [a, b]` onto its bottom level `P × {a}` (`SymplecticGeometry.couplingContraction`) commutes
with the circle action, and the homotopy operator of `c^* η` (`SymplecticGeometry.couplingHomotopy`)
is a form `K η` with

* `d (K η) = η - pr^* η`, for a closed `η`, where `pr (p, t) = (p, a)` is the projection to the
  bottom level (`SymplecticGeometry.mextDerivₗ_couplingHomotopy`);
* `K η` invariant under the circle action when `η` is
  (`SymplecticGeometry.mpullback_smul_couplingHomotopy`);
* for a two-form `η`, `K η` vanishes on the direction of the interval
  (`SymplecticGeometry.couplingHomotopy_apply_inr`), and on the fundamental field `(X, 0)` when
  `ι_{(X, 0)} η = 0` (`SymplecticGeometry.couplingHomotopy_apply_couplingField`).

For two coupling forms for the same family, the difference `δ = ω₁ - ω₀` is closed, invariant,
vanishes on the bottom level and has `ι_{(X, 0)} δ = 0`, so `σ = K δ` is an invariant primitive of
`δ` that vanishes on `(X, 0)` (`SymplecticGeometry.IsCouplingForm.mextDerivₗ_couplingHomotopy_sub`,
`SymplecticGeometry.IsCouplingForm.couplingHomotopy_sub_apply_couplingField`). The forms
`ω₀ + s • δ` are coupling forms (`SymplecticGeometry.IsCouplingForm.lineMap`), hence symplectic
over a family of nondegenerate forms (`SymplecticGeometry.IsCouplingForm.isSymplectic`). A vector
`Y` with `ι_Y η = -σ` at a point, for a coupling form `η`, has `dt(Y) = 0`
(`SymplecticGeometry.IsCouplingForm.mfderiv_snd_eq_zero_of_apply_eq_neg`): the Moser field of
the segment is tangent to the levels of `t`.

## Implementation notes

The proof of `SymplecticGeometry.mpullback_smul_couplingHomotopy` adapts that of the private
lemma `SymplecticGeometry.IsCouplingForm.mpullback_smul_primitive` of `Coupling/Basic.lean`,
with the contraction in place of the segment map there: both follow from the naturality of the
homotopy operator (`TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9 (uniqueness of coupling forms) and §3.2 (Moser's argument).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  homotopy operator).
-/

public section

noncomputable section

open Bundle Manifold MulOpposite TauCeti Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P]
  {a b : ℝ} [Fact (a < b)]

/-! ### The contraction onto the bottom level -/

variable (P a b) in
/-- The contraction `((p, t), u) ↦ (p, a + u (t - a))` of `P × [a, b]` onto its bottom level
`P × {a}`, along the unit interval: the identity at `u = 1`, and the projection `(p, t) ↦ (p, a)`
at `u = 0`. -/
def couplingContraction (x : (ManifoldTotalSpace Circle P × Icc a b) × Icc (0 : ℝ) 1) :
    ManifoldTotalSpace Circle P × Icc a b :=
  (x.1.1, Set.Icc.lineMap ⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ x.1.2 x.2)

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] in
theorem couplingContraction_def (x : (ManifoldTotalSpace Circle P × Icc a b) × Icc (0 : ℝ) 1) :
    couplingContraction P a b x =
      (x.1.1, Set.Icc.lineMap ⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ x.1.2 x.2) :=
  (rfl)

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] in
/-- At time `1` the contraction is the identity. -/
@[simp]
theorem couplingContraction_one (x : ManifoldTotalSpace Circle P × Icc a b) :
    couplingContraction P a b (x, 1) = x := by
  simp [couplingContraction_def]

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] in
/-- At time `0` the contraction is the projection to the bottom level. -/
@[simp]
theorem couplingContraction_zero (x : ManifoldTotalSpace Circle P × Icc a b) :
    couplingContraction P a b (x, 0) = (x.1, ⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩) := by
  simp [couplingContraction_def]

omit [TopologicalSpace B] [∀ b, TopologicalSpace (P b)] [FiberBundle Circle P] in
/-- The contraction commutes with the circle action on the total space. -/
theorem couplingContraction_smul [∀ b, MulAction Circleᵐᵒᵖ (P b)] (z : Circle)
    (x : (ManifoldTotalSpace Circle P × Icc a b) × Icc (0 : ℝ) 1) :
    couplingContraction P a b ((op z • x.1.1, x.1.2), x.2) =
      (op z • (couplingContraction P a b x).1, (couplingContraction P a b x).2) :=
  (rfl)

variable (IB P a b) in
/-- The contraction of `P × [a, b]` onto its bottom level is smooth, up to the boundary. -/
theorem contMDiff_couplingContraction :
    ContMDiff (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (couplingContraction P a b) :=
  (contMDiff_fst.comp contMDiff_fst).prodMk
    (Set.Icc.contMDiff_lineMap_comp contMDiff_const (contMDiff_snd.comp contMDiff_fst)
      contMDiff_snd)

variable (IB P a b) in
/-- The projection `(p, t) ↦ (p, a)` of `P × [a, b]` to its bottom level is smooth. -/
theorem contMDiff_bottom :
    ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (fun x : ManifoldTotalSpace Circle P × Icc a b ↦
        (x.1, (⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ : Icc a b))) :=
  contMDiff_fst.prodMk contMDiff_const

/-- The first component of the derivative of the contraction is the first component of the
vector on `P`. -/
theorem fst_mfderiv_couplingContraction
    (x : (ManifoldTotalSpace Circle P × Icc a b) × Icc (0 : ℝ) 1)
    (v : TangentSpace (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) x) :
    (mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (couplingContraction P a b) x v).1 = v.1.1 := by
  refine (((contMDiff_couplingContraction IB P a b).mdifferentiable (by simp) x).mfderiv_fst_apply
    v).symm.trans ?_
  have h := mfderiv_comp_fst (I := (IB.prod (𝓡 1)).prod (𝓡∂ 1)) (J := 𝓡∂ 1)
    (I'' := IB.prod (𝓡 1)) (Prod.fst : ManifoldTotalSpace Circle P × Icc a b → _) x
  rw [mfderiv_fst] at h
  -- the first component of the contraction is `Prod.fst ∘ Prod.fst`, by definition
  exact DFunLike.congr_fun h v

/-- The derivative of the contraction sends a vector with no component along `[a, b]` and the
unit interval to a vector with no component along `[a, b]`. -/
theorem snd_mfderiv_couplingContraction_of_eq_zero
    (x : (ManifoldTotalSpace Circle P × Icc a b) × Icc (0 : ℝ) 1)
    (v : TangentSpace (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) x)
    (h₁ : v.1.2 = 0) (h₂ : v.2 = 0) :
    (mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (couplingContraction P a b) x v).2 = 0 := by
  have hc := (contMDiff_couplingContraction IB P a b).mdifferentiable (by simp) x
  rw [← hc.mfderiv_snd_apply, mfderiv_prod_eq_add_apply hc.snd, h₂]
  refine (congrArg₂ (· + ·) ?_ (map_zero _)).trans (add_zero _)
  -- in the direction of `P × [a, b]`, the second component is `t ↦ a + u (t - a)` composed with
  -- the second projection
  have h := mfderiv_comp_snd (I := IB.prod (𝓡 1)) (J := 𝓡∂ 1) (I'' := 𝓡∂ 1)
    (fun t : Icc a b ↦ Set.Icc.lineMap ⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ t x.2) x.1
  refine (DFunLike.congr_fun h v.1).trans ?_
  -- the second projection of `v.1` is `v.1.2`, by definition
  exact (congrArg (mfderiv (𝓡∂ 1) (𝓡∂ 1)
    (fun t : Icc a b ↦ Set.Icc.lineMap ⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ t x.2) x.1.2)
    h₁).trans (map_zero _)

/-! ### The homotopy operator of the contraction -/

section Homotopy

variable [∀ b, MulAction Circleᵐᵒᵖ (P b)] [IsManifold IB ∞ B] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable (IB P a b F k) in
/-- The homotopy operator `K` of the contraction of `P × [a, b]` onto its bottom level: the
`k`-form `K η = h (c^* η)` built from a `(k + 1)`-form `η`, where `c` is
`SymplecticGeometry.couplingContraction` and `h` is the homotopy operator
`TauCeti.SmoothForm.homotopyOperator`. -/
def couplingHomotopy :
    SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F (k + 1) →ₗ[ℝ]
      SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F k :=
  SmoothForm.homotopyOperator ∘ₗ
    SmoothForm.mpullback (couplingContraction P a b) (contMDiff_couplingContraction IB P a b)

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
theorem couplingHomotopy_apply
    (η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F
      (k + 1)) :
    couplingHomotopy IB P a b F k η = SmoothForm.homotopyOperator
      (SmoothForm.mpullback (couplingContraction P a b) (contMDiff_couplingContraction IB P a b)
        η) :=
  (rfl)

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- **The homotopy formula of the contraction.** For a closed form `η` on `P × [a, b]`,
`d (K η) = η - pr^* η`, where `pr (p, t) = (p, a)` is the projection to the bottom level. -/
theorem mextDerivₗ_couplingHomotopy [CompleteSpace F]
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F
      (k + 1)}
    (hη : mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (k + 1) η = 0) :
    mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) k (couplingHomotopy IB P a b F k η) =
      η - SmoothForm.mpullback _ (contMDiff_bottom IB P a b) η := by
  have hcl : mextDerivₗ (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) (k + 1)
      (SmoothForm.mpullback (couplingContraction P a b) (contMDiff_couplingContraction IB P a b)
        η) = 0 := by
    rw [SmoothForm.mextDerivₗ_mpullback, hη, map_zero]
  have h₁ : couplingContraction P a b ∘ (fun x ↦ (x, (1 : Icc (0 : ℝ) 1))) = id :=
    funext couplingContraction_one
  have h₀ : couplingContraction P a b ∘ (fun x ↦ (x, (0 : Icc (0 : ℝ) 1))) =
      fun x : ManifoldTotalSpace Circle P × Icc a b ↦
        (x.1, (⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ : Icc a b)) :=
    funext couplingContraction_zero
  rw [couplingHomotopy_apply, SmoothForm.mextDerivₗ_homotopyOperator hcl,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  simp only [h₁, h₀, SmoothForm.mpullback_id, LinearMap.id_apply]

/-- **Invariance of `K η`.** If a form `η` on `P × [a, b]` is invariant under the action of
`z : Circle` on the total space, then so is `K η`, as the contraction commutes with the
action. -/
theorem mpullback_smul_couplingHomotopy [CompleteSpace F] (z : Circle)
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F
      (k + 1)}
    (hη : SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
      (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd) η = η) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (couplingHomotopy IB P a b F k η) =
      couplingHomotopy IB P a b F k η := by
  have hz : ContMDiff ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) :=
    ((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd
  have hzc : ContMDiff (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1))
      (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ∞
      (Prod.map (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (id : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)) := hz.prodMap contMDiff_id
  refine Subtype.ext ?_
  rw [couplingHomotopy_apply, SmoothForm.coe_mpullback, SmoothForm.coe_homotopyOperator,
    ← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm (hz.mdifferentiable (by simp))
      ((SmoothForm.mpullback (couplingContraction P a b)
        (contMDiff_couplingContraction IB P a b) η).isSmoothForm.of_le (by simp)),
    ← SmoothForm.coe_mpullback _ hzc, ← SmoothForm.coe_homotopyOperator]
  have hcomp : couplingContraction P a b ∘ Prod.map (fun x ↦ (op z • x.1, x.2)) id =
      (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2)) ∘
        couplingContraction P a b :=
    funext (couplingContraction_smul z)
  rw [SmoothForm.mpullback_mpullback]
  conv_rhs => rw [← hη, SmoothForm.mpullback_mpullback]
  rw [SmoothForm.coe_homotopyOperator]
  simp only [hcomp]

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- The value of `K η` on a tangent vector `w`, for a two-form `η`: the integral over the unit
interval of `η` at `c (x, u)` on the images under the derivative of the contraction of the unit
time vector and of `w`. -/
theorem couplingHomotopy_apply_apply [CompleteSpace F]
    (η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F 2)
    (x : ManifoldTotalSpace Circle P × Icc a b)
    (w : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x) :
    (couplingHomotopy IB P a b F 1 η).val x ![w] = ∫ r in (0 : ℝ)..1,
      η.val (couplingContraction P a b (x, projIcc 0 1 zero_le_one r))
        ![mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
            (couplingContraction P a b) (x, projIcc 0 1 zero_le_one r)
            ((0 : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x),
              (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one r))),
          mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
            (couplingContraction P a b) (x, projIcc 0 1 zero_le_one r)
            (w, (0 : EuclideanSpace ℝ (Fin 1)))] := by
  rw [couplingHomotopy_apply, SmoothForm.coe_homotopyOperator]
  refine (homotopyOperator_apply_apply ((SmoothForm.mpullback (couplingContraction P a b)
    (contMDiff_couplingContraction IB P a b) η).isSmoothForm.of_le (by simp)) x ![w]).trans ?_
  refine intervalIntegral.integral_congr fun r _ ↦ ?_
  rw [SmoothForm.mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P] in
/-- **`K η` has no component along the interval.** For a two-form `η` on `P × [a, b]`, the
one-form `K η` vanishes on every vector `(0, v)` tangent to `[a, b]`. -/
theorem couplingHomotopy_apply_inr [CompleteSpace F]
    (η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F 2)
    (x : ManifoldTotalSpace Circle P × Icc a b) (v : TangentSpace (𝓡∂ 1) x.2) :
    (couplingHomotopy IB P a b F 1 η).val x
      ![((0 : TangentSpace (IB.prod (𝓡 1)) x.1), v)] = 0 := by
  refine (couplingHomotopy_apply_apply η x _).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : F)) fun r _ ↦ ?_).trans
    intervalIntegral.integral_zero
  dsimp only
  generalize projIcc 0 1 zero_le_one r = u
  set D := mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
    (couplingContraction P a b) (x, u)
  -- both images are vectors along `[a, b]`, multiples of the unit tangent vector `1`
  let e : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (couplingContraction P a b (x, u)) :=
    ((0 : TangentSpace (IB.prod (𝓡 1)) x.1),
      (1 : TangentSpace (𝓡∂ 1) (couplingContraction P a b (x, u)).2))
  have hvert : ∀ w : TangentSpace (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) (x, u),
      w.1.1 = 0 → ∃ c : ℝ, D w = c • e := by
    intro w hw
    obtain ⟨c, hc⟩ : ∃ c : ℝ, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ)
        (couplingContraction P a b (x, u)).2 (D w).2 = c := ⟨_, rfl⟩
    refine ⟨c, Prod.ext ?_ ?_⟩
    · rw [fst_mfderiv_couplingContraction, hw]
      exact (smul_zero c).symm
    · exact eq_smul_one_of_mfderiv_subtypeVal_Icc hc
  obtain ⟨c₁, hc₁⟩ := hvert ((0 : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x),
    (1 : TangentSpace (𝓡∂ 1) u)) rfl
  obtain ⟨c₂, hc₂⟩ := hvert (((0 : TangentSpace (IB.prod (𝓡 1)) x.1), v), 0) rfl
  rw [hc₁, hc₂, ContinuousAlternatingMap.vecCons_smul, ContinuousAlternatingMap.apply_vecCons_swap,
    ContinuousAlternatingMap.vecCons_smul,
    (η.val (couplingContraction P a b (x, u))).map_eq_zero_of_eq ![e, e] (i := 0) (j := 1) rfl
      zero_ne_one, smul_zero, neg_zero, smul_zero]

omit [PrincipalBundle Circle P] in
/-- **`K η` vanishes on `(X, 0)` when `η` does.** If the contraction of a two-form `η` on
`P × [a, b]` with the fundamental field `(X, 0)` vanishes, then `K η` vanishes on `(X, 0)`. -/
theorem couplingHomotopy_apply_couplingField [CompleteSpace F]
    {η : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) F 2}
    (hη : ∀ x v, η.val x ![couplingField IB P a b x, v] = 0)
    (x : ManifoldTotalSpace Circle P × Icc a b) :
    (couplingHomotopy IB P a b F 1 η).val x ![couplingField IB P a b x] = 0 := by
  refine (couplingHomotopy_apply_apply η x _).trans ?_
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : F)) fun r _ ↦ ?_).trans
    intervalIntegral.integral_zero
  dsimp only
  generalize projIcc 0 1 zero_le_one r = u
  have hX : mfderiv (((IB.prod (𝓡 1)).prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((IB.prod (𝓡 1)).prod (𝓡∂ 1))
      (couplingContraction P a b) (x, u) (couplingField IB P a b x, 0) =
      couplingField IB P a b (couplingContraction P a b (x, u)) :=
    Prod.ext ((fst_mfderiv_couplingContraction _ _).trans (by simp only [couplingField_fst]; rfl))
      ((snd_mfderiv_couplingContraction_of_eq_zero _ _ (couplingField_snd x) rfl).trans
        (couplingField_snd _).symm)
  rw [hX, ContinuousAlternatingMap.apply_vecCons_swap, hη, neg_zero]

end Homotopy

/-! ### The primitive of the difference of two coupling forms -/

namespace IsCouplingForm

variable [∀ b, MulAction Circleᵐᵒᵖ (P b)] [IsManifold IB ∞ B] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {η ω₀ ω₁ :
    SmoothTwoForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b)}
  {τ : Icc a b → SmoothTwoForm IB B}

/-- Two coupling forms for the same family agree on the bottom level: the pull-back of their
difference along the projection `(p, t) ↦ (p, a)` vanishes. -/
theorem mpullback_bottom_sub (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) :
    SmoothForm.mpullback _ (contMDiff_bottom IB P a b) (ω₁ - ω₀) = 0 := by
  have hb : (fun x : ManifoldTotalSpace Circle P × Icc a b ↦
      (x.1, (⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ : Icc a b))) =
      (fun p ↦ (p, (⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ : Icc a b))) ∘ Prod.fst :=
    rfl
  have hp := SmoothForm.mpullback_mpullback (I := (IB.prod (𝓡 1)).prod (𝓡∂ 1)) (I' := IB.prod (𝓡 1))
    (I'' := (IB.prod (𝓡 1)).prod (𝓡∂ 1))
    (Prod.fst : ManifoldTotalSpace Circle P × Icc a b → ManifoldTotalSpace Circle P)
    (fun p : ManifoldTotalSpace Circle P ↦
      (p, (⟨a, left_mem_Icc.2 (Fact.out : a < b).le⟩ : Icc a b)))
    contMDiff_fst (contMDiff_id.prodMk contMDiff_const) (ω₁ - ω₀)
  simp only [← hb] at hp
  rw [← hp, map_sub, h₀.mpullback_slice, h₁.mpullback_slice, sub_self, map_zero]

/-- **The primitive of the difference.** For two coupling forms `ω₀` and `ω₁` for the same
family, `K (ω₁ - ω₀)` is a primitive of `ω₁ - ω₀`. -/
theorem mextDerivₗ_couplingHomotopy_sub (h₀ : IsCouplingForm ω₀ τ) (h₁ : IsCouplingForm ω₁ τ) :
    mextDerivₗ ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 1 (couplingHomotopy IB P a b ℝ 1 (ω₁ - ω₀)) =
      ω₁ - ω₀ := by
  rw [mextDerivₗ_couplingHomotopy, mpullback_bottom_sub h₀ h₁, sub_zero]
  exact (SmoothForm.isClosed_iff_mextDerivₗ_eq_zero _).mp (h₁.isClosed.sub h₀.isClosed)

/-- The primitive `K (ω₁ - ω₀)` of the difference of two coupling forms is invariant under the
circle action. -/
theorem mpullback_smul_couplingHomotopy_sub (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (z : Circle) :
    SmoothForm.mpullback (fun x : ManifoldTotalSpace Circle P × Icc a b ↦ (op z • x.1, x.2))
        (((contMDiff_const_smul (op z)).comp contMDiff_fst).prodMk contMDiff_snd)
        (couplingHomotopy IB P a b ℝ 1 (ω₁ - ω₀)) =
      couplingHomotopy IB P a b ℝ 1 (ω₁ - ω₀) :=
  mpullback_smul_couplingHomotopy z (by rw [map_sub, h₀.mpullback_smul, h₁.mpullback_smul])

/-- The primitive `K (ω₁ - ω₀)` of the difference of two coupling forms vanishes on the
fundamental field `(X, 0)`, since both forms have the same contraction `-dt` with it. -/
theorem couplingHomotopy_sub_apply_couplingField (h₀ : IsCouplingForm ω₀ τ)
    (h₁ : IsCouplingForm ω₁ τ) (x : ManifoldTotalSpace Circle P × Icc a b) :
    (couplingHomotopy IB P a b ℝ 1 (ω₁ - ω₀)).val x ![couplingField IB P a b x] = 0 :=
  couplingHomotopy_apply_couplingField (fun y v ↦ by
    simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
      h₀.apply_couplingField, h₁.apply_couplingField]
    exact sub_self _) x

/-- **The Moser field is tangent to the levels of `t`.** Let `η` be a coupling form and `σ` a
one-form that vanishes on the fundamental field `(X, 0)` at a point `x`. A tangent vector `Y` at
`x` with `ι_Y η = -σ` there has `dt(Y) = 0`. -/
theorem mfderiv_snd_eq_zero_of_apply_eq_neg (h : IsCouplingForm η τ)
    {σ : SmoothForm ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) (ManifoldTotalSpace Circle P × Icc a b) ℝ 1}
    {x : ManifoldTotalSpace Circle P × Icc a b}
    (hσ : σ.val x ![couplingField IB P a b x] = 0)
    {Y : TangentSpace ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) x}
    (hY : ∀ v, η.val x ![Y, v] = -σ.val x ![v]) :
    mfderiv ((IB.prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ)
      (fun y : ManifoldTotalSpace Circle P × Icc a b ↦ (y.2 : ℝ)) x Y = 0 := by
  have hX := h.apply_couplingField x Y
  rw [ContinuousAlternatingMap.apply_vecCons_swap, hY, hσ, neg_zero, neg_zero] at hX
  exact neg_eq_zero.mp hX.symm

end IsCouplingForm

end SymplecticGeometry

end
