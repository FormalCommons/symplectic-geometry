/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.ExtDeriv.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.LiouvilleMeasure
import SymplecticGeometry.LinearAlgebra.Alternating.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Pow
import TauCeti.Geometry.Manifold.DeRham.Wedge
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Normalizing a closed two-form on a product by its fibre integral

Let `B` be a boundaryless manifold and `F` a compact, Hausdorff manifold of dimension `2 * k` with
a nondegenerate two-form `σ`, oriented by `σᵏ`. Let `τ` be a two-form on `B × F` whose slices,
its pull-backs along the inclusions `y ↦ (b, y)`, are all `σ`. The fibre integral
`SymplecticGeometry.prodFiberIntegral` of `τ ^ (k + 1)`, a form of degree `2 + 2 * k` after the
cast `2 * (k + 1) = 2 + 2 * k`, is a two-form on `B`.

Its integrand is computed pointwise. At `(b, y)`, pick a vector `x` tangent to `F` with
`τ((w₁, x), (0, v)) = 0` for every `v`; it exists because `σ` is nondegenerate. Replacing
`(w₁, 0)` by `(w₁, x)` does not change the integrand, since `x` lies in the `2 * k`-dimensional
space that the last arguments span (`AlternatingMap.map_append_add_of_mem`), and then
`ContinuousAlternatingMap.wedgePow_succ_apply_append_of_eq_zero` gives the value
`(k + 1) * τ((w₁, x), (w₂, 0)) * σᵏ` (`SymplecticGeometry.prodFiberIntegrand_wedgePow_apply`).
Adding the pull-back `pr₁^* γ` of a two-form `γ` on `B` changes neither the slices nor the choice
of `x` (`TauCeti.SmoothForm.mpullback_prodMk_mpullback_fst`), so the fibre integral of
`(τ + pr₁^* γ) ^ (k + 1)` is that of `τ ^ (k + 1)` plus `(k + 1) * k! * V • γ`, with `V` the
symplectic volume of `F` (`SymplecticGeometry.prodFiberIntegral_wedgePow_add_mpullback_fst`). The
argument is that of `TauCeti.IsEhresmannConnection.fiberIntegral_wedgePow_apply` and
`TauCeti.IsEhresmannConnection.fiberMean_add_mpullback`, carried out on a product, where no
connection needs to be chosen.

So, for `F` nonempty, subtracting `c • pr₁^* β`, with `β` the fibre integral of `τ ^ (k + 1)` and
`c = 1 / ((k + 1) * k! * V)`, makes the fibre integral of the `(k + 1)`-st wedge power vanish
(`SymplecticGeometry.prodFiberIntegral_wedgePow_sub_smul_mpullback_fst_eq_zero`). When `τ` is
closed, so is `β` (`SymplecticGeometry.isClosed_prodFiberIntegral`), and the new form is closed,
has the slices `σ`, and has the horizontal spaces of `τ`
(`TauCeti.SmoothTwoForm.horizontalDistribution_add_mpullback`); this is
`SymplecticGeometry.isClosed_sub_smul_mpullback_fst_prodFiberIntegral`. It is the normalization
of coupling forms of McDuff–Salamon [McDuffSalamon2017], equations (6.4.3)–(6.4.5), with the
errata [McDuffSalamon2019Errata], over a product.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F] {k : ℕ}

/-- The slices `y ↦ (b, y)` of the pull-back of a form on `B` to `B × F` along the first
projection vanish, for forms of positive degree. -/
theorem mpullback_prodMk_mpullback_fst (γ : SmoothForm IB B ℝ (k + 1)) (b : B) :
    TauCeti.mpullback IF (IB.prod IF) (Prod.mk b)
      (mpullback (Prod.fst : B × F → B) contMDiff_fst γ).val = 0 := by
  funext y
  ext v
  rw [TauCeti.mpullback_apply, mpullback_fst_apply]
  simp only [mfderiv_prod_right]
  exact (γ.val b).map_coord_zero 0 (by rw [Manifold.tangentSpaceProdEquiv_apply]; rfl)

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {σ : SmoothTwoForm IF F} {k : ℕ}

variable [FiniteDimensional ℝ EF]

/-- **The integrand of the top wedge power.** Let the slice of a two-form `τ` on `B × F` over `b`
be `σ`, with `F` of dimension `2 * k`. If a vector `x` tangent to `F` at `y` makes `(w₁, x)`
`τ`-orthogonal to the tangent space of the fibre, then the integrand over `b` of `τ ^ (k + 1)`,
read in degree `2 + 2 * k`, on `w₁, w₂` takes at `y` the value
`(k + 1) * k! * τ((w₁, x), (w₂, 0))` times the symplectic volume form `σᵏ / k!`. -/
theorem prodFiberIntegrand_wedgePow_apply (hk : finrank ℝ EF = 2 * k)
    {τ : SmoothTwoForm (IB.prod IF) (B × F)} {b : B}
    (hτ : mpullback IF (IB.prod IF) (Prod.mk b) τ.val = σ.val) (w₁ w₂ : TangentSpace IB b) (y : F)
    {x : TangentSpace IF y} (hx : ∀ v : TangentSpace IF y, τ.val (b, y) ![(w₁, x), (0, v)] = 0) :
    prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q)
        (by ring : 2 * (k + 1) = 2 + 2 * k) (τ.wedgePow (k + 1))).val b ![w₁, w₂] y =
      ((k + 1) * k.factorial * (τ.val (b, y) ![(w₁, x), (w₂, 0)] : ℝ)) •
        (σ.volumeForm k).val y := by
  ext v
  set φ := τ.val (b, y)
  let u : Fin 2 → TangentSpace (IB.prod IF) (b, y) := fun i ↦ (![w₁, w₂] i, 0)
  let d : Fin 2 → TangentSpace (IB.prod IF) (b, y) := ![(0, x), 0]
  let w : Fin (2 * k) → TangentSpace (IB.prod IF) (b, y) := fun j ↦ (0, v j)
  -- The vectors tangent to the fibre form a subspace of dimension at most `2 * k`.
  have : FiniteDimensional ℝ (TangentSpace IF y) := inferInstanceAs (FiniteDimensional ℝ EF)
  let V : Submodule ℝ (TangentSpace (IB.prod IF) (b, y)) :=
    LinearMap.range (LinearMap.inr ℝ (TangentSpace IB b) (TangentSpace IF y))
  have : Module.Finite ℝ V := LinearMap.finiteDimensional_range _
  have hV : finrank ℝ V ≤ 2 * k := (LinearMap.finrank_range_le _).trans hk.le
  have hd (i : Fin 2) : d i ∈ V := by
    fin_cases i
    · exact ⟨x, rfl⟩
    · exact ⟨0, rfl⟩
  have hw (j : Fin (2 * k)) : w j ∈ V := ⟨v j, rfl⟩
  let g := (φ.wedgePow (k + 1)).toAlternatingMap.domDomCongr
    (finCongr (by ring : 2 * (k + 1) = 2 + 2 * k))
  have hlhs : prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q)
        (by ring : 2 * (k + 1) = 2 + 2 * k) (τ.wedgePow (k + 1))).val b ![w₁, w₂] y v =
      g (Fin.append u w) := by
    rw [prodFiberIntegrand_apply, SmoothForm.cast_apply, SmoothForm.wedgePow_apply]
    have hfun : (fun p ↦ (Manifold.tangentSpaceProdEquiv (I := IB) (J := IF) (b, y)).symm
        (Fin.append (fun i ↦ (![w₁, w₂] i, 0)) (fun j ↦ (0, v j)) p)) = Fin.append u w := by
      funext p
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
        simp only [Fin.append_left, Fin.append_right] <;>
        exact Manifold.tangentSpaceProdEquiv_symm_apply _ _
    rw [hfun]
    -- `g` precomposes with `Fin.cast`, by the definition of `AlternatingMap.domDomCongr`.
    rfl
  have hud : u + d = ![(w₁, x), (w₂, 0)] := by
    funext i
    fin_cases i
    · exact Prod.ext (add_zero w₁) (zero_add x)
    · exact Prod.ext (add_zero w₂) (add_zero 0)
  -- On the fibre, `τ ^ k` is `σ ^ k`, since the slice of `τ` is `σ`.
  have hσk : (σ.val y).wedgePow k v = φ.wedgePow k w := by
    rw [← hτ, ← TauCeti.mpullback_wedgePow_apply, mpullback_apply, SmoothForm.wedgePow_apply]
    congr 1
    funext j
    rw [mfderiv_prod_right]
    rfl
  have hφ (j : Fin (2 * k)) : φ ![(u + d) 0, w j] = 0 := by
    rw [hud]
    exact hx (v j)
  rw [hlhs, ← AlternatingMap.map_append_add_of_mem g hV u hd hw]
  -- Unfold `g` again, to the form of `wedgePow_succ_apply_append_of_eq_zero`.
  change φ.wedgePow (k + 1) (Fin.append (u + d) w ∘ Fin.cast (by ring)) = _
  rw [ContinuousAlternatingMap.wedgePow_succ_apply_append_of_eq_zero φ hφ, ← hσk, hud,
    ← SmoothForm.wedgePow_apply, SmoothTwoForm.wedgePow_eq_factorial_smul_volumeForm]
  simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  -- The two sides evaluate `τ` on the same vectors, written in two defeq types.
  exact (fun s t (hst : s = t) ↦ by subst hst; ring : ∀ s t : ℝ, s = t →
    ((k : ℝ) + 1) * s * (k.factorial * (σ.volumeForm k).val y v) =
      (k + 1) * k.factorial * t * (σ.volumeForm k).val y v) _ _ rfl

variable [FiniteDimensional ℝ EB] [BoundarylessManifold IB B] [CompactSpace F] [T2Space F]

/-- **Adding a pull-back from the base.** Let `σ` be nondegenerate on `F`, of dimension `2 * k`,
and let all slices of the two-form `τ` on `B × F` along the fibres be `σ`. For a two-form `γ` on
`B`, the fibre integral of `(τ + pr₁^* γ) ^ (k + 1)` is that of `τ ^ (k + 1)` plus
`(k + 1) * k! * V • γ`, where `V` is the integral of `σᵏ / k!` over `F`, both read in degree
`2 + 2 * k`. -/
theorem prodFiberIntegral_wedgePow_add_mpullback_fst (hσ : σ.IsNondegenerate)
    (hk : finrank ℝ EF = 2 * k) {τ : SmoothTwoForm (IB.prod IF) (B × F)}
    (hτ : ∀ b, mpullback IF (IB.prod IF) (Prod.mk b) τ.val = σ.val) (γ : SmoothTwoForm IB B) :
    prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        ((τ + SmoothForm.mpullback Prod.fst contMDiff_fst γ).wedgePow (k + 1))) =
      prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        (τ.wedgePow (k + 1))) +
      (((k : ℝ) + 1) * k.factorial *
        integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val) • γ := by
  set τ' := τ + SmoothForm.mpullback Prod.fst contMDiff_fst γ
  set C : ℝ := ((k : ℝ) + 1) * k.factorial
  have hτ' (b : B) : mpullback IF (IB.prod IF) (Prod.mk b) τ'.val = σ.val := by
    rw [Submodule.coe_add, mpullback_add, hτ, SmoothForm.mpullback_prodMk_mpullback_fst, add_zero]
  refine SmoothBundleForm.ext fun b v ↦ ?_
  rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm]
  -- At each `y`, a vector `x y` tangent to `F` that makes `(v 0, x y)` orthogonal to the fibre.
  have hx (y : F) : ∃ x : TangentSpace IF y,
      ∀ u : TangentSpace IF y, τ.val (b, y) ![(v 0, x), (0, u)] = 0 := by
    let e : TangentSpace IF y →L[ℝ] TangentSpace (IB.prod IF) (b, y) :=
      ContinuousLinearMap.inr ℝ (TangentSpace IB b) (TangentSpace IF y)
    let a : TangentSpace (IB.prod IF) (b, y) := (v 0, 0)
    obtain ⟨x, hx⟩ := (hσ.isInvertible_flat y).surjective (-((τ.flat (b, y) a).comp e))
    refine ⟨x, fun u ↦ ?_⟩
    have h : σ.flat y x u = -(τ.flat (b, y) a (e u)) := by
      rw [hx]
      rfl
    rw [SmoothTwoForm.flat_apply, SmoothTwoForm.flat_apply, SmoothBundleForm.eval₂_apply,
      SmoothBundleForm.eval₂_apply, ← hτ b, mpullback_apply_pair, mfderiv_prod_right] at h
    have hadd := (τ.bilinFormAt (b, y)).map_add₂ a (e x) (e u)
    simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] at hadd
    have hsplit : a + e x = (v 0, x) := Prod.ext (add_zero _) (zero_add _)
    rw [hsplit] at hadd
    -- `e u` is `(0, u)`, written through `ContinuousLinearMap.inr`.
    change τ.val (b, y) ![(v 0, x), e u] = 0
    exact hadd.trans ((congrArg (τ.val (b, y) ![a, e u] + ·) h).trans (add_neg_cancel _))
  choose x hx using hx
  have hx' (y : F) (u : TangentSpace IF y) : τ'.val (b, y) ![(v 0, x y), (0, u)] = 0 := by
    rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, hx, zero_add]
    exact (SmoothForm.mpullback_fst_apply γ (b, y) _).trans
      ((γ.val b).map_coord_zero 1 (by rw [Manifold.tangentSpaceProdEquiv_apply]; rfl))
  have hint : prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        (τ'.wedgePow (k + 1))).val b ![v 0, v 1] =
      prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        (τ.wedgePow (k + 1))).val b ![v 0, v 1] +
      (C * (γ.val b ![v 0, v 1] : ℝ)) • (σ.volumeForm k).val := by
    funext y
    rw [Pi.add_apply, Pi.smul_apply, prodFiberIntegrand_wedgePow_apply hk (hτ' b) _ _ y (hx' y),
      prodFiberIntegrand_wedgePow_apply hk (hτ b) _ _ y (hx y), ← add_smul]
    congr 1
    have hsplit : (τ'.val (b, y) ![(v 0, x y), (v 1, 0)] : ℝ) =
        τ.val (b, y) ![(v 0, x y), (v 1, 0)] + γ.val b ![v 0, v 1] := by
      rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
      refine congrArg _ ((SmoothForm.mpullback_fst_apply γ (b, y) _).trans (congrArg _ ?_))
      funext i
      fin_cases i <;> (rw [Manifold.tangentSpaceProdEquiv_apply]; rfl)
    exact (fun s t r (h : s = t + r) ↦ by subst h; ring : ∀ s t r : ℝ, s = t + r →
      ((k : ℝ) + 1) * k.factorial * s = (k + 1) * k.factorial * t + C * r) _ _ _ hsplit
  rw [prodFiberIntegral_apply, hint, integralTopForm_add_of_compactSpace _
      ((isSmoothForm_prodFiberIntegrand (SmoothForm.isSmoothForm _) b _).of_le bot_le)
      (((σ.volumeForm k).isSmoothForm.smul _).of_le bot_le),
    integralTopForm_smul, SmoothBundleForm.add_apply, ContinuousAlternatingMap.add_apply,
    prodFiberIntegral_apply, SmoothBundleForm.smul_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  congr 1
  exact (fun s t c i (h : s = t) ↦ by subst h; ring : ∀ s t c i : ℝ, s = t →
    c * s * i = c * i * t) _ _ _ _ rfl

/-- **The normalized form has vanishing fibre integral.** Let `σ` be nondegenerate on the
nonempty `F`, of dimension `2 * k`, with symplectic volume `V`, and let all slices of the two-form
`τ` on `B × F` be `σ`. For `β` the fibre integral of `τ ^ (k + 1)` and
`c = 1 / ((k + 1) * k! * V)`, the fibre integral of `(τ - c • pr₁^* β) ^ (k + 1)` vanishes, both
fibre integrals being read in degree `2 + 2 * k`. -/
theorem prodFiberIntegral_wedgePow_sub_smul_mpullback_fst_eq_zero [Nonempty F]
    (hσ : σ.IsNondegenerate) (hk : finrank ℝ EF = 2 * k) {τ : SmoothTwoForm (IB.prod IF) (B × F)}
    (hτ : ∀ b, mpullback IF (IB.prod IF) (Prod.mk b) τ.val = σ.val) :
    prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        ((τ - (1 / ((k + 1) * k.factorial *
            integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val) : ℝ) •
          SmoothForm.mpullback Prod.fst contMDiff_fst
            (prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
              (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q)
              (by ring : 2 * (k + 1) = 2 + 2 * k) (τ.wedgePow (k + 1))))).wedgePow (k + 1))) =
      0 := by
  set β := prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
    (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
    (τ.wedgePow (k + 1)))
  set C : ℝ := ((k : ℝ) + 1) * k.factorial *
    integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val
  have hC : C ≠ 0 := by
    have := hσ.integralTopForm_volumeForm_pos hk
    positivity
  rw [sub_eq_add_neg, ← map_smul, ← map_neg,
    prodFiberIntegral_wedgePow_add_mpullback_fst hσ hk hτ,
    smul_neg, smul_smul, mul_one_div_cancel hC, one_smul, add_neg_cancel]

/-- **Normalizing a closed form on a product by its fibre integral.** Let `F` be nonempty, of
dimension `2 * k`, with a nondegenerate two-form `σ` of symplectic volume `V`, and let `τ` be a
closed two-form on `B × F` all of whose slices are `σ`. Then the fibre integral `β` of
`τ ^ (k + 1)` is a closed two-form on `B`, and for `c = 1 / ((k + 1) * k! * V)` the form
`τ' = τ - c • pr₁^* β` is closed, has the slices `σ`, has the same horizontal spaces as `τ` for
the first projection, and the fibre integral of `τ' ^ (k + 1)` vanishes; the fibre integrals are
read in degree `2 + 2 * k`. -/
theorem isClosed_sub_smul_mpullback_fst_prodFiberIntegral [BoundarylessManifold IF F] [Nonempty F]
    (hσ : σ.IsNondegenerate) (hk : finrank ℝ EF = 2 * k) {τ : SmoothTwoForm (IB.prod IF) (B × F)}
    (hτ : τ.IsClosed) (hτσ : ∀ b, mpullback IF (IB.prod IF) (Prod.mk b) τ.val = σ.val) :
    let β := prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
      (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
      (τ.wedgePow (k + 1)))
    let τ' := τ - (1 / ((k + 1) * k.factorial *
      integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val) : ℝ) •
        SmoothForm.mpullback Prod.fst contMDiff_fst β
    β.IsClosed ∧ τ'.IsClosed ∧ (∀ b, mpullback IF (IB.prod IF) (Prod.mk b) τ'.val = σ.val) ∧
      SmoothTwoForm.horizontalDistribution IB Prod.fst τ' =
        SmoothTwoForm.horizontalDistribution IB Prod.fst τ ∧
      prodFiberIntegral (hσ.volumeOrientation hk) (LinearEquiv.cast (R := ℝ)
        (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) (by ring : 2 * (k + 1) = 2 + 2 * k)
        (τ'.wedgePow (k + 1))) = 0 := by
  intro β τ'
  -- A degree cast of a closed form is closed.
  have hcast {p q : ℕ} (h : p = q) {α : SmoothForm (IB.prod IF) (B × F) ℝ p} (hα : α.IsClosed) :
      (LinearEquiv.cast (R := ℝ) (M := fun q ↦ SmoothForm (IB.prod IF) (B × F) ℝ q) h
        α).IsClosed := by
    subst h
    exact hα
  have hβ : β.IsClosed := isClosed_prodFiberIntegral _ (hcast _ <| (SmoothForm.isClosed_def _).2
    ((mem_closedForms (I := IB.prod IF) _).1
      (SmoothForm.wedgePow_mem_closedForms ((mem_closedForms (I := IB.prod IF) _).2
        ((SmoothForm.isClosed_def _).1 hτ)) _)))
  have hτ' : τ' = τ + SmoothForm.mpullback Prod.fst contMDiff_fst
      (-((1 / ((k + 1) * k.factorial *
        integralTopForm (hσ.volumeOrientation hk) (σ.volumeForm k).val) : ℝ) • β)) := by
    rw [map_neg, map_smul, ← sub_eq_add_neg]
  refine ⟨hβ, hτ.sub ((hβ.mpullback _ _).smul _), fun b ↦ ?_, ?_,
    prodFiberIntegral_wedgePow_sub_smul_mpullback_fst_eq_zero hσ hk hτσ⟩
  · rw [hτ', Submodule.coe_add, mpullback_add, hτσ, SmoothForm.mpullback_prodMk_mpullback_fst,
      add_zero]
  · rw [hτ']
    exact SmoothTwoForm.horizontalDistribution_add_mpullback _ τ _

end SymplecticGeometry
