/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition

import SymplecticGeometry.Algebra.BigOperators.Module
import SymplecticGeometry.Algebra.Order.Floor.Semiring
import SymplecticGeometry.Analysis.Calculus.BumpFunction.SmoothApprox
import SymplecticGeometry.Analysis.Calculus.Deriv.Rectangle
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Lemmas
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ConvexShape.SmoothedMax
/-!
# Weakly increasing chains of `i`-convex shapes

This file builds a family of `i`-convex shapes `R = C ℓ r`, smooth on `ℝ²` and weakly increasing
in `ℓ`, that follows a given family `χ` of shapes, which may be only `C²` in `r`. It is a step
towards a smooth family that is strictly increasing in `ℓ`. The first piece is one step of the
chain:

* `SymplecticGeometry.smoothedMaxPath δ η M A`: the path
  `σ ↦ (r ↦ smoothedMax δ (M r) (A r - (1 - ρ σ) η))`, `ρ = TauCeti.collaredSmoothTransition`,
  from the smoothed maximum of `M` and `A - η` (up to `σ = 1 / 4`,
  `SymplecticGeometry.smoothedMaxPath_of_le`) to that of `M` and `A` (from `σ = 3 / 4`,
  `SymplecticGeometry.smoothedMaxPath_of_ge`). It is smooth in `(σ, r)`
  (`SymplecticGeometry.contDiff_smoothedMaxPath`) and, for `η ≥ 0`, monotone in `σ`
  (`SymplecticGeometry.monotone_smoothedMaxPath`, so `Monotone.deriv_nonneg` makes its
  `σ`-derivative nonnegative), since `smoothedMax` is monotone in its second
  argument and `ρ` is monotone (`TauCeti.monotone_collaredSmoothTransition`). It consists of
  `i`-convex shapes where `M` and `A - η` are and `δ (M' + A') ≤ 2 r`
  (`SymplecticGeometry.isConvexShapeAt_smoothedMaxPath`, from
  `SymplecticGeometry.isConvexShapeAt_smoothedMax`), with margins at least the smaller of those
  of `M` and of `A - η` (`SymplecticGeometry.min_le_deriv_smoothedMaxPath_div_sub_one_div`,
  `SymplecticGeometry.min_le_iteratedDeriv_two_smoothedMaxPath_add_pow_three_div_sub_one_div`).
  Each shape of the path is the smoothed maximum of `M` and some `A - c` with `c ∈ [0, η]`
  (`SymplecticGeometry.exists_mem_Icc_smoothedMaxPath_eq`). The margins of `A - η` are those of
  `A` less `η / (A (A - η))` (`SymplecticGeometry.deriv_sub_const_div_sub_one_div_sub_const`),
  which lets a caller choose `η` from a margin of `A`.

These paths, between consecutive members `M i` and `M (i + 1)` of the chain of smoothed maxima
`M = SymplecticGeometry.smoothedMaxChain δ A`, string together into one family:

* `SymplecticGeometry.shapeChain δ η a h A N`: on the mesh `a + i h`, `i ≤ N`, the sum of `M 0`
  and, for each `i < N`, the increment of the `i`-th path at the parameter `(ℓ - a - i h) / h`
  over its value at `0`. Written as a sum rather than glued piece by piece, it is smooth on all of
  `ℝ²` (`SymplecticGeometry.contDiff_shapeChain`), monotone in `ℓ` for `h > 0` and `η ≥ 0`
  (`SymplecticGeometry.monotone_shapeChain`), `A 0` up to `ℓ = a + h / 4`
  (`SymplecticGeometry.shapeChain_of_le`) and constant in `ℓ` from `ℓ = a + (N - 1 / 4) h` on
  (`SymplecticGeometry.shapeChain_eq_of_ge`). Where the joints match,
  `A (i + 1) - η + δ ≤ M i` for `i < N`, the sum telescopes: between `a + j h` and
  `a + (j + 1) h` it is the `j`-th path (`SymplecticGeometry.shapeChain_eq_smoothedMaxPath`), and
  from `a + N h` on it is `M N` (`SymplecticGeometry.shapeChain_eq_smoothedMaxChain`), also as
  germs along a filter on which the joints eventually match
  (`SymplecticGeometry.shapeChain_eventuallyEq_smoothedMaxPath`,
  `SymplecticGeometry.shapeChain_eventuallyEq_smoothedMaxChain`); for continuous `A i`, the
  joints match near `r` once they match strictly at `r`
  (`SymplecticGeometry.eventually_forall_sub_add_le_smoothedMaxChain`). Its members are then
  `i`-convex shapes at each `r` where the joints match nearby, the `A i` are `C²` and `i`-convex
  shapes at `r` with `deriv (A i) r ≤ G` and `δ G ≤ r`, and the `A (i + 1) - η` are `i`-convex
  shapes at `r` (`SymplecticGeometry.isConvexShapeAt_shapeChain`): `A 0` before the mesh, `M N`
  after it, and a path between smoothed maxima on each of its intervals. Where moreover
  `A 0, …, A j` climb by `δ` near `r`, so that `M j = A j` there, a member on the `j`-th interval
  is the smoothed maximum of `A j` and some `A (j + 1) - c`, `c ∈ [0, η]`, near `r`; its value and
  first two derivatives at `r` are then within the farther of those of `A j` and `A (j + 1)` of
  any given values, up to `η + δ / 2` and a curvature term of order `1 / δ`
  (`SymplecticGeometry.abs_iteratedDeriv_shapeChain_sub_le`, from
  `SymplecticGeometry.abs_iteratedDeriv_two_smoothedMax_sub_le` and its analogues).

The members `A i` of such a chain are smooth stand-ins for members `χ ℓ` of a family that is only
`C²` away from an open set where it is smooth:

* `SymplecticGeometry.exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc`: a smooth `g` within
  `θ` of `χ ℓ` in value and two derivatives on `[r₁, r₂]`, equal to `χ ℓ` near the band
  `[r₃, r₂]`, and equal to `χ a` near all of `[r₁, r₂]` when `ℓ = a`. It applies
  `ContDiffOn.exists_contDiff_abs_iteratedDeriv_sub_lt_of_contDiffAt` to the slice of the open
  set at `ℓ`.

Together they give the chain itself:

* `SymplecticGeometry.exists_monotone_shapeChain`: for a family `χ` of `i`-convex shapes on
  `[a, b] × [r₁, r₂]`, smooth near the band `[a, b] × [r₃, r₂]` with `∂χ/∂ℓ > 0` on it, a family
  `C` smooth on `ℝ²`, of `i`-convex shapes and weakly increasing in `ℓ` there, constant in `ℓ`
  near `a` and `b` with `C a` equal to `χ a` near `[r₁, r₂]`, with `C b` at most `ε` above the
  members of `χ` and less than `ε` below `χ b`, and within `τ` of `χ` in value and two
  `r`-derivatives on the band. It is the `shapeChain` of the stand-ins of `χ (a + i h)` on a
  mesh of size `h = (b - a) / N` with width `δ = c h`: first the margin of stability of the
  shapes (step 1 of the design, `SymplecticGeometry.exists_forall_isConvexShapeAt_of_abs_sub_lt`)
  fixes the lowering `η` and the error of the stand-ins, so that the joints match and the
  stand-ins and their lowerings are convex shapes, then `c` is taken below the rate of increase
  of `χ` on the band
  (`IsCompact.exists_pos_mul_sub_le_sub_of_deriv_pos`), and last `h` small by uniform continuity
  in `ℓ` (`IsCompact.exists_pos_abs_sub_lt_of_continuousOn`) and against the Lipschitz constant
  of `∂χ/∂r` in `ℓ` (`IsCompact.exists_abs_deriv_sub_le_mul`), which makes the curvature term
  of `SymplecticGeometry.abs_iteratedDeriv_shapeChain_sub_le` of order `h / c`. The mesh cell of
  a point of `[a, b]` comes from `SymplecticGeometry.exists_lt_mem_Icc_add_mul`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 3.25 and Corollary 4.29.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Set Filter Topology Complex TauCeti
open scoped ContDiff Manifold

variable {χ : ℝ → ℝ → ℝ} {r₁ r₂ : ℝ}

/-! ### The path between consecutive smoothed maxima -/

/-- The **path between consecutive smoothed maxima**: for `σ` from `0` to `1`, the shape
`r ↦ smoothedMax δ (M r) (A r - (1 - ρ σ) η)`, where `ρ = collaredSmoothTransition`. It runs
from the smoothed maximum of `M` and `A - η` to that of `M` and `A`, and is constant in `σ` near
both ends. -/
def smoothedMaxPath (δ η : ℝ) (M A : ℝ → ℝ) (σ r : ℝ) : ℝ :=
  smoothedMax δ (M r) (A r - (1 - collaredSmoothTransition σ) * η)

theorem smoothedMaxPath_def (δ η : ℝ) (M A : ℝ → ℝ) (σ r : ℝ) :
    smoothedMaxPath δ η M A σ r =
      smoothedMax δ (M r) (A r - (1 - collaredSmoothTransition σ) * η) :=
  (rfl)

variable {δ η σ r : ℝ} {M A : ℝ → ℝ}

/-- The path between smoothed maxima of `Cⁿ` functions is `Cⁿ` in `(σ, r)`. -/
theorem contDiff_smoothedMaxPath {n : ℕ∞} (hM : ContDiff ℝ n M) (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (Function.uncurry (smoothedMaxPath δ η M A)) := by
  have hρ : ContDiff ℝ n collaredSmoothTransition :=
    contDiff_collaredSmoothTransition (WithTop.coe_le_coe.2 le_top)
  have h : ContDiff ℝ n fun x : ℝ × ℝ ↦
      smoothedMax δ (M x.2) (A x.2 - (1 - collaredSmoothTransition x.1) * η) :=
    (contDiff_smoothedMax δ).comp ((hM.comp contDiff_snd).prodMk ((hA.comp contDiff_snd).sub
      ((contDiff_const.sub (hρ.comp contDiff_fst)).mul contDiff_const)))
  convert h using 1
  funext ⟨σ, r⟩
  rw [Function.uncurry_apply_pair, smoothedMaxPath_def]

/-- Up to `σ = 1 / 4`, the path is the smoothed maximum of `M` and `A - η`. -/
theorem smoothedMaxPath_of_le (hσ : σ ≤ 1 / 4) :
    smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r - η) := by
  funext r
  rw [smoothedMaxPath_def, collaredSmoothTransition_eq_zero_of_le hσ, sub_zero, one_mul]

/-- From `σ = 3 / 4` on, the path is the smoothed maximum of `M` and `A`. -/
theorem smoothedMaxPath_of_ge (hσ : 3 / 4 ≤ σ) :
    smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r) := by
  funext r
  rw [smoothedMaxPath_def, collaredSmoothTransition_eq_one_of_ge hσ, sub_self, zero_mul,
    sub_zero]

/-- From `σ = 3 / 4` on, the path from the `i`-th member of the chain of smoothed maxima towards
`A (i + 1)` is the `(i + 1)`-st member. -/
theorem smoothedMaxPath_smoothedMaxChain_of_ge {A : ℕ → ℝ → ℝ} {i : ℕ} (hσ : 3 / 4 ≤ σ) :
    smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) σ = smoothedMaxChain δ A (i + 1) := by
  rw [smoothedMaxPath_of_ge hσ, smoothedMaxChain_succ]

/-- Up to `σ = 1 / 4`, the path is `M` wherever `A - η` lies at least `δ` below `M`. -/
theorem smoothedMaxPath_eq_left (hδ : 0 < δ) (hσ : σ ≤ 1 / 4) (h : A r - η + δ ≤ M r) :
    smoothedMaxPath δ η M A σ r = M r := by
  rw [smoothedMaxPath_of_le hσ]
  exact smoothedMax_eq_left hδ h

/-- For `η ≥ 0`, the path is monotone in `σ` at each `r`. -/
theorem monotone_smoothedMaxPath (hη : 0 ≤ η) (r : ℝ) :
    Monotone fun σ ↦ smoothedMaxPath δ η M A σ r := fun σ σ' hσ ↦ by
  simp only [smoothedMaxPath_def]
  refine monotone_smoothedMax_right δ (M r) ?_
  have := monotone_collaredSmoothTransition hσ
  nlinarith

/-- For `η ≥ 0`, the shape of the path at `σ` is the smoothed maximum of `M` and `A - c` for some
`c ∈ [0, η]`, namely `c = (1 - collaredSmoothTransition σ) * η`. -/
theorem exists_mem_Icc_smoothedMaxPath_eq (hη : 0 ≤ η) (σ : ℝ) :
    ∃ c ∈ Icc 0 η, smoothedMaxPath δ η M A σ = fun r ↦ smoothedMax δ (M r) (A r - c) :=
  ⟨_, one_sub_collaredSmoothTransition_mul_mem_Icc hη σ,
    funext fun r ↦ smoothedMaxPath_def δ η M A σ r⟩

/-- For `η ≥ 0`, the path consists of `i`-convex shapes at `r` if `M` and `A` are `C²`, `M` and
`A - η` are `i`-convex shapes at `r`, and `δ (M' r + A' r) ≤ 2 r`. -/
theorem isConvexShapeAt_smoothedMaxPath (hδ : 0 < δ) (hη : 0 ≤ η) (hM : ContDiff ℝ 2 M)
    (hA : ContDiff ℝ 2 A) (hcM : IsConvexShapeAt M r)
    (hcA : IsConvexShapeAt (fun r ↦ A r - η) r)
    (hδr : δ * (deriv M r + deriv A r) ≤ 2 * r) (σ : ℝ) :
    IsConvexShapeAt (smoothedMaxPath δ η M A σ) r := by
  obtain ⟨c, hc, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  rw [he]
  have hAc : IsConvexShapeAt (fun r ↦ A r - c) r := by
    convert hcA.add_const (c := η - c) (by linarith [hc.2]) using 2
    ring
  exact isConvexShapeAt_smoothedMax hM.contDiffAt (hA.sub contDiff_const).contDiffAt hδ hcM hAc
    (by rwa [deriv_sub_const])

/-- **The path keeps the smaller margin in (4.3).** For `δ > 0`, `0 ≤ η < A r`, `M r > 0` and
`M`, `A` differentiable at `r`, the margin `χ' / r - 1 / χ` of each shape `χ` of the path at `r`
is at least the smaller of those of `M` and of `A - η`. The latter is that of `A` less
`η / (A r (A r - η))` (`deriv_sub_const_div_sub_one_div_sub_const`). -/
theorem min_le_deriv_smoothedMaxPath_div_sub_one_div (hδ : 0 < δ) (hη : 0 ≤ η)
    (hηA : η < A r) (hM₀ : 0 < M r) (hMd : DifferentiableAt ℝ M r)
    (hAd : DifferentiableAt ℝ A r) (σ : ℝ) :
    min (deriv M r / r - 1 / M r) (deriv A r / r - 1 / (A r - η)) ≤
      deriv (smoothedMaxPath δ η M A σ) r / r - 1 / smoothedMaxPath δ η M A σ r := by
  obtain ⟨c, ⟨-, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  have hAc : 0 < A r - c := by linarith
  have h := min_le_deriv_smoothedMax_div_sub_one_div hMd (hAd.sub_const c) hδ hM₀ hAc
  rw [deriv_sub_const] at h
  have hb : 1 / (A r - c) ≤ 1 / (A r - η) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [he]
  exact (min_le_min_left _ (by linarith)).trans h

/-- **The path keeps the smaller margin in the case `σ = r` of (4.4).** For `δ > 0`, `r > 0`,
`0 ≤ η < A r`, `M r > 0`, `M` and `A` of class `C²` with `M' r, A' r ≥ 0` and
`δ (M' r + A' r) ≤ 2 r`, the margin `χ'' + χ'³ / r - 1 / χ` of each shape `χ` of the path at
`r` is at least the smaller of those of `M` and of `A - η`. The latter is that of `A` less
`η / (A r (A r - η))` (`iteratedDeriv_two_sub_const_add_pow_three_div_sub_one_div_sub_const`). -/
theorem min_le_iteratedDeriv_two_smoothedMaxPath_add_pow_three_div_sub_one_div (hδ : 0 < δ)
    (hr : 0 < r) (hη : 0 ≤ η) (hηA : η < A r) (hM₀ : 0 < M r) (hM : ContDiff ℝ 2 M)
    (hA : ContDiff ℝ 2 A) (hMd : 0 ≤ deriv M r) (hAd : 0 ≤ deriv A r)
    (hδr : δ * (deriv M r + deriv A r) ≤ 2 * r) (σ : ℝ) :
    min (iteratedDeriv 2 M r + deriv M r ^ 3 / r - 1 / M r)
        (iteratedDeriv 2 A r + deriv A r ^ 3 / r - 1 / (A r - η)) ≤
      iteratedDeriv 2 (smoothedMaxPath δ η M A σ) r +
        deriv (smoothedMaxPath δ η M A σ) r ^ 3 / r - 1 / smoothedMaxPath δ η M A σ r := by
  obtain ⟨c, ⟨-, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq (δ := δ) (M := M) (A := A) hη σ
  have hAc : 0 < A r - c := by linarith
  have h := min_le_iteratedDeriv_two_smoothedMax_add_pow_three_div_sub_one_div hM.contDiffAt
    (hA.sub contDiff_const).contDiffAt hδ hr hM₀ hAc hMd (by rwa [deriv_sub_const])
    (by rwa [deriv_sub_const])
  rw [deriv_sub_const, iteratedDeriv_sub_const two_pos] at h
  have hb : 1 / (A r - c) ≤ 1 / (A r - η) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [he]
  exact (min_le_min_left _ (by linarith)).trans h

/-! ### A chain of paths between smoothed maxima -/

section shapeChain

variable {a h ℓ ℓ' : ℝ} {A : ℕ → ℝ → ℝ} {N : ℕ}

/-- The **chain of paths between smoothed maxima** on the mesh `a + i h`, `i ≤ N`: the family
`(ℓ, r) ↦ shapeChain δ η a h A N ℓ r`, starting from `smoothedMaxChain δ A 0 = A 0`, that adds for
each `i < N` the increment of the path `smoothedMaxPath δ η (M i) (A (i + 1))` at the parameter
`(ℓ - a - i h) / h` over its value at the start, where `M = smoothedMaxChain δ A`. For `h > 0`,
each increment vanishes up to `ℓ = a + (i + 1 / 4) h` and is constant in `ℓ` from
`ℓ = a + (i + 3 / 4) h` on, and where the joints match the family runs along the path from `M j`
to `M (j + 1)` while `ℓ` runs from `a + j h` to `a + (j + 1) h`
(`shapeChain_eq_smoothedMaxPath`). -/
def shapeChain (δ η a h : ℝ) (A : ℕ → ℝ → ℝ) (N : ℕ) (ℓ r : ℝ) : ℝ :=
  smoothedMaxChain δ A 0 r + ∑ i ∈ Finset.range N,
    (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
      smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η))

theorem shapeChain_def (δ η a h : ℝ) (A : ℕ → ℝ → ℝ) (N : ℕ) (ℓ r : ℝ) :
    shapeChain δ η a h A N ℓ r = smoothedMaxChain δ A 0 r + ∑ i ∈ Finset.range N,
      (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
        smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η)) :=
  (rfl)

/-- The chain of paths between smoothed maxima of `Cⁿ` functions is `Cⁿ` in `(ℓ, r)`. -/
theorem contDiff_shapeChain {n : ℕ∞} (hA : ∀ i ≤ N, ContDiff ℝ n (A i)) :
    ContDiff ℝ n (Function.uncurry (shapeChain δ η a h A N)) := by
  have hM {i : ℕ} (hi : i ≤ N) : ContDiff ℝ n (smoothedMaxChain δ A i) :=
    contDiff_smoothedMaxChain δ fun j hj ↦ hA j (hj.trans hi)
  have hσ (i : ℕ) : ContDiff ℝ n fun x : ℝ × ℝ ↦ ((x.1 - a - i * h) / h, x.2) :=
    (((contDiff_fst.sub contDiff_const).sub contDiff_const).div_const h).prodMk contDiff_snd
  have key : ContDiff ℝ n fun x : ℝ × ℝ ↦ smoothedMaxChain δ A 0 x.2 + ∑ i ∈ Finset.range N,
      (Function.uncurry (smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)))
          ((x.1 - a - i * h) / h, x.2) -
        smoothedMax δ (smoothedMaxChain δ A i x.2) (A (i + 1) x.2 - η)) :=
    ((hM (Nat.zero_le N)).comp contDiff_snd).add (ContDiff.sum fun i hi ↦ by
      have hi : i < N := Finset.mem_range.1 hi
      exact ((contDiff_smoothedMaxPath (hM hi.le) (hA (i + 1) hi)).comp (hσ i)).sub
        ((contDiff_smoothedMax δ).comp (((hM hi.le).comp contDiff_snd).prodMk
          (((hA (i + 1) hi).comp contDiff_snd).sub contDiff_const))))
  convert key using 1
  funext ⟨ℓ, r⟩
  simp only [Function.uncurry_apply_pair, shapeChain_def]

/-- For `h > 0` and `η ≥ 0`, the chain of paths between smoothed maxima is monotone in `ℓ` at each
`r`; so its `ℓ`-derivative is nonnegative (`Monotone.deriv_nonneg`). -/
theorem monotone_shapeChain (hh : 0 < h) (hη : 0 ≤ η) (r : ℝ) :
    Monotone fun ℓ ↦ shapeChain δ η a h A N ℓ r := fun ℓ ℓ' hℓ ↦ by
  simp only [shapeChain_def]
  gcongr with i
  exact monotone_smoothedMaxPath hη r (div_le_div_of_nonneg_right
    (sub_le_sub_right (sub_le_sub_right hℓ a) _) hh.le)

/-- For `h > 0`, the chain of paths between smoothed maxima is `A 0` up to `ℓ = a + h / 4`. -/
theorem shapeChain_of_le (hh : 0 < h) (hℓ : ℓ ≤ a + h / 4) :
    shapeChain δ η a h A N ℓ = A 0 := by
  funext r
  rw [shapeChain_def, smoothedMaxChain_zero, add_eq_left]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi := mul_nonneg i.cast_nonneg hh.le
  rw [smoothedMaxPath_of_le ((div_le_iff₀ hh).2 (by linarith)), sub_self]

/-- For `h > 0`, the chain of paths between smoothed maxima does not depend on `ℓ` from
`ℓ = a + (N - 1 / 4) h` on. -/
theorem shapeChain_eq_of_ge (hh : 0 < h) (hℓ : a + (N - 1 / 4) * h ≤ ℓ)
    (hℓ' : a + (N - 1 / 4) * h ≤ ℓ') :
    shapeChain δ η a h A N ℓ = shapeChain δ η a h A N ℓ' := by
  funext r
  simp only [shapeChain_def]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
  have hle : a + (i + 3 / 4) * h ≤ a + (N - 1 / 4) * h := by nlinarith
  rw [smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by linarith)),
    smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by linarith))]

/-- **The local form of the chain of paths.** For `δ > 0` and `h > 0`, at an `r` where the joints
match, `A (i + 1) r - η + δ ≤ M i r` for `i < N` with `M = smoothedMaxChain δ A`, the chain of
paths between smoothed maxima is, for `ℓ ∈ [a + j h, a + (j + 1) h]` and `j < N`, the path from
`M j` to `M (j + 1)` at the parameter `(ℓ - a - j h) / h`. -/
theorem shapeChain_eq_smoothedMaxPath (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) {j : ℕ} (hj : j < N)
    (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) :
    shapeChain δ η a h A N ℓ r =
      smoothedMaxPath δ η (smoothedMaxChain δ A j) (A (j + 1)) ((ℓ - a - j * h) / h) r := by
  rw [shapeChain_def, Finset.add_sum_range_eq_of_lt (v := fun i ↦ smoothedMaxChain δ A i r) hj
    (fun i hij ↦ ?_) (fun i hij hiN ↦ ?_), smoothedMax_eq_left hδ (hJ j hj), add_sub_cancel]
  · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    rw [smoothedMax_eq_left hδ (hJ i (hij.trans hj)),
      smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by nlinarith [hℓ.1]))]
  · have hij' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
    have hσ : (ℓ - a - i * h) / h ≤ 1 / 4 := (div_le_iff₀ hh).2 (by nlinarith [hℓ.2])
    rw [smoothedMaxPath_eq_left hδ hσ (hJ i hiN), smoothedMax_eq_left hδ (hJ i hiN), sub_self]

/-- For `δ > 0` and `h > 0`, at an `r` where the joints match, `A (i + 1) r - η + δ ≤ M i r` for
`i < N` with `M = smoothedMaxChain δ A`, the chain of paths between smoothed maxima is `M N` from
`ℓ = a + N h` on. -/
theorem shapeChain_eq_smoothedMaxChain (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) (hℓ : a + N * h ≤ ℓ) :
    shapeChain δ η a h A N ℓ r = smoothedMaxChain δ A N r := by
  have key : ∀ i ∈ Finset.range N,
      smoothedMaxPath δ η (smoothedMaxChain δ A i) (A (i + 1)) ((ℓ - a - i * h) / h) r -
        smoothedMax δ (smoothedMaxChain δ A i r) (A (i + 1) r - η) =
          smoothedMaxChain δ A (i + 1) r - smoothedMaxChain δ A i r := by
    intro i hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
    rw [smoothedMax_eq_left hδ (hJ i (Finset.mem_range.1 hi)),
      smoothedMaxPath_smoothedMaxChain_of_ge ((le_div_iff₀ hh).2 (by nlinarith))]
  rw [shapeChain_def, Finset.sum_congr rfl key,
    Finset.sum_range_sub fun i ↦ smoothedMaxChain δ A i r]
  ring

/-- For `δ > 0` and `h > 0`, along a filter on which the joints eventually match,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, the shape of the chain of
paths between smoothed maxima at `ℓ ∈ [a + j h, a + (j + 1) h]`, `j < N`, is eventually that of
the path from `M j` to `M (j + 1)` at the parameter `(ℓ - a - j h) / h`. -/
theorem shapeChain_eventuallyEq_smoothedMaxPath {l : Filter ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ᶠ r in l, ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r) {j : ℕ}
    (hj : j < N) (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) :
    shapeChain δ η a h A N ℓ =ᶠ[l]
      smoothedMaxPath δ η (smoothedMaxChain δ A j) (A (j + 1)) ((ℓ - a - j * h) / h) :=
  hJ.mono fun _ hr ↦ shapeChain_eq_smoothedMaxPath hδ hh hr hj hℓ

/-- For `δ > 0` and `h > 0`, along a filter on which the joints eventually match,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, the shape of the chain of
paths between smoothed maxima at `ℓ ≥ a + N h` is eventually `M N`. -/
theorem shapeChain_eventuallyEq_smoothedMaxChain {l : Filter ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hJ : ∀ᶠ r in l, ∀ i < N, A (i + 1) r - η + δ ≤ smoothedMaxChain δ A i r)
    (hℓ : a + N * h ≤ ℓ) :
    shapeChain δ η a h A N ℓ =ᶠ[l] smoothedMaxChain δ A N :=
  hJ.mono fun _ hr ↦ shapeChain_eq_smoothedMaxChain hδ hh hr hℓ

/-- For `δ > 0`, if the `A i`, `i ≤ N`, are continuous at `r` and the joints match strictly at
`r`, `A (i + 1) r - η + δ < A i r` for `i < N`, then the joints match near `r`:
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`. -/
theorem eventually_forall_sub_add_le_smoothedMaxChain (hδ : 0 < δ)
    (hA : ∀ i ≤ N, ContinuousAt (A i) r) (hJ : ∀ i < N, A (i + 1) r - η + δ < A i r) :
    ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r' := by
  have h : ∀ᶠ r' in 𝓝 r, ∀ i ∈ Iio N, A (i + 1) r' - η + δ < A i r' :=
    (finite_Iio N).eventually_all.2 fun i hi ↦
      (((hA (i + 1) hi).sub continuousAt_const).add continuousAt_const).eventually_lt
        (hA i hi.le) (hJ i hi)
  filter_upwards [h] with r' hr' i hi
  exact (hr' i hi).le.trans (le_smoothedMaxChain hδ A i r')

/-- **The chain of paths consists of `i`-convex shapes.** For `δ, h > 0` and `η ≥ 0`, let the
`A i`, `i ≤ N`, be `C²` and `i`-convex shapes at `r` with `deriv (A i) r ≤ G` and `δ G ≤ r`, let
the `A (i + 1) - η`, `i < N`, be `i`-convex shapes at `r`, and let the joints match near `r`:
`A (i + 1) - η + δ ≤ M i` for `i < N`, with `M = smoothedMaxChain δ A`. Then every member of the
chain of paths between smoothed maxima is an `i`-convex shape at `r`. -/
theorem isConvexShapeAt_shapeChain {G : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hη : 0 ≤ η)
    (hA : ∀ i ≤ N, ContDiff ℝ 2 (A i))
    (hJ : ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r')
    (hc : ∀ i ≤ N, IsConvexShapeAt (A i) r)
    (hcη : ∀ i < N, IsConvexShapeAt (fun r ↦ A (i + 1) r - η) r)
    (hG : ∀ i ≤ N, deriv (A i) r ≤ G) (hδG : δ * G ≤ r) (ℓ : ℝ) :
    IsConvexShapeAt (shapeChain δ η a h A N ℓ) r := by
  have hM {j : ℕ} (hj : j ≤ N) : IsConvexShapeAt (smoothedMaxChain δ A j) r :=
    isConvexShapeAt_smoothedMaxChain hδ (fun i hi ↦ hA i (hi.trans hj))
      (fun i hi ↦ hc i (hi.trans hj)) (fun i hi ↦ hG i (hi.trans hj)) hδG
  rcases le_or_gt ℓ a with hℓa | hℓa
  · rw [shapeChain_of_le hh (by linarith)]
    exact hc 0 (Nat.zero_le N)
  rcases le_or_gt (a + N * h) ℓ with hℓN | hℓN
  · exact (hM le_rfl).congr_of_eventuallyEq
      (shapeChain_eventuallyEq_smoothedMaxChain hδ hh hJ hℓN)
  -- `ℓ` lies in the `j`-th interval of the mesh for some `j < N`.
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hℓN; linarith
  obtain ⟨j, hj, hℓj⟩ := exists_lt_mem_Icc_add_mul hh hN ⟨hℓa.le, hℓN.le⟩
  refine IsConvexShapeAt.congr_of_eventuallyEq ?_
    (shapeChain_eventuallyEq_smoothedMaxPath hδ hh hJ hj hℓj)
  have hd : ∀ i ≤ j, DifferentiableAt ℝ (A i) r := fun i hi ↦
    ((hA i (hi.trans hj.le)).differentiable two_ne_zero).differentiableAt
  have hdM := deriv_smoothedMaxChain_le δ hd fun i hi ↦ hG i (hi.trans hj.le)
  have hdA := hG (j + 1) hj
  refine isConvexShapeAt_smoothedMaxPath hδ hη
    (contDiff_smoothedMaxChain δ fun i hi ↦ hA i (hi.trans hj.le)) (hA (j + 1) hj) (hM hj.le)
    (hcη j hj) ?_ _
  nlinarith

/-- **The chain of paths stays `C²`-close to what its ends are close to.** For `δ, h > 0` and
`η ≥ 0`, let `A j` and `A (j + 1)` be `C²`, let the joints match near `r`,
`A (i + 1) - η + δ ≤ M i` for `i < N` with `M = smoothedMaxChain δ A`, and let `A 0, …, A j` each
lie at least `δ` below the next near `r`, so that `M j = A j` near `r`. If `C / δ` bounds the
curvature of `smoothedAbs δ`, then for `ℓ ∈ [a + j h, a + (j + 1) h]` and any values `φ 0`,
`φ 1`, `φ 2`, the value and the first two derivatives at `r` of the member of the chain at `ℓ`
are as close to `φ 0`, `φ 1`, `φ 2` as the farther of those of `A j` and `A (j + 1)`, up to
`η + δ / 2` for the value and `C (A j' r - A (j + 1)' r)² / (2 δ)` for the second derivative. -/
theorem abs_iteratedDeriv_shapeChain_sub_le {C : ℝ} {j : ℕ} (hδ : 0 < δ) (hh : 0 < h)
    (hη : 0 ≤ η) (hAj : ContDiff ℝ 2 (A j)) (hAj₁ : ContDiff ℝ 2 (A (j + 1)))
    (hJ : ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r')
    (hup : ∀ᶠ r' in 𝓝 r, ∀ i < j, A i r' + δ ≤ A (i + 1) r')
    (hC : ∀ t, iteratedDeriv 2 (smoothedAbs δ) t ≤ C / δ) (hj : j < N)
    (hℓ : ℓ ∈ Icc (a + j * h) (a + (j + 1) * h)) (φ : ℕ → ℝ) :
    |shapeChain δ η a h A N ℓ r - φ 0| ≤
        max |A j r - φ 0| |A (j + 1) r - φ 0| + η + δ / 2 ∧
      |deriv (shapeChain δ η a h A N ℓ) r - φ 1| ≤
        max |deriv (A j) r - φ 1| |deriv (A (j + 1)) r - φ 1| ∧
      |iteratedDeriv 2 (shapeChain δ η a h A N ℓ) r - φ 2| ≤
        max |iteratedDeriv 2 (A j) r - φ 2| |iteratedDeriv 2 (A (j + 1)) r - φ 2| +
          C * (deriv (A j) r - deriv (A (j + 1)) r) ^ 2 / (2 * δ) := by
  obtain ⟨c, ⟨hc₀, hcη⟩, he⟩ := exists_mem_Icc_smoothedMaxPath_eq
    (δ := δ) (M := smoothedMaxChain δ A j) (A := A (j + 1)) hη ((ℓ - a - j * h) / h)
  -- Near `r`, the member of the chain at `ℓ` is the smoothed maximum of `A j` and `A (j + 1) - c`.
  have hloc : shapeChain δ η a h A N ℓ =ᶠ[𝓝 r]
      fun r' ↦ smoothedMax δ (A j r') (A (j + 1) r' - c) := by
    filter_upwards [shapeChain_eventuallyEq_smoothedMaxPath hδ hh hJ hj hℓ,
      smoothedMaxChain_eventuallyEq hδ hup] with r' h₁ h₂
    rw [h₁, he]
    exact congrArg (smoothedMax δ · (A (j + 1) r' - c)) h₂
  have hd : DifferentiableAt ℝ (A j) r := (hAj.differentiable two_ne_zero).differentiableAt
  have hd₁ : DifferentiableAt ℝ (A (j + 1)) r :=
    (hAj₁.differentiable two_ne_zero).differentiableAt
  refine ⟨?_, ?_, ?_⟩
  · rw [hloc.eq_of_nhds]
    have hc : |A (j + 1) r - c - φ 0| ≤ |A (j + 1) r - φ 0| + η := by
      rw [sub_right_comm]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hc₀]; linarith)
    have hm : max |A j r - φ 0| |A (j + 1) r - c - φ 0| ≤
        max |A j r - φ 0| |A (j + 1) r - φ 0| + η :=
      max_le (by linarith [le_max_left |A j r - φ 0| |A (j + 1) r - φ 0|])
        (hc.trans (by linarith [le_max_right |A j r - φ 0| |A (j + 1) r - φ 0|]))
    linarith [abs_smoothedMax_sub_le hδ (A j r) (A (j + 1) r - c) (φ 0)]
  · rw [hloc.deriv_eq]
    simpa only [deriv_sub_const] using abs_deriv_smoothedMax_sub_le hd (hd₁.sub_const c) (φ 1)
  · rw [hloc.iteratedDeriv_eq 2]
    simpa only [deriv_sub_const, iteratedDeriv_sub_const two_pos] using
      abs_iteratedDeriv_two_smoothedMax_sub_le hAj.contDiffAt (hAj₁.sub contDiff_const).contDiffAt
        hδ.le (hC _) (φ 2)

end shapeChain

/-- A member `χ ℓ` of a family that is `C²` in `r` over `[a, b] × [r₁, r₂]` and smooth on an open
set `U` containing `[a, b] × [r₃, r₂]` and `{a} × [r₁, r₂]` has, for every `θ > 0`, a smooth
replacement `g` whose value and first two derivatives are within `θ` of those of `χ ℓ` on
`[r₁, r₂]`, which agrees with `χ ℓ` near `[r₃, r₂]`, and which for `ℓ = a` agrees with `χ a`
near `[r₁, r₂]`. -/
theorem exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc {a b r₃ ℓ θ : ℝ} {U : Set (ℝ × ℝ)}
    (hC2 : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, ContDiffAt ℝ 2 (χ x.1) x.2) (hU : IsOpen U)
    (hEU : {a} ×ˢ Icc r₁ r₂ ∪ Icc a b ×ˢ Icc r₃ r₂ ⊆ U)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry χ) U) (hℓ : ℓ ∈ Icc a b) (hθ : 0 < θ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ 2, ∀ r ∈ Icc r₁ r₂, |iteratedDeriv k g r - iteratedDeriv k (χ ℓ) r| < θ) ∧
      g =ᶠ[𝓝ˢ (Icc r₃ r₂)] χ ℓ ∧ (ℓ = a → g =ᶠ[𝓝ˢ (Icc r₁ r₂)] χ a) := by
  -- The slice of `U` at `ℓ` is open, and `χ ℓ` is smooth on it.
  have hcont : Continuous fun r : ℝ ↦ (ℓ, r) := by fun_prop
  have hS : IsOpen {r | (ℓ, r) ∈ U} := hU.preimage hcont
  have hχS : ContDiffOn ℝ ∞ (χ ℓ) {r | (ℓ, r) ∈ U} :=
    hsmooth.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hr ↦ hr
  -- The approximation that agrees with `χ ℓ` near `[c, r₂]`, for `[c, r₂]` in the slice.
  have key : ∀ c, Icc c r₂ ⊆ {r | (ℓ, r) ∈ U} → ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      (∀ k ≤ 2, ∀ r ∈ Icc r₁ r₂, |iteratedDeriv k g r - iteratedDeriv k (χ ℓ) r| < θ) ∧
      g =ᶠ[𝓝ˢ (Icc c r₂)] χ ℓ := fun c hc ↦
    hχS.exists_contDiff_abs_iteratedDeriv_sub_lt_of_contDiffAt
      (fun r hr ↦ hC2 (ℓ, r) ⟨hℓ, hr⟩) hS hc hθ
  by_cases ha : ℓ = a
  · subst ha
    obtain ⟨g, hg, hgθ, hgc⟩ := key (min r₁ r₃) fun r hr ↦ by
      rcases le_or_gt r₁ r with h | h
      · exact hEU (Or.inl ⟨rfl, h, hr.2⟩)
      · exact hEU (Or.inr ⟨⟨le_rfl, hℓ.2⟩, (min_le_iff.1 hr.1).resolve_left h.not_ge, hr.2⟩)
    exact ⟨g, hg, hgθ, hgc.filter_mono (nhdsSet_mono (Icc_subset_Icc_left (min_le_right _ _))),
      fun _ ↦ hgc.filter_mono (nhdsSet_mono (Icc_subset_Icc_left (min_le_left _ _)))⟩
  · obtain ⟨g, hg, hgθ, hgc⟩ := key r₃ fun r hr ↦ hEU (Or.inr ⟨hℓ, hr⟩)
    exact ⟨g, hg, hgθ, hgc, fun h ↦ absurd h ha⟩

/-- A step of `exists_monotone_shapeChain`, at a point `r`: let the `A i` be within `θ` in value
and first two derivatives of members `χ (t i)` whose `C²`-neighbourhoods of radius `η₁` at `r`
consist of `i`-convex shapes at `r`, let consecutive members differ at `r` by less than `ε₀`, and
let `θ + η < η₁` and `2 θ + ε₀ + δ ≤ η` with `η > 0`. Then the joints match strictly at `r`,
`A (i + 1) r - η + δ < A i r` for `i < N`, and each `A i` and each `A i - η` is an `i`-convex
shape at `r`. -/
private theorem sub_add_lt_and_isConvexShapeAt_of_abs_iteratedDeriv_sub_lt
    {A : ℕ → ℝ → ℝ} {t : ℕ → ℝ} {N : ℕ} {r θ η δ η₁ ε₀ : ℝ}
    (hstab : ∀ i, ∀ g : ℝ → ℝ,
      (∀ k ≤ 2, |iteratedDeriv k g r - iteratedDeriv k (χ (t i)) r| < η₁) → IsConvexShapeAt g r)
    (hAθ : ∀ i, ∀ k ≤ 2, |iteratedDeriv k (A i) r - iteratedDeriv k (χ (t i)) r| < θ)
    (hu : ∀ i < N, |χ (t (i + 1)) r - χ (t i) r| < ε₀) (hη : 0 < η) (hθη₁ : θ + η < η₁)
    (hJη : 2 * θ + ε₀ + δ ≤ η) :
    (∀ i < N, A (i + 1) r - η + δ < A i r) ∧ (∀ i, IsConvexShapeAt (A i) r) ∧
      ∀ i, IsConvexShapeAt (fun r ↦ A i r - η) r := by
  refine ⟨fun i hi ↦ ?_, fun i ↦ hstab i _ fun k hk ↦ (hAθ i k hk).trans (by linarith),
    fun i ↦ hstab i _ fun k hk ↦ ?_⟩
  · have h₁ := (abs_lt.1 (hAθ (i + 1) 0 (by norm_num))).2
    have h₂ := (abs_lt.1 (hAθ i 0 (by norm_num))).1
    have h₃ := (abs_lt.1 (hu i hi)).2
    simp only [iteratedDeriv_zero] at h₁ h₂
    linarith
  · have h := hAθ i k hk
    interval_cases k
    · simp only [iteratedDeriv_zero] at h ⊢
      have h' : |A i r - η - χ (t i) r| ≤ |A i r - χ (t i) r| + η := by
        rw [sub_right_comm]
        exact (abs_sub _ _).trans (by rw [abs_of_pos hη])
      linarith
    · simp only [iteratedDeriv_one, deriv_sub_const] at h ⊢
      linarith
    · rw [iteratedDeriv_sub_const two_pos]
      linarith

/-- A step of `exists_monotone_shapeChain`, on the band `[a, b] × [r₃, r₂]`: let `δ, h > 0`,
`η ≥ 0`, let the `A i` be `C²` and equal to `χ (t i)` near `[r₃, r₂]`, on the mesh
`t i = a + i h`, `i ≤ N`, with `a + N h = b`, and let the joints match near `r`. Let `χ` climb in
`ℓ` at rate at least `m` on the band, with `δ < m h`, let `∂χ/∂r` be `L`-Lipschitz in `ℓ` there,
let `Q / δ` bound the curvature of `smoothedAbs δ`, with `Q L² h² ≤ τ δ`, and let the value and
first two derivatives of `χ` vary by less than `ε₀` over steps in `ℓ` of at most `h`. If
`ε₀, η, δ ≤ τ / 4`, then at each point of the band the members of `shapeChain δ η a h A N` are
within `τ` of those of `χ` in value and first two derivatives. -/
private theorem abs_iteratedDeriv_shapeChain_sub_lt_of_mem_band {A : ℕ → ℝ → ℝ} {t : ℕ → ℝ}
    {N k : ℕ} {a b r₃ δ η h m L Q ε₀ τ ℓ r : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hη : 0 ≤ η)
    (hN : 0 < N) (hNh : a + N * h = b) (ht : ∀ i ≤ N, t i = a + i * h)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (hAb : ∀ i, A i =ᶠ[𝓝ˢ (Icc r₃ r₂)] χ (t i))
    (hJ : ∀ᶠ r' in 𝓝 r, ∀ i < N, A (i + 1) r' - η + δ ≤ smoothedMaxChain δ A i r')
    (hrate : ∀ r ∈ Icc r₃ r₂, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, ℓ ≤ ℓ' →
      m * (ℓ' - ℓ) ≤ χ ℓ' r - χ ℓ r) (hδm : δ < m * h)
    (hL : ∀ r ∈ Icc r₃ r₂, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b,
      |deriv (χ ℓ') r - deriv (χ ℓ) r| ≤ L * |ℓ' - ℓ|)
    (hQ : 0 ≤ Q) (hQδ : ∀ s, iteratedDeriv 2 (smoothedAbs δ) s ≤ Q / δ)
    (hQL : Q * L ^ 2 * h ^ 2 ≤ τ * δ)
    (hu : ∀ k ≤ 2, ∀ r ∈ Icc r₃ r₂, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b, |ℓ' - ℓ| ≤ h →
      |iteratedDeriv k (χ ℓ') r - iteratedDeriv k (χ ℓ) r| < ε₀)
    (hε₀ : ε₀ ≤ τ / 4) (hητ : η ≤ τ / 4) (hδτ : δ ≤ τ / 4)
    (hℓ : ℓ ∈ Icc a b) (hr : r ∈ Icc r₃ r₂) (hk : k ≤ 2) :
    |iteratedDeriv k (shapeChain δ η a h A N ℓ) r - iteratedDeriv k (χ ℓ) r| < τ := by
  have htI (i : ℕ) (hi : i ≤ N) : t i ∈ Icc a b := by
    have : (i : ℝ) ≤ N := by exact_mod_cast hi
    rw [ht i hi]
    exact ⟨le_add_of_nonneg_right (by positivity), by nlinarith⟩
  have hstep (i : ℕ) (hi : i < N) : t (i + 1) - t i = h := by
    rw [ht _ hi, ht _ hi.le]
    push_cast
    ring
  obtain ⟨j, hj, hℓj⟩ := exists_lt_mem_Icc_add_mul hh hN ⟨hℓ.1, by linarith [hℓ.2]⟩
  have hAe (i : ℕ) : A i =ᶠ[𝓝 r] χ (t i) := (hAb i).filter_mono (nhds_le_nhdsSet hr)
  -- Near `r`, the stand-ins climb by more than `δ` up to the `j`-th one.
  have hup : ∀ᶠ r' in 𝓝 r, ∀ i < j, A i r' + δ ≤ A (i + 1) r' := by
    have h : ∀ᶠ r' in 𝓝 r, ∀ i ∈ Iio j, A i r' + δ < A (i + 1) r' :=
      (finite_Iio j).eventually_all.2 fun i hi ↦
        ((hA i).continuous.add continuous_const).continuousAt.eventually_lt
          (hA (i + 1)).continuous.continuousAt (by
            have hiN : i < N := lt_trans hi hj
            simp only [Pi.add_apply]
            rw [(hAe i).eq_of_nhds, (hAe (i + 1)).eq_of_nhds]
            have h₁ := hrate r hr (t i) (htI i hiN.le) (t (i + 1)) (htI _ hiN)
              (by linarith [hstep i hiN])
            rw [hstep i hiN] at h₁
            linarith)
    filter_upwards [h] with r' hr' i hi using (hr' i hi).le
  obtain ⟨e₀, e₁, e₂⟩ := abs_iteratedDeriv_shapeChain_sub_le hδ hh hη (hA j) (hA (j + 1))
    hJ hup hQδ hj hℓj (fun k ↦ iteratedDeriv k (χ ℓ) r)
  rw [(hAe j).eq_of_nhds, (hAe (j + 1)).eq_of_nhds] at e₀
  rw [(hAe j).deriv_eq, (hAe (j + 1)).deriv_eq] at e₁ e₂
  rw [(hAe j).iteratedDeriv_eq 2, (hAe (j + 1)).iteratedDeriv_eq 2] at e₂
  -- The ends `t j` and `t (j + 1)` of the interval of the mesh that contains `ℓ` are within `h`
  -- of `ℓ`.
  have hjh : ((j : ℝ) + 1) * h = j * h + h := by ring
  have hj₁ : |t j - ℓ| ≤ h := by
    rw [ht j hj.le, abs_le]
    constructor <;> linarith [hℓj.1, hℓj.2, hjh]
  have hj₂ : |t (j + 1) - ℓ| ≤ h := by
    rw [ht (j + 1) hj, abs_le]
    push_cast
    constructor <;> linarith [hℓj.1, hℓj.2, hjh]
  have a₁ := hu k hk r hr ℓ hℓ (t j) (htI j hj.le) hj₁
  have a₂ := hu k hk r hr ℓ hℓ (t (j + 1)) (htI _ hj) hj₂
  simp only [iteratedDeriv_zero] at e₀
  simp only [iteratedDeriv_one] at e₁
  interval_cases k
  · simp only [iteratedDeriv_zero] at a₁ a₂ ⊢
    linarith [max_lt a₁ a₂]
  · simp only [iteratedDeriv_one] at a₁ a₂ ⊢
    linarith [max_lt a₁ a₂]
  · -- The curvature term is at most `τ / 2`.
    have hd := hL r hr (t (j + 1)) (htI _ hj) (t j) (htI j hj.le)
    rw [abs_sub_comm (t j), hstep j hj, abs_of_pos hh] at hd
    have hd2 : (deriv (χ (t j)) r - deriv (χ (t (j + 1))) r) ^ 2 ≤ (L * h) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have hLh : Q * (L * h) ^ 2 = Q * L ^ 2 * h ^ 2 := by ring
    have hkey : Q * (deriv (χ (t j)) r - deriv (χ (t (j + 1))) r) ^ 2 / (2 * δ) ≤ τ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [mul_le_mul_of_nonneg_left hd2 hQ, hLh]
    linarith [max_lt a₁ a₂]

/-- **A smooth weakly increasing chain of `i`-convex shapes.** Let `χ ℓ`, `ℓ ∈ [a, b]`, be
`i`-convex shapes on `[r₁, r₂]`, `r₁ > 0`, `C²` there with value and first two derivatives
continuous in `(ℓ, r)`, and let the family be smooth on an open set `U` that contains
`{a} × [r₁, r₂]` and the band `[a, b] × [r₃, r₂]`, `r₁ ≤ r₃`, with `∂χ/∂ℓ > 0` on the band.
Then for all `τ, ε > 0` there is a family `C`, smooth on all of `ℝ²`, such that on
`[a, b] × [r₁, r₂]` each `C ℓ` is an `i`-convex shape and `∂C/∂ℓ ≥ 0`; `C` is constant in `ℓ`
near `a` and near `b`, and `C a` equals `χ a` near `[r₁, r₂]`; at each `r ∈ [r₁, r₂]`, `C b r`
is at most `ε` above some `χ ℓ r`, `ℓ ∈ [a, b]`, and more than `χ b r - ε`; and on the band,
`C ℓ` is within `τ` of `χ ℓ` in value and first two derivatives. -/
theorem exists_monotone_shapeChain {a b r₃ τ ε : ℝ} {U : Set (ℝ × ℝ)} (hr₁ : 0 < r₁)
    (hab : a < b) (hr₁₃ : r₁ ≤ r₃)
    (hC2 : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, ContDiffAt ℝ 2 (χ x.1) x.2)
    (hc : ∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, IsConvexShapeAt (χ x.1) x.2)
    (hcont : ∀ k ≤ 2, ContinuousOn (fun x : ℝ × ℝ ↦ iteratedDeriv k (χ x.1) x.2)
      (Icc a b ×ˢ Icc r₁ r₂))
    (hU : IsOpen U) (hEU : {a} ×ˢ Icc r₁ r₂ ∪ Icc a b ×ˢ Icc r₃ r₂ ⊆ U)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry χ) U)
    (hmono : ∀ x ∈ Icc a b ×ˢ Icc r₃ r₂, 0 < deriv (fun ℓ' ↦ χ ℓ' x.2) x.1)
    (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ C : ℝ → ℝ → ℝ, ContDiff ℝ ∞ (Function.uncurry C) ∧
      (∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, IsConvexShapeAt (C x.1) x.2) ∧
      (∀ x ∈ Icc a b ×ˢ Icc r₁ r₂, 0 ≤ deriv (fun ℓ' ↦ C ℓ' x.2) x.1) ∧
      ((∀ᶠ ℓ in 𝓝 a, C ℓ = C a) ∧ C a =ᶠ[𝓝ˢ (Icc r₁ r₂)] χ a) ∧
      (∀ᶠ ℓ in 𝓝 b, C ℓ = C b) ∧
      (∀ r ∈ Icc r₁ r₂, ∃ ℓ ∈ Icc a b, C b r ≤ χ ℓ r + ε) ∧
      (∀ r ∈ Icc r₁ r₂, χ b r - ε < C b r) ∧
      ∀ x ∈ Icc a b ×ˢ Icc r₃ r₂, ∀ k ≤ 2,
        |iteratedDeriv k (C x.1) x.2 - iteratedDeriv k (χ x.1) x.2| < τ := by
  have hK : IsCompact (Icc a b ×ˢ Icc r₁ r₂) := isCompact_Icc.prod isCompact_Icc
  have hband : Icc a b ×ˢ Icc r₃ r₂ ⊆ U := fun x hx ↦ hEU (Or.inr hx)
  have hsub : Icc r₃ r₂ ⊆ Icc r₁ r₂ := Icc_subset_Icc_left hr₁₃
  have hba : 0 < b - a := sub_pos.2 hab
  -- The margin of stability of the convex shapes `χ ℓ` on the rectangle, a bound for their
  -- slopes there, and on the band a rate of increase in `ℓ` and a Lipschitz bound in `ℓ` for
  -- the slopes; last, a bound `C₀ / δ` for the curvature of `smoothedAbs δ`.
  obtain ⟨η₁, hη₁, hstab⟩ := exists_forall_isConvexShapeAt_of_abs_sub_lt hK hc hcont
  obtain ⟨G₀, hG₀⟩ := hK.exists_bound_of_continuousOn (hcont 1 (by norm_num))
  obtain ⟨m, hm, hrate⟩ := isCompact_Icc.exists_pos_mul_sub_le_sub_of_deriv_pos hU hband
    (hsmooth.of_le (by norm_cast)) hmono
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_abs_deriv_sub_le_mul hU hband
    (hsmooth.of_le (by norm_cast))
  obtain ⟨C₀, hC₀⟩ := exists_forall_iteratedDeriv_two_smoothedAbs_le
  set G := |G₀| + 1
  have hG : 0 < G := by positivity
  set Q := max C₀ 0
  have hQ : 0 ≤ Q := le_max_right _ _
  -- The constants: the lowering `η`, the error `θ` of the smooth stand-ins, the ratio `c` of the
  -- width `δ = c h` to the mesh `h`, and the error `ε₀` of uniform continuity in `ℓ`, up to a
  -- step `w` in `ℓ`.
  obtain ⟨η, hη, hηη₁, hητ⟩ : ∃ η > 0, η ≤ η₁ / 2 ∧ η ≤ τ / 4 :=
    ⟨min (η₁ / 2) (τ / 4), by positivity, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨θ, hθ, hθε, hθη, hθ1⟩ : ∃ θ > 0, θ ≤ ε / 2 ∧ θ ≤ η / 8 ∧ θ ≤ 1 :=
    ⟨min (ε / 2) (min (η / 8) 1), by positivity, by simp⟩
  obtain ⟨c, hc0, hcm, hcε, hcG, hcη⟩ :
      ∃ c > 0, c ≤ m / 2 ∧ c ≤ ε / (b - a) ∧ c ≤ r₁ / G ∧ c ≤ η / 4 :=
    ⟨min (min (m / 2) (ε / (b - a))) (min (r₁ / G) (η / 4)), by positivity, by simp⟩
  obtain ⟨ε₀, hε₀, hε₀η, hε₀τ⟩ : ∃ ε₀ > 0, ε₀ ≤ η / 2 ∧ ε₀ ≤ τ / 4 :=
    ⟨min (η / 2) (τ / 4), by positivity, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨w, hw, hu⟩ : ∃ w > 0, ∀ k ≤ 2, ∀ r ∈ Icc r₁ r₂, ∀ ℓ ∈ Icc a b, ∀ ℓ' ∈ Icc a b,
      |ℓ' - ℓ| ≤ w → |iteratedDeriv k (χ ℓ') r - iteratedDeriv k (χ ℓ) r| < ε₀ := by
    choose! w hw hu using fun k (hk : k ≤ 2) ↦
      isCompact_Icc.exists_pos_abs_sub_lt_of_continuousOn (hcont k hk) hε₀
    refine ⟨min (w 0) (min (w 1) (w 2)),
      lt_min (hw 0 (by norm_num)) (lt_min (hw 1 (by norm_num)) (hw 2 le_rfl)),
      fun k hk r hr ℓ hℓ ℓ' hℓ' hl ↦ hu k hk r hr ℓ hℓ ℓ' hℓ' (hl.trans ?_)⟩
    interval_cases k <;> simp
  obtain ⟨h₀, hh₀, hh₀w, hh₀1, hh₀τ⟩ :
      ∃ h₀ > 0, h₀ ≤ w ∧ h₀ ≤ 1 ∧ h₀ ≤ τ * c / (Q * L ^ 2 + 1) :=
    ⟨min w (min 1 (τ * c / (Q * L ^ 2 + 1))), by positivity, by simp⟩
  -- The mesh `t i = a + i h`, `i ≤ N`, of size `h = (b - a) / N < h₀`, and the width `δ = c h`.
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / h₀)
  have hN0 : 0 < N := by exact_mod_cast (div_pos hba hh₀).trans hN
  have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
  set h := (b - a) / N with hh_def
  have hh : 0 < h := div_pos hba hN0'
  have hNh : (N : ℝ) * h = b - a := by rw [hh_def]; field_simp
  have hhh₀ : h < h₀ := by
    rw [hh_def, div_lt_iff₀ hN0']
    rw [div_lt_iff₀ hh₀] at hN
    linarith
  set δ := c * h with hδ_def
  have hδ : 0 < δ := mul_pos hc0 hh
  have hδc : δ ≤ c := mul_le_of_le_one_right hc0.le (hhh₀.le.trans hh₀1)
  set t : ℕ → ℝ := fun i ↦ a + (min i N : ℕ) * h with ht_def
  have ht (i : ℕ) (hi : i ≤ N) : t i = a + i * h := by simp [ht_def, hi]
  have htI (i : ℕ) : t i ∈ Icc a b := by
    have h₁ : ((min i N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right i N
    have h₂ : (0 : ℝ) ≤ (min i N : ℕ) := Nat.cast_nonneg _
    simp only [ht_def]
    exact ⟨le_add_of_nonneg_right (mul_nonneg h₂ hh.le),
      by linarith [mul_le_mul_of_nonneg_right h₁ hh.le]⟩
  have ht0 : t 0 = a := by simp [ht_def]
  have hstep (i : ℕ) (hi : i < N) : t (i + 1) - t i = h := by
    rw [ht _ hi, ht _ hi.le]
    push_cast
    ring
  -- The smooth stand-ins `A i` for the members `χ (t i)`.
  choose A hAs hAθ hAb hAa using fun i ↦
    exists_contDiff_abs_iteratedDeriv_sub_lt_of_mem_Icc hC2 hU hEU hsmooth (htI i) hθ
  have hA2 (i : ℕ) : ContDiff ℝ 2 (A i) := (hAs i).of_le (by norm_cast)
  -- On `[r₁, r₂]` the joints match, near each point, and the stand-ins and their lowerings by
  -- `η` are convex shapes, with slopes at most `G`.
  have hjc (r : ℝ) (hr : r ∈ Icc r₁ r₂) :=
    sub_add_lt_and_isConvexShapeAt_of_abs_iteratedDeriv_sub_lt (χ := χ) (A := A) (N := N)
      (θ := θ) (η := η) (δ := δ) (η₁ := η₁) (ε₀ := ε₀)
      (fun i g hg ↦ hstab g (t i, r) ⟨htI i, hr⟩ hg) (fun i k hk ↦ hAθ i k hk r hr)
      (fun i hi ↦ by
        simpa only [iteratedDeriv_zero] using hu 0 (by norm_num) r hr (t i) (htI i) (t (i + 1))
          (htI _) (by rw [hstep i hi, abs_of_pos hh]; linarith))
      hη (by linarith) (by linarith)
  have hJ (r : ℝ) (hr : r ∈ Icc r₁ r₂) :=
    eventually_forall_sub_add_le_smoothedMaxChain hδ (fun i _ ↦ (hAs i).continuous.continuousAt)
      (hjc r hr).1
  have hGA (i : ℕ) (r : ℝ) (hr : r ∈ Icc r₁ r₂) : deriv (A i) r ≤ G := by
    have h₁ := (abs_lt.1 (hAθ i 1 (by norm_num) r hr)).2
    have h₂ := hG₀ (t i, r) ⟨htI i, hr⟩
    simp only [iteratedDeriv_one, Real.norm_eq_abs] at h₁ h₂
    linarith [le_abs_self (deriv (χ (t i)) r), le_abs_self G₀]
  -- The last member is the last smoothed maximum of the stand-ins.
  have hCb (r : ℝ) (hr : r ∈ Icc r₁ r₂) : shapeChain δ η a h A N b r = smoothedMaxChain δ A N r :=
    shapeChain_eq_smoothedMaxChain hδ hh
      (fun i hi ↦ ((hjc r hr).1 i hi).le.trans (le_smoothedMaxChain hδ A i r)) (by linarith)
  refine ⟨shapeChain δ η a h A N, contDiff_shapeChain fun i _ ↦ hAs i, fun x hx ↦ ?_,
    fun x _ ↦ (monotone_shapeChain hh hη.le x.2).deriv_nonneg, ⟨?_, ?_⟩, ?_, fun r hr ↦ ?_,
    fun r hr ↦ ?_, fun x hx k hk ↦ ?_⟩
  · -- The members are convex shapes.
    have hδG : δ * G ≤ x.2 := by
      have := (le_div_iff₀ hG).1 hcG
      linarith [hx.2.1, mul_le_mul_of_nonneg_right hδc hG.le]
    exact isConvexShapeAt_shapeChain hδ hh hη.le (fun i _ ↦ hA2 i) (hJ x.2 hx.2)
      (fun i _ ↦ (hjc x.2 hx.2).2.1 i) (fun i _ ↦ (hjc x.2 hx.2).2.2 (i + 1))
      (fun i _ ↦ hGA i x.2 hx.2) hδG x.1
  · -- Flat near `a`.
    filter_upwards [Iio_mem_nhds (by linarith : a < a + h / 4)] with ℓ hℓ
    rw [shapeChain_of_le hh hℓ.le, shapeChain_of_le hh (by linarith)]
  · rw [shapeChain_of_le hh (by linarith)]
    exact hAa 0 ht0
  · -- Flat near `b`.
    have he : a + (N - 1 / 4) * h = b - h / 4 := by linear_combination hNh
    filter_upwards [Ioi_mem_nhds (by linarith : b - h / 4 < b)] with ℓ hℓ
    exact shapeChain_eq_of_ge hh (by rw [he]; exact hℓ.le) (by rw [he]; linarith)
  · -- The last member lies at most `ε` above some member of `χ`.
    obtain ⟨j, -, hj⟩ := exists_smoothedMaxChain_le_add hδ A N r
    refine ⟨t j, htI j, ?_⟩
    rw [hCb r hr]
    have h₁ := (abs_lt.1 (hAθ j 0 (by norm_num) r hr)).2
    simp only [iteratedDeriv_zero] at h₁
    have h₂ : N * δ ≤ ε := by
      have := (le_div_iff₀ hba).1 hcε
      rw [hδ_def, mul_left_comm, hNh]
      linarith
    linarith
  · -- The last member lies above `A N`, which is within `θ < ε` of `χ b`.
    have htN : t N = b := by rw [ht N le_rfl, hNh]; ring
    rw [hCb r hr]
    have h₁ := (abs_lt.1 (hAθ N 0 (by norm_num) r hr)).1
    simp only [iteratedDeriv_zero, htN] at h₁
    linarith [le_smoothedMaxChain hδ A N r]
  · -- On the band, the chain follows `χ`.
    have hδm : δ < m * h := by linarith [mul_le_mul_of_nonneg_right hcm hh.le, mul_pos hm hh]
    have hX : h * (Q * L ^ 2 + 1) ≤ τ * c := (le_div_iff₀ (by positivity)).1 (hhh₀.le.trans hh₀τ)
    have hQL : Q * L ^ 2 * h ^ 2 ≤ τ * δ := by
      rw [hδ_def]
      nlinarith [mul_le_mul_of_nonneg_right hX hh.le, sq_nonneg h]
    exact abs_iteratedDeriv_shapeChain_sub_lt_of_mem_band hδ hh hη.le hN0 (by linarith) ht hA2
      hAb (hJ x.2 (hsub hx.2)) hrate hδm hL hQ
      (fun s ↦ (hC₀ δ hδ s).trans (div_le_div_of_nonneg_right (le_max_left _ _) hδ.le)) hQL
      (fun k hk r hr ℓ hℓ ℓ' hℓ' hl ↦
        hu k hk r (hsub hr) ℓ hℓ ℓ' hℓ' (hl.trans (hhh₀.le.trans hh₀w)))
      hε₀τ hητ (by linarith) hx.1 hx.2 hk

end SymplecticGeometry

end
