/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Laurent approximation on `X × Circle` with continuous coefficients

For a topological space `X` and a complex normed space `V`, a *Laurent monomial* on `X × Circle`
is a map `(x, u) ↦ u ^ k • g x` with `k : ℤ` and `g : C(X, V)`. This file shows that when `X` is
compact Hausdorff and `V` is finite-dimensional, finite sums of Laurent monomials are uniformly
dense in `C(X × Circle, V)`: every continuous map on `X × Circle` is a uniform limit of Laurent
polynomials in the circle variable whose coefficients are continuous functions on `X`.

For `V = ℂ` the span of the Laurent monomials is a star subalgebra, since the conjugate of a unit
complex number is its inverse, and it separates points, so the Stone–Weierstrass theorem
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` makes it dense. This
scalar case adapts Mathlib's `fourierSubalgebra`, `fourierSubalgebra_coe`,
`fourierSubalgebra_closure_eq_top` and `span_fourier_closure_eq_top`
(`Mathlib/Analysis/Fourier/AddCircle.lean`) to maps with a parameter in `X`. For general `V`, a
map is a finite sum of scalar maps times the vectors of a basis.

## Main definitions

* `ContinuousMap.laurentMonomial k`: the linear map `g ↦ ((x, u) ↦ u ^ k • g x)` from `C(X, V)` to
  `C(X × Circle, V)`.
* `ContinuousMap.laurentSubmodule X V`: the span of the Laurent monomials.
* `ContinuousMap.laurentStarSubalgebra X`: the same span for `V = ℂ`, as a star subalgebra.

## Main results

* `ContinuousMap.mem_laurentSubmodule_iff`: the elements of `laurentSubmodule X V` are the sums
  `∑ i ∈ Finset.Icc (-N) N, laurentMonomial i (c i)`.
* `ContinuousMap.laurentStarSubalgebra_topologicalClosure_eq_top`: `laurentStarSubalgebra X` is
  dense.
* `ContinuousMap.laurentSubmodule_topologicalClosure_eq_top`: `laurentSubmodule X V` is dense.
* `ContinuousMap.exists_norm_sub_laurent_lt`: the same density, as a uniform estimate.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1
-/

public section

open Finset

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The Laurent monomial of degree `k` with coefficient `g`: the map `(x, u) ↦ u ^ k • g x` on
`X × Circle`, as a linear map in `g`. -/
noncomputable def laurentMonomial (k : ℤ) : C(X, V) →ₗ[ℂ] C(X × Circle, V) where
  toFun g :=
    ⟨fun w => (w.2 : ℂ) ^ k • g w.1,
      ((continuous_subtypeVal.comp continuous_snd).zpow₀ k
        fun w => Or.inl (Circle.coe_ne_zero w.2)).smul (g.continuous.comp continuous_fst)⟩
  map_add' g h := by ext w; exact smul_add _ _ _
  map_smul' a g := by ext w; exact smul_comm _ _ _

@[simp]
theorem laurentMonomial_apply (k : ℤ) (g : C(X, V)) (w : X × Circle) :
    laurentMonomial k g w = (w.2 : ℂ) ^ k • g w.1 :=
  (rfl)

/-- The product of two scalar Laurent monomials is a Laurent monomial. -/
@[simp]
theorem laurentMonomial_mul_laurentMonomial (i j : ℤ) (g h : C(X, ℂ)) :
    laurentMonomial i g * laurentMonomial j h = laurentMonomial (i + j) (g * h) := by
  ext w
  simp only [mul_apply, laurentMonomial_apply, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero w.2)]
  ring

/-- The conjugate of a scalar Laurent monomial is the Laurent monomial of the opposite degree with
the conjugate coefficient. -/
@[simp]
theorem star_laurentMonomial (k : ℤ) (g : C(X, ℂ)) :
    star (laurentMonomial k g) = laurentMonomial (-k) (star g) := by
  ext w
  simp [zpow_neg, ← Circle.coe_inv_eq_conj]

variable (X V) in
/-- The submodule of `C(X × Circle, V)` spanned by the Laurent monomials `(x, u) ↦ u ^ k • g x`,
for `k : ℤ` and `g : C(X, V)`. -/
noncomputable def laurentSubmodule : Submodule ℂ C(X × Circle, V) :=
  Submodule.span ℂ (Set.range fun p : ℤ × C(X, V) => laurentMonomial p.1 p.2)

theorem laurentSubmodule_def :
    laurentSubmodule X V =
      Submodule.span ℂ (Set.range fun p : ℤ × C(X, V) => laurentMonomial p.1 p.2) :=
  (rfl)

/-- Every Laurent monomial lies in `laurentSubmodule X V`. -/
theorem laurentMonomial_mem_laurentSubmodule (k : ℤ) (g : C(X, V)) :
    laurentMonomial k g ∈ laurentSubmodule X V :=
  Submodule.subset_span ⟨(k, g), rfl⟩

/-- The elements of `laurentSubmodule X V` are the Laurent polynomials
`∑ i ∈ Icc (-N) N, laurentMonomial i (c i)` with continuous coefficients `c i : C(X, V)`. -/
theorem mem_laurentSubmodule_iff {f : C(X × Circle, V)} :
    f ∈ laurentSubmodule X V ↔ ∃ (N : ℕ) (c : ℤ → C(X, V)),
      f = ∑ i ∈ Icc (-(N : ℤ)) N, laurentMonomial i (c i) := by
  refine ⟨fun hf => ?_, ?_⟩
  · rw [laurentSubmodule_def] at hf
    obtain ⟨c, rfl⟩ : ∃ c : ℤ →₀ C(X, V), f = c.sum fun i g => laurentMonomial i g := by
      induction hf using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨⟨k, g⟩, rfl⟩ := h
        exact ⟨Finsupp.single k g, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h₁ h₂ =>
        obtain ⟨c, rfl⟩ := h₁
        obtain ⟨d, rfl⟩ := h₂
        exact ⟨c + d, (Finsupp.sum_add_index' (by simp) (by simp)).symm⟩
      | smul a _ _ h =>
        obtain ⟨c, rfl⟩ := h
        exact ⟨a • c, by rw [Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]; simp⟩
    refine ⟨c.support.sup Int.natAbs, c, Finset.sum_subset (fun i hi => ?_) fun i _ hi => ?_⟩
    · have := Finset.le_sup (f := Int.natAbs) hi
      simp only [mem_Icc]
      omega
    · simp [Finsupp.notMem_support_iff.1 hi]
  · rintro ⟨N, c, rfl⟩
    exact Submodule.sum_mem _ fun i _ => laurentMonomial_mem_laurentSubmodule i (c i)

/-- The constant function `1` is a Laurent polynomial. -/
theorem one_mem_laurentSubmodule : (1 : C(X × Circle, ℂ)) ∈ laurentSubmodule X ℂ := by
  convert laurentMonomial_mem_laurentSubmodule (X := X) 0 (1 : C(X, ℂ))
  ext
  simp

/-- Scalar Laurent polynomials are closed under multiplication. -/
theorem mul_mem_laurentSubmodule {f g : C(X × Circle, ℂ)} (hf : f ∈ laurentSubmodule X ℂ)
    (hg : g ∈ laurentSubmodule X ℂ) : f * g ∈ laurentSubmodule X ℂ := by
  have := Submodule.mul_mem_mul hf hg
  rw [laurentSubmodule_def, Submodule.span_mul_span] at this
  refine Submodule.span_le.2 ?_ this
  rintro _ ⟨_, ⟨⟨i, a⟩, rfl⟩, _, ⟨⟨j, b⟩, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe, laurentMonomial_mul_laurentMonomial]
  exact laurentMonomial_mem_laurentSubmodule _ _

/-- Scalar Laurent polynomials are closed under complex conjugation. -/
theorem star_mem_laurentSubmodule {f : C(X × Circle, ℂ)} (hf : f ∈ laurentSubmodule X ℂ) :
    star f ∈ laurentSubmodule X ℂ := by
  rw [laurentSubmodule_def] at hf
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨⟨k, g⟩, rfl⟩ := h
    exact star_laurentMonomial k g ▸ laurentMonomial_mem_laurentSubmodule _ _
  | zero => simp
  | add _ _ _ _ h₁ h₂ => simpa using Submodule.add_mem _ h₁ h₂
  | smul a _ _ h => simpa using Submodule.smul_mem _ (star a) h

variable (X) in
/-- The span of the scalar Laurent monomials, as a star subalgebra of `C(X × Circle, ℂ)`. -/
noncomputable def laurentStarSubalgebra : StarSubalgebra ℂ C(X × Circle, ℂ) where
  __ := (laurentSubmodule X ℂ).toSubalgebra one_mem_laurentSubmodule
    fun _ _ => mul_mem_laurentSubmodule
  star_mem' := star_mem_laurentSubmodule

/-- As a submodule, `laurentStarSubalgebra X` is `laurentSubmodule X ℂ`. -/
@[simp]
theorem toSubmodule_laurentStarSubalgebra :
    Subalgebra.toSubmodule (laurentStarSubalgebra X).toSubalgebra = laurentSubmodule X ℂ :=
  Submodule.toSubalgebra_toSubmodule _ _ _

@[simp]
theorem mem_laurentStarSubalgebra {f : C(X × Circle, ℂ)} :
    f ∈ laurentStarSubalgebra X ↔ f ∈ laurentSubmodule X ℂ :=
  Iff.rfl

variable [CompactSpace X] [T2Space X]

/-- For `X` compact Hausdorff, the scalar Laurent polynomials with continuous coefficients form a
dense star subalgebra of `C(X × Circle, ℂ)`. -/
theorem laurentStarSubalgebra_topologicalClosure_eq_top :
    (laurentStarSubalgebra X).topologicalClosure = ⊤ := by
  refine starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  rintro w w' hw
  by_cases h : w.1 = w'.1
  · refine ⟨_, ⟨laurentMonomial 1 1,
      mem_laurentStarSubalgebra.2 (laurentMonomial_mem_laurentSubmodule 1 1), rfl⟩, ?_⟩
    have : w.2 ≠ w'.2 := fun h' => hw (Prod.ext h h')
    simpa [Circle.coe_inj] using this
  · obtain ⟨g, hg, hgw⟩ := separatesPoints_continuous_of_t35Space h
    refine ⟨_, ⟨laurentMonomial 0 ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp hg⟩,
      mem_laurentStarSubalgebra.2 (laurentMonomial_mem_laurentSubmodule _ _), rfl⟩, ?_⟩
    simpa using hgw

/-- For `X` compact Hausdorff and `V` finite-dimensional, the Laurent polynomials in the circle
variable with continuous coefficients on `X` are dense in `C(X × Circle, V)`. -/
theorem laurentSubmodule_topologicalClosure_eq_top [FiniteDimensional ℂ V] :
    (laurentSubmodule X V).topologicalClosure = ⊤ := by
  have hC : (laurentSubmodule X ℂ).topologicalClosure = ⊤ := by
    rw [← toSubmodule_laurentStarSubalgebra]
    exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
      (laurentStarSubalgebra_topologicalClosure_eq_top (X := X))
  rw [eq_top_iff]
  intro F _
  let b := Module.finBasis ℂ V
  -- the map `f ↦ f • v` carries scalar Laurent polynomials to `V`-valued ones
  have key (v : V) (f : C(X × Circle, ℂ)) :
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).compLeftContinuous ℂ (X × Circle) f ∈
        (laurentSubmodule X V).topologicalClosure := by
    let T := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).compLeftContinuous ℂ (X × Circle)
    have hmaps : Set.MapsTo T (laurentSubmodule X ℂ) (laurentSubmodule X V) := by
      intro f hf
      refine (Submodule.map_span_le _ _ _).2 ?_ ⟨f, hf, rfl⟩
      rintro _ ⟨⟨k, g⟩, rfl⟩
      convert laurentMonomial_mem_laurentSubmodule k
        (⟨fun x => g x • v, by fun_prop⟩ : C(X, V)) using 1
      ext w
      simp [T, smul_smul]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine map_mem_closure T.continuous ?_ hmaps
    rw [← Submodule.topologicalClosure_coe, hC, Submodule.top_coe]
    exact Set.mem_univ f
  have hF : F = ∑ j, (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b j)).compLeftContinuous
      ℂ (X × Circle) ((b.coord j).toContinuousLinearMap.compLeftContinuous ℂ (X × Circle) F) := by
    ext w
    simp [b.sum_repr]
  rw [hF]
  exact Submodule.sum_mem _ fun j _ => key (b j) _

/-- Uniform approximation on `X × Circle` by Laurent polynomials in the circle variable with
continuous coefficients: for `X` compact Hausdorff, `V` a finite-dimensional complex normed space,
`F : C(X × Circle, V)` and `ε > 0`, there are `N` and `c : ℤ → C(X, V)` with
`‖F (x, u) - ∑_{|i| ≤ N} u ^ i • c i x‖ < ε` for all `x` and `u`. -/
theorem exists_norm_sub_laurent_lt [FiniteDimensional ℂ V] (F : C(X × Circle, V)) {ε : ℝ}
    (hε : 0 < ε) : ∃ (N : ℕ) (c : ℤ → C(X, V)), ∀ w : X × Circle,
      ‖F w - ∑ i ∈ Icc (-(N : ℤ)) N, (w.2 : ℂ) ^ i • c i w.1‖ < ε := by
  have hF : F ∈ closure (laurentSubmodule X V : Set C(X × Circle, V)) := by
    rw [← Submodule.topologicalClosure_coe, laurentSubmodule_topologicalClosure_eq_top]
    exact Submodule.mem_top
  obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.1 hF ε hε
  obtain ⟨N, c, rfl⟩ := mem_laurentSubmodule_iff.1 hG
  refine ⟨N, c, fun w => ?_⟩
  have := (dist_apply_le_dist w).trans_lt hFG
  simpa [dist_eq_norm] using this

end ContinuousMap

end
