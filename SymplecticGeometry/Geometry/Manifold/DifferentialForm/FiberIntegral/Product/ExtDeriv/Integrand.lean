/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.OpensModelSpace
import TauCeti.Data.Fin.Tuple.Basic
import SymplecticGeometry.Data.Fin.Tuple.RemoveNth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ExtDeriv
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens

/-!
# The integrand of `dα` on a product with flat base

Let `U` be an open subset of a normed space `E`, with the model `𝓘(ℝ, E)`, so that tangent vectors
of `U` are vectors of `E`, let `F` be a manifold over `J`, and let `α` be a smooth form of degree
`r + m` on `U × F`. This file computes the integrand `prodFiberIntegrand (dα) b v` of the fibre
integral of `dα` at `b ∈ U`, on `v₀, …, vᵣ ∈ E`, before any integration. It splits into a part
that differentiates in the base and a part that is `d` of a form on the fibre:

* `SymplecticGeometry.prodFiberIntegrand_cast_mextDerivₗ_apply_succ`: for `m = n + 1`,
  `prodFiberIntegrand (dα) b v y = ∑ᵢ (-1)ⁱ Dᵢ + (-1) ^ (r + 1) d_F γ (y)`, where `Dᵢ` is the
  derivative at `b`, in the direction `vᵢ`, of `b' ↦ prodFiberIntegrand α b' (v without vᵢ) y`,
  and `γ = prodFiberIntegrand α b v` is a form of degree `n` on `F`;
* `SymplecticGeometry.prodFiberIntegrand_cast_mextDerivₗ_apply_zero`: for `m = 0`, the same
  without the fibre term.

The degrees are matched by `LinearEquiv.cast`, along `(r + m) + 1 = (r + 1) + m` for `dα` and
along `r + (n + 1) = (r + 1) + n` for `γ`. The sign `(-1) ^ (r + 1)` is that of moving `d` past
the `r + 1` base vectors, which `prodFiberIntegrand` places first, as in Bott–Tu, §6.

The proof is the coordinate formula for `d` in the product chart at `(b, y)`
(`TauCeti.mextDeriv_apply_eq_sum_fderivWithin`): on the vectors
`(v₀, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)`, the integrand of `dα` is the alternating sum of the
derivatives of the coordinate expression of `α` in these directions
(`SymplecticGeometry.prodFiberIntegrand_cast_mextDerivₗ_apply`, for every `m`). The chart of `U`
is the identity, and at the chart centre the coordinate expression of `α` on `(u, 0), (0, w)` is
the integrand (`SymplecticGeometry.inChartAt_prodFiberIntegrand_apply_opens` and
`SymplecticGeometry.prodFiberIntegrand_apply_eq_inChartAt_self`, from
`SymplecticGeometry.inChartAt_prodFiberIntegrand`). So the derivatives in the base directions
`(vᵢ, 0)` are the base derivatives `Dᵢ` of the integrand
(`SymplecticGeometry.mfderiv_prodFiberIntegrand_apply`), and those in the fibre directions
`(0, wⱼ)` are the derivatives of the coordinate expression of `γ` in the chart of `F` at `y`
(`SymplecticGeometry.fderivWithin_inChartAt_prodFiberIntegrand_apply`), whose alternating sum is
`d_F γ`, again by `TauCeti.mextDeriv_apply_eq_sum_fderivWithin`. Splitting the sum over the two
blocks of vectors is `Fin.sum_neg_one_pow_smul_removeNth_append`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Set Function Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E E' H' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F]
  {U : Opens E} {r m : ℕ}

/-- The product chart of `U × F` at `(b, y)` sends `(b, y)` to `(b, φ y)`, where `φ` is the
extended chart of `F` at `y`: the chart of an open subset of `E` is the identity. -/
theorem _root_.TopologicalSpace.Opens.extChartAt_opens_prod_self (b : U) (y : F) :
    extChartAt (𝓘(ℝ, E).prod J) (b, y) (b, y) = ((b : E), extChartAt J y y) := by
  simp only [extChartAt_prod, PartialEquiv.prod_coe, Opens.extChartAt_opens_apply]

/-- The chart point `(b, φ y)` of `(b, y)` lies in the range of the model of `U × F`. -/
theorem _root_.TopologicalSpace.Opens.extChartAt_opens_prod_self_mem_range (b : U) (y : F) :
    ((b : E), extChartAt J y y) ∈ range (𝓘(ℝ, E).prod J) :=
  Opens.extChartAt_opens_prod_self (J := J) b y ▸ extChartAt_target_subset_range (b, y)
    (mem_extChartAt_target (b, y))

section IsManifoldOne

variable [IsManifold J 1 F]

/-- The coordinate expression of a smooth form on `U × F` in the product chart at `(b, y)` is
differentiable within the model range at the chart point of `(b, y)`. -/
theorem _root_.TauCeti.SmoothForm.differentiableWithinAt_inChartAt_opens_prod {k : ℕ}
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k) (b : U) (y : F) :
    DifferentiableWithinAt ℝ (RoughForm.inChartAt α.val (b, y)) (range (𝓘(ℝ, E).prod J))
      ((b : E), extChartAt J y y) := by
  have h := RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt α.val
    (α.mdifferentiableAt (b, y))
  rwa [Opens.extChartAt_opens_prod_self] at h

/-- **The integrand in the product chart.** For `b, b' ∈ U`, vectors `u₁, …, uᵣ ∈ E` and `z` in
the target of the chart of `F` at `y`, the coordinate expression at `z` of
`prodFiberIntegrand α b' u` in the chart of `F` at `y`, on `w`, is that of `α` in the product
chart at `(b, y)`, at `(b', z)`, on `(u₁, 0), …, (uᵣ, 0), (0, w₁), …, (0, wₘ)`. -/
theorem inChartAt_prodFiberIntegrand_apply_opens
    (α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (b b' : U) (u : Fin r → E) {y : F} {z : E'} (hz : z ∈ (extChartAt J y).target)
    (w : Fin m → E') :
    (prodFiberIntegrand α b' u).inChartAt y z w =
      α.inChartAt (b, y) ((b' : E), z) (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, w j)) := by
  have hb' : b' ∈ (extChartAt 𝓘(ℝ, E) b).source := by
    rw [extChartAt_source, Opens.chartAt_opens_model_space_eq b b']
    exact mem_chart_source E b'
  -- The tangent trivializations of an open subset of `E` are the identity.
  have ht (i : Fin r) : (trivializationAt E (TangentSpace 𝓘(ℝ, E)) b ⟨b', u i⟩).2 = u i := by
    have h := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) b).symm_apply_apply_mk
      (Manifold.mem_trivializationAt_opens_model_space_baseSet (𝕜 := ℝ) b b') (u i)
    rw [← Trivialization.symmL_apply (R := ℝ), Manifold.trivializationAt_opens_model_space_symmL]
      at h
    · exact h
    · exact Manifold.mem_trivializationAt_opens_model_space_baseSet b b'
  rw [inChartAt_prodFiberIntegrand α hb' u y hz, Opens.extChartAt_opens_apply,
    prodFiberIntegrandCLM_apply]
  simp only [ht]

/-- At the centre of the chart of `F`, the value of `prodFiberIntegrand α b' u` at `y` on `w` is
the coordinate expression of `α` in the product chart at `(b, y)`, at `(b', φ y)`, on
`(u₁, 0), …, (uᵣ, 0), (0, w₁), …, (0, wₘ)`. -/
theorem prodFiberIntegrand_apply_eq_inChartAt_self
    (α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (b b' : U) (u : Fin r → E) (y : F) (w : Fin m → E') :
    prodFiberIntegrand α b' u y w =
      α.inChartAt (b, y) ((b' : E), extChartAt J y y)
        (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, w j)) := by
  rw [← inChartAt_prodFiberIntegrand_apply_opens α b b' u (mem_extChartAt_target y),
    RoughForm.inChartAt_extChartAt_self]
  rfl

variable {b : U} {y : F}

/-- **The base derivative of the integrand.** If the coordinate expression of `α` in the product
chart at `(b, y)` is differentiable at the chart point, then the derivative at `b`, in the
direction `a ∈ E`, of `b' ↦ prodFiberIntegrand α b' u y`, evaluated on `w`, is the derivative of
the coordinate expression of `α` on `(u₁, 0), …, (uᵣ, 0), (0, w₁), …, (0, wₘ)` in the direction
`(a, 0)`. -/
theorem mfderiv_prodFiberIntegrand_apply (α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (hα : DifferentiableWithinAt ℝ (α.inChartAt (b, y)) (range (𝓘(ℝ, E).prod J))
      ((b : E), extChartAt J y y)) (u : Fin r → E) (a : E) (w : Fin m → E') :
    (show E' [⋀^Fin m]→L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α b' u y) b a) w =
      fderivWithin ℝ (fun x ↦ α.inChartAt (b, y) x (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, w j)))
        (range (𝓘(ℝ, E).prod J)) ((b : E), extChartAt J y y) (a, 0) := by
  set s := range (𝓘(ℝ, E).prod J)
  set x₀ : E × E' := ((b : E), extChartAt J y y)
  have hs : UniqueDiffWithinAt ℝ s x₀ :=
    (𝓘(ℝ, E).prod J).uniqueDiffOn _ (Opens.extChartAt_opens_prod_self_mem_range b y)
  -- The integrand at `y` is read off the coordinate expression of `α` by a fixed linear map.
  let L := prodFiberIntegrandCLM E' m u
  have hmaps : MapsTo (fun e : E ↦ (e, extChartAt J y y)) univ s := fun e _ ↦ by
    simp only [s, ModelWithCorners.range_prod]
    exact ⟨by simp, extChartAt_target_subset_range y (mem_extChartAt_target y)⟩
  have hcomp : HasFDerivAt (fun e : E ↦ L (α.inChartAt (b, y) (e, extChartAt J y y)))
      (L.comp ((fderivWithin ℝ (α.inChartAt (b, y)) s x₀).comp
        (ContinuousLinearMap.inl ℝ E E'))) (b : E) := by
    have h := hα.hasFDerivWithinAt.comp (b : E)
      (hasFDerivAt_prodMk_left (b : E) (extChartAt J y y)).hasFDerivWithinAt hmaps
    rw [hasFDerivWithinAt_univ] at h
    exact L.hasFDerivAt.comp _ h
  have heq : (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α b' u y) =
      (fun e : E ↦ L (α.inChartAt (b, y) (e, extChartAt J y y))) ∘ Subtype.val := by
    funext b'
    ext w'
    -- `w'` is a family of vectors of `E'`; read it as tangent vectors of `F` at `y`.
    change prodFiberIntegrand α b' u y w' = _
    rw [prodFiberIntegrand_apply_eq_inChartAt_self α b b' u y w', Function.comp_apply,
      prodFiberIntegrandCLM_apply]
  dsimp only at heq ⊢
  have hmf := mfderiv_modelSpace_comp_subtypeVal_apply (𝕜 := ℝ) (U := U)
    (f := fun e : E ↦ L (α.inChartAt (b, y) (e, extChartAt J y y))) (x := b) a
  rw [hcomp.fderiv] at hmf
  rw [heq]
  refine (congrArg (fun φ : E' [⋀^Fin m]→L[ℝ] ℝ ↦ φ w) hmf).trans ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, prodFiberIntegrandCLM_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply hs hα]

/-- **The fibre derivative of the integrand.** Let `X₁, …, Xₘ ∈ E'`. If the coordinate expression
of `α` in the product chart at `(b, y)`, evaluated on `(u₁, 0), …, (uᵣ, 0), (0, X₁), …, (0, Xₘ)`,
is differentiable at the chart point, then the derivative at `φ y`, in the direction `c`, of the
coordinate expression of `prodFiberIntegrand α b u` in the chart `φ` of `F` at `y`, evaluated on
`X`, is the derivative of that function in the direction `(0, c)`. -/
theorem fderivWithin_inChartAt_prodFiberIntegrand_apply
    (α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (u : Fin r → E) (X : Fin m → E')
    (hα : DifferentiableWithinAt ℝ
      (fun x ↦ α.inChartAt (b, y) x (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, X j)))
      (range (𝓘(ℝ, E).prod J)) ((b : E), extChartAt J y y)) (c : E') :
    fderivWithin ℝ (fun z ↦ (prodFiberIntegrand α b u).inChartAt y z X) (range J)
        (extChartAt J y y) c =
      fderivWithin ℝ (fun x ↦ α.inChartAt (b, y) x (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, X j)))
        (range (𝓘(ℝ, E).prod J)) ((b : E), extChartAt J y y) (0, c) := by
  have hz₀ : extChartAt J y y ∈ range J :=
    extChartAt_target_subset_range y (mem_extChartAt_target y)
  have hmaps : MapsTo (fun z : E' ↦ ((b : E), z)) (range J) (range (𝓘(ℝ, E).prod J)) :=
    fun z hz ↦ by
      simp only [ModelWithCorners.range_prod]
      exact ⟨by simp, hz⟩
  have hι : HasFDerivWithinAt (fun z : E' ↦ ((b : E), z)) (ContinuousLinearMap.inr ℝ E E')
      (range J) (extChartAt J y y) :=
    (hasFDerivAt_prodMk_right (b : E) (extChartAt J y y)).hasFDerivWithinAt
  have h := hα.hasFDerivWithinAt.comp (extChartAt J y y) hι hmaps
  have heq : (fun z ↦ (prodFiberIntegrand α b u).inChartAt y z X) =ᶠ[nhdsWithin
      (extChartAt J y y) (range J)]
      (fun x ↦ α.inChartAt (b, y) x (Fin.append (fun i ↦ (u i, 0)) fun j ↦ (0, X j))) ∘
        fun z : E' ↦ ((b : E), z) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin y] with z hz
    exact inChartAt_prodFiberIntegrand_apply_opens α b b u hz X
  rw [(h.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hz₀)).fderivWithin
    (J.uniqueDiffOn _ hz₀), ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end IsManifoldOne

/-- **The integrand of `dα` on a product with flat base, in coordinates.** Let `α` be a smooth
form of degree `r + m` on `U × F`, `U` open in `E`. For `b ∈ U`, `v₀, …, vᵣ ∈ E`, `y ∈ F` and
`w₁, …, wₘ ∈ E'`, let `V` be the family `(v₀, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)`, indexed by
`Fin (r + m + 1)` along `h`. The integrand of `dα` at `b` on `v`, at `y`, evaluated on `w`, is the
alternating sum over `p` of the derivatives in the direction `Vₚ` of the coordinate expression of
`α` in the product chart at `(b, y)`, evaluated on the other vectors of `V`. -/
theorem prodFiberIntegrand_cast_mextDerivₗ_apply [IsManifold J 2 F]
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)) (b : U) (v : Fin (r + 1) → E)
    (y : F) (w : Fin m → E') (h : r + m + 1 = r + 1 + m) :
    prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k) h
        (mextDerivₗ (𝓘(ℝ, E).prod J) (r + m) α)).val b v y w =
      ∑ p : Fin (r + m + 1), (-1 : ℤ) ^ (p : ℕ) •
        fderivWithin ℝ (fun x ↦ RoughForm.inChartAt α.val (b, y) x
            (p.removeNth (Fin.append (fun i ↦ (v i, (0 : E'))) (fun j ↦ ((0 : E), w j)) ∘
              Fin.cast h)))
          (range (𝓘(ℝ, E).prod J)) ((b : E), extChartAt J y y)
          ((Fin.append (fun i ↦ (v i, (0 : E'))) (fun j ↦ ((0 : E), w j)) ∘ Fin.cast h) p) := by
  refine (prodFiberIntegrand_apply _ b v y w).trans ?_
  rw [SmoothForm.cast_apply, mextDerivₗ_apply]
  refine (congrArg (mextDeriv α.val (b, y)) (funext fun p ↦
    Manifold.tangentSpaceProdEquiv_symm_apply (I := 𝓘(ℝ, E)) (J := J) (b, y)
      (Fin.append (fun i ↦ (v i, (0 : E'))) (fun j ↦ ((0 : E), w j)) (Fin.cast h p)))).trans ?_
  refine (mextDeriv_apply_eq_sum_fderivWithin
    (RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt α.val
      (α.mdifferentiableAt (b, y))) _).trans ?_
  rw [Opens.extChartAt_opens_prod_self]
  -- The two sides differ only in that the tuples of the left one are typed as tangent vectors
  -- of `U × F` at `(b, y)`, which are the vectors of `E × E'` by definition.
  rfl

/-- **The integrand of `dα` on a product with flat base, fibre of positive degree.** Let `α` be
a smooth form of degree `r + (n + 1)` on `U × F`, `U` open in `E`. For `b ∈ U`, `v₀, …, vᵣ ∈ E`
and `y ∈ F`, the integrand of `dα` at `b` on `v`, at `y`, evaluated on `w`, is
`∑ᵢ (-1)ⁱ Dᵢ w + (-1) ^ (r + 1) (d_F γ)_y w`, where `Dᵢ` is the derivative at `b` in the direction
`vᵢ` of `b' ↦ prodFiberIntegrand α b' (Fin.removeNth i v) y` and `γ = prodFiberIntegrand α b v`
is a form of degree `n` on `F`. The degrees are matched along `(r + (n + 1)) + 1 =
(r + 1) + (n + 1)` and `r + (n + 1) = (r + 1) + n`. -/
theorem prodFiberIntegrand_cast_mextDerivₗ_apply_succ [IsManifold J 2 F] {n : ℕ}
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + (n + 1))) (b : U) (v : Fin (r + 1) → E)
    (y : F) (w : Fin (n + 1) → E') :
    prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + (n + 1) + 1 = r + 1 + (n + 1))
        (mextDerivₗ (𝓘(ℝ, E).prod J) (r + (n + 1)) α)).val b v y w =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) • (show E' [⋀^Fin (n + 1)]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin (n + 1)]→L[ℝ] ℝ)
          (fun b' : U ↦ show E' [⋀^Fin (n + 1)]→L[ℝ] ℝ from
            prodFiberIntegrand α.val b' (Fin.removeNth i v) y) b (v i)) w +
      (-1 : ℤ) ^ (r + 1) • mextDeriv (prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + (n + 1) = r + 1 + n) α).val b v) y w := by
  have h₁ : r + (n + 1) + 1 = r + 1 + (n + 1) := by omega
  have h₂ : r + (n + 1) = r + 1 + n := by omega
  set α' := LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k) h₂ α
  -- The derivatives of the coordinate expression of `α` at the chart point of `(b, y)`.
  set δ : (Fin (r + (n + 1)) → E × E') → E × E' → ℝ := fun X c ↦
    fderivWithin ℝ (fun x ↦ RoughForm.inChartAt α.val (b, y) x X) (range (𝓘(ℝ, E).prod J))
      ((b : E), extChartAt J y y) c with hδ
  have hγ : DifferentiableWithinAt ℝ ((prodFiberIntegrand α'.val b v).inChartAt y) (range J)
      (extChartAt J y y) :=
    RoughForm.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt _
      (SmoothForm.mdifferentiableAt
        ⟨_, (isSmoothForm_prodFiberIntegrand α'.isSmoothForm b v).mem_smoothBundleForms⟩ y)
  -- The fibre term: `d_F γ` in the chart of `F` at `y`, through the coordinates of `α`.
  have hfib : mextDeriv (prodFiberIntegrand α'.val b v) y w =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        δ ((Fin.append (fun i ↦ (v i, (0 : E'))) (fun k ↦ ((0 : E), Fin.removeNth j w k))) ∘
          Fin.cast h₂) (0, w j) := by
    refine (mextDeriv_apply_eq_sum_fderivWithin hγ w).trans ?_
    refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
    have hα' := (α'.differentiableWithinAt_inChartAt_opens_prod b y
      ).continuousAlternatingMap_apply_const
        (Fin.append (fun i ↦ (v i, (0 : E'))) fun k ↦ ((0 : E), Fin.removeNth j w k))
    rw [fderivWithin_inChartAt_prodFiberIntegrand_apply α'.val v _ hα' (w j), hδ]
    refine congrArg (fun f ↦ fderivWithin ℝ f _ _ _) (funext fun x ↦ ?_)
    rw [RoughForm.inChartAt_apply, RoughForm.inChartAt_apply, SmoothForm.cast_apply]
    rfl
  rw [prodFiberIntegrand_cast_mextDerivₗ_apply α b v y w h₁,
    Fin.sum_neg_one_pow_smul_removeNth_append δ _ _ h₁ h₂, hfib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.removeNth_comp (·, (0 : E')) i v,
    mfderiv_prodFiberIntegrand_apply α.val (α.differentiableWithinAt_inChartAt_opens_prod b y)]

/-- **The integrand of `dα` on a product with flat base, fibre of degree zero.** Let `α` be a
smooth form of degree `r + 0` on `U × F`, `U` open in `E`. For `b ∈ U`, `v₀, …, vᵣ ∈ E` and
`y ∈ F`, the integrand of `dα` at `b` on `v`, at `y`, is `∑ᵢ (-1)ⁱ Dᵢ`, where `Dᵢ` is the
derivative at `b` in the direction `vᵢ` of `b' ↦ prodFiberIntegrand α b' (Fin.removeNth i v) y`.
The degrees are matched along `(r + 0) + 1 = (r + 1) + 0`. -/
theorem prodFiberIntegrand_cast_mextDerivₗ_apply_zero [IsManifold J 2 F]
    (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + 0)) (b : U) (v : Fin (r + 1) → E)
    (y : F) (w : Fin 0 → E') :
    prodFiberIntegrand (LinearEquiv.cast (R := ℝ)
        (M := fun k ↦ SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ k)
        (by omega : r + 0 + 1 = r + 1 + 0)
        (mextDerivₗ (𝓘(ℝ, E).prod J) (r + 0) α)).val b v y w =
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) • (show E' [⋀^Fin 0]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin 0]→L[ℝ] ℝ)
          (fun b' : U ↦ show E' [⋀^Fin 0]→L[ℝ] ℝ from
            prodFiberIntegrand α.val b' (Fin.removeNth i v) y) b (v i)) w := by
  have h : r + 0 + 1 = r + 1 + 0 := by omega
  rw [prodFiberIntegrand_cast_mextDerivₗ_apply α b v y w h,
    Fin.sum_neg_one_pow_smul_removeNth_append_zero
      (fun X c ↦ fderivWithin ℝ (fun x ↦ RoughForm.inChartAt α.val (b, y) x X)
        (range (𝓘(ℝ, E).prod J)) ((b : E), extChartAt J y y) c) _ _ h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.removeNth_comp (·, (0 : E')) i v,
    mfderiv_prodFiberIntegrand_apply α.val (α.differentiableWithinAt_inChartAt_opens_prod b y)]

end SymplecticGeometry

end
