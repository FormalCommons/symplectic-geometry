/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import TauCeti.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Interval.Basic

/-!
# The inclusion and the unit vector field of a closed interval

The inclusion `Icc x y → ℝ` of a closed interval, `x < y`, is differentiable everywhere, ends
included (`mdifferentiable_subtypeVal_Icc`, `mdifferentiableAt_subtypeVal_Icc`), by Mathlib's
`contMDiff_subtypeVal_Icc`. Its derivative sends `r` times the unit tangent vector `1` to `r`
(`mfderiv_subtypeVal_Icc_smul_one`). For a normed space `V`, the map `V × [x, y] → V × ℝ` that
includes the second factor is smooth (`contMDiff_prodMap_id_subtypeVal_Icc`). For a manifold `M`,
the derivative of the map `M × [x, y] → M × ℝ` that includes the second factor sends `(w, r • 1)`
to `(w, r)` (`mfderiv_prodMap_id_subtypeVal_Icc`).

A closed interval `[x, y]`, `x < y`, with its manifold-with-boundary structure, carries the unit
tangent vector `1` of Mathlib's `oneTangentSpaceIcc` at every point. The vector field `z ↦ 1` is
smooth, up to both ends, by Tau Ceti's `TauCeti.contMDiff_one_tangentSpace_Icc`.

On a cylinder `[0, 1] × P`, the product (Tau Ceti's `TauCeti.Manifold.prodVectorField`) of this
field with the zero field of `P` is the unit time field `∂ₜ = (1, 0)`. It is smooth, up to both
ends (`contMDiff_prodVectorField_one_zero`), so it is a smooth section of the tangent bundle
(`unitIntervalTimeField`). In the same way, on `[0, 1]² × P` the unit field `∂ₛ = ((0, 1), 0)`
of the second time coordinate is a smooth section (`unitIntervalSqSndField`).

Every tangent vector of the interval is a real multiple of `1`, its image under the inclusion
(Tau Ceti's `TauCeti.eq_mvfderiv_subtypeVal_smul_one_Icc`). So the derivative of a map into the
interval is read off from that of its composite with the inclusion
(`mfderiv_apply_eq_smul_one_Icc`), and continuous linear maps on a tangent space of the interval
agree when they agree on `1` (`ContinuousLinearMap.ext_tangentSpace_Icc`).

A map `Φ : M × [x, y] → F` into a normed space that is affine in time on the slice through `p`,
`Φ (p, s) = a + s • v`, has derivative at `(p, t)` sending the unit time vector `(0, 1)` to `v`,
ends of the interval included (`mfderiv_apply_zero_one_of_eq_add_smul_Icc`).

Between two points `s` and `t` of `[x, y]`, the derivative of Mathlib's convex combination
`Set.Icc.convexComb s t`, from the unit interval, sends the unit vector to `t - s` times the
unit vector (`Set.Icc.mfderiv_convexComb_one`); its smoothness is Tau Ceti's
`ContMDiff.convexComb`.

Mathlib's affine homeomorphism `iccHomeoI x y h : [x, y] ≃ₜ [0, 1]` and its inverse are smooth,
up to both ends (`contMDiff_iccHomeoI`, `contMDiff_iccHomeoI_symm`), since their composites with
the inclusions into `ℝ` are affine.

On the unit interval, the derivative of left multiplication `s ↦ T s` sends the unit vector at
`t` to `T` times the unit vector at `T t` (`unitInterval.mfderiv_mul_left_one`).

Tau Ceti's stationary-time gluing `ContMDiff.glue_collaredHalves`, of maps on `M × [0, 1]`, also
holds for maps on `[0, 1] × M` (`ContMDiff.glue_collaredHalves_left`). The concatenation of two
families `a b : [0, 1] → α` with these time maps is `SymplecticGeometry.collaredConcat a b`; it
starts where `a` starts and ends where `b` ends (`collaredConcat_zero`, `collaredConcat_one`), and
it is `C^n` when `a` and `b` are and meet at the seam (`ContMDiff.collaredConcat`). Two such
concatenations give a smooth path in the square `[0, 1] × [0, 1]` from `(0, 0)` to `(1, 0)` that
stays on the three other sides (`unitInterval.exists_contMDiff_path_sq_boundary`).

The infinite concatenation `SymplecticGeometry.infiniteConcat a e` of families
`a k : [0, 1] → α`, `k : ℕ`, runs through `a k` on the times `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹]`,
reparametrized by Tau Ceti's `TauCeti.collaredSmoothTransitionUnit`, and takes the value `e` at
time `1`. It starts at `a 0 0` and ends at `e` (`infiniteConcat_zero`, `infiniteConcat_one`), and
its values are values of the `a k` or `e` (`infiniteConcat_mem`), of the `a m` with `m > k` or
`e` after stage `k` (`infiniteConcat_mem_of_le`), which holds near time `1` for each `k`
(`unitInterval.eventually_two_pow_mul_one_sub_lt`). When consecutive families meet, it runs
through `a k` on an open set of times around stage `k` (`infiniteConcat_of_mem_Ioo`,
`infiniteConcat_eventuallyEq`, `unitInterval.eventually_two_sub_two_pow_mul_mem_Ioo`), since the
time step is constant near the ends of each stage. A function applied to it is the infinite
concatenation of the function applied to the families and the end (`apply_infiniteConcat`).
-/

public section

open Set
open scoped Manifold ContDiff

variable {x y : ℝ} [Fact (x < y)] {n : WithTop ℕ∞}

/-- The inclusion `Icc x y → ℝ` of a closed interval is differentiable, up to both ends. -/
theorem mdifferentiable_subtypeVal_Icc :
    MDifferentiable (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) :=
  (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero

/-- The inclusion `Icc x y → ℝ` of a closed interval is differentiable at each point, ends
included. -/
theorem mdifferentiableAt_subtypeVal_Icc (z : Icc x y) :
    MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z :=
  mdifferentiable_subtypeVal_Icc z

/-- The derivative of the inclusion `Icc x y → ℝ` sends `r` times the unit tangent vector `1` to
`r`. -/
theorem mfderiv_subtypeVal_Icc_smul_one (z : Icc x y) (r : ℝ) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z (r • (1 : TangentSpace (𝓡∂ 1) z)) = r := by
  rw [map_smul, mfderiv_subtypeVal_Icc_one]
  exact mul_one (M := ℝ) _

section ProdMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a normed space `V`, the map `(v, s) ↦ (v, s)` from `V × [x, y]` to `V × ℝ` is smooth, up
to both ends. -/
theorem contMDiff_prodMap_id_subtypeVal_Icc :
    ContMDiff (𝓘(ℝ, V).prod (𝓡∂ 1)) 𝓘(ℝ, V × ℝ) n
      (Prod.map (id : V → V) (Subtype.val : Icc x y → ℝ)) :=
  contMDiff_fst.prodMk_space (contMDiff_subtypeVal_Icc.comp contMDiff_snd)

end ProdMap

section ProdMapManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The derivative of `(p, s) ↦ (p, s)`, from `M × [x, y]` to `M × ℝ`, sends `(w, r • 1)` to
`(w, r)`. -/
theorem mfderiv_prodMap_id_subtypeVal_Icc (z : M × Icc x y) (w : TangentSpace I z.1) (r : ℝ) :
    mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map (id : M → M) (Subtype.val : Icc x y → ℝ)) z
        (w, r • (1 : TangentSpace (𝓡∂ 1) z.2)) = (w, r) := by
  rw [mfderiv_prodMap mdifferentiableAt_id (mdifferentiableAt_subtypeVal_Icc z.2), mfderiv_id]
  -- `TangentSpace (I.prod (𝓡∂ 1)) z` is the product of the factors' tangent spaces only by
  -- unfolding, so `rw` cannot see the components; they are closed by `Prod.ext`.
  exact Prod.ext rfl (mfderiv_subtypeVal_Icc_smul_one z.2 r)

end ProdMapManifold

section Cylinder

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J 1 P]

namespace TauCeti.Manifold

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P` is smooth, up to both ends. -/
theorem contMDiff_prodVectorField_one_zero :
    ContMDiff ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J).tangent ∞ (fun p : unitInterval × P ↦
      (⟨p, TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) p⟩ : TangentBundle ((𝓡∂ 1).prod J) (unitInterval × P))) :=
  TauCeti.Manifold.contMDiff_prodVectorField
    TauCeti.contMDiff_one_tangentSpace_Icc
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))

end TauCeti.Manifold

namespace SymplecticGeometry

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P`, as a smooth section of the
tangent bundle. -/
noncomputable def unitIntervalTimeField :
    Cₛ^∞⟮(𝓡∂ 1).prod J; EuclideanSpace ℝ (Fin 1) × E',
      TangentSpace ((𝓡∂ 1).prod J) (M := unitInterval × P)⟯ :=
  ⟨TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
    (0 : Π y : P, TangentSpace J y), TauCeti.Manifold.contMDiff_prodVectorField_one_zero⟩

/-- The unit time field of the cylinder is the product field of `1` on `[0, 1]` and `0` on
`P`. -/
@[simp]
theorem coe_unitIntervalTimeField :
    ⇑(unitIntervalTimeField : Cₛ^∞⟮(𝓡∂ 1).prod J; EuclideanSpace ℝ (Fin 1) × E',
      TangentSpace ((𝓡∂ 1).prod J) (M := unitInterval × P)⟯) =
      TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) :=
  (rfl)

/-- The unit field `∂ₛ = ((0, 1), 0)` of the second time coordinate on `[0, 1]² × P`, as a
smooth section of the tangent bundle. -/
noncomputable def unitIntervalSqSndField :
    Cₛ^∞⟮((𝓡∂ 1).prod (𝓡∂ 1)).prod J;
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × E',
      TangentSpace (((𝓡∂ 1).prod (𝓡∂ 1)).prod J) (M := (unitInterval × unitInterval) × P)⟯ :=
  ⟨TauCeti.Manifold.prodVectorField
    (TauCeti.Manifold.prodVectorField (0 : Π t : unitInterval, TangentSpace (𝓡∂ 1) t)
      fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
    (0 : Π y : P, TangentSpace J y),
    TauCeti.Manifold.contMDiff_prodVectorField
      (TauCeti.Manifold.contMDiff_prodVectorField (Bundle.contMDiff_zeroSection ℝ _)
        TauCeti.contMDiff_one_tangentSpace_Icc)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))⟩

/-- The field `∂ₛ` on `[0, 1]² × P` is the product field of `(0, 1)` on `[0, 1]²` and `0` on
`P`. -/
@[simp]
theorem coe_unitIntervalSqSndField :
    ⇑(unitIntervalSqSndField (J := J) (P := P)) = TauCeti.Manifold.prodVectorField
      (TauCeti.Manifold.prodVectorField (0 : Π t : unitInterval, TangentSpace (𝓡∂ 1) t)
        fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
      (0 : Π y : P, TangentSpace J y) :=
  (rfl)

/-- The value of the field `∂ₛ` at `((t, s), x)` is `((0, 1), 0)`. -/
theorem unitIntervalSqSndField_apply (p : (unitInterval × unitInterval) × P) :
    unitIntervalSqSndField (J := J) p =
      (((0 : EuclideanSpace ℝ (Fin 1)), (1 : TangentSpace (𝓡∂ 1) p.1.2)), (0 : E')) := by
  rw [coe_unitIntervalSqSndField, TauCeti.Manifold.prodVectorField_apply,
    TauCeti.Manifold.prodVectorField_apply, Pi.zero_apply, Pi.zero_apply]
  -- The two sides differ only in the types `TangentSpace` and its model space for the zeros.
  rfl

end SymplecticGeometry

end Cylinder

/-- Let `f` be a map from a manifold `M` into a closed interval `[x, y]`, `x < y`, differentiable
at `t`. If the derivative at `t` of `Subtype.val ∘ f : M → ℝ` sends `v` to `r`, then the
derivative of `f` at `t` sends `v` to `r` times the unit tangent vector `1` at `f t`. -/
theorem mfderiv_apply_eq_smul_one_Icc {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → Icc x y} {t : M} (hf : MDifferentiableAt I (𝓡∂ 1) f t) {v : TangentSpace I t}
    {r : ℝ} (h : mfderiv I 𝓘(ℝ) (Subtype.val ∘ f) t v = r) :
    mfderiv I (𝓡∂ 1) f t v = r • (1 : TangentSpace (𝓡∂ 1) (f t)) := by
  refine (TauCeti.eq_mvfderiv_subtypeVal_smul_one_Icc _ _).trans ?_
  rw [mvfderiv_apply_eq_mfderiv_apply,
    ← mfderiv_comp_apply t (mdifferentiableAt_subtypeVal_Icc _) hf, h]

/-- Let `Φ : M × [x, y] → F`, with `F` a normed space, be differentiable at `(p, t)` and affine in
time along the slice through `p`: `Φ (p, s) = a + s • v` for every `s`. Then the derivative of
`Φ` at `(p, t)` sends the unit time vector `(0, 1)` to `v`. This holds at the ends of the interval
too, where the derivative is one-sided. -/
theorem mfderiv_apply_zero_one_of_eq_add_smul_Icc {E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : M × Icc x y → F} {p : M}
    {t : Icc x y} (hΦ : MDifferentiableAt (I.prod (𝓡∂ 1)) 𝓘(ℝ, F) Φ (p, t)) {a v : F}
    (h : ∀ s : Icc x y, Φ (p, s) = a + (s : ℝ) • v) :
    mfderiv (I.prod (𝓡∂ 1)) 𝓘(ℝ, F) Φ (p, t)
      ((0 : TangentSpace I p), (1 : TangentSpace (𝓡∂ 1) t)) = v := by
  -- The vector `(0, 1)` only sees the slice `s ↦ Φ (p, s)`, the affine map `r ↦ a + r • v`
  -- composed with the inclusion of the interval.
  have hd : HasFDerivAt (fun r : ℝ ↦ a + r • v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) (t : ℝ) :=
    ((hasFDerivAt_id (t : ℝ)).smul_const v).const_add a
  have hslice : Function.curry Φ p = (fun r : ℝ ↦ a + r • v) ∘ Subtype.val := funext h
  have H := hd.hasMFDerivAt.comp t (mdifferentiableAt_subtypeVal_Icc t).hasMFDerivAt
  rw [← hslice] at H
  refine (hΦ.mfderiv_uncurry_apply_zero_mk (f := Function.curry Φ) 1).trans ?_
  rw [H.mfderiv]
  -- The tangent spaces of `ℝ` are `ℝ` only up to unfolding `TangentSpace`, so `comp_apply` and
  -- `smulRight_apply` do not rewrite here; both hold by definition.
  exact (congrArg ((1 : ℝ →L[ℝ] ℝ).smulRight v) (mfderiv_subtypeVal_Icc_one t)).trans
    (one_smul ℝ v)

/-- Two continuous linear maps on a tangent space of a closed interval `[x, y]`, `x < y`, are equal
when they agree on the unit tangent vector `1`. -/
theorem ContinuousLinearMap.ext_tangentSpace_Icc {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {z : Icc x y} {f g : TangentSpace (𝓡∂ 1) z →L[ℝ] F} (h : f 1 = g 1) :
    f = g := by
  ext1 v
  rw [TauCeti.eq_mvfderiv_subtypeVal_smul_one_Icc z v, map_smul, map_smul, h]

/-- Mathlib's affine homeomorphism `iccHomeoI x y h : Icc x y ≃ₜ unitInterval`,
`z ↦ (z - x) / (y - x)`, is `C^n` for every `n`, up to both ends. -/
theorem contMDiff_iccHomeoI (h : x < y) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iccHomeoI x y h) := by
  refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨(iccHomeoI x y h).continuous, ?_⟩
  have hval : Subtype.val ∘ iccHomeoI x y h = (fun z : ℝ ↦ (z - x) / (y - x)) ∘ Subtype.val :=
    funext (iccHomeoI_apply_coe x y h)
  rw [hval]
  exact ((contDiff_id.sub contDiff_const).div_const _).contMDiff.comp contMDiff_subtypeVal_Icc

/-- The inverse `u ↦ (y - x) u + x` of Mathlib's affine homeomorphism
`iccHomeoI x y h : Icc x y ≃ₜ unitInterval` is `C^n` for every `n`, up to both ends. -/
theorem contMDiff_iccHomeoI_symm (h : x < y) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iccHomeoI x y h).symm := by
  refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨(iccHomeoI x y h).symm.continuous, ?_⟩
  have hval : Subtype.val ∘ (iccHomeoI x y h).symm =
      (fun u : ℝ ↦ (y - x) * u + x) ∘ Subtype.val :=
    funext (iccHomeoI_symm_apply_coe x y h)
  rw [hval]
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff.comp
    contMDiff_subtypeVal_Icc

namespace Set.Icc

/-- The derivative of Mathlib's convex combination `u ↦ (1 - u) s + u t`, the affine path from
`s` to `t` in a closed interval, sends the unit tangent vector to `t - s` times the unit tangent
vector. -/
theorem mfderiv_convexComb_one (s t : Icc x y) (u : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (convexComb s t) u 1 =
      ((t : ℝ) - s) • (1 : TangentSpace (𝓡∂ 1) (convexComb s t u)) := by
  have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 1) 1 (convexComb s t) :=
    contMDiff_const.convexComb contMDiff_const contMDiff_id
  refine mfderiv_apply_eq_smul_one_Icc (hc.mdifferentiable one_ne_zero u) ?_
  have hval : Subtype.val ∘ convexComb s t = (fun r : ℝ ↦ (1 - r) * s + r * t) ∘ Subtype.val :=
    funext (coe_convexComb s t)
  have hd : HasDerivAt (fun r : ℝ ↦ (1 - r) * s + r * t) ((t : ℝ) - s) (u : ℝ) :=
    funext (AffineMap.lineMap_apply_ring (s : ℝ) t) ▸ AffineMap.hasDerivAt_lineMap
  rw [hval, mfderiv_comp_apply u hd.differentiableAt.mdifferentiableAt
    (mdifferentiableAt_subtypeVal_Icc u), mfderiv_subtypeVal_Icc_one,
    mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply]
  rw [NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_symm_apply]
  exact one_smul ℝ ((t : ℝ) - s)

end Set.Icc

namespace unitInterval

/-- The derivative of `s ↦ T s` on the unit interval sends the unit tangent vector at `t` to `T`
times the unit tangent vector at `T t`. -/
theorem mfderiv_mul_left_one (T t : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (T * ·) t 1 = (T : ℝ) • (1 : TangentSpace (𝓡∂ 1) (T * t)) := by
  refine mfderiv_apply_eq_smul_one_Icc mdifferentiableAt_mul_left ?_
  have hval : (Subtype.val : unitInterval → ℝ) ∘ (T * ·) = (T : ℝ) • Subtype.val :=
    funext fun s ↦ Set.Icc.coe_mul T s
  rw [hval, const_smul_mfderiv (mdifferentiableAt_subtypeVal_Icc t)]
  -- The tangent spaces of `ℝ` at `t` and at `(T • Subtype.val) t` are equal only up to
  -- unfolding, so `smul_apply` does not rewrite the left side.
  exact (map_smul _ (T : ℝ) 1).symm.trans
    (mfderiv_subtypeVal_Icc_smul_one t T)

end unitInterval

section Glue

namespace SymplecticGeometry

open TauCeti

variable {α β : Sort*}

/-- The **stationary-time concatenation** of two families `a b : [0, 1] → α`: it runs through `a`
reparametrized by `TauCeti.collaredFirstHalf` for `t ≤ 1 / 2`, and through `b` reparametrized by
`TauCeti.collaredSecondHalf` afterwards. -/
noncomputable def collaredConcat (a b : unitInterval → α) (t : unitInterval) : α :=
  if (t : ℝ) ≤ 1 / 2 then a (collaredFirstHalf le_rfl t) else b (collaredSecondHalf le_rfl t)

theorem collaredConcat_def (a b : unitInterval → α) (t : unitInterval) :
    collaredConcat a b t =
      if (t : ℝ) ≤ 1 / 2 then a (collaredFirstHalf le_rfl t)
      else b (collaredSecondHalf le_rfl t) :=
  (rfl)

variable {a b : unitInterval → α} {t : unitInterval}

/-- On the first half, the concatenation runs through the first family. -/
theorem collaredConcat_of_le (ht : (t : ℝ) ≤ 1 / 2) :
    collaredConcat a b t = a (collaredFirstHalf le_rfl t) := by
  rw [collaredConcat_def, ite_eq_left ht]

/-- On the second half, the concatenation runs through the second family. -/
theorem collaredConcat_of_lt (ht : 1 / 2 < (t : ℝ)) :
    collaredConcat a b t = b (collaredSecondHalf le_rfl t) := by
  rw [collaredConcat_def, ite_eq_right ht.not_ge]

/-- The concatenation starts where the first family starts. -/
@[simp]
theorem collaredConcat_zero (a b : unitInterval → α) : collaredConcat a b 0 = a 0 := by
  rw [collaredConcat_of_le (by norm_num [Set.Icc.coe_zero]), collaredFirstHalf_zero]

/-- The concatenation ends where the second family ends. -/
@[simp]
theorem collaredConcat_one (a b : unitInterval → α) : collaredConcat a b 1 = b 1 := by
  rw [collaredConcat_of_lt (by norm_num [Set.Icc.coe_one]), collaredSecondHalf_one]

/-- A function applied to a concatenation is the concatenation of the function applied to the
two families. -/
theorem apply_collaredConcat (g : α → β) (a b : unitInterval → α) (t : unitInterval) :
    g (collaredConcat a b t) = collaredConcat (fun s ↦ g (a s)) (fun s ↦ g (b s)) t := by
  simp only [collaredConcat_def, apply_ite g]

end SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

open SymplecticGeometry TauCeti in
/-- **Stationary-time gluing, with time as the first factor.** Two `C^n` maps
`f g : [0, 1] × M → N` with `f (1, x) = g (0, x)` glue to a `C^n` map whose value at `(t, x)` is
the concatenation `SymplecticGeometry.collaredConcat` of the curves `f (·, x)` and `g (·, x)` at
`t`. This is Tau Ceti's `ContMDiff.glue_collaredHalves` with the two factors swapped. -/
theorem ContMDiff.glue_collaredHalves_left {f g : unitInterval × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J n f) (hg : ContMDiff ((𝓡∂ 1).prod I) J n g)
    (hfg : ∀ x, f (1, x) = g (0, x)) (hn : n ≤ ∞) :
    ContMDiff ((𝓡∂ 1).prod I) J n fun q : unitInterval × M ↦
      collaredConcat (fun t ↦ f (t, q.2)) (fun t ↦ g (t, q.2)) q.1 :=
  have hswap : ContMDiff ((𝓡∂ 1).prod I) (I.prod (𝓡∂ 1)) n Prod.swap :=
    contMDiff_snd.prodMk contMDiff_fst
  have hswap' : ContMDiff (I.prod (𝓡∂ 1)) ((𝓡∂ 1).prod I) n Prod.swap :=
    contMDiff_snd.prodMk contMDiff_fst
  (((hf.comp hswap').glue_collaredHalves (hg.comp hswap') hfg hn).comp hswap).congr fun q ↦ by
    -- The time maps depend on `hn` only through a proof, so both sides unfold to the same map.
    simp only [collaredConcat_def, collaredFirstHalf_apply, collaredSecondHalf_apply,
      Function.comp_apply, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap]

open SymplecticGeometry in
/-- **Concatenation of curves.** Two `C^n` curves `a b : [0, 1] → N` with `a 1 = b 0`
concatenate to a `C^n` curve `SymplecticGeometry.collaredConcat a b`. -/
theorem ContMDiff.collaredConcat {a b : unitInterval → N} (ha : ContMDiff (𝓡∂ 1) J n a)
    (hb : ContMDiff (𝓡∂ 1) J n b) (hab : a 1 = b 0) (hn : n ≤ ∞) :
    ContMDiff (𝓡∂ 1) J n (collaredConcat a b) :=
  -- Glue on `[0, 1] × [0, 1]`, constant along the second factor, and restrict to `t ↦ (t, 0)`.
  ((ha.comp contMDiff_fst).glue_collaredHalves_left (M := unitInterval) (I := 𝓡∂ 1)
    (hb.comp contMDiff_fst) (fun _ ↦ hab) hn).comp (contMDiff_id.prodMk contMDiff_const :
      ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 1)) n
        fun t : unitInterval ↦ (t, (0 : unitInterval)))

namespace unitInterval

open SymplecticGeometry

/-- A smooth path in the square `[0, 1] × [0, 1]` from `(0, 0)` to `(1, 0)` that runs along the
three other sides: each of its points lies on `{0} × [0, 1]`, on `{1} × [0, 1]` or on
`[0, 1] × {1}`. -/
theorem exists_contMDiff_path_sq_boundary :
    ∃ γ : unitInterval → unitInterval × unitInterval,
      ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 1)) ∞ γ ∧ γ 0 = (0, 0) ∧ γ 1 = (1, 0) ∧
      ∀ t, (γ t).1 = 0 ∨ (γ t).1 = 1 ∨ (γ t).2 = 1 := by
  -- Up the side `{0} × [0, 1]`, along the top, and down the side `{1} × [0, 1]`.
  let a : unitInterval → unitInterval × unitInterval := fun u ↦ (0, u)
  let b : unitInterval → unitInterval × unitInterval := fun u ↦ (u, 1)
  let c : unitInterval → unitInterval × unitInterval := fun u ↦ (1, symm u)
  have ha : ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 1)) ∞ a := contMDiff_const.prodMk contMDiff_id
  have hb : ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 1)) ∞ b := contMDiff_id.prodMk contMDiff_const
  have hc : ContMDiff (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 1)) ∞ c :=
    contMDiff_const.prodMk contMDiff_symm
  refine ⟨collaredConcat a (collaredConcat b c),
    ha.collaredConcat (hb.collaredConcat hc (by simp [b, c]) le_rfl) (by simp [a, b]) le_rfl,
    by simp [a], by simp [c], fun t ↦ ?_⟩
  rw [collaredConcat_def, collaredConcat_def]
  split_ifs <;> simp [a, b, c]

end unitInterval

end Glue


section InfiniteConcat

namespace SymplecticGeometry

open TauCeti
open scoped Topology

variable {α : Type*}

/-- The **infinite concatenation** of families `a k : [0, 1] → α`, `k : ℕ`, ending at `e`. For
`t < 1`, let `k` be least with `2 ^ (k + 1) * (1 - t) > 1`, so that
`1 - 2⁻ᵏ ≤ t < 1 - 2⁻ᵏ⁻¹`: the value at `t` is that of `a k` at the time
`collaredSmoothTransitionUnit (2 - 2 ^ (k + 1) * (1 - t))`, which runs from `0` to `1` on that
interval and is constant near its ends. The value at `1` is `e`. -/
noncomputable def infiniteConcat (a : ℕ → unitInterval → α) (e : α) (t : unitInterval) : α :=
  if (t : ℝ) < 1 then
    a (sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))})
      (collaredSmoothTransitionUnit
        (2 - 2 ^ (sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))} + 1) * (1 - (t : ℝ))))
  else e

theorem infiniteConcat_def (a : ℕ → unitInterval → α) (e : α) (t : unitInterval) :
    infiniteConcat a e t =
      if (t : ℝ) < 1 then
        a (sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))})
          (collaredSmoothTransitionUnit
            (2 - 2 ^ (sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))} + 1) * (1 - (t : ℝ))))
      else e :=
  (rfl)

variable {a : ℕ → unitInterval → α} {e : α} {t : unitInterval}

/-- On the time interval `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹)`, written as `2 - 2 ^ (k + 1) * (1 - t) ∈ [0, 1)`,
the infinite concatenation runs through `a k`. -/
theorem infiniteConcat_of_mem_Ico {k : ℕ} (ht' : 2 - 2 ^ (k + 1) * (1 - (t : ℝ)) ∈ Set.Ico 0 1) :
    infiniteConcat a e t =
      a k (collaredSmoothTransitionUnit (2 - 2 ^ (k + 1) * (1 - (t : ℝ)))) := by
  obtain ⟨h₀, h₁⟩ := ht'
  have ht : (t : ℝ) < 1 := by
    by_contra h
    have : (1 : ℝ) - t ≤ 0 := by linarith
    nlinarith [pow_pos (two_pos (α := ℝ)) (k + 1)]
  have hk : sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))} = k := by
    refine le_antisymm (Nat.sInf_le (show 1 < 2 ^ (k + 1) * (1 - (t : ℝ)) by linarith)) ?_
    refine le_of_not_gt fun hlt ↦ ?_
    have hmem := Nat.sInf_mem (s := {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))}) ⟨k, by
      rw [Set.mem_ofPred_eq]; linarith⟩
    rw [Set.mem_ofPred_eq] at hmem
    have hpow : (2 : ℝ) ^ (sInf {k | 1 < 2 ^ (k + 1) * (1 - (t : ℝ))} + 1) ≤ 2 ^ k :=
      pow_le_pow_right₀ one_le_two hlt
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have := mul_le_mul_of_nonneg_right hpow h1t
    rw [pow_succ] at h₀
    linarith
  rw [infiniteConcat_def, ite_eq_left ht, hk]

/-- The infinite concatenation ends at `e`. -/
@[simp]
theorem infiniteConcat_one (a : ℕ → unitInterval → α) (e : α) : infiniteConcat a e 1 = e := by
  rw [infiniteConcat_def, ite_eq_right (by simp)]

/-- The infinite concatenation starts where the first family starts. -/
@[simp]
theorem infiniteConcat_zero (a : ℕ → unitInterval → α) (e : α) :
    infiniteConcat a e 0 = a 0 0 := by
  rw [infiniteConcat_of_mem_Ico (k := 0) (by norm_num),
    collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num)]

/-- Every time before `1` lies in one of the intervals `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹)`. -/
theorem exists_mem_Ico_two_sub_two_pow_mul (ht : (t : ℝ) < 1) :
    ∃ k : ℕ, 2 - 2 ^ (k + 1) * (1 - (t : ℝ)) ∈ Set.Ico 0 1 := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  -- `2 ^ k ≤ (1 - t)⁻¹ < 2 ^ (k + 1)`, by Mathlib's `exists_nat_pow_near`.
  obtain ⟨k, hk₀, hk₁⟩ :=
    exists_nat_pow_near ((one_le_inv₀ h1t).2 (by linarith [unitInterval.nonneg t]))
      one_lt_two
  have hk₀ := mul_le_mul_of_nonneg_right hk₀ h1t.le
  rw [inv_mul_cancel₀ h1t.ne'] at hk₀
  rw [inv_lt_iff_one_lt_mul₀ h1t, mul_comm] at hk₁
  refine ⟨k, ?_, by linarith⟩
  rw [pow_succ]
  linarith

/-- The times around stage `k` where `2 - 2 ^ (k + 1) * (1 - t) ∈ (-1 / 8, 9 / 8)` form a
neighbourhood of each of their points. -/
theorem _root_.unitInterval.eventually_two_sub_two_pow_mul_mem_Ioo {k : ℕ}
    (ht : 2 - 2 ^ (k + 1) * (1 - (t : ℝ)) ∈ Set.Ioo (-1 / 8) (9 / 8)) :
    ∀ᶠ s : unitInterval in 𝓝 t, 2 - 2 ^ (k + 1) * (1 - (s : ℝ)) ∈ Set.Ioo (-1 / 8) (9 / 8) :=
  (by fun_prop : Continuous fun s : unitInterval ↦ 2 - 2 ^ (k + 1) * (1 - (s : ℝ))).continuousAt
    |>.eventually (isOpen_Ioo.mem_nhds ht)

/-- Every stage `k` ends before a neighbourhood of time `1`: near `1`,
`2 ^ (k + 1) * (1 - t) < 1`, that is, `t > 1 - 2⁻ᵏ⁻¹`. -/
theorem _root_.unitInterval.eventually_two_pow_mul_one_sub_lt (k : ℕ) :
    ∀ᶠ s : unitInterval in 𝓝 1, 2 ^ (k + 1) * (1 - (s : ℝ)) < 1 :=
  (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)

/-- **The infinite concatenation near the times of stage `k`.** If consecutive families meet,
`a (k + 1) 0 = a k 1`, then for `2 - 2 ^ (k + 1) * (1 - t) ∈ (-1 / 8, 9 / 8)`, an open set of
times around `[1 - 2⁻ᵏ, 1 - 2⁻ᵏ⁻¹]`, the infinite concatenation runs through `a k`. -/
theorem infiniteConcat_of_mem_Ioo (hab : ∀ k, a (k + 1) 0 = a k 1) {k : ℕ}
    (ht : 2 - 2 ^ (k + 1) * (1 - (t : ℝ)) ∈ Set.Ioo (-1 / 8) (9 / 8)) :
    infiniteConcat a e t =
      a k (collaredSmoothTransitionUnit (2 - 2 ^ (k + 1) * (1 - (t : ℝ)))) := by
  obtain ⟨h₀, h₁⟩ := ht
  set u : ℝ := 2 ^ k * (1 - t) with hu
  have hk : (2 : ℝ) ^ (k + 1) * (1 - t) = 2 * u := by rw [hu, pow_succ]; ring
  rw [hk] at h₀ h₁ ⊢
  rcases lt_or_ge (2 - 2 * u) 0 with hneg | hnn
  · -- Before stage `k`: at the end of stage `k - 1`, where both families are at their seam.
    obtain _ | j := k
    · rw [pow_zero, one_mul] at hu
      linarith [unitInterval.nonneg t]
    have hj : (2 : ℝ) ^ (j + 1) * (1 - t) = u := by rw [hu, pow_succ]
    rw [infiniteConcat_of_mem_Ico (k := j) ⟨by rw [hj]; linarith, by rw [hj]; linarith⟩,
      collaredSmoothTransitionUnit_eq_one_of_ge (by rw [hj]; linarith),
      collaredSmoothTransitionUnit_eq_zero_of_le (by linarith), hab]
  rcases lt_or_ge (2 - 2 * u) 1 with hlt | hge
  · rw [infiniteConcat_of_mem_Ico (k := k) ⟨by rw [hk]; exact hnn, by rw [hk]; exact hlt⟩, hk]
  · -- After stage `k`: at the start of stage `k + 1`, where both families are at their seam.
    have hj : (2 : ℝ) ^ (k + 1 + 1) * (1 - t) = 4 * u := by rw [hu, pow_succ, pow_succ]; ring
    rw [infiniteConcat_of_mem_Ico (k := k + 1) ⟨by rw [hj]; linarith, by rw [hj]; linarith⟩,
      collaredSmoothTransitionUnit_eq_zero_of_le (by rw [hj]; linarith),
      collaredSmoothTransitionUnit_eq_one_of_ge (by linarith), hab]

/-- **The infinite concatenation is locally one stage.** If consecutive families meet, then
near each time `t` with `2 - 2 ^ (k + 1) * (1 - t) ∈ (-1 / 8, 9 / 8)`, in particular near each
time of stage `k`, the infinite concatenation is `a k` reparametrized by the time step of
stage `k`. -/
theorem infiniteConcat_eventuallyEq (hab : ∀ k, a (k + 1) 0 = a k 1) {k : ℕ}
    (ht : 2 - 2 ^ (k + 1) * (1 - (t : ℝ)) ∈ Set.Ioo (-1 / 8) (9 / 8)) :
    infiniteConcat a e =ᶠ[𝓝 t]
      fun s ↦ a k (collaredSmoothTransitionUnit (2 - 2 ^ (k + 1) * (1 - (s : ℝ)))) :=
  (unitInterval.eventually_two_sub_two_pow_mul_mem_Ioo ht).mono fun _ hs ↦
    infiniteConcat_of_mem_Ioo hab hs

/-- **Every value of the infinite concatenation is a value of one of its families, or its end.**
If every value of every `a k` lies in `s`, and `e` lies in `s`, then so does every value of
`infiniteConcat a e`. -/
theorem infiniteConcat_mem {s : Set α} (ha : ∀ k t, a k t ∈ s) (he : e ∈ s) (t : unitInterval) :
    infiniteConcat a e t ∈ s := by
  rw [infiniteConcat_def]
  split_ifs
  exacts [ha _ _, he]

/-- **After stage `k`, the infinite concatenation runs through the later families.** For times
`t ≥ 1 - 2⁻ᵏ⁻¹`, if every value of `a m` for `m > k` lies in `s`, and `e` lies in `s`, then the
value of `infiniteConcat a e` at `t` lies in `s`. -/
theorem infiniteConcat_mem_of_le {s : Set α} {k : ℕ} (ha : ∀ m, k < m → ∀ t, a m t ∈ s)
    (he : e ∈ s) (ht : 2 ^ (k + 1) * (1 - (t : ℝ)) ≤ 1) : infiniteConcat a e t ∈ s := by
  rcases lt_or_ge (t : ℝ) 1 with h | h
  · obtain ⟨m, hm⟩ := exists_mem_Ico_two_sub_two_pow_mul h
    rw [infiniteConcat_of_mem_Ico hm]
    refine ha m (lt_of_not_ge fun hmk ↦ ?_) _
    have hpow : (2 : ℝ) ^ (m + 1) ≤ 2 ^ (k + 1) := pow_le_pow_right₀ one_le_two (by omega)
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have := mul_le_mul_of_nonneg_right hpow h1t
    linarith [hm.2]
  · rw [show t = 1 from Subtype.ext (le_antisymm (unitInterval.le_one t) h), infiniteConcat_one]
    exact he

/-- A function applied to an infinite concatenation is the infinite concatenation of the
function applied to the families and to the end. -/
theorem apply_infiniteConcat {β : Type*} (g : α → β) (a : ℕ → unitInterval → α) (e : α)
    (t : unitInterval) :
    g (infiniteConcat a e t) = infiniteConcat (fun k s ↦ g (a k s)) (g e) t := by
  simp only [infiniteConcat_def, apply_ite g]

end SymplecticGeometry

end InfiniteConcat

end
