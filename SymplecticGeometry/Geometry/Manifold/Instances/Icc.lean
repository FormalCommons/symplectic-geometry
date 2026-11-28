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
ends of the interval included (`mfderiv_apply_zero_one_of_eq_add_smul`).

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
it is `C^n` when `a` and `b` are and meet at the seam (`ContMDiff.collaredConcat`).
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

namespace SymplecticGeometry

section Cylinder

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J 1 P]

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P` is smooth, up to both ends. -/
theorem contMDiff_prodVectorField_one_zero :
    ContMDiff ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J).tangent ∞ (fun p : unitInterval × P ↦
      (⟨p, TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) p⟩ : TangentBundle ((𝓡∂ 1).prod J) (unitInterval × P))) :=
  TauCeti.Manifold.contMDiff_prodVectorField
    TauCeti.contMDiff_one_tangentSpace_Icc
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P`, as a smooth section of the
tangent bundle. -/
noncomputable def unitIntervalTimeField :
    Cₛ^∞⟮(𝓡∂ 1).prod J; EuclideanSpace ℝ (Fin 1) × E',
      TangentSpace ((𝓡∂ 1).prod J) (M := unitInterval × P)⟯ :=
  ⟨TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
    (0 : Π y : P, TangentSpace J y), contMDiff_prodVectorField_one_zero⟩

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

end Cylinder

end SymplecticGeometry

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
theorem mfderiv_apply_zero_one_of_eq_add_smul {E H M F : Type*} [NormedAddCommGroup E]
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

end Glue

end
