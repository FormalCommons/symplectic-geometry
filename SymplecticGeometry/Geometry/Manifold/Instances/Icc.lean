/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorField.Prod
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.MFDeriv.Prod

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

Every tangent vector of the interval is a real multiple of `1`: a vector that the inclusion sends
to `r` is `r • 1` (`eq_smul_one_of_mfderiv_subtypeVal_Icc`). So the derivative of a map into the
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
-/

public section

open Set
open scoped Manifold ContDiff

variable {x y : ℝ} [Fact (x < y)] {n : WithTop ℕ∞}

namespace SymplecticGeometry

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

/-- A tangent vector `v` of a closed interval `[x, y]`, `x < y`, is `r` times the unit tangent
vector `1` when the inclusion `Icc x y → ℝ` sends it to `r`. -/
theorem eq_smul_one_of_mfderiv_subtypeVal_Icc {z : Icc x y} {v : TangentSpace (𝓡∂ 1) z} {r : ℝ}
    (h : mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r) :
    v = r • (1 : TangentSpace (𝓡∂ 1) z) := by
  -- The inclusion has invertible derivative, which sends `1` to `1`.
  refine (TauCeti.isInvertible_mfderiv_subtypeVal_Icc z).injective ?_
  rw [mfderiv_subtypeVal_Icc_smul_one, h]

/-- Let `f` be a map from a manifold `M` into a closed interval `[x, y]`, `x < y`, differentiable
at `t`. If the derivative at `t` of `Subtype.val ∘ f : M → ℝ` sends `v` to `r`, then the
derivative of `f` at `t` sends `v` to `r` times the unit tangent vector `1` at `f t`. -/
theorem mfderiv_apply_eq_smul_one_Icc {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → Icc x y} {t : M} (hf : MDifferentiableAt I (𝓡∂ 1) f t) {v : TangentSpace I t}
    {r : ℝ} (h : mfderiv I 𝓘(ℝ) (Subtype.val ∘ f) t v = r) :
    mfderiv I (𝓡∂ 1) f t v = r • (1 : TangentSpace (𝓡∂ 1) (f t)) := by
  refine eq_smul_one_of_mfderiv_subtypeVal_Icc ?_
  rw [← mfderiv_comp_apply t (mdifferentiableAt_subtypeVal_Icc _) hf, h]

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

end SymplecticGeometry

/-- Two continuous linear maps on a tangent space of a closed interval `[x, y]`, `x < y`, are equal
when they agree on the unit tangent vector `1`. -/
theorem ContinuousLinearMap.ext_tangentSpace_Icc {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {z : Icc x y} {f g : TangentSpace (𝓡∂ 1) z →L[ℝ] F} (h : f 1 = g 1) :
    f = g := by
  ext1 v
  obtain ⟨r, hr⟩ : ∃ r : ℝ, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r := ⟨_, rfl⟩
  rw [SymplecticGeometry.eq_smul_one_of_mfderiv_subtypeVal_Icc hr, map_smul, map_smul, h]

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
  refine SymplecticGeometry.mfderiv_apply_eq_smul_one_Icc (hc.mdifferentiable one_ne_zero u) ?_
  have hval : Subtype.val ∘ convexComb s t = (fun r : ℝ ↦ (1 - r) * s + r * t) ∘ Subtype.val :=
    funext (coe_convexComb s t)
  have hd : HasDerivAt (fun r : ℝ ↦ (1 - r) * s + r * t) ((t : ℝ) - s) (u : ℝ) :=
    funext (AffineMap.lineMap_apply_ring (s : ℝ) t) ▸ AffineMap.hasDerivAt_lineMap
  rw [hval, mfderiv_comp_apply u hd.differentiableAt.mdifferentiableAt
    (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc u), mfderiv_subtypeVal_Icc_one,
    mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply]
  -- The tangent spaces of `ℝ` are `ℝ` itself, through `NormedSpace.fromTangentSpace`, which is
  -- the identity; Mathlib has no lemma that evaluates it.
  exact one_smul ℝ ((t : ℝ) - s)

end Set.Icc

namespace unitInterval

/-- The derivative of `s ↦ T s` on the unit interval sends the unit tangent vector at `t` to `T`
times the unit tangent vector at `T t`. -/
theorem mfderiv_mul_left_one (T t : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (T * ·) t 1 = (T : ℝ) • (1 : TangentSpace (𝓡∂ 1) (T * t)) := by
  refine SymplecticGeometry.mfderiv_apply_eq_smul_one_Icc mdifferentiableAt_mul_left ?_
  have hval : (Subtype.val : unitInterval → ℝ) ∘ (T * ·) = (T : ℝ) • Subtype.val :=
    funext fun s ↦ Set.Icc.coe_mul T s
  rw [hval, const_smul_mfderiv (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc t)]
  -- The tangent spaces of `ℝ` at `t` and at `(T • Subtype.val) t` are equal only up to
  -- unfolding, so `smul_apply` does not rewrite the left side.
  exact (map_smul _ (T : ℝ) 1).symm.trans
    (SymplecticGeometry.mfderiv_subtypeVal_Icc_smul_one t T)

end unitInterval

end
