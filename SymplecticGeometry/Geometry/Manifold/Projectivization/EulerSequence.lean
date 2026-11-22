/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
public import SymplecticGeometry.LinearAlgebra.Projectivization.HermitianProjector

import SymplecticGeometry.Geometry.Manifold.Instances.Projectivization

/-!
# The Euler sequence on complex projective space

On `ℂℙᵐ = ℙ ℂ (Fin (m + 1) → ℂ)`, the Euler sequence
`0 → ℂ → Hom(ℓ, ℂ^{m+1}) → TℂPᵐ → 0` identifies the tangent bundle with
`Hom(ℓ, ℂ^{m+1} / ℓ)`, where `ℓ` is the tautological line. The bundle `Hom(ℓ, ℂ^{m+1})` is
`𝒪(1)^{⊕(m+1)}`, which is `Projectivization.twistPiCore 1 (Fin (m + 1))`: in the chart `i`, a
homomorphism `φ` is read through its value at the representative `v` of the line with `v i = 1`,
and these values change from chart to chart by `twistTransition 1`. The standard Hermitian product
splits the sequence, so that `TℂPᵐ ⊕ ℂ ≅ 𝒪(1)^{⊕(m+1)}`.

## Main declarations

* `Projectivization.eulerSequenceEquiv m x`: the fibrewise isomorphism
  `(TℂPᵐ ×ᵇ ℂ)_x ≃L[ℂ] (𝒪(1)^{⊕(m+1)})_x`. In the chart `i = (twistCore 1).indexAt x`, with `v`
  the representative of `x` with `v i = 1`, it sends `(ξ, c)` to `(1 - P) ξ̃ + c v`, where `ξ̃` is
  `ξ` with a zero inserted at `i` and `P = Projectivization.hermitianProjector x` is the orthogonal
  projection onto the line (`Projectivization.eulerSequenceEquiv_apply`); its inverse is
  `Projectivization.eulerSequenceEquiv_symm_apply`.
* `Projectivization.continuous_eulerSequenceEquiv` and
  `Projectivization.continuous_eulerSequenceEquiv_symm`: it is continuous on total spaces in both
  directions.

## Implementation notes

The fibres of both bundles are their model fibres, so the isomorphism is built on the model
fibres in an arbitrary chart `i`, and evaluated in the preferred chart at `x`. Its continuity on
total spaces is checked in the preferred trivializations at a base point `x₀`: there, the
coordinate change of the tangent bundle is the derivative of a transition map, that of
`𝒪(1)^{⊕(m+1)}` is multiplication by `twistTransition 1`, and the two are intertwined by the model
maps, because the orthogonal projection kills the line. The continuity of the inverse is Tau Ceti's
`TauCeti.continuous_bundle_symm`. The derivative of a transition map is
`Projectivization.insertNth_fderiv_affineChart_comp_affineChart_symm`. The continuity of the
Hermitian projector on a chart follows the proof of Tau Ceti's
`Projectivization.continuous_hermitianProjector`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 1,
  §1 (the Euler sequence) and Chapter 0, §2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Example 4.4.3.
-/

public noncomputable section

open Bundle Matrix Topology
open scoped Manifold LinearAlgebra.Projectivization ComplexOrder

namespace Projectivization

/-! ### The splitting on model fibres -/

variable {m : ℕ}

/-- The splitting of the Euler sequence on the model fibres, in the chart `i`:
`(ξ, c) ↦ (1 - P) ξ̃ + c v`, where `v` is the representative of `x` with `v i = 1`, `ξ̃` is `ξ` with
a zero inserted at `i`, and `P` is the Hermitian projector of `x`. -/
private def eulerModel (i : Fin (m + 1)) (x : ℙ ℂ (Fin (m + 1) → ℂ)) :
    (Fin m → ℂ) × ℂ →L[ℂ] Fin (m + 1) → ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun v := (1 - hermitianProjector x) *ᵥ Fin.insertNth (α := fun _ ↦ ℂ) i 0 v.1 +
        v.2 • Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)
      map_add' v w := by
        have h : Fin.insertNth (α := fun _ ↦ ℂ) i 0 (v.1 + w.1) =
            Fin.insertNth (α := fun _ ↦ ℂ) i 0 v.1 + Fin.insertNth (α := fun _ ↦ ℂ) i 0 w.1 := by
          simpa using Fin.insertNth_add (α := fun _ ↦ ℂ) i 0 0 v.1 w.1
        simp only [Prod.fst_add, Prod.snd_add, h, mulVec_add, add_smul]
        abel
      map_smul' c v := by
        have h : Fin.insertNth (α := fun _ ↦ ℂ) i 0 (c • v.1) =
            c • Fin.insertNth (α := fun _ ↦ ℂ) i 0 v.1 := by
          ext l
          induction l using i.succAboveCases <;> simp
        simp [h, mulVec_smul, smul_add, smul_smul] }

private theorem eulerModel_apply (i : Fin (m + 1)) (x : ℙ ℂ (Fin (m + 1) → ℂ))
    (v : (Fin m → ℂ) × ℂ) :
    eulerModel i x v = (1 - hermitianProjector x) *ᵥ Fin.insertNth (α := fun _ ↦ ℂ) i 0 v.1 +
        v.2 • Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) :=
  rfl

/-- The inverse of `eulerModel i x`, for `x` in `U_i`: `w ↦ (ξ, c)`, where `ξ̃ = w - w i • v` and
`c v` is the orthogonal projection of `w` onto the line spanned by `v`. -/
private def eulerModelInv (i : Fin (m + 1)) (x : ℙ ℂ (Fin (m + 1) → ℂ)) :
    (Fin (m + 1) → ℂ) →L[ℂ] (Fin m → ℂ) × ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun w := (fun k ↦ w (i.succAbove k) -
          w i * Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) (i.succAbove k),
        (star (Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)) ⬝ᵥ w) /
          (star (Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)) ⬝ᵥ
            Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)))
      map_add' v w := by
        ext k
        · simp only [Pi.add_apply, Prod.fst_add]
          ring
        · simp [dotProduct_add, add_div]
      map_smul' c v := by
        ext k
        · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst]
          ring
        · simp [mul_div_assoc] }

private theorem eulerModelInv_apply (i : Fin (m + 1)) (x : ℙ ℂ (Fin (m + 1) → ℂ))
    (w : Fin (m + 1) → ℂ) :
    eulerModelInv i x w = (fun k ↦ w (i.succAbove k) -
          w i * Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) (i.succAbove k),
        (star (Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)) ⬝ᵥ w) /
          (star (Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)) ⬝ᵥ
            Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x))) :=
  rfl

private theorem eulerModelInv_eulerModel (i : Fin (m + 1)) {x : ℙ ℂ (Fin (m + 1) → ℂ)}
    (hx : x ∈ affineOpen i) (v : (Fin m → ℂ) × ℂ) :
    eulerModelInv i x (eulerModel i x v) = v := by
  rw [eulerModel_apply, one_sub_hermitianProjector_mulVec i hx, eulerModelInv_apply]
  have hV : Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) i = 1 :=
    Fin.insertNth_apply_same ..
  have hN := dotProduct_star_self_eq_zero.not.2 (Fin.insertNth_one_ne_zero i (affineChart i x))
  generalize Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) = V at hV hN ⊢
  ext k
  · simp [hV]
    ring
  · simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring

private theorem eulerModel_eulerModelInv (i : Fin (m + 1)) {x : ℙ ℂ (Fin (m + 1) → ℂ)}
    (hx : x ∈ affineOpen i) (w : Fin (m + 1) → ℂ) :
    eulerModel i x (eulerModelInv i x w) = w := by
  rw [eulerModelInv_apply, eulerModel_apply, one_sub_hermitianProjector_mulVec i hx]
  have hV : Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) i = 1 :=
    Fin.insertNth_apply_same ..
  have hN := dotProduct_star_self_eq_zero.not.2 (Fin.insertNth_one_ne_zero i (affineChart i x))
  generalize Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) = V at hV hN ⊢
  have h : Fin.insertNth (α := fun _ ↦ ℂ) i 0
      (fun k ↦ w (i.succAbove k) - w i * V (i.succAbove k)) = w - w i • V := by
    ext l
    induction l using i.succAboveCases <;> simp [hV]
  simp only [h, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ext l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The model maps of two charts are intertwined by the coordinate changes of the two bundles:
the derivative of the transition map on the tangent part, and `twistTransition 1` on
`𝒪(1)^{⊕(m+1)}`. -/
private theorem smul_eulerModel (i j : Fin (m + 1)) {x : ℙ ℂ (Fin (m + 1) → ℂ)}
    (hi : x ∈ affineOpen i) (hj : x ∈ affineOpen j) (v : (Fin m → ℂ) × ℂ) :
    twistTransition 1 i j x • eulerModel i x v =
      eulerModel j x
        (fderiv ℂ (affineChart j ∘ (affineChart i).symm) (affineChart i x) v.1, v.2) := by
  have hvj : Fin.insertNth (α := fun _ ↦ ℂ) j 1 (affineChart j x) =
      twistTransition 1 i j x • Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x) := by
    rw [insertNth_one_affineChart_eq_normalizedRep i hi,
      insertNth_one_affineChart_eq_normalizedRep j hj, normalizedRep_def, normalizedRep_def,
      LinearMap.proj_apply, LinearMap.proj_apply, twistTransition_def, zpow_one, smul_smul,
      div_mul_eq_mul_div, mul_inv_cancel₀ ((mem_affineOpen_iff i x).1 hi), one_div]
  have hker :
      (1 - hermitianProjector x) *ᵥ Fin.insertNth (α := fun _ ↦ ℂ) j 1 (affineChart j x) = 0 :=
    one_sub_hermitianProjector_mulVec_of_mem_submodule
      (insertNth_one_affineChart_eq_normalizedRep j hj ▸ normalizedRep_mem_submodule _ x)
  rw [eulerModel_apply, eulerModel_apply,
    insertNth_fderiv_affineChart_comp_affineChart_symm i j hi hj, ← zpow_one (_ / _),
    ← twistTransition_def, mulVec_smul, mulVec_sub,
    mulVec_smul, hker, smul_zero, sub_zero, smul_add, hvj, smul_comm]

private theorem continuousOn_eulerModel (i : Fin (m + 1)) :
    ContinuousOn (eulerModel (m := m) i) (affineOpen i) := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have hV : ContinuousOn (fun x : ℙ ℂ (Fin (m + 1) → ℂ) ↦
      Fin.insertNth (α := fun _ ↦ ℂ) i 1 (affineChart i x)) (affineOpen i) :=
    (continuous_const.finInsertNth (A := fun _ ↦ ℂ) i continuous_id).comp_continuousOn
      (continuousOn_affineChart i)
  set u := Fin.insertNth (α := fun _ ↦ ℂ) i 0 v.1
  have hg : ContinuousOn (fun V : Fin (m + 1) → ℂ ↦
      u - ((star V ⬝ᵥ u) / (star V ⬝ᵥ V)) • V + v.2 • V) {V | V ≠ 0} := by
    have h₁ : ContinuousOn (fun V : Fin (m + 1) → ℂ ↦ (star V ⬝ᵥ u) / (star V ⬝ᵥ V))
        {V | V ≠ 0} :=
      ((continuous_star.dotProduct continuous_const).continuousOn).div
        (continuous_star.dotProduct continuous_id).continuousOn
        fun V hV ↦ dotProduct_star_self_eq_zero.not.2 hV
    have h₂ : Continuous fun V : Fin (m + 1) → ℂ ↦ v.2 • V := continuous_const_smul _
    exact (continuousOn_const.sub (h₁.smul continuousOn_id)).add h₂.continuousOn
  refine (hg.comp hV fun x _ ↦ Fin.insertNth_one_ne_zero i _).congr fun x hx ↦ ?_
  rw [eulerModel_apply, one_sub_hermitianProjector_mulVec i hx]
  rfl

/-! ### The Euler sequence -/

variable (m) in
/-- **The splitting of the Euler sequence** `TℂPᵐ ⊕ ℂ ≅ 𝒪(1)^{⊕(m+1)}` at a point `x` of
`ℂℙᵐ`. In the chart `i = (twistCore 1).indexAt x`, with `v` the representative of `x` with
`v i = 1`, it sends a tangent vector `ξ` and a scalar `c` to `(1 - P) ξ̃ + c v`, where `ξ̃` is `ξ`
with a zero inserted at `i` and `P` is the orthogonal projection onto the line `x`
(`eulerSequenceEquiv_apply`). It is continuous on total spaces in both directions
(`continuous_eulerSequenceEquiv` and `continuous_eulerSequenceEquiv_symm`). -/
def eulerSequenceEquiv (x : ℙ ℂ (Fin (m + 1) → ℂ)) :
    ((TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) ×ᵇ
      Bundle.Trivial (ℙ ℂ (Fin (m + 1) → ℂ)) ℂ) x ≃L[ℂ] (twistPiCore 1 (Fin (m + 1))).Fiber x :=
  -- The fibres of both bundles are their model fibres `(Fin m → ℂ) × ℂ` and `Fin (m + 1) → ℂ`.
  ContinuousLinearEquiv.ofContinuousLinearMap (eulerModel ((twistCore 1).indexAt x) x)
    (eulerModelInv ((twistCore 1).indexAt x) x)
    (ContinuousLinearMap.ext (eulerModel_eulerModelInv _ (mem_affineOpen_twistCore_indexAt 1 x)))
    (ContinuousLinearMap.ext (eulerModelInv_eulerModel _ (mem_affineOpen_twistCore_indexAt 1 x)))

/-- `eulerSequenceEquiv` in the preferred chart `i` at `x`: `(ξ, c) ↦ (1 - P) ξ̃ + c v`, where `v`
is the representative of `x` with `v i = 1`, `ξ̃` is `ξ` with a zero inserted at `i`, and `P` is the
Hermitian projector of `x`. -/
theorem eulerSequenceEquiv_apply (x : ℙ ℂ (Fin (m + 1) → ℂ))
    (v : ((TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) ×ᵇ
      Bundle.Trivial (ℙ ℂ (Fin (m + 1) → ℂ)) ℂ) x) :
    eulerSequenceEquiv m x v =
      (1 - hermitianProjector x) *ᵥ
          Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 0 v.1 +
        v.2 • Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 1
          (affineChart ((twistCore 1).indexAt x) x) :=
  (rfl)

/-- The inverse of `eulerSequenceEquiv` in the preferred chart `i` at `x`: it sends `w` to the
tangent vector `ξ` with `ξ̃ = w - w i • v` and the scalar `c` with `c v` the orthogonal projection
of `w` onto the line `x`, where `v` is the representative of `x` with `v i = 1`. -/
theorem eulerSequenceEquiv_symm_apply (x : ℙ ℂ (Fin (m + 1) → ℂ))
    (w : (twistPiCore 1 (Fin (m + 1))).Fiber x) :
    (eulerSequenceEquiv m x).symm w =
      ((fun k ↦ w (((twistCore 1).indexAt x).succAbove k) - w ((twistCore 1).indexAt x) *
          Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 1
            (affineChart ((twistCore 1).indexAt x) x) (((twistCore 1).indexAt x).succAbove k),
        (star (Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 1
            (affineChart ((twistCore 1).indexAt x) x)) ⬝ᵥ w) /
          (star (Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 1
              (affineChart ((twistCore 1).indexAt x) x)) ⬝ᵥ
            Fin.insertNth (α := fun _ ↦ ℂ) ((twistCore 1).indexAt x) 1
              (affineChart ((twistCore 1).indexAt x) x))) :
        (Fin m → ℂ) × ℂ) :=
  (rfl)

/-- `eulerSequenceEquiv` is continuous on total spaces. -/
theorem continuous_eulerSequenceEquiv :
    Continuous fun p : TotalSpace ((Fin m → ℂ) × ℂ)
        ((TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) ×ᵇ
          Bundle.Trivial (ℙ ℂ (Fin (m + 1) → ℂ)) ℂ) ↦
      TotalSpace.mk' (Fin (m + 1) → ℂ) (E := (twistPiCore 1 (Fin (m + 1))).Fiber) p.proj
        (eulerSequenceEquiv m p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj _ _).continuousAt, ?_⟩
  set c₀ := (twistCore (𝕜 := ℂ) (n := m) 1).indexAt p₀.proj
  have hc₀ : p₀.proj ∈ affineOpen c₀ := mem_affineOpen_twistCore_indexAt 1 p₀.proj
  have hU : ∀ᶠ p in 𝓝 p₀, p.proj ∈ affineOpen c₀ :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((isOpen_affineOpen c₀).mem_nhds hc₀)
  -- Near `p₀`, the map reads `eulerModel c₀` in the trivializations at `p₀`.
  refine ContinuousAt.congr (f := fun p ↦ eulerModel c₀ p.proj
      ((trivializationAt ((Fin m → ℂ) × ℂ)
        ((TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) ×ᵇ
          Bundle.Trivial (ℙ ℂ (Fin (m + 1) → ℂ)) ℂ) p₀.proj p).2))
    ?_ (hU.mono fun p hp ↦ ?_)
  · exact (((continuousOn_eulerModel c₀).continuousAt
      ((isOpen_affineOpen c₀).mem_nhds hc₀)).comp
      (FiberBundle.continuous_proj _ _).continuousAt).clm_apply
      (continuous_snd.continuousAt.comp ((trivializationAt _ _ p₀.proj).continuousAt
        FiberBundle.mem_trivializationAt_proj_source))
  · set c := (twistCore (𝕜 := ℂ) (n := m) 1).indexAt p.proj
    have hc : p.proj ∈ affineOpen c := mem_affineOpen_twistCore_indexAt 1 p.proj
    simp only [VectorBundleCore.trivializationAt, ← VectorBundleCore.localTrivAt_def,
      twistPiCore_indexAt, FiberBundle.prod_trivializationAt']
    rw [twistPiCore_localTriv_apply]
    refine Eq.trans ?_ (smul_eulerModel c c₀ hc hp p.snd).symm
    -- The tangent coordinate change is the derivative of the transition map between the charts
    -- at `p.proj` and at `p₀.proj`.
    simp [Trivialization.prod_apply, Trivialization.Prod.toFun',
      TangentBundle.trivializationAt_apply, fderivWithin_univ,
      chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt 1 p.proj,
      chartAt_eq_affineOpenPartialHomeomorph_twistCore_indexAt 1 p₀.proj, c, c₀]

/-- The inverse of `eulerSequenceEquiv` is continuous on total spaces. -/
theorem continuous_eulerSequenceEquiv_symm :
    Continuous fun q : TotalSpace (Fin (m + 1) → ℂ) (twistPiCore (𝕜 := ℂ) (n := m) 1
        (Fin (m + 1))).Fiber ↦
      TotalSpace.mk' ((Fin m → ℂ) × ℂ)
        (E := (TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) ×ᵇ
          Bundle.Trivial (ℙ ℂ (Fin (m + 1) → ℂ)) ℂ) q.proj
        ((eulerSequenceEquiv m q.proj).symm q.snd) :=
  TauCeti.continuous_bundle_symm _ continuous_eulerSequenceEquiv

end Projectivization

end
