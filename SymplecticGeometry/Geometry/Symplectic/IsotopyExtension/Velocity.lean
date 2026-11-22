/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Diffeotopy
public import TauCeti.Geometry.Manifold.VectorField.Prod
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Velocity forms of symplectic isotopies

Let `F : [0, 1] × P → M` be a smooth isotopy of embeddings (`TauCeti.SmoothIsotopy`), and let `τ`
and `σ` be two-forms on `P` and `M`. The isotopy is symplectic
(`TauCeti.SmoothIsotopy.IsSymplectic τ σ F`) when every slice `F_t = F (t, ·)` pulls `σ` back to
`τ`. Its velocity form (`TauCeti.SmoothIsotopy.velocityForm σ F`) is the one-form `ι_{∂ₜ} F^* σ` on
the cylinder `[0, 1] × P`, the contraction of `F^* σ` with the unit time field `∂ₜ = (1, 0)`. Its
slice at time `t` is the one-form `v ↦ σ (∂ₜ F (t, x), dF_t v)` on `P`, the velocity one-form of
the isotopy at that time, as in McDuff–Salamon, §3.3.

When `σ` is closed and `F` is symplectic, every slice of the velocity form is closed. The form
`F^* σ` on the cylinder is closed, so Cartan's formula makes `d ι_{∂ₜ} F^* σ` the Lie derivative
`L_{∂ₜ} F^* σ`, and the slices of this Lie derivative vanish because the slices of `F^* σ` do not
depend on `t`. The last step holds for any form on a product `N × P` with constant slices and the
horizontal lift `(X, 0)` of any vector field on `N`
(`TauCeti.mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero`, in
`SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv`).

For a diffeotopy `φ_t` of `M`, the slices of the velocity form of the isotopy `(t, x) ↦ φ_t x`
are the integrands of Tau Ceti's `TauCeti.Diffeotopy.HasHamiltonian`. So a function `F` on
`M × [0, 1]` is a Hamiltonian of `φ_t` exactly when it is smooth and the slices of the velocity
form are the differentials of the `F (·, t)`. This passes between the cylinder `M × [0, 1]` of
diffeotopies and the cylinder `[0, 1] × M` of isotopies.

## Main definitions

* `TauCeti.SmoothIsotopy.IsSymplectic τ σ F`: every slice of `F` pulls `σ` back to `τ`.
* `TauCeti.SmoothIsotopy.velocityForm σ F`: the one-form `ι_{∂ₜ} F^* σ` on `[0, 1] × P`.

## Main results

* `TauCeti.SmoothIsotopy.velocityForm_apply`, `TauCeti.SmoothIsotopy.mpullback_prodMk_velocityForm`:
  the velocity form and its slices on a spatial vector `v` give `σ (∂ₜ F (t, x), dF_t v)`.
* `TauCeti.SmoothIsotopy.eq_mfderiv_of_forall_eq_mpullback_prodMk_velocityForm`: for a
  nondegenerate `σ` and manifolds of the same dimension, the velocity `∂ₜ F (t, x)` is the only
  vector at `F (t, x)` whose contraction with `σ`, pulled back by `F_t`, is the slice of the
  velocity form.
* `TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`: for a closed `σ`,
  the slices of the velocity form of a symplectic isotopy are closed.
* `TauCeti.SmoothIsotopy.IsSymplectic.refl`, `TauCeti.Diffeotopy.isSymplectic_smoothIsotopy`: the
  constant isotopy of a map pulling `σ` back to `τ`, and the restriction of a diffeotopy whose
  slices preserve `σ` to an embedding `f`, are symplectic (for `f^* σ`).
* `TauCeti.SmoothIsotopy.IsSymplectic.of_apply_eq_diffeotopy_apply`,
  `TauCeti.SmoothIsotopy.IsSymplectic.of_apply_eq_apply_diffeomorph`: an isotopy that is a
  symplectic isotopy composed with a diffeotopy preserving `σ`, or with a diffeomorphism of the
  source, is symplectic.
* `TauCeti.Diffeotopy.hasHamiltonian_iff_velocityForm`: Hamiltonians of a diffeotopy are the
  smooth functions whose slices are primitives of the slices of its velocity form.

## Implementation notes

The form `σ` on `M` is not called `ω`, which is a token once the scope `ContDiff` is open. The
proof of `hasHamiltonian_iff_velocityForm` reads the derivatives of the motion as that of
`TauCeti.Diffeotopy.hasHamiltonian_iff_isHamiltonianVectorField_velocity` does, through
`TauCeti.Diffeotopy.mfderiv_cylinderMap_time` and `TauCeti.Diffeotopy.mfderiv_cylinderMap_space`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 14.35
  (Cartan's formula) and Corollary 12.33 (the bracket formula for Lie derivatives of forms).
-/

public noncomputable section

open Set Bundle VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

/-! ### The unit time field of the cylinder -/

section TimeField

variable [IsManifold J ∞ P]

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P` is smooth, up to both ends. -/
theorem contMDiff_prodVectorField_one_zero :
    ContMDiff ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J).tangent ∞ (fun p : unitInterval × P ↦
      (⟨p, Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) p⟩ : TangentBundle ((𝓡∂ 1).prod J) (unitInterval × P))) :=
  Manifold.contMDiff_prodVectorField contMDiff_totalSpaceMk_one_Icc
    (contMDiff_zeroSection ℝ (TangentSpace J))

end TimeField

namespace SmoothIsotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P] {f₀ f₁ : C^∞⟮J, P; I, M⟯}

/-! ### Symplectic isotopies -/

/-- A smooth isotopy `F` from `P` to `M` is **symplectic** for two-forms `τ` on `P` and `σ` on
`M` when every slice `F_t = F (t, ·)` pulls `σ` back to `τ`. -/
def IsSymplectic (τ : SmoothTwoForm J P) (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁) :
    Prop :=
  ∀ t, mpullback J I (fun x ↦ F (t, x)) σ.val = τ.val

/-- Unfolding `TauCeti.SmoothIsotopy.IsSymplectic`. -/
theorem isSymplectic_def {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} :
    F.IsSymplectic τ σ ↔ ∀ t, mpullback J I (fun x ↦ F (t, x)) σ.val = τ.val :=
  Iff.rfl

/-! ### Velocity forms -/

/-- The **velocity form** of a smooth isotopy `F` for a two-form `σ`: the one-form
`ι_{∂ₜ} F^* σ` on the cylinder `[0, 1] × P`, the contraction of the pullback of `σ` with the unit
time field `∂ₜ = (1, 0)`. At `(t, x)` it sends `(0, v)` to `σ (∂ₜ F (t, x), dF_t v)`
(`TauCeti.SmoothIsotopy.velocityForm_apply`), so its slice at time `t` is the velocity one-form
`α_t = ι_t^* ι_{∂ₜ} F^* σ` of `F` at that time. -/
def velocityForm (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁) :
    SmoothForm ((𝓡∂ 1).prod J) (unitInterval × P) ℝ 1 :=
  ⟨RoughForm.interior
      (Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y))
      (mpullback ((𝓡∂ 1).prod J) I (F : unitInterval × P → M) σ.val), by
    rw [← SmoothForm.coe_mpullback _ F.contMDiff]
    exact ((SmoothForm.mpullback F F.contMDiff σ).isSmoothForm.interior
      contMDiff_prodVectorField_one_zero).mem_smoothBundleForms⟩

variable (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁)

/-- The velocity form is the contraction of `F^* σ` with the unit time field. -/
theorem velocityForm_def :
    (F.velocityForm σ).val = RoughForm.interior
      (Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y))
      (mpullback ((𝓡∂ 1).prod J) I (F : unitInterval × P → M) σ.val) :=
  (rfl)

/-- The value of the velocity form at `(t, x)` on a spatial vector `(0, v)` is
`σ (∂ₜ F (t, x), dF_t v)`. -/
theorem velocityForm_apply (t : unitInterval) (x : P) (v : E') :
    (F.velocityForm σ).val (t, x) ![((0 : EuclideanSpace ℝ (Fin 1)), v)] =
      σ.val (F (t, x)) ![mfderiv (𝓡∂ 1) I (fun s ↦ F (s, x)) t 1,
        mfderiv J I (fun y ↦ F (t, y)) x v] := by
  have hF := F.contMDiff.mdifferentiableAt (x := (t, x)) (by simp)
  have hT : Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
      (0 : Π y : P, TangentSpace J y) (t, x) = ((1 : TangentSpace (𝓡∂ 1) t), (0 : E')) :=
    Prod.ext (Manifold.prodVectorField_fst _ _ _) (Manifold.prodVectorField_snd _ _ _)
  rw [velocityForm_def, RoughForm.interior_apply, mpullback_apply, hT]
  congr 1
  funext i
  fin_cases i
  · exact hF.mfderiv_curry_left_apply _
  · exact hF.mfderiv_curry_right_apply v

/-- The slice of the velocity form at time `t` sends `v` at `x` to `σ (∂ₜ F (t, x), dF_t v)`. -/
theorem mpullback_prodMk_velocityForm (t : unitInterval) (x : P) (v : E') :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (F.velocityForm σ)).val x ![v] =
      σ.val (F (t, x)) ![mfderiv (𝓡∂ 1) I (fun s ↦ F (s, x)) t 1,
        mfderiv J I (fun y ↦ F (t, y)) x v] := by
  rw [SmoothForm.coe_mpullback, mpullback_apply, ← velocityForm_apply]
  congr 1
  funext i
  fin_cases i
  rw [mfderiv_prod_right]
  -- `inr v` is `(0, v)` by definition.
  rfl

variable {σ} in
/-- **The velocity is determined by the velocity form.** Let `σ` be nondegenerate and let `P` and
`M` have the same dimension. A vector `Y` at `F (t, x)` whose contraction with `σ`, pulled
back by `F_t`, is the slice at `x` of the velocity form, is the velocity `∂ₜ F (t, x)`. -/
theorem eq_mfderiv_of_forall_eq_mpullback_prodMk_velocityForm [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [I.Boundaryless] [J.Boundaryless] (hσ : σ.IsNondegenerate)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {t : unitInterval} {x : P}
    {Y : TangentSpace I (F (t, x))}
    (hY : ∀ v : E', σ.val (F (t, x)) ![Y, mfderiv J I (fun y ↦ F (t, y)) x v] =
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (F.velocityForm σ)).val x ![v]) :
    Y = mfderiv (𝓡∂ 1) I (fun s ↦ F (s, x)) t 1 := by
  have hloc : IsLocalDiffeomorph J I ∞ (fun y ↦ F (t, y)) :=
    (F.isSmoothEmbedding t).isImmersion.isLocalDiffeomorph hd (by simp)
  -- Both vectors contract with `σ` to the same covector on the image of `dF_t`, which is onto.
  refine (hσ.isInvertible_flat _).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := ((hloc x).isInvertible_mfderiv (by simp)).surjective w
  rw [SmoothTwoForm.flat_apply, SmoothTwoForm.flat_apply, SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_apply]
  exact (hY v).trans (mpullback_prodMk_velocityForm σ F t x v)

/-! ### Closedness of the velocity forms -/

/-- **The velocity forms of a symplectic isotopy are closed.** If `σ` is closed and every slice of
`F` pulls `σ` back to the same form `τ`, then every slice `α_t` of the velocity form is closed. -/
theorem IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm [CompleteSpace E']
    {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M} {F : SmoothIsotopy f₀ f₁}
    (hσ : σ.IsClosed) (hF : F.IsSymplectic τ σ) (t : unitInterval) :
    mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (F.velocityForm σ)).val = 0 := by
  set β := SmoothForm.mpullback F F.contMDiff σ
  have hβ : mextDeriv β.val = 0 := (SmoothForm.isClosed_def _).1 (hσ.mpullback F F.contMDiff)
  have hd : mextDeriv (F.velocityForm σ).val = mlieDerivForm
      (Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y)) β.val := by
    rw [velocityForm_def, ← SmoothForm.coe_mpullback _ F.contMDiff]
    exact (mlieDerivForm_eq_mextDeriv_interior (fun p ↦ β.mdifferentiableAt p)
      (contMDiff_prodVectorField_one_zero.mdifferentiable (by simp)) hβ).symm
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.coe_mpullback, mextDerivₗ_apply, hd]
  funext x
  refine mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero (β.mdifferentiableAt _)
    ((contMDiff_totalSpaceMk_one_Icc (n := 1)).mdifferentiableAt one_ne_zero) fun s ↦ ?_
  have hs (s : unitInterval) : mpullback J ((𝓡∂ 1).prod J) (Prod.mk s) β.val = τ.val := by
    have hι : MDifferentiable J ((𝓡∂ 1).prod J) (Prod.mk s : P → unitInterval × P) :=
      mdifferentiable_const.prodMk mdifferentiable_id
    rw [SmoothForm.coe_mpullback, ← mpullback_comp hι (F.contMDiff.mdifferentiable (by simp))]
    exact hF s
  rw [hs, hs]

/-! ### Examples and invariance of symplectic isotopies -/

/-- The constant isotopy of a smooth embedding that pulls `σ` back to `τ` is symplectic. -/
theorem IsSymplectic.refl {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {f : C^∞⟮J, P; I, M⟯} (hf : Manifold.IsSmoothEmbedding J I ∞ f)
    (h : mpullback J I f σ.val = τ.val) : (f.smoothIsotopyRefl hf).IsSymplectic τ σ :=
  fun _ ↦ by simpa only [ContMDiffMap.smoothIsotopyRefl_apply] using h

/-- A slice of a symplectic isotopy, as a smooth embedding, pulls `σ` back to `τ`. -/
theorem IsSymplectic.mpullback_timeSlice {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} (hF : F.IsSymplectic τ σ) (t : unitInterval) :
    mpullback J I (F.timeSlice t) σ.val = τ.val := by
  simpa only [← timeSlice_apply] using hF t

/-- Reversing time keeps an isotopy symplectic. -/
theorem IsSymplectic.symm {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M}
    {F : SmoothIsotopy f₀ f₁} (hF : F.IsSymplectic τ σ) : F.symm.IsSymplectic τ σ := fun t ↦ by
  simpa only [symm_apply] using hF (unitInterval.symm t)

/-- **Composition with a symplectic diffeotopy.** If `F` is symplectic and every slice of the
diffeotopy `Φ` of `M` preserves `σ`, then an isotopy `G` with `G (t, x) = Φ (t, F (t, x))` is
symplectic. -/
theorem IsSymplectic.of_apply_eq_diffeotopy_apply {g₀ g₁ : C^∞⟮J, P; I, M⟯}
    {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M} {F : SmoothIsotopy f₀ f₁}
    {G : SmoothIsotopy g₀ g₁} (hF : F.IsSymplectic τ σ) {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ)
    (hG : ∀ t x, G (t, x) = Φ (t, F (t, x))) : G.IsSymplectic τ σ := fun t ↦ by
  have hfun : (fun x ↦ G (t, x)) = Φ.timeSlice t ∘ F.timeSlice t :=
    funext fun x ↦ by rw [hG, Function.comp_apply, Diffeotopy.timeSlice_apply, timeSlice_apply]
  have hΦt : mpullback I I (Φ.timeSlice t) σ.val = σ.val := by
    rw [← SmoothForm.coe_mpullback _ (Φ.timeSlice t).contMDiff,
      SmoothForm.mem_diffeomorphStabilizer.1 (hΦ t)]
  rw [hfun, mpullback_comp ((F.timeSlice t).contMDiff.mdifferentiable (by simp))
    ((Φ.timeSlice t).contMDiff.mdifferentiable (by simp)), hΦt]
  exact hF.mpullback_timeSlice t

/-- **Composition with a diffeomorphism of the source.** If `F` is symplectic for `τ` and `σ`, and
`χ : Q → P` is a diffeomorphism, then an isotopy `G` with `G (t, y) = F (t, χ y)` is symplectic for
`χ^* τ` and `σ`. -/
theorem IsSymplectic.of_apply_eq_apply_diffeomorph {E'' H'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [TopologicalSpace H''] {J' : ModelWithCorners ℝ E'' H''} {Q : Type*}
    [TopologicalSpace Q] [ChartedSpace H'' Q] [IsManifold J' ∞ Q] {g₀ g₁ : C^∞⟮J', Q; I, M⟯}
    {τ : SmoothTwoForm J P} {σ : SmoothTwoForm I M} {F : SmoothIsotopy f₀ f₁}
    {G : SmoothIsotopy g₀ g₁} (hF : F.IsSymplectic τ σ) (χ : Q ≃ₘ⟮J', J⟯ P)
    (hG : ∀ t y, G (t, y) = F (t, χ y)) :
    G.IsSymplectic (SmoothForm.mpullback χ χ.contMDiff τ) σ := fun t ↦ by
  have hfun : (fun y ↦ G (t, y)) = F.timeSlice t ∘ χ :=
    funext fun y ↦ by rw [hG, Function.comp_apply, timeSlice_apply]
  rw [hfun, mpullback_comp (χ.contMDiff.mdifferentiable (by simp))
    ((F.timeSlice t).contMDiff.mdifferentiable (by simp)), hF.mpullback_timeSlice t,
    SmoothForm.coe_mpullback]

end SmoothIsotopy

namespace Diffeotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P]

/-- The restriction `t ↦ φ_t ∘ f` of a diffeotopy whose slices preserve `σ` to a smooth embedding
`f` is a symplectic isotopy, for `f^* σ` on the source. -/
theorem isSymplectic_smoothIsotopy {σ : SmoothTwoForm I M} {Φ : Diffeotopy I ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) (f : C^∞⟮J, P; I, M⟯)
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    (Φ.smoothIsotopy f hf).IsSymplectic (SmoothForm.mpullback f f.contMDiff σ) σ :=
  SmoothIsotopy.IsSymplectic.of_apply_eq_diffeotopy_apply
    (SmoothIsotopy.IsSymplectic.refl hf (SmoothForm.coe_mpullback _ _ _).symm) hΦ
    fun _ _ ↦ by simp

/-- **Hamiltonians and velocity forms.** A function `F` on `M × [0, 1]` is a Hamiltonian of the
diffeotopy `φ_t`, read along the motion as in `TauCeti.Diffeotopy.HasHamiltonian`, exactly when
it is smooth and, for every `t`, the slice at time `t` of the velocity form of the isotopy
`(t, x) ↦ φ_t x` on the cylinder `[0, 1] × M` is the differential of `F (·, t)`. -/
theorem hasHamiltonian_iff_velocityForm {σ : SmoothTwoForm I M} {Φ : Diffeotopy I ∞ M}
    {F : M × unitInterval → ℝ} :
    Φ.HasHamiltonian σ F ↔ ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ F ∧ ∀ t,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        ((Φ.smoothIsotopy ContMDiffMap.id Manifold.IsSmoothEmbedding.id).velocityForm σ)).val =
        mextDeriv (RoughForm.ofFunction I fun x ↦ F (x, t)) := by
  set G := Φ.smoothIsotopy ContMDiffMap.id Manifold.IsSmoothEmbedding.id with hGdef
  have hG (p : unitInterval × M) : G p = Φ p := by
    rw [hGdef]
    exact (smoothIsotopy_apply Φ _ _ p).trans
      (congrArg (fun y ↦ Φ (p.1, y)) (ContMDiffMap.id_apply p.2))
  -- The slices of the velocity form are the integrands of `HasHamiltonian`.
  have hα (t : unitInterval) (x : M) (v : E) :
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
          (G.velocityForm σ)).val x ![v] =
        mpullback (I.prod (𝓡∂ 1)) I Φ.cylinderMap σ.val (x, t)
          ![((0 : E), (1 : TangentSpace (𝓡∂ 1) t)), (v, (0 : EuclideanSpace ℝ (Fin 1)))] := by
    have h1 : (fun s ↦ G (s, x)) = fun s ↦ Φ (s, x) := funext fun s ↦ by
      rw [hG]
    have h2 : (fun y ↦ G (t, y)) = Φ.timeSlice t := funext fun y ↦ by
      rw [hG, timeSlice_apply]
    rw [SmoothIsotopy.mpullback_prodMk_velocityForm, h1, h2, mpullback_apply]
    congr 1
    · rw [hG, cylinderMap_apply]
    · funext i
      fin_cases i
      · exact (Φ.mfderiv_cylinderMap_time (by simp) (x, t)).symm
      · exact (Φ.mfderiv_cylinderMap_space (by simp) (x, t) v).symm
  -- The differentials of the slices of `F` are its partial derivatives in space.
  have hd (hF : ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ F) (t : unitInterval) (x : M) (v : E) :
      mextDeriv (RoughForm.ofFunction I fun y ↦ F (y, t)) x ![v] =
        mvfderiv (I.prod (𝓡∂ 1)) F (x, t) (v, (0 : EuclideanSpace ℝ (Fin 1))) := by
    refine (mextDeriv_ofFunction_apply _ x v).trans ?_
    exact ((hF.mdifferentiableAt (x := (x, t)) (by simp)).mfderiv_curry_left_apply v).symm.trans
      (mvfderiv_apply_eq_mfderiv_apply F (x, t) _).symm
  rw [hasHamiltonian_iff]
  refine and_congr_right fun hF ↦ ⟨fun h t ↦ ?_, fun h p v ↦ ?_⟩
  · funext x
    ext w
    have hw : w = ![w 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hw]
    exact (hα t x (w 0)).trans ((h (x, t) (w 0)).trans (hd hF t x (w 0)).symm)
  · rw [← hα, ← hd hF, h]

end Diffeotopy

end TauCeti

end
