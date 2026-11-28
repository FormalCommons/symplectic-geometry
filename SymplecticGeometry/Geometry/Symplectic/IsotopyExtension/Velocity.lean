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
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.LieDeriv
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Opens
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Velocity forms of symplectic isotopies

Let `F : [0, 1] × P → M` be a smooth isotopy of embeddings (`TauCeti.SmoothIsotopy`), and let `τ`
and `σ` be two-forms on `P` and `M`. The isotopy is symplectic
(`TauCeti.SmoothIsotopy.IsSymplectic τ σ F`, in
`SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.IsSymplectic`) when every slice
`F_t = F (t, ·)` pulls `σ` back to `τ`. Its velocity form
(`TauCeti.SmoothIsotopy.velocityForm σ F`) is the one-form `ι_{∂ₜ} F^* σ` on
the cylinder `[0, 1] × P`, the interior product (`TauCeti.SmoothForm.interiorProduct`) of `F^* σ`
with the unit time field `∂ₜ = (1, 0)`, a smooth section of the tangent bundle
(`SymplecticGeometry.unitIntervalTimeField`). Its slice at time `t` is the one-form
`v ↦ σ (∂ₜ F (t, x), dF_t v)` on `P`, the velocity one-form of the isotopy at that time, as in
McDuff–Salamon, §3.3.

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

For a family of isotopies `k_t` with a parameter `t ∈ [0, 1]`, given by a smooth map
`Ĝ : [0, 1]² × P → M` as `k_t (s, x) = Ĝ ((t, s), x)`, the slices of the velocity forms are the
slices of the one-form `ι_{∂ₛ} Ĝ^* σ` on `[0, 1]² × P`, with `∂ₛ = ((0, 1), 0)` the unit field of
the second time coordinate (`SymplecticGeometry.unitIntervalSqSndField`). So they form a smooth
family over `(t, s)`; the computation is that of `TauCeti.SmoothIsotopy.velocityForm_apply`,
with one more time coordinate. When the `k_t` are symplectic, `σ` is closed and `P` is a
nonempty open convex set, the parametric Poincaré lemma
(`IsSmoothlyContractible.exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms`)
then gives jointly smooth primitives. Normalized to vanish at a point of `P`, they vanish for each
`t` at which `Ĝ ((t, ·), ·)` stands still, since the velocity forms vanish there and `P` is
connected.

## Main definitions

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
* `TauCeti.Diffeotopy.hasHamiltonian_iff_velocityForm`: Hamiltonians of a diffeotopy are the
  smooth functions whose slices are primitives of the slices of its velocity form.
* `TauCeti.SmoothIsotopy.mpullback_prodMk_velocityForm_restrict`: the slices of the velocity form
  of a restriction (`TauCeti.SmoothIsotopy.restrict`, in
  `SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Basic`) are the restrictions of the slices.
* `TauCeti.SmoothIsotopy.exists_opens_forall_apply_eq_of_forall_isCompact`: if the restriction
  of an isotopy to an open `V ⊇ Q` agrees on each compact subset of `V` with a diffeotopy of a
  given kind, the isotopy agrees with one on an open neighbourhood of `Q`.
* `SymplecticGeometry.isSmoothFamily_velocityForm`: the slices of the velocity forms of a jointly
  smooth family of isotopies form a smooth family over both parameters.
* `SymplecticGeometry.exists_contMDiff_velocityForm_eq_mextDeriv`: jointly smooth primitives of
  the velocity forms of a family of symplectic isotopies of a convex set, zero where the family
  stands still.

## Implementation notes

The form `σ` on `M` is not called `ω`, which is a token once the scope `ContDiff` is open. The
proof of `hasHamiltonian_iff_velocityForm` reads the derivatives of the motion through
`TauCeti.Diffeotopy.mfderiv_cylinderMap_time` and `TauCeti.Diffeotopy.mfderiv_cylinderMap_inl`,
much as Tau Ceti's `TauCeti.Diffeotopy.mpullback_cylinderMap_apply_eq_eval₂_velocity` does.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 14.35
  (Cartan's formula) and Corollary 12.33 (the bracket formula for Lie derivatives of forms).
-/

public noncomputable section

open Set Bundle VectorField
open scoped Manifold ContDiff
open SymplecticGeometry (unitIntervalTimeField coe_unitIntervalTimeField)

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

namespace SmoothIsotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P] {f₀ f₁ : C^∞⟮J, P; I, M⟯}

/-! ### Velocity forms -/

/-- The **velocity form** of a smooth isotopy `F` for a two-form `σ`: the one-form
`ι_{∂ₜ} F^* σ` on the cylinder `[0, 1] × P`, the contraction of the pullback of `σ` with the unit
time field `∂ₜ = (1, 0)`. At `(t, x)` it sends `(0, v)` to `σ (∂ₜ F (t, x), dF_t v)`
(`TauCeti.SmoothIsotopy.velocityForm_apply`), so its slice at time `t` is the velocity one-form
`α_t = ι_t^* ι_{∂ₜ} F^* σ` of `F` at that time. -/
def velocityForm (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁) :
    SmoothForm ((𝓡∂ 1).prod J) (unitInterval × P) ℝ 1 :=
  SmoothForm.interiorProduct unitIntervalTimeField (SmoothForm.mpullback F F.contMDiff σ)

variable (σ : SmoothTwoForm I M) (F : SmoothIsotopy f₀ f₁)

/-- The velocity form is the interior product of `F^* σ` with the unit time field. -/
theorem velocityForm_def :
    F.velocityForm σ =
      SmoothForm.interiorProduct unitIntervalTimeField (SmoothForm.mpullback F F.contMDiff σ) :=
  (rfl)

/-- The underlying form of the velocity form is the contraction of `F^* σ` with the unit time
field. -/
@[simp]
theorem coe_velocityForm :
    (F.velocityForm σ).val = RoughForm.interior
      (Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y))
      (mpullback ((𝓡∂ 1).prod J) I (F : unitInterval × P → M) σ.val) := by
  rw [velocityForm_def, SmoothForm.coe_interiorProduct, coe_unitIntervalTimeField,
    SmoothForm.coe_mpullback]

/-- The value of the velocity form at `(t, x)` on a spatial vector `(0, v)` is
`σ (∂ₜ F (t, x), dF_t v)`. -/
theorem velocityForm_apply (t : unitInterval) (x : P) (v : E') :
    (F.velocityForm σ).val (t, x) ![((0 : EuclideanSpace ℝ (Fin 1)), v)] =
      σ.val (F (t, x)) ![mfderiv (𝓡∂ 1) I (fun s ↦ F (s, x)) t 1,
        mfderiv J I (fun y ↦ F (t, y)) x v] := by
  have hF := F.contMDiff.mdifferentiableAt (x := (t, x)) (by simp)
  have hT : Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
      (0 : Π y : P, TangentSpace J y) (t, x) = ((1 : TangentSpace (𝓡∂ 1) t), (0 : E')) :=
    Manifold.prodVectorField_apply _ _ _
  rw [coe_velocityForm, RoughForm.interior_apply]
  -- The spatial vector `(0, v)` lies in the model space rather than in a tangent space, so the
  -- evaluation lemma is applied by unification rather than by `rw`.
  refine (mpullback_apply_pair _ _ _ _ _).trans ?_
  rw [hT]
  exact congrArg₂ (fun a b ↦ σ.val (F (t, x)) ![a, b])
    (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun s y ↦ F (s, y)) hF _)
    (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun s y ↦ F (s, y)) hF v)

/-- The slice of the velocity form at time `t` sends `v` at `x` to `σ (∂ₜ F (t, x), dF_t v)`. -/
theorem mpullback_prodMk_velocityForm (t : unitInterval) (x : P) (v : E') :
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (F.velocityForm σ)).val x ![v] =
      σ.val (F (t, x)) ![mfderiv (𝓡∂ 1) I (fun s ↦ F (s, x)) t 1,
        mfderiv J I (fun y ↦ F (t, y)) x v] := by
  rw [SmoothForm.coe_mpullback]
  refine ((mpullback_apply_one _ _ x v).trans ?_).trans (velocityForm_apply σ F t x v)
  exact congrArg (fun w ↦ (F.velocityForm σ).val (t, x) ![w]) (mfderiv_prodMk_right_apply v)

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
    rw [velocityForm_def, SmoothForm.coe_interiorProduct, coe_unitIntervalTimeField]
    exact (mlieDerivForm_eq_mextDeriv_interior (fun p ↦ β.mdifferentiableAt p)
      (Manifold.contMDiff_prodVectorField_one_zero.mdifferentiable (by simp)) hβ).symm
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.coe_mpullback, mextDerivₗ_apply, hd]
  funext x
  refine mpullback_prodMk_mlieDerivForm_prodVectorField_zero_eq_zero (β.mdifferentiableAt _)
    ((TauCeti.contMDiff_one_tangentSpace_Icc (n := 1)).mdifferentiableAt one_ne_zero)
    fun s ↦ ?_
  have hs (s : unitInterval) : mpullback J ((𝓡∂ 1).prod J) (Prod.mk s) β.val = τ.val := by
    have hι : MDifferentiable J ((𝓡∂ 1).prod J) (Prod.mk s : P → unitInterval × P) :=
      mdifferentiable_const.prodMk mdifferentiable_id
    rw [SmoothForm.coe_mpullback, ← mpullback_comp hι (F.contMDiff.mdifferentiable (by simp))]
    exact isSymplectic_def.1 hF s
  rw [hs, hs]

/-! ### Restriction to an open subset -/

section Restrict

open TopologicalSpace

variable {V W : Opens P} {g₀ g₁ : C^∞⟮J, W; I, M⟯}

/-- The slices of the velocity form of a restriction are the restrictions of the slices of the
velocity form. -/
theorem mpullback_prodMk_velocityForm_restrict (σ : SmoothTwoForm I M) (G : SmoothIsotopy g₀ g₁)
    (h : V ≤ W) (t : unitInterval) :
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        ((G.restrict h).velocityForm σ) =
      SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
          (G.velocityForm σ)) := by
  refine SmoothBundleForm.ext_eval₁ fun x w ↦ ?_
  have hcomp : mfderiv J I (fun y ↦ G (t, Opens.inclusion h y)) x w =
      mfderiv J I (fun y ↦ G (t, y)) (Opens.inclusion h x) w :=
    mfderiv_comp_inclusion_apply (g := fun y ↦ G (t, y)) h x w
  conv_rhs => rw [SmoothForm.mpullback_apply_one, Manifold.mfderiv_inclusion_apply]
  refine (mpullback_prodMk_velocityForm σ (G.restrict h) t x w).trans
    (Eq.trans ?_ (mpullback_prodMk_velocityForm σ G t (Opens.inclusion h x) w).symm)
  have h₁ : (fun s ↦ G.restrict h (s, x)) = fun s ↦ G (s, Opens.inclusion h x) :=
    funext fun s ↦ restrict_apply G h (s, x)
  have h₂ : (fun y ↦ G.restrict h (t, y)) = fun y ↦ G (t, Opens.inclusion h y) :=
    funext fun y ↦ restrict_apply G h (t, y)
  rw [restrict_apply, h₁, h₂, hcomp]

/-- **From compact sets to a neighbourhood.** Let `φ` be a smooth isotopy of an open `U ⊆ M` that
starts at the inclusion, `V ⊆ U` open and `Q ⊆ V` compact. If on every compact `K ⊆ V` the
restriction of `φ` to `V` agrees with a diffeotopy of `M` with a property `R`, then there are an
open `N` with `Q ⊆ N ⊆ U` and a diffeotopy `Ψ` of `M` with property `R` such that
`Ψ_t x = φ_t x` for every `t` and every `x ∈ N`. -/
theorem exists_opens_forall_apply_eq_of_forall_isCompact [FiniteDimensional ℝ E]
    {U V : Opens M} {f₀ f₁ : C^∞⟮I, U; I, M⟯} (φ : SmoothIsotopy f₀ f₁) (hf₀ : ∀ x, f₀ x = x)
    (hVU : V ≤ U) {Q : Set M} (hQ : IsCompact Q) (hQV : Q ⊆ V) {R : Diffeotopy I ∞ M → Prop}
    (hext : ∀ K : Set V, IsCompact K →
      ∃ Ψ, R Ψ ∧ ∀ t, ∀ x ∈ K, Ψ (t, f₀.comp (SmoothEmbedding.inclusion hVU).toContMDiffMap x) =
        φ.restrict hVU (t, x)) :
    ∃ N : Opens M, Q ⊆ N ∧ N ≤ U ∧ ∃ Ψ, R Ψ ∧ ∀ t, ∀ x : U, (x : M) ∈ N → Ψ (t, x) = φ (t, x) := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨L, hL, hQL, hLV⟩ := exists_compact_between hQ V.isOpen hQV
  obtain ⟨Ψ, hR, happly⟩ := hext _
    (Topology.IsInducing.subtypeVal.isCompact_preimage' hL (by rwa [Subtype.range_coe]))
  refine ⟨⟨interior L, isOpen_interior⟩, hQL, fun x hx ↦ hVU (hLV (interior_subset hx)), Ψ, hR,
    fun t x hx ↦ ?_⟩
  have := happly t ⟨x, hLV (interior_subset hx)⟩ (mem_preimage.2 (interior_subset hx))
  simpa [hf₀] using this

end Restrict

end SmoothIsotopy

namespace Diffeotopy

variable [IsManifold I ∞ M] [IsManifold J ∞ P]

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
    rw [SmoothIsotopy.mpullback_prodMk_velocityForm, h1, h2]
    refine Eq.trans ?_ (mpullback_apply_pair _ _ _ _ _).symm
    congr 1
    · rw [hG, cylinderMap_apply]
    · exact congrArg₂ (fun a b ↦ ![a, b]) (Φ.mfderiv_cylinderMap_time (by simp) (x, t)).symm
        (Φ.mfderiv_cylinderMap_inl (by simp) (x, t) v).symm
  -- The differentials of the slices of `F` are its partial derivatives in space.
  have hd (hF : ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ F) (t : unitInterval) (x : M) (v : E) :
      mextDeriv (RoughForm.ofFunction I fun y ↦ F (y, t)) x ![v] =
        mvfderiv (I.prod (𝓡∂ 1)) F (x, t) (v, (0 : EuclideanSpace ℝ (Fin 1))) := by
    refine (mextDeriv_ofFunction_apply _ x v).trans ?_
    exact (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun x t ↦ F (x, t))
      (hF.mdifferentiableAt (x := (x, t)) (by simp)) v).symm.trans
      (mvfderiv_apply_eq_mfderiv_apply F (x, t) _).symm
  rw [hasHamiltonian_iff]
  refine and_congr_right fun hF ↦ ⟨fun h t ↦ ?_, fun h p v ↦ ?_⟩
  · funext x
    ext w
    exact (hα t x w).trans ((h (x, t) w).trans (hd hF t x w).symm)
  · rw [← hα, ← hd hF, h]

end Diffeotopy

end TauCeti

namespace SymplecticGeometry

open TauCeti

/-! ### Families of isotopies with a parameter -/

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Family

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ P]

/-- **The velocity forms of a family of isotopies form a smooth family.** Let `Ĝ` be a smooth map
`[0, 1]² × P → M`, and `k_t`, for each `t`, a smooth isotopy with `k_t (s, x) = Ĝ ((t, s), x)`.
Then the slices `α_{t, s}` of the velocity forms of the `k_t` form a smooth family over
`[0, 1]²`: they are the slices of `ι_{∂ₛ} Ĝ^* σ`. -/
theorem isSmoothFamily_velocityForm (σ : SmoothTwoForm I M)
    {Ĝ : (unitInterval × unitInterval) × P → M}
    (hĜ : ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod J) I ∞ Ĝ) {f₀ f₁ : unitInterval → C^∞⟮J, P; I, M⟯}
    (k : ∀ t, SmoothIsotopy (f₀ t) (f₁ t)) (hk : ∀ t p, k t p = Ĝ ((t, p.1), p.2)) :
    IsSmoothFamily ((𝓡∂ 1).prod (𝓡∂ 1)) fun q : unitInterval × unitInterval ↦
      SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
        ((k q.1).velocityForm σ) := by
  refine isSmoothFamily_def.2 ⟨SmoothForm.interiorProduct unitIntervalSqSndField
    (SmoothForm.mpullback Ĝ hĜ σ),
    fun ⟨t, s⟩ ↦ SmoothBundleForm.ext_eval₁ fun x w ↦ ?_⟩
  have hkt : (k t : unitInterval × P → M) = fun p ↦ Ĝ ((t, p.1), p.2) := funext (hk t)
  have hĜd := hĜ.mdifferentiableAt (x := ((t, s), x)) (by simp)
  rw [SmoothIsotopy.mpullback_prodMk_velocityForm σ (k t) s x w, hkt]
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply_one, SmoothForm.coe_interiorProduct,
    RoughForm.interior_apply, SmoothForm.coe_mpullback, TauCeti.mpullback_apply_pair,
    unitIntervalSqSndField_apply]
  refine congrArg₂ (fun a b ↦ σ.val _ ![a, b]) ?_ ?_
  · exact (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun q y ↦ Ĝ (q, y)) hĜd _).trans
      (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun t' s' ↦ Ĝ ((t', s'), x))
        (MDifferentiableAt.curry_left (f := fun q y ↦ Ĝ (q, y)) hĜd) _)
  · exact (congrArg (mfderiv _ I Ĝ ((t, s), x)) (mfderiv_prodMk_right_apply w)).trans
      (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun q y ↦ Ĝ (q, y)) hĜd _)

end Family

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']

/-- **Primitives of the velocity forms of a family of symplectic isotopies.** Let `σ` be a closed
two-form on `M`, `P` a nonempty open convex subset of a Banach space, and `Ĝ : [0, 1]² × P → M`
smooth. Let `k_t`, for each `t`, be a symplectic isotopy (for some two-form `τ_t` on `P`) with
`k_t (s, x) = Ĝ ((t, s), x)`. Then there is a smooth `h` on `[0, 1]² × P` such that:
* for all `t` and `s`, `h ((t, s), ·)` is a primitive of the slice at time `s` of the velocity
  form of `k_t`;
* `h ((t, ·), ·) = 0` for every `t` such that `Ĝ ((t, s), x) = Ĝ ((t, 0), x)` for all `s` and
  `x`. -/
theorem exists_contMDiff_velocityForm_eq_mextDeriv {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    {P : TopologicalSpace.Opens E'} (hPc : Convex ℝ (P : Set E')) (hPne : (P : Set E').Nonempty)
    {Ĝ : (unitInterval × unitInterval) × P → M}
    (hĜ : ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod 𝓘(ℝ, E')) I ∞ Ĝ)
    {f₀ f₁ : unitInterval → C^∞⟮𝓘(ℝ, E'), P; I, M⟯} (k : ∀ t, SmoothIsotopy (f₀ t) (f₁ t))
    (hk : ∀ t p, k t p = Ĝ ((t, p.1), p.2)) {τ : unitInterval → SmoothTwoForm 𝓘(ℝ, E') P}
    (hks : ∀ t, (k t).IsSymplectic (τ t) σ) :
    ∃ h : (unitInterval × unitInterval) × P → ℝ,
      ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod 𝓘(ℝ, E')) 𝓘(ℝ) ∞ h ∧
      (∀ t s, (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id)
          ((k t).velocityForm σ)).val =
        mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E') fun x ↦ h ((t, s), x))) ∧
      ∀ t, (∀ s x, Ĝ ((t, s), x) = Ĝ ((t, 0), x)) → ∀ s x, h ((t, s), x) = 0 := by
  have hcl (q : unitInterval × unitInterval) :
      SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
        ((k q.1).velocityForm σ) ∈ closedForms 𝓘(ℝ, E') P 1 :=
    (mem_closedForms _ _).2 ((hks q.1).mextDeriv_mpullback_prodMk_velocityForm hσ q.2)
  obtain ⟨h, hh, hdh⟩ := (Convex.isSmoothlyContractible hPc hPne
    ).exists_contMDiff_mextDeriv_eq_of_forall_mem_closedForms
    (isSmoothFamily_velocityForm σ hĜ k hk) hcl
  -- Normalize the primitives to vanish at a point `x₀` of `P`.
  obtain ⟨x₀, hx₀⟩ := hPne
  have hd (t s : unitInterval) :
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E')
        fun x ↦ h ((t, s), x) - h ((t, s), ⟨x₀, hx₀⟩)) =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E') fun x ↦ h ((t, s), x)) :=
    funext fun x ↦ mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (Filter.Eventually.of_forall fun y ↦ sub_eq_add_neg _ _)
  refine ⟨fun q ↦ h q - h (q.1, ⟨x₀, hx₀⟩),
    hh.sub (hh.comp (contMDiff_fst.prodMk contMDiff_const)),
    fun t s ↦ ((hd t s).trans (hdh (t, s))).symm, fun t ht s x ↦ sub_eq_zero.2 ?_⟩
  -- Where `Ĝ ((t, ·), ·)` does not move, the velocity forms vanish, so `h ((t, s), ·)` is
  -- constant.
  have hzero : mextDeriv (RoughForm.ofFunction 𝓘(ℝ, E') fun x ↦ h ((t, s), x)) = 0 := by
    rw [hdh (t, s)]
    refine funext fun y ↦ ContinuousAlternatingMap.ext_fin_one fun w ↦ ?_
    have hconst : (fun s₁ ↦ k t (s₁, y)) = fun _ ↦ k t (0, y) :=
      funext fun s₁ ↦ by rw [hk, hk, ht s₁ y]
    refine (SmoothIsotopy.mpullback_prodMk_velocityForm σ (k t) s y w).trans ?_
    rw [hconst, mfderiv_const, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl
  have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.1 hPc.isPreconnected
  exact ((mextDeriv_ofFunction_eq_zero_iff
    ((hh.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp))).1 hzero
    ).apply_eq_of_preconnectedSpace _ _

end SymplecticGeometry

end
