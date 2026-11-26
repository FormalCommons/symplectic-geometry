/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Extension of isotopies by symplectic and Hamiltonian flows

Let `k : [0, 1] × P → M` be a smooth isotopy of embeddings (`TauCeti.SmoothIsotopy`) between
manifolds of the same dimension, so that its slices `k_t` are open embeddings, and let `σ` be a
symplectic form on `M`. The velocity form `α_t` of `k` (`TauCeti.SmoothIsotopy.velocityForm`)
sends `v` at `x` to `σ (∂ₜ k (t, x), dk_t v)`. Suppose that `α_t = k_t^* β_t + dh_t`, for a smooth
family of closed one-forms `β_t` on `M` vanishing off a compact set, and for functions `h_t` on
`P` that are jointly smooth in `(t, x)`. Then on a compact set `K ⊆ P` the isotopy is the
restriction of a diffeotopy `φ_t` of `M` preserving `σ`, at every time: `φ_t (k_0 x) = k_t x` for
`x ∈ K`. When `β = 0`, the diffeotopy is a compactly supported Hamiltonian diffeotopy. The isotopy
extension theorems of McDuff–Salamon, §3.3 (Theorems 3.3.1 and 3.3.2), end with this step: a
family of symplectic embeddings with suitable velocity forms is moved by an ambient flow.

The construction (`TauCeti.SmoothIsotopy.exists_diffeotopy_interior_velocity_eq_forall_apply_eq`):

1. A function `G` on `M × [0, 1]` vanishing off a compact set with `G_t ∘ k_t = h_t` near `K`
   (`TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`, in
   `SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension`).
2. The diffeotopy `φ_t` whose velocity `X_t` satisfies `ι_{X_t} σ = β_t + dG_t`, which preserves
   `σ` and fixes every point off a compact set
   (`TauCeti.Diffeotopy.exists_interior_velocity_eq_add_mextDeriv`, in
   `SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport`).
3. At `k_t x`, `x ∈ K`, the vectors `X_t` and `∂ₜ k` have the same contraction with `σ` on the
   image of `dk_t`: pulled back by `k_t`, both are `k_t^* β_t + dh_t`. So they agree
   (`TauCeti.SmoothIsotopy.eq_mfderiv_of_forall_eq_mpullback_prodMk_velocityForm`), and
   uniqueness of solutions on `[0, 1]` gives `φ_t (k_0 x) = k_t x`
   (`TauCeti.Diffeotopy.apply_eq_of_mfderiv_eq_velocity`).

When `β = 0`, `X_t` is the Hamiltonian vector field of `G_t`, so `G` generates `φ_t`
(`TauCeti.Diffeotopy.IsGeneratedBy`), and `φ_t` is a compactly supported Hamiltonian diffeotopy
(`TauCeti.Diffeotopy.IsCompactlySupportedHamiltonian`).

## Main results

* `TauCeti.SmoothIsotopy.exists_diffeotopy_interior_velocity_eq_forall_apply_eq`: the extension
  for velocity forms `k_t^* β_t + dh_t`, with `β_t` closed and vanishing off a compact set.
* `TauCeti.SmoothIsotopy.exists_hasHamiltonian_forall_apply_eq`: if the velocity forms are exact,
  `α_t = dh_t`, the isotopy is on `K` the restriction of a compactly supported Hamiltonian
  diffeotopy.
* `TauCeti.SmoothIsotopy.exists_diffeotopy_mem_diffeomorphStabilizer_forall_apply_eq`: on a compact
  `M`, if `α_t = k_t^* β_t + dh_t` with every `β_t` closed, the isotopy is on `K` the restriction
  of a diffeotopy preserving `σ`.

## Implementation notes

The isotopy `k` need not be symplectic: the hypothesis on its velocity forms is all the proofs use.
For a symplectic isotopy and a closed `σ` the velocity forms are closed
(`TauCeti.SmoothIsotopy.IsSymplectic.mextDeriv_mpullback_prodMk_velocityForm`), which is how the
hypothesis arises. The form on `M` is called `σ` and not `ω`, which is a token once the scope
`ContDiff` is open.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3,
  proof of Theorem 3.3.2.
-/

public noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothIsotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] {P : Type*}
  [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]
  {f₀ f₁ : C^∞⟮J, P; I, M⟯}

variable {σ : SmoothTwoForm I M}

omit [T2Space M] [SigmaCompactSpace M] in
/-- Along an isotopy `k` of embeddings between manifolds of the same dimension whose velocity form
at time `t` is `k_t^* β_t + dh_t`, a field `Y` with `ι_Y σ = β_t + dG_t`, where `σ` is
nondegenerate and `G_t ∘ k_t = h_t` near `x`, is the velocity of `k` at `k_t x`. -/
private theorem apply_eq_mfderiv_of_interior_eq (hσ : σ.IsNondegenerate) (k : SmoothIsotopy f₀ f₁)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E)
    {β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1} {h : unitInterval × P → ℝ}
    {t : unitInterval}
    (hα : (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (k.velocityForm σ)).val =
      mpullback J I (fun x ↦ k (t, x))
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
        mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x)))
    {G : M × unitInterval → ℝ} (hG : ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ G) {x : P}
    (hGk : (fun y ↦ G (k (t, y), t)) =ᶠ[𝓝 x] fun y ↦ h (t, y)) {Y : (y : M) → TangentSpace I y}
    (hY : RoughForm.interior Y σ.val =
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
        mextDeriv (RoughForm.ofFunction I fun y ↦ G (y, t))) :
    Y (k (t, x)) = mfderiv (𝓡∂ 1) I (fun s ↦ k (s, x)) t 1 := by
  refine k.eq_mfderiv_of_forall_eq_mpullback_prodMk_velocityForm hσ hd
    -- `v` is taken in `TangentSpace J x`, the form in which `hcomp` below applies `mfderiv`.
    fun (v : TangentSpace J x) ↦ ?_
  have hkt : MDifferentiableAt J I (fun y ↦ k (t, y)) x :=
    (k.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
  have hGt : MDifferentiableAt I 𝓘(ℝ) (fun z ↦ G (z, t)) (k (t, x)) :=
    (hG.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  have hcomp : mfderiv J 𝓘(ℝ) (fun y ↦ G (k (t, y), t)) x v =
      mfderiv I 𝓘(ℝ) (fun z ↦ G (z, t)) (k (t, x)) (mfderiv J I (fun y ↦ k (t, y)) x v) :=
    mfderiv_comp_apply x hGt hkt v
  have hmf : mfderiv J 𝓘(ℝ) (fun y ↦ G (k (t, y), t)) x v =
      mfderiv J 𝓘(ℝ) (fun y ↦ h (t, y)) x v := by
    rw [hGk.mfderiv_eq]
    -- The cast between the tangent spaces `TangentSpace 𝓘(ℝ) _` is the identity of `ℝ`.
    rfl
  rw [← RoughForm.interior_apply, hY, hα, Pi.add_apply, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.add_apply, mpullback_apply_one,
    mextDeriv_ofFunction_apply, mextDeriv_ofFunction_apply, ← hcomp, hmf]

/-- **Extension by a symplectic flow.** Let `σ` be a symplectic form on `M`, `k` a smooth isotopy
of embeddings of `P` into `M` of the same dimension, and `K ⊆ P` compact. Suppose that the
velocity forms of `k` are `α_t = k_t^* β_t + dh_t`, for a smooth form `β` on `[0, 1] × M` whose
slices `β_t` are closed and vanish off a compact set `L`, and a smooth function `h` on `[0, 1] × P`.
Then there are a diffeotopy `φ_t` of `M`, a smooth function `G` on `M × [0, 1]` and a compact set
`L'` such that `G` vanishes off `L'`, the velocity `X_t` of `φ_t` satisfies
`ι_{X_t} σ = β_t + dG_t`, every `φ_t` preserves `σ` and fixes every point outside `L'`, and
`φ_t (k_0 x) = k_t x` for every `t` and every `x ∈ K`. -/
theorem exists_diffeotopy_interior_velocity_eq_forall_apply_eq (hσ : σ.IsSymplectic)
    (k : SmoothIsotopy f₀ f₁) (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {K : Set P}
    (hK : IsCompact K) {β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1}
    (hβ : ∀ t, mextDeriv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val = 0)
    {L : Set M} (hL : IsCompact L)
    (hβL : ∀ t, ∀ y ∉ L,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val y = 0)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h)
    (hα : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (k.velocityForm σ)).val =
      mpullback J I (fun x ↦ k (t, x))
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
        mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x))) :
    ∃ (Φ : Diffeotopy I ∞ M) (G : M × unitInterval → ℝ) (L' : Set M), IsCompact L' ∧
      ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ G ∧ (∀ p, p.1 ∉ L' → G p = 0) ∧
      (∀ t, RoughForm.interior (Φ.velocity t) σ.val =
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
          mextDeriv (RoughForm.ofFunction I fun y ↦ G (y, t))) ∧
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      (∀ t, ∀ y ∉ L', Φ (t, y) = y) ∧ ∀ t, ∀ x ∈ K, Φ (t, f₀ x) = k (t, x) := by
  obtain ⟨G, C, hG, hC, hGC, hGk⟩ := k.exists_contMDiff_comp_eventuallyEq hd hK hh
  obtain ⟨Φ, hint, hpres, hfix⟩ :=
    Diffeotopy.exists_interior_velocity_eq_add_mextDeriv hσ hβ hL hβL hG hC hGC
  refine ⟨Φ, G, L ∪ C, hL.union hC, hG, fun p hp ↦ hGC p fun h ↦ hp (Or.inr h), hint, hpres,
    hfix, fun t x hx ↦ ?_⟩
  -- Along `k`, the velocity of `Φ` is that of `k` on `K`, and uniqueness of solutions applies.
  rw [← k.apply_zero x]
  exact Φ.apply_eq_of_mfderiv_eq_velocity (γ := fun s ↦ k (s, x))
    ((k.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))
    (fun s ↦ (apply_eq_mfderiv_of_interior_eq hσ.isNondegenerate k hd (hα s) hG (hGk s x hx)
      (hint s)).symm) t

/-- **Extension by a Hamiltonian flow.** Let `σ` be a symplectic form on `M`, `k` a smooth
isotopy of embeddings of `P` into `M` of the same dimension, and `K ⊆ P` compact. If the velocity
forms of `k` are exact, `α_t = dh_t` for a smooth function `h` on `[0, 1] × P`, then `k` is on `K`
the restriction of a compactly supported Hamiltonian diffeotopy `φ_t` of `M`: there are a compact
set `L` and a Hamiltonian `F` of `φ_t`, read along the motion, with `F (x, t) = 0` and
`φ_t x = x` for `x ∉ L`, and `φ_t (k_0 x) = k_t x` for every `t` and every `x ∈ K`. -/
theorem exists_hasHamiltonian_forall_apply_eq (hσ : σ.IsSymplectic) (k : SmoothIsotopy f₀ f₁)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {K : Set P} (hK : IsCompact K)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h)
    (hα : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (k.velocityForm σ)).val = mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x))) :
    ∃ (Φ : Diffeotopy I ∞ M) (F : M × unitInterval → ℝ) (L : Set M), IsCompact L ∧
      Φ.IsCompactlySupportedHamiltonian σ ∧ Φ.HasHamiltonian σ F ∧ (∀ p, p.1 ∉ L → F p = 0) ∧
      (∀ t, ∀ y ∉ L, Φ (t, y) = y) ∧ ∀ t, ∀ x ∈ K, Φ (t, f₀ x) = k (t, x) := by
  have h0 (t : unitInterval) : SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) (0 : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1)
      = 0 := map_zero _
  obtain ⟨Φ, G, L, hL, hG, hGL, hint, hpres, hfix, happly⟩ :=
    k.exists_diffeotopy_interior_velocity_eq_forall_apply_eq hσ hd hK
      (β := 0) (fun t ↦ by rw [h0, ZeroMemClass.coe_zero, mextDeriv_zero]) isCompact_empty
      (fun t y _ ↦ by rw [h0, ZeroMemClass.coe_zero, Pi.zero_apply]) hh
      (fun t ↦ by rw [hα t, h0, ZeroMemClass.coe_zero, mpullback_zero, zero_add])
  have hgen : Φ.IsGeneratedBy σ G := Diffeotopy.isGeneratedBy_iff.2 ⟨hG, fun t ↦
    SmoothTwoForm.isHamiltonianVectorField_iff_interior_eq.2 (by
      rw [hint t, h0, ZeroMemClass.coe_zero, zero_add])⟩
  refine ⟨Φ, fun p ↦ G (Φ.cylinderMap p, p.2), L, hL,
    Diffeotopy.isCompactlySupportedHamiltonian_iff_isGeneratedBy.2 ⟨hpres, G, hgen, L, hL, hGL⟩,
    Diffeotopy.hasHamiltonian_comp_iff.2 hgen, fun p hp ↦ hGL _ ?_, hfix, happly⟩
  rwa [Diffeotopy.cylinderMap_apply, hfix _ _ hp]

omit [SigmaCompactSpace M] in
/-- **Extension by a symplectic flow on a compact manifold.** Let `σ` be a symplectic form on a
compact manifold `M`, `k` a smooth isotopy of embeddings of `P` into `M` of the same dimension,
and `K ⊆ P` compact. If the velocity forms of `k` are `α_t = k_t^* β_t + dh_t`, for a smooth form
`β` on `[0, 1] × M` whose slices `β_t` are closed and a smooth function `h` on `[0, 1] × P`, then
`k` is on `K` the restriction of a diffeotopy `φ_t` of `M` whose slices preserve `σ`:
`φ_t (k_0 x) = k_t x` for every `t` and every `x ∈ K`. -/
theorem exists_diffeotopy_mem_diffeomorphStabilizer_forall_apply_eq [CompactSpace M]
    (hσ : σ.IsSymplectic) (k : SmoothIsotopy f₀ f₁)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {K : Set P} (hK : IsCompact K)
    {β : SmoothForm ((𝓡∂ 1).prod I) (unitInterval × M) ℝ 1}
    (hβ : ∀ t, mextDeriv
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val = 0)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h)
    (hα : ∀ t, (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (k.velocityForm σ)).val =
      mpullback J I (fun x ↦ k (t, x))
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
        mextDeriv (RoughForm.ofFunction J fun x ↦ h (t, x))) :
    ∃ Φ : Diffeotopy I ∞ M, (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      ∀ t, ∀ x ∈ K, Φ (t, f₀ x) = k (t, x) := by
  obtain ⟨Φ, -, -, -, -, -, -, hpres, -, happly⟩ :=
    k.exists_diffeotopy_interior_velocity_eq_forall_apply_eq hσ hd hK hβ isCompact_univ
      (fun _ _ hy ↦ (hy (mem_univ _)).elim) hh hα
  exact ⟨Φ, hpres, happly⟩

end TauCeti.SmoothIsotopy

end
