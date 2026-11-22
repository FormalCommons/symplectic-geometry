/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import SymplecticGeometry.Geometry.Symplectic.Flux.CompactSupport
public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
import Mathlib.Geometry.Manifold.Algebra.Structures
import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension
import SymplecticGeometry.Geometry.Manifold.Flow.TimeDependent
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.SymplecticIsotopy
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Symplectic.Manifold.Family

/-!
# Extension of isotopies by symplectic and Hamiltonian flows

Let `k : [0, 1] × P → M` be a smooth isotopy of embeddings (`TauCeti.SmoothIsotopy`) between
manifolds of the same dimension, so that its slices `k_t` are open embeddings, and let `σ` be a
symplectic form on `M`. The velocity form `α_t` of `k` (`TauCeti.SmoothIsotopy.velocityForm`)
sends `v` at `x` to `σ (∂ₜ k (t, x), dk_t v)`. Suppose that `α_t = k_t^* β_t + dh_t`, for a smooth
family of closed one-forms `β_t` on `M` vanishing off a compact set and a smooth family of
functions `h_t` on `P`. Then on a compact set `K ⊆ P` the isotopy is the restriction of a
diffeotopy `φ_t` of `M` preserving `σ`, at every time: `φ_t (k_0 x) = k_t x` for `x ∈ K`. When
`β = 0`, the diffeotopy is a compactly supported Hamiltonian diffeotopy. The isotopy extension
theorems of McDuff–Salamon, §3.3 (Theorems 3.3.1 and 3.3.2), end with this step: a family of
symplectic embeddings with suitable velocity forms is moved by an ambient flow.

The construction (`TauCeti.SmoothIsotopy.exists_diffeotopy_interior_velocity_eq_forall_apply_eq`):

1. Isotopy extension at every time (`TauCeti.SmoothIsotopy.exists_diffeotopy_forall_apply_eq`)
   gives a diffeotopy `Ψ` of `M` with `Ψ_t ∘ k_0 = k_t` on a compact neighbourhood `K'` of `K`.
   With a cutoff `χ` on `M` that is `1` near `k_0 (K)` and supported in `k_0 (K')`, the function
   `G_t = (χ · h_t ∘ k_0⁻¹) ∘ Ψ_t⁻¹` is smooth, vanishes off a compact set, and satisfies
   `G_t ∘ k_t = h_t` near `K` (`TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`).
   Here `k_0⁻¹` is smooth on the image of `k_0` because `k_0` is a local diffeomorphism.
2. The forms `β_t + dG_t` extend past both ends of `[0, 1]` by Seeley's operator
   (`TauCeti.SmoothForm.timeExtend`), and `X_t = (σ♭)⁻¹ (β_t + dG_t)` is a smooth time-dependent
   field (`TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`). It vanishes off a
   compact set, so its flow is a diffeotopy `φ_t` (`TauCeti.timeDependentFlowDiffeotopy`).
3. At `k_t x`, `x ∈ K`, the vectors `X_t` and `∂ₜ k` have the same contraction with `σ` on the
   image of `dk_t`: pulled back by `k_t`, both are `k_t^* β_t + dh_t`. Since `dk_t` is onto, they
   agree, and uniqueness of solutions on `[0, 1]`
   (`TauCeti.timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq`) gives
   `φ_t (k_0 x) = k_t x`.
4. For `t ∈ [0, 1]`, the velocity `X_t` of `φ_t` has `d (ι_{X_t} σ) = d (β_t + dG_t) = 0`, so
   `φ_t` preserves `σ` (`TauCeti.Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff`).
   Past the ends of `[0, 1]` the extended forms need not be closed, and they are not needed there.

When `β = 0`, `X_t` is the Hamiltonian vector field of `G_t`, so `G` generates `φ_t`
(`TauCeti.Diffeotopy.IsGeneratedBy`), and `φ_t` is a compactly supported Hamiltonian diffeotopy
(`TauCeti.Diffeotopy.IsCompactlySupportedHamiltonian`).

The construction of the flow from a time extension follows the proof of
`TauCeti.Diffeotopy.exists_isCompactlySupportedHamiltonian`.

## Main results

* `TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`: a smooth family of functions on `P`
  is, near a compact set, the composite with `k_t` of a smooth family of functions on `M` vanishing
  off a compact set.
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
* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
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

/-- **Transport of functions along an isotopy.** Let `k` be a smooth isotopy of embeddings of `P`
into a manifold `M` of the same dimension, `K ⊆ P` compact, and `h` a smooth function on
`[0, 1] × P`. There is a smooth function `G` on `M × [0, 1]` that vanishes off a compact set and
satisfies `G (k (t, y), t) = h (t, y)` for every `t` and every `y` near `K`. -/
theorem exists_contMDiff_comp_eventuallyEq (k : SmoothIsotopy f₀ f₁)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {K : Set P} (hK : IsCompact K)
    {h : unitInterval × P → ℝ} (hh : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ h) :
    ∃ (G : M × unitInterval → ℝ) (C : Set M), ContMDiff (I.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ G ∧
      IsCompact C ∧ (∀ p, p.1 ∉ C → G p = 0) ∧
      ∀ t, ∀ x ∈ K, (fun y ↦ G (k (t, y), t)) =ᶠ[𝓝 x] fun y ↦ h (t, y) := by
  rcases isEmpty_or_nonempty P with hP | hP
  · exact ⟨0, ∅, contMDiff_const, isCompact_empty, fun _ _ ↦ rfl, fun _ x ↦ isEmptyElim x⟩
  have := Manifold.locallyCompact_of_finiteDimensional J (M := P)
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨Ψ, -, -, -, hΨ⟩ := k.exists_diffeotopy_forall_apply_eq hK'
  have hf₀ : IsLocalDiffeomorph J I ∞ f₀ :=
    k.isSmoothEmbedding_left.isImmersion.isLocalDiffeomorph hd (by simp)
  have hinj : Function.Injective f₀ := k.isSmoothEmbedding_left.isEmbedding.injective
  obtain ⟨χ, hχ, hχ1, hχc, hχW, -⟩ :=
    (hK.image f₀.contMDiff.continuous).exists_contMDiff_one_nhds_tsupport_subset
    I (hf₀.isOpenMap _ isOpen_interior) (image_mono hKK')
  set g : unitInterval × M → ℝ := fun q ↦ χ q.2 * h (q.1, Function.invFun f₀ q.2)
  have hg : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) ∞ g := by
    rintro ⟨t, y⟩
    by_cases hy : y ∈ tsupport χ
    · obtain ⟨p, -, rfl⟩ := hχW hy
      have hp := hf₀ p
      have hinv : Function.invFun f₀ =ᶠ[𝓝 (f₀ p)] hp.localInverse := by
        filter_upwards [hp.localInverse_eventuallyEq_right] with z hz
        have hz' : f₀ (hp.localInverse z) = z := hz
        calc Function.invFun f₀ z = Function.invFun f₀ (f₀ (hp.localInverse z)) := by rw [hz']
          _ = hp.localInverse z := Function.leftInverse_invFun hinj _
      refine ContMDiffAt.congr_of_eventuallyEq (f := fun q : unitInterval × M ↦
        χ q.2 * h (q.1, hp.localInverse q.2)) ?_ ((continuous_snd.tendsto (t, f₀ p)).eventually
        hinv |>.mono fun q hq ↦ by simp only [g, hq])
      exact (hχ.contMDiffAt.comp _ contMDiffAt_snd).mul (hh.contMDiffAt.comp _
        (contMDiffAt_fst.prodMk
          (ContMDiffAt.comp (t, f₀ p) hp.contMDiffAt_localInverse contMDiffAt_snd)))
    · refine contMDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto (t, y)).eventually
        (notMem_tsupport_iff_eventuallyEq.1 hy)] with q hq
      simp only [g, show χ q.2 = 0 from hq, zero_mul]
  refine ⟨fun p ↦ g (p.2, Ψ.symm (p.2, p.1)), Ψ.cylinderMap '' (tsupport χ ×ˢ univ),
    hg.comp (contMDiff_snd.prodMk (Ψ.symm.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst))),
    (hχc.isCompact.prod isCompact_univ).image Ψ.contMDiff_cylinderMap.continuous,
    fun p hp ↦ ?_, fun t x hx ↦ ?_⟩
  · have : Ψ.symm (p.2, p.1) ∉ tsupport χ := fun h ↦ hp ⟨(_, p.2), ⟨h, mem_univ _⟩, by
      rw [Diffeotopy.cylinderMap_apply, Diffeotopy.apply_mk_symm_apply]⟩
    simp only [g, image_eq_zero_of_notMem_tsupport this, zero_mul]
  · filter_upwards [isOpen_interior.mem_nhds (hKK' hx),
      (f₀.contMDiff.continuous.tendsto x).eventually
        (hχ1.filter_mono (nhds_le_nhdsSet (mem_image_of_mem f₀ hx)))]
      with y hy hy1
    simp only [g, ← hΨ t y (interior_subset hy), Diffeotopy.symm_apply_mk_apply, hy1, one_mul,
      Function.leftInverse_invFun hinj y]

variable {σ : SmoothTwoForm I M}

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [FiniteDimensional ℝ E'] in
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
  have hloc : IsLocalDiffeomorph J I ∞ (fun y ↦ k (t, y)) :=
    (k.isSmoothEmbedding t).isImmersion.isLocalDiffeomorph hd (by simp)
  have hsurj : Function.Surjective (mfderiv J I (fun y ↦ k (t, y)) x) :=
    ((hloc x).isInvertible_mfderiv (by simp)).surjective
  have hkt : MDifferentiableAt J I (fun y ↦ k (t, y)) x :=
    (k.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
  have hGt : MDifferentiableAt I 𝓘(ℝ) (fun z ↦ G (z, t)) (k (t, x)) :=
    (hG.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
  -- Both vectors contract with `σ` to the same covector on the image of `dk_t`, which is onto.
  refine (hσ.isInvertible_flat _).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := hsurj w
  rw [SmoothTwoForm.flat_apply, SmoothTwoForm.flat_apply, SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_apply]
  refine Eq.trans ?_ (mpullback_prodMk_velocityForm σ k t x v)
  have hcomp : mfderiv J 𝓘(ℝ) (fun y ↦ G (k (t, y), t)) x v =
      mfderiv I 𝓘(ℝ) (fun z ↦ G (z, t)) (k (t, x)) (mfderiv J I (fun y ↦ k (t, y)) x v) :=
    mfderiv_comp_apply x hGt hkt v
  have hmf : mfderiv J 𝓘(ℝ) (fun y ↦ G (k (t, y), t)) x v =
      mfderiv J 𝓘(ℝ) (fun y ↦ h (t, y)) x v := by
    rw [hGk.mfderiv_eq]
    -- The cast between the tangent spaces `TangentSpace 𝓘(ℝ) _` is the identity of `ℝ`.
    rfl
  rw [← RoughForm.interior_apply, hY, hα, Pi.add_apply, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.add_apply, mpullback_apply,
    mextDeriv_ofFunction_apply, mextDeriv_ofFunction_apply, ← hcomp, hmf]
  congr 2
  funext i
  fin_cases i
  rfl

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
  let Gc : C^∞⟮(𝓡∂ 1).prod I, unitInterval × M; 𝓘(ℝ, ℝ), ℝ⟯ :=
    ⟨fun q ↦ G (q.2, q.1), hG.comp (contMDiff_snd.prodMk contMDiff_fst)⟩
  set Ω := β + mextDerivₗ ((𝓡∂ 1).prod I) 0 (SmoothForm.ofFunction Gc)
  -- The slices of `Ω` are `β_t + dG_t`, and they are closed.
  have hΩ (t : unitInterval) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω =
        SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β +
          mextDerivₗ I 0 (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
            (SmoothForm.ofFunction Gc)) := by
    rw [map_add, SmoothForm.mextDerivₗ_mpullback]
  have hΩval (t : unitInterval) :
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω).val =
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
          mextDeriv (RoughForm.ofFunction I fun y ↦ G (y, t)) := by
    rw [hΩ, Submodule.coe_add, mextDerivₗ_apply,
      SmoothForm.coe_mpullback _ _ (SmoothForm.ofFunction Gc), SmoothForm.coe_ofFunction,
      mpullback_ofFunction, ContMDiffMap.coeFn_mk, Function.comp_def]
  have hΩd (t : unitInterval) :
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω).val
        = 0 := by
    rw [← mextDerivₗ_apply, hΩ, map_add, Submodule.coe_add, mextDerivₗ_apply, hβ t,
      ← LinearMap.comp_apply, mextDerivₗ_comp_mextDerivₗ]
    simp
  -- The time extension `α` of `Ω`, and the constant family `σ'` of `σ` on `ℝ × M`.
  set α := SmoothForm.timeExtend Ω
  set σ' : SmoothTwoForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) :=
    SmoothForm.mpullback Prod.snd contMDiff_snd σ
  have hσ' (u : ℝ) : SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) σ' =
      σ := by
    rw [SmoothForm.mpullback_mpullback]
    exact LinearMap.congr_fun SmoothForm.mpullback_id σ
  have hnd (u : ℝ) : SmoothTwoForm.IsNondegenerate
      (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) σ') :=
    (hσ' u).symm ▸ hσ.isNondegenerate
  -- The field `X_u = (σ♭)⁻¹ α_u`.
  set X : ℝ → (y : M) → TangentSpace I y := fun u ↦ hσ.isNondegenerate.interiorEquiv.symm
    (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α) with hXdef
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) :=
    (SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk σ' hnd α).congr fun p ↦ by
      simp only [hXdef, SmoothTwoForm.IsNondegenerate.interiorEquiv_symm_apply, hσ']
  -- On `[0, 1]`, `ι_{X_t} σ = β_t + dG_t`.
  have hint (t : unitInterval) : RoughForm.interior (X t) σ.val =
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).val +
        mextDeriv (RoughForm.ofFunction I fun y ↦ G (y, t)) := by
    rw [hXdef, SmoothTwoForm.IsNondegenerate.interior_interiorEquiv_symm,
      SmoothForm.mpullback_prodMk_timeExtend, hΩval]
  -- `X` vanishes off `L ∪ C`, so its suspension is complete.
  have hXL (u : ℝ) (y : M) (hy : y ∉ L ∪ C) : X u y = 0 := by
    rw [hXdef, SmoothTwoForm.IsNondegenerate.interiorEquiv_symm_apply_eq_zero_iff,
      SmoothForm.mpullback_prodMk_timeExtend_eq_timeExtendSlice, SmoothForm.coe_timeExtendSlice]
    refine SymplecticGeometry.timeExtend_eq_zero (F := E [⋀^Fin 1]→L[ℝ] ℝ) (fun s ↦ ?_) u
    rw [mem_union, not_or] at hy
    have hGy : (fun z ↦ G (z, s)) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hy.2] with z hz
      exact hGC (z, s) hz
    rw [hΩval, Pi.add_apply, hβL s y hy.1, zero_add]
    exact mextDeriv_ofFunction_apply_eq_zero_iff.2 (by
      rw [hGy.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero])
  have hc := isCompleteVectorField_timeDependentSuspensionField (hX.of_le (by simp)) (hL.union hC)
    hXL
  set Φ := timeDependentFlowDiffeotopy le_top hX hc
  have hvel (t : unitInterval) : ⇑(Φ.velocity t) = X t :=
    Diffeotopy.velocity_timeDependentFlowDiffeotopy hX hc t
  -- Along `k`, the field `X` is the velocity of `k` at the points of `K`.
  have hcurve (t : unitInterval) (x : P) (hx : x ∈ K) :
      X t (k (t, x)) = mfderiv (𝓡∂ 1) I (fun s ↦ k (s, x)) t 1 :=
    apply_eq_mfderiv_of_interior_eq hσ.isNondegenerate k hd (hα t) hG (hGk t x hx) (hint t)
  -- The slices of `Φ` preserve `σ`: `d (ι_{X_u} σ) = d (β_u + dG_u) = 0` for `u ∈ [0, 1]`.
  have hpres : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ :=
    (Diffeotopy.forall_timeSlice_mem_diffeomorphStabilizer_iff Φ hσ.isClosed).2 fun t ↦
      SmoothTwoForm.mem_symplecticVectorFields_iff.2 (by
        rw [hvel, hXdef, SmoothTwoForm.IsNondegenerate.interior_interiorEquiv_symm,
          SmoothForm.mpullback_prodMk_timeExtend]
        exact hΩd t)
  -- Uniqueness of solutions gives `Φ (t, f₀ x) = k (t, x)` on `K`.
  have happly (t : unitInterval) (x : P) (hx : x ∈ K) : Φ (t, f₀ x) = k (t, x) := by
    rw [← k.apply_zero x]
    exact timeDependentFlowDiffeotopy_apply_eq_of_mfderiv_eq hX hc
      (γ := fun s ↦ k (s, x))
      ((k.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp))
      (fun s ↦ (hcurve s x hx).symm) t
  exact ⟨Φ, G, L ∪ C, hL.union hC, hG, fun p hp ↦ hGC p fun h ↦ hp (Or.inr h),
    fun t ↦ by rw [hvel, hint], hpres, fun t y hy ↦
      timeDependentFlowDiffeotopy_apply_of_forall_eq_zero le_top hX hc (fun u ↦ hXL u y hy) t,
    happly⟩

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
