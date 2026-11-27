/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import Mathlib.Topology.LocallyConstant.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Topology.UnitInterval
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.LinearAlgebra.BilinearForm.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
import SymplecticGeometry.LinearAlgebra.BilinearForm.Pullback
import SymplecticGeometry.LinearAlgebra.Orientation.Prod

/-!
# Symplectic orientations: transported bases, continuous families and orthogonal splittings

If a symplectic form `ω` on `V` tames an almost complex structure `J`, and `e : V ≃ W` is a
linear equivalence, then every basis `(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport
`J' = e ∘ J ∘ e⁻¹` induces the image under `e` of the symplectic orientation of `ω`
(`TauCeti.SymplecticForm.Tames.orientation_reindex_transport`). This combines Tau Ceti's
`TauCeti.SymplecticForm.Tames.orientation_reindex`, applied to the transported form, with the
naturality `TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`.

The symplectic orientation is also unchanged along a continuous family of symplectic forms. If
`x ↦ ω x v w` is continuous at `x₀` for all `v, w`, an almost complex structure tamed by
`ω x₀` is tamed by `ω x` for `x` near `x₀` (`TauCeti.SymplecticForm.eventually_tames`), since
taming is an open condition (`TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos`).
Taking such a structure (`TauCeti.SymplecticForm.exists_tames`), and since forms taming a common
structure have the same orientation (`TauCeti.SymplecticForm.Tames.orientation_eq`), `ω x` has
the orientation of `ω x₀` near `x₀` (`TauCeti.SymplecticForm.eventually_orientation_eq`). Under
continuity everywhere, `x ↦ (ω x).orientation hk` is therefore locally constant
(`TauCeti.SymplecticForm.isLocallyConstant_orientation`), hence constant over a preconnected
parameter space (`TauCeti.SymplecticForm.orientation_eq_of_preconnectedSpace`). This adapts the
proof of Tau Ceti's private `eventually_mapOrientation_orientation_eq`
(`TauCeti/Geometry/Symplectic/Manifold/Orientation.lean`) from the tangent spaces of a manifold
to a family of forms on one vector space.

If `V = H ⊕ L` is a splitting into `ω`-orthogonal subspaces, then the symplectic orientation of
`ω` is the image under `H × L ≃ V` of the product of the symplectic orientations of the
restrictions of `ω` to `H` and to `L`
(`TauCeti.SymplecticForm.orientation_eq_map_prod_of_isCompl`). The splitting gives `L = H^ω`
and makes both summands symplectic, by `TauCeti.SymplecticForm.orthogonal_eq_of_isCompl`,
`TauCeti.SymplecticForm.isSymplectic_left_of_isCompl` and
`TauCeti.SymplecticForm.isSymplectic_right_of_isCompl` of the library's
`LinearAlgebra/Symplectic/Subspace.lean`; the proof then combines Tau Ceti's
`TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`,
`TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation` and
`TauCeti.SymplecticForm.orientation_prod`.

Adding a large multiple of a symplectic form `β` to an alternating form `τ` keeps the orientation
of `β` for as long as the sum stays nondegenerate: if `τ + c • β` is nondegenerate for every
`c ≥ c₁`, its symplectic orientation is that of `β` for every `c ≥ c₁`
(`TauCeti.SymplecticForm.orientation_eq_of_forall_ge_nondegenerate_add_smul`). Indeed the forms
`t • τ + (t * c + 1 - t) • β`, `t ∈ [0, 1]`, are nonzero multiples of such sums for `t > 0` and
equal `β` at `t = 0`, so the constancy along a connected family applies.

This computes the orientation of the forms `τ + c • β.comp L L` that the library's
`LinearAlgebra/BilinearForm/Pullback.lean` shows nondegenerate for large `c`, the linear algebra
behind symplectic forms on fibrations (McDuff–Salamon, Theorem 6.1.4). If `D : V ≃ U × W` has
first component `L`, and `τ` restricts along `{0} × W` to a symplectic form `σ`, then `D`
carries the orientation of `τ + c • β.comp L L` to the product of the orientations of `β` and
`σ` (`TauCeti.SymplecticForm.map_orientation_of_forall_ge_nondegenerate_add_smul_comp`). The
proof splits `V` into the `τ`-orthogonal `H` of `ker L` and `ker L`, for which the form is block
diagonal (`LinearMap.BilinForm.add_smul_comp_eq_zero_of_mem_orthogonal_of_mem_ker`). On `ker L`
the form is `τ`, which `D` carries to `σ`. On `H`, carried to `U` by `L`, it is `τ' + c • β`
for an alternating `τ'`, so it has the orientation of `β`
(`TauCeti.SymplecticForm.map_orientation_restrict_orthogonal_ker`). The two blocks are put
together by `TauCeti.SymplecticForm.orientation_eq_map_prod_of_isCompl` and the library's
`Orientation.map_map_prodEquivOfIsCompl_prod`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

open Module Topology

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {n k : ℕ}
  {b : Basis (Fin n × Fin 2) ℝ W}

/-- If `ω` tames `J` and `e : V ≃ W` is a linear equivalence, every basis
`(v₁, J' v₁, …, vₙ, J' vₙ)` of `W` adapted to the transport `J' = e ∘ J ∘ e⁻¹` induces the
image under `e` of the symplectic orientation of `ω`. -/
theorem Tames.orientation_reindex_transport (hJ : ω.Tames J) (e : V ≃ₗ[ℝ] W)
    (hk : finrank ℝ V = k) (hb : ∀ i, b (i, 1) = J.transport e (b (i, 0))) (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
      Orientation.map (Fin k) e (ω.orientation hk) := by
  rw [(hJ.transport e).orientation_reindex hb (e.finrank_eq.symm.trans hk) h,
    (isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk]

section Family

variable {X : Type*} [TopologicalSpace X] {ω : X → SymplecticForm V}

/-- If `ω x₀` tames `J` and the values `ω x v w` depend continuously on `x` at `x₀`, then `ω x`
tames `J` for all `x` near `x₀`. -/
theorem eventually_tames {x₀ : X} (hω : ∀ v w, ContinuousAt (fun x ↦ ω x v w) x₀)
    (hJ : (ω x₀).Tames J) : ∀ᶠ x in 𝓝 x₀, (ω x).Tames J := by
  -- Carry the forms and `J` to a normed space, where taming is an open condition.
  let e := (Module.finBasis ℝ V).equivFun
  let B : X → (Fin (finrank ℝ V) → ℝ) →L[ℝ] (Fin (finrank ℝ V) → ℝ) →L[ℝ] ℝ := fun x ↦
    ((ω x).toBilinForm.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap).toContinuousBilinearMap
  have hB (x u u') : B x u u' = ω x (e.symm u) (e.symm u') := by simp [B]
  let A := LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ J.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hA (u) : A u = e (J (e.symm u)) := by simp [A]
  have hc : ContinuousAt (fun x ↦ (B x, A)) x₀ := by
    refine ContinuousAt.prodMk
      (continuousAt_clm_apply.2 fun u ↦ continuousAt_clm_apply.2 fun u' ↦ ?_) continuousAt_const
    simpa only [hB] using hω _ _
  refine (hc.eventually_mem
    (TauCeti.isOpen_setOf_forall_bilinear_apply_endomorphism_pos.mem_nhds fun u hu ↦ ?_)).mono
    fun x hx v hv ↦ ?_
  · simpa [hB, hA] using hJ _ ((LinearEquiv.map_ne_zero_iff _).2 hu)
  · simpa [hB, hA] using hx (e v) ((LinearEquiv.map_ne_zero_iff _).2 hv)

/-- If the values `ω x v w` of a family of symplectic forms depend continuously on `x` at `x₀`,
then `ω x` has the symplectic orientation of `ω x₀` for all `x` near `x₀`. -/
theorem eventually_orientation_eq {x₀ : X} (hω : ∀ v w, ContinuousAt (fun x ↦ ω x v w) x₀)
    (hk : finrank ℝ V = k) : ∀ᶠ x in 𝓝 x₀, (ω x).orientation hk = (ω x₀).orientation hk := by
  obtain ⟨J, hJ⟩ := (ω x₀).exists_tames
  exact (eventually_tames hω hJ).mono fun x hx ↦ hx.orientation_eq hJ hk

/-- Along a family of symplectic forms `ω x` on `V` whose values `ω x v w` depend continuously on
`x`, the symplectic orientation is locally constant. -/
theorem isLocallyConstant_orientation (hω : ∀ v w, Continuous fun x ↦ ω x v w)
    (hk : finrank ℝ V = k) : IsLocallyConstant fun x ↦ (ω x).orientation hk :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun _ ↦
    eventually_orientation_eq (fun v w ↦ (hω v w).continuousAt) hk

/-- Along a family of symplectic forms over a preconnected parameter space, whose values
`ω x v w` depend continuously on `x`, the symplectic orientation is constant. -/
theorem orientation_eq_of_preconnectedSpace [PreconnectedSpace X]
    (hω : ∀ v w, Continuous fun x ↦ ω x v w) (hk : finrank ℝ V = k) (x y : X) :
    (ω x).orientation hk = (ω y).orientation hk :=
  (isLocallyConstant_orientation hω hk).apply_eq_of_preconnectedSpace x y

end Family

section Splitting

variable {H L : Submodule ℝ V}

/-- If `V = H ⊕ L` with `H` and `L` orthogonal for `ω`, the symplectic orientation of `ω` is the
image under `H × L ≃ V` of the product of the symplectic orientations of the restrictions of `ω`
to `H` and to `L`. -/
theorem orientation_eq_map_prod_of_isCompl (ω : SymplecticForm V) (hc : IsCompl H L)
    (hHL : ∀ h ∈ H, ∀ l ∈ L, ω h l = 0) {m n : ℕ} (hm : finrank ℝ H = m)
    (hn : finrank ℝ L = n) (hV : finrank ℝ V = m + n) :
    ω.orientation hV = Orientation.map (Fin (m + n)) (Submodule.prodEquivOfIsCompl H L hc)
      (((ω.restrict H (ω.isSymplectic_left_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hm).prod
        ((ω.restrict L (ω.isSymplectic_right_of_isCompl hc hHL).nondegenerate_restrict).orientation
          hn) hm hn) := by
  obtain rfl := ω.orthogonal_eq_of_isCompl hc hHL
  rw [← orientation_prod _ _ hm hn (by rw [finrank_prod, hm, hn]),
    (ω.isSymplectomorphism_prodEquivOfIsCompl hc).map_orientation]

end Splitting

section Pullback

variable {U : Type*} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]

/-- Let `β` be a symplectic form on `U` and `τ` an alternating form such that `τ + c • β` is
nondegenerate for every `c ≥ c₁`. Then for every `c ≥ c₁`, a symplectic form `ω` with underlying
form `τ + c • β` has the symplectic orientation of `β`. -/
theorem orientation_eq_of_forall_ge_nondegenerate_add_smul (β : SymplecticForm U)
    {τ : LinearMap.BilinForm ℝ U} (hτ : τ.IsAlt) {c₁ : ℝ}
    (h : ∀ c ≥ c₁, (τ + c • β.toBilinForm).Nondegenerate) {c : ℝ} (hc : c₁ ≤ c)
    (ω : SymplecticForm U) (hω : ω.toBilinForm = τ + c • β.toBilinForm)
    (hk : finrank ℝ U = k) : ω.orientation hk = β.orientation hk := by
  -- The forms `t • τ + (t * c + 1 - t) • β`, `t ∈ [0, 1]`, join `β` to `ω`; for `t ≠ 0` such a
  -- form is `t • (τ + (c + (1 - t) / t) • β)`, which is nondegenerate.
  let F : unitInterval → SymplecticForm U := fun t ↦
    { toBilinForm := (t : ℝ) • τ + ((t : ℝ) * c + 1 - t) • β.toBilinForm
      isAlt := (hτ.smul _).add (β.isAlt.smul _)
      nondegenerate := by
        rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht | ht
        · simpa [← ht] using β.nondegenerate
        · have h' := h (c + (1 - t) / t) (le_add_of_le_of_nonneg hc
            (div_nonneg (sub_nonneg.2 (unitInterval.le_one t)) ht.le))
          rw [← TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero ht.ne')] at h'
          convert h' using 1
          rw [smul_add, smul_smul]
          congr 2
          field_simp
          ring }
  have h0 : F 0 = β := toBilinForm_injective (by simp [F])
  have h1 : F 1 = ω := toBilinForm_injective (by simp [F, hω])
  rw [← h0, ← h1]
  exact orientation_eq_of_preconnectedSpace (fun v w ↦ by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, F]; fun_prop) hk 1 0

variable {τ : LinearMap.BilinForm ℝ V} {L : V →ₗ[ℝ] U}

/-- Let `τ` be an alternating form on `V`, nondegenerate on `ker L`, and `β` a symplectic form on
`U`, such that `τ + c • β.comp L L` is nondegenerate for every `c ≥ c₁`. Let `H` be the
`τ`-orthogonal of `ker L` and `e : H ≃ U` the restriction of `L`. Then for every `c ≥ c₁`, `e`
carries the symplectic orientation of the restriction of `τ + c • β.comp L L` to `H` to the
symplectic orientation of `β`. -/
theorem map_orientation_restrict_orthogonal_ker (hτ : τ.IsAlt) (β : SymplecticForm U)
    (hτL : (τ.restrict (LinearMap.ker L)).Nondegenerate)
    (e : τ.orthogonal (LinearMap.ker L) ≃ₗ[ℝ] U) (he : ∀ h, e h = L h) {c₁ : ℝ}
    (h : ∀ c ≥ c₁, (τ + c • β.toBilinForm.comp L L).Nondegenerate) {c : ℝ} (hc : c₁ ≤ c)
    (ω : SymplecticForm V) (hω : ω.toBilinForm = τ + c • β.toBilinForm.comp L L)
    (hH : (ω.toBilinForm.restrict (τ.orthogonal (LinearMap.ker L))).Nondegenerate)
    (hk : finrank ℝ (τ.orthogonal (LinearMap.ker L)) = k) :
    Orientation.map (Fin k) e ((ω.restrict _ hH).orientation hk) =
      β.orientation (e.finrank_eq.symm.trans hk) := by
  have hc' : IsCompl (τ.orthogonal (LinearMap.ker L)) (LinearMap.ker L) :=
    (τ.isCompl_orthogonal_of_restrict_nondegenerate hτ.isRefl hτL).symm
  -- Carried to `U` by `e`, the restriction of `τ + c' • β.comp L L` to `H` is `τ' + c' • β`.
  let f : U →ₗ[ℝ] V := (τ.orthogonal (LinearMap.ker L)).subtype ∘ₗ e.symm.toLinearMap
  have hT (ω' : SymplecticForm V) (c' : ℝ)
      (hω' : ω'.toBilinForm = τ + c' • β.toBilinForm.comp L L) (hH') :
      ((ω'.restrict _ hH').transport e).toBilinForm = τ.comp f f + c' • β.toBilinForm := by
    ext u u'
    rw [transport_toBilinForm, restrict_toBilinForm, hω']
    simp [f, ← he]
  have h' (c' : ℝ) (hc'' : c' ≥ c₁) : (τ.comp f f + c' • β.toBilinForm).Nondegenerate := by
    let ω' : SymplecticForm V :=
      ⟨τ + c' • β.toBilinForm.comp L L, hτ.add ((β.isAlt.comp L).smul c'), h c' hc''⟩
    have hHK : ∀ x ∈ τ.orthogonal (LinearMap.ker L), ∀ y ∈ LinearMap.ker L, ω' x y = 0 :=
      fun _ hx _ hy ↦
      LinearMap.BilinForm.add_smul_comp_eq_zero_of_mem_orthogonal_of_mem_ker hτ.isRefl _ c' hx hy
    rw [← hT ω' c' rfl (ω'.isSymplectic_left_of_isCompl hc' hHK).nondegenerate_restrict]
    exact (transport _ _).nondegenerate
  rw [(isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk]
  exact orientation_eq_of_forall_ge_nondegenerate_add_smul β (hτ.comp f) h' hc _ (hT ω c hω _) _

/-- Let `L : V → U` be a linear map, `τ` an alternating form on `V`, and `β`, `σ` symplectic
forms on `U` and `W`. Let `D : V ≃ U × W` be a linear equivalence with first component `L`,
through which `τ` restricts to `σ` on `{0} × W`. If `τ + c • β.comp L L` is nondegenerate for
every `c ≥ c₁`, then for every `c ≥ c₁`, `D` carries the symplectic orientation of
`τ + c • β.comp L L` to the product of the symplectic orientations of `β` and `σ`.

The hypothesis is needed for all `c ≥ c₁` and not only for large `c`: for `V = U` of dimension
two, `L = id` and `τ = -2 • β`, the form is `(c - 2) • β`, whose orientation changes at
`c = 2`. -/
theorem map_orientation_of_forall_ge_nondegenerate_add_smul_comp (hτ : τ.IsAlt)
    (β : SymplecticForm U) (σ : SymplecticForm W) (D : V ≃ₗ[ℝ] U × W) (hD₁ : ∀ v, (D v).1 = L v)
    (hD₂ : ∀ w w', τ (D.symm (0, w)) (D.symm (0, w')) = σ w w') {c₁ : ℝ}
    (h : ∀ c ≥ c₁, (τ + c • β.toBilinForm.comp L L).Nondegenerate) {c : ℝ} (hc : c₁ ≤ c)
    (ω : SymplecticForm V) (hω : ω.toBilinForm = τ + c • β.toBilinForm.comp L L)
    {m n : ℕ} (hm : finrank ℝ U = m) (hn : finrank ℝ W = n) (hV : finrank ℝ V = m + n) :
    Orientation.map (Fin (m + n)) D (ω.orientation hV) =
      (β.orientation hm).prod (σ.orientation hn) hm hn := by
  set K := LinearMap.ker L
  set H := τ.orthogonal K
  have hDK (k : K) : D k = (0, (D k).2) :=
    Prod.ext (by rw [hD₁, LinearMap.mem_ker.1 k.property]) rfl
  -- `k ↦ (D k).2` identifies `ker L` with `W`, carrying `τ` to `σ`.
  let e' : K ≃ₗ[ℝ] W := LinearEquiv.ofBijective (LinearMap.snd ℝ U W ∘ₗ D.toLinearMap ∘ₗ K.subtype)
    ⟨fun k k' hkk' ↦ Subtype.ext (D.injective (by rw [hDK k, hDK k']; exact Prod.ext rfl hkk')),
      fun w ↦ ⟨⟨D.symm (0, w), LinearMap.mem_ker.2 (by rw [← hD₁, D.apply_symm_apply])⟩,
        by simp⟩⟩
  have he' (k : K) : D k = (0, e' k) := by
    rw [hDK k, show e' k = _ from LinearEquiv.ofBijective_apply _ k]
    simp
  have hτK (k k' : K) : τ k k' = σ (e' k) (e' k') := by
    rw [← hD₂, ← he', ← he', D.symm_apply_apply, D.symm_apply_apply]
  have hτL : (τ.restrict K).Nondegenerate := by
    convert σ.nondegenerate.congr e'.symm using 1
    ext k k'
    simp [hτK]
  have hc' : IsCompl H K := (τ.isCompl_orthogonal_of_restrict_nondegenerate hτ.isRefl hτL).symm
  have hn' : finrank ℝ K = n := e'.finrank_eq.trans hn
  have hm' : finrank ℝ H = m := by
    have := Submodule.finrank_add_eq_of_isCompl hc'
    omega
  -- `L` identifies `H` with `U`.
  have hLH : Function.Injective (L ∘ₗ H.subtype) := fun x y hxy ↦ Subtype.ext <| by
    rw [← sub_eq_zero]
    refine Submodule.disjoint_def.1 hc'.disjoint _ (H.sub_mem x.property y.property) ?_
    simpa [K, sub_eq_zero] using hxy
  let e : H ≃ₗ[ℝ] U := LinearEquiv.ofBijective (L ∘ₗ H.subtype)
    ⟨hLH, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hm'.trans hm.symm)).1 hLH⟩
  have he (x : H) : e x = L x := LinearEquiv.ofBijective_apply (L ∘ₗ H.subtype) x
  have hHK : ∀ x ∈ H, ∀ y ∈ K, ω x y = 0 := fun x hx y hy ↦ (LinearMap.congr_fun₂ hω x y).trans
    (LinearMap.BilinForm.add_smul_comp_eq_zero_of_mem_orthogonal_of_mem_ker hτ.isRefl _ c hx hy)
  rw [ω.orientation_eq_map_prod_of_isCompl hc' hHK hm' hn' hV,
    Orientation.map_map_prodEquivOfIsCompl_prod hc' D e e' (fun x ↦ (hD₁ x).trans (he x).symm) he']
  congr 1
  · exact map_orientation_restrict_orthogonal_ker hτ β hτL e he h hc ω hω _ hm'
  · refine (isSymplectomorphism_iff.2 fun k k' ↦ ?_).map_orientation hn'
    rw [restrict_apply, ← hτK]
    exact ((LinearMap.congr_fun₂ hω k k').trans (by simp [LinearMap.mem_ker.1 k'.property])).symm

end Pullback

end TauCeti.SymplecticForm

end
