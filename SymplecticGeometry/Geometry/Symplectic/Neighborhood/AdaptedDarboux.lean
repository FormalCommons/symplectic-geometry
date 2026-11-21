/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Darboux.Immersion
import TauCeti.Geometry.Symplectic.Manifold.Darboux
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Extend

/-!
# Darboux charts adapted to submanifolds

Let `(M, σ)` be a symplectic manifold of dimension `2n` and `f : Q → M` a smooth embedding, not
necessarily with closed image. Near each point `f q₀` there is a Darboux chart
`e : M → StdSpace (Fin n)`, pulling `stdForm (Fin n)` (that is, `ω₀ = ∑ⱼ dxⱼ ∧ dyⱼ`) back to `σ`,
centred at `f q₀`, in which `Q` is a linear subspace `S`: the source of `e` meets the image of `f`
exactly where `e` takes values in `S`. With the coordinates `xⱼ = z.x j`, `yⱼ = z.y j`,
`j : Fin n`, the subspace `S` is given by

* `xⱼ = yⱼ = 0` for `k ≤ j`, if `Q` is a symplectic submanifold of dimension `2k`
  (`HasSymplecticTangentImages.exists_darbouxChart_inter_range_eq`);
* `y = 0` and `xⱼ = 0` for `k ≤ j`, if `Q` is an isotropic submanifold of dimension `k`
  (`IsIsotropicMap.exists_darbouxChart_inter_range_eq`);
* `y = 0`, if `Q` is a Lagrangian submanifold
  (`IsLagrangianMap.exists_darbouxChart_inter_range_eq`).

These names are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, of Tau Ceti's
predicates on maps. All three come from `exists_darbouxChart_inter_range_eq_of_chart`: given a
chart `c` of `Q` with `c q₀ = 0` and an injective linear map `ι : E' → StdSpace (Fin n)` such
that `f ∘ c⁻¹` pulls `σ` back to the pull-back of `stdForm` along `ι`, the conclusion holds with
`S` the range of `ι`. Its proof extends `f ∘ c⁻¹` along `ι` to a local diffeomorphism `G` from a
neighbourhood of `0` in `StdSpace (Fin n)` into `M`
(`SymplecticGeometry.exists_localDiffeomorph_extend`), corrects `G` by Tau Ceti's relative Darboux
theorem along the linear immersion `ι`
(`TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`) so that it
pulls `σ` back to `stdForm`, and inverts the result. For a symplectic `Q`, the chart `c` is a
Darboux chart of `f^* σ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`);
for an isotropic one both forms vanish along `Q`, and any chart with `c q₀ = 0` will do.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4
  (Darboux charts adapted to submanifolds, and the neighbourhood theorems).
-/

public section

open Set Filter Function Module
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open SymplecticGeometry

variable {E H M E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  {σ : SmoothTwoForm I M} {n : ℕ}

/-! ### Relative Darboux charts along a linear subspace of the model -/

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] in
/-- Let `G : StdSpace (Fin n) → M` be a local diffeomorphism at `0` which agrees near `0` with
`u : E' → M` along an injective linear map `ι`, and suppose that `u` pulls `σ` back to the
pull-back of `stdForm` along `ι` near `0`. Then a local diffeomorphism `H` at `0`, still agreeing
with `u` along `ι` near `0`, pulls `σ` back to `stdForm` near `0`. -/
private theorem exists_localDiffeomorph_mpullback_eq (hσ : σ.IsNondegenerate) (hcl : σ.IsClosed)
    {G : StdSpace (Fin n) → M} (hG : IsLocalDiffeomorphAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ G 0)
    {u : E' → M} {ι : E' →L[ℝ] StdSpace (Fin n)} (hι : Injective ι)
    (hGu : ∀ᶠ s in 𝓝 0, G (ι s) = u s)
    (hc : ∀ᶠ s in 𝓝 (0 : E'), ∀ a b : TangentSpace 𝓘(ℝ, E') s,
      σ.eval₂ (u s) (mfderiv 𝓘(ℝ, E') I u s a) (mfderiv 𝓘(ℝ, E') I u s b) =
        stdForm (Fin n) (ι a) (ι b)) :
    ∃ H : StdSpace (Fin n) → M, IsLocalDiffeomorphAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ H 0 ∧
      (∀ᶠ v in 𝓝 0, TauCeti.mpullback 𝓘(ℝ, StdSpace (Fin n)) I H σ.val v =
        (stdForm (Fin n)).constSmooth.val v) ∧
      ∀ᶠ s in 𝓝 0, H (ι s) = u s := by
  obtain ⟨W, hWsub, hWo, hW0⟩ := mem_nhds_iff.1 hG.eventually
  have hGW (v : StdSpace (Fin n)) (hv : v ∈ W) : ContMDiffAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ G v :=
    (hWsub hv : IsLocalDiffeomorphAt _ _ _ G v).contMDiffAt
  -- The two flat forms: `σ` read through `G`, and the constant standard form.
  set σ₁ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    TauCeti.mpullback 𝓘(ℝ, StdSpace (Fin n)) I G σ.val with hσ₁_def
  set σ₀ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    (stdForm (Fin n)).constSmooth.val
  have hσ₁ : ContDiffOn ℝ (⊤ : ℕ∞) σ₁ W :=
    SmoothForm.contDiffOn_mpullback σ hWo fun v hv ↦ (hGW v hv).contMDiffWithinAt
  have hσ₀ : ContDiffOn ℝ (⊤ : ℕ∞) σ₀ W := by
    simpa [mpullback_id] using SmoothForm.contDiffOn_mpullback (stdForm (Fin n)).constSmooth
      hWo contMDiffOn_id
  have hdσ₁ (v : StdSpace (Fin n)) (hv : v ∈ W) : extDeriv σ₁ v = 0 :=
    SmoothForm.IsClosed.extDeriv_mpullback_eq_zero hcl ((hGW v hv).of_le (by simp))
  have hdσ₀ (v : StdSpace (Fin n)) (_ : v ∈ W) : extDeriv σ₀ v = 0 := by
    simpa [mpullback_id] using SmoothForm.IsClosed.extDeriv_mpullback_eq_zero
      (SymplecticForm.isClosed_constSmooth (stdForm (Fin n))) (contMDiffAt_id (x := v))
  -- Both forms are nondegenerate at `ι 0 = 0`.
  have hG0 : IsLocalDiffeomorphAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ G (ι 0) := by rwa [map_zero]
  have hσ₀_apply (v a b : StdSpace (Fin n)) : σ₀ v ![a, b] = stdForm (Fin n) a b :=
    (SmoothBundleForm.eval₂_apply _ v a b).symm.trans (SymplecticForm.constSmooth_apply _ v a b)
  have hnd₀ : ∀ a, (∀ b, σ₀ (ι 0) ![a, b] = 0) → a = 0 := fun a ha ↦
    (stdForm (Fin n)).separatingLeft a fun b ↦ (hσ₀_apply _ a b).symm.trans (ha b)
  have hnd₁ : ∀ a, (∀ b, σ₁ (ι 0) ![a, b] = 0) → a = 0 := by
    intro a ha
    have hinv := hG0.isInvertible_mfderiv (by simp)
    have h : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I G (ι 0) a = 0 :=
      isNondegenerate_iff_separatingLeft.1 hσ (G (ι 0)) _ fun w ↦ by
        obtain ⟨b, rfl⟩ := hinv.surjective w
        rw [SmoothBundleForm.eval₂_apply, ← mpullback_apply_pair G σ.val (ι 0) a b]
        exact ha b
    exact hinv.injective (h.trans (map_zero _).symm)
  -- Both forms pull back along `ι` to the restriction of `stdForm`.
  have hpull_flat (γ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (s : E') :
      (γ (ι s)).compContinuousLinearMap (fderiv ℝ ι s) =
        TauCeti.mpullback 𝓘(ℝ, E') 𝓘(ℝ, StdSpace (Fin n)) ι γ s := by
    exact (congrFun (mpullback_eq_flat (ι : E' → StdSpace (Fin n)) γ) s).symm
  have htan : ∀ᶠ s in 𝓝 (0 : E'), (σ₁ (ι s)).compContinuousLinearMap (fderiv ℝ ι s) =
      (σ₀ (ι s)).compContinuousLinearMap (fderiv ℝ ι s) := by
    have hWι : ∀ᶠ s in 𝓝 (0 : E'), ι s ∈ W :=
      ι.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hWo.mem_nhds hW0)
    filter_upwards [hc, hGu.eventually_nhds, hWι] with s hcs hGus hsW
    -- `hGus` says that `G ∘ ι` and `u` agree near `s`, which is `G ∘ ι =ᶠ[𝓝 s] u` by definition.
    rw [hpull_flat, hpull_flat, hσ₁_def, ← mpullback_comp_at ι.mdifferentiableAt
      ((hGW _ hsW).mdifferentiableAt (by simp)), (show G ∘ ι =ᶠ[𝓝 s] u from hGus).mpullback_eq]
    ext v
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, mpullback_apply_pair, mpullback_apply_pair, ContinuousLinearMap.mfderiv_eq,
      ← SmoothBundleForm.eval₂_apply]
    exact (hcs (v 0) (v 1)).trans (hσ₀_apply _ _ _).symm
  -- The relative Darboux theorem along `ι` gives `Φ` fixing the image of `ι` near `0`, with
  -- `Φ^* σ₁ = σ₀`.
  obtain ⟨Φ, h0Φι, hfix, hpb⟩ :=
    TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq (r := ⊤)
      le_top hWo (by rwa [map_zero]) hσ₀ hσ₁ hdσ₀ hdσ₁
      (Eventually.of_forall fun _ ↦ ι.contDiff.contDiffAt) (by rwa [ι.fderiv]) htan hnd₀ hnd₁
  have hΦ0 : Φ 0 = 0 := by simpa using hfix.self_of_nhds
  have h0Φ : (0 : StdSpace (Fin n)) ∈ Φ.source := by simpa using h0Φι
  -- `H = G ∘ Φ` is a local diffeomorphism at `0` which pulls `σ` back to `σ₀`.
  refine ⟨G ∘ Φ, (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ h0Φ).comp (K := I) (P := M)
    (by rw [hΦ0]; exact hG), ?_, ?_⟩
  · have hO : Φ.source ∩ Φ ⁻¹' W ∈ 𝓝 0 :=
      (Φ.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_source hWo).mem_nhds
        ⟨h0Φ, by rwa [mem_preimage, hΦ0]⟩
    filter_upwards [hO] with v ⟨hv, hvW⟩
    rw [mpullback_comp_at (Φ.mdifferentiableAt (by simp) hv)
      ((hGW _ hvW).mdifferentiableAt (by simp)), ← hσ₁_def]
    exact (congrFun (mpullback_eq_flat (Φ : StdSpace (Fin n) → StdSpace (Fin n)) σ₁) v).trans
      (hpb v hv)
  · filter_upwards [hfix, hGu] with s h₁ h₂
    rw [comp_apply, h₁, h₂]

/-- **Darboux charts in which a submanifold is a linear subspace.** Let `f : Q → M` be a smooth
embedding into a manifold of dimension `2n` with a closed nondegenerate two-form `σ`, let `c` be a
chart of `Q` with `c q₀ = 0`, and let `ι : E' → StdSpace (Fin n)` be an injective linear map such
that, near `0`, `f ∘ c⁻¹` pulls `σ` back to the pull-back of `stdForm` along `ι`. Then some chart
`e` of `M` with `e (f q₀) = 0` pulls `stdForm` back to `σ`, and its source meets the image of `f`
exactly where `e` takes values in the range of `ι`. -/
theorem exists_darbouxChart_inter_range_eq_of_chart (hσ : σ.IsNondegenerate)
    (hcl : σ.IsClosed) (hn : finrank ℝ E = 2 * n) (f : SmoothEmbedding J I ∞ Q M) {q₀ : Q}
    (c : PartialDiffeomorph J 𝓘(ℝ, E') Q E' ∞) (hq₀ : q₀ ∈ c.source) (hc₀ : c q₀ = 0)
    {ι : E' →L[ℝ] StdSpace (Fin n)} (hι : Injective ι)
    (hc : ∀ᶠ s in 𝓝 (0 : E'), ∀ a b : TangentSpace 𝓘(ℝ, E') s,
      σ.eval₂ (f (c.symm s)) (mfderiv 𝓘(ℝ, E') I (f ∘ c.symm) s a)
        (mfderiv 𝓘(ℝ, E') I (f ∘ c.symm) s b) = stdForm (Fin n) (ι a) (ι b)) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f = e.source ∩ e ⁻¹' range ι := by
  -- The parametrization `u = f ∘ c⁻¹` of `Q` near `q₀` is an immersion at `0`.
  set u : E' → M := f ∘ c.symm with hu_def
  have h0t : (0 : E') ∈ c.target := hc₀ ▸ c.map_source hq₀
  have hcs0 : c.symm 0 = q₀ := hc₀ ▸ c.left_inv hq₀
  have hu : ∀ᶠ s in 𝓝 0, ContMDiffAt 𝓘(ℝ, E') I ∞ u s := by
    filter_upwards [c.open_target.mem_nhds h0t] with s hs
    exact f.contMDiff.contMDiffAt.comp s
      (c.symm.contMDiffOn.contMDiffAt (c.symm.open_source.mem_nhds hs))
  have hinj : Injective (mfderiv 𝓘(ℝ, E') I u 0) := by
    rw [hu_def, mfderiv_comp 0 (f.contMDiff.mdifferentiableAt (by simp))
      (c.symm.mdifferentiableAt (by simp) (by simpa using h0t))]
    exact (f.isImmersion.mfderiv_injective (by simp) _).comp
      (c.symm.isInvertible_mfderiv (by simp) (by simpa using h0t)).injective
  -- Extend `u` along `ι`, then correct the extension to `H`, with `H^* σ = stdForm` near `0`.
  have hdim : finrank ℝ (StdSpace (Fin n)) = finrank ℝ E := by
    rw [finrank_stdSpace, Fintype.card_fin, hn]
  obtain ⟨G, hG, hGu⟩ := exists_localDiffeomorph_extend hι hu hinj hdim
  obtain ⟨H, hH, hHpb, hHu⟩ := exists_localDiffeomorph_mpullback_eq hσ hcl hG hι hGu hc
  -- The chart is a restriction of the local inverse `e₀` of `H`.
  set e₀ := hH.localInverse
  obtain ⟨π, hπ⟩ := (ι : E' →ₗ[ℝ] StdSpace (Fin n)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hι)
  let π' : StdSpace (Fin n) →L[ℝ] E' := LinearMap.toContinuousLinearMap π
  have hπι (s : E') : π' (ι s) = s := LinearMap.congr_fun hπ s
  have hB : ∀ᶠ s in 𝓝 (0 : E'), s ∈ c.target ∧ H (ι s) = u s ∧ ι s ∈ e₀.target := by
    have h₂ : ∀ᶠ s in 𝓝 (0 : E'), ι s ∈ e₀.target :=
      ι.continuous.continuousAt.preimage_mem_nhds
        (by rw [map_zero]; exact e₀.open_target.mem_nhds hH.localInverse_mem_target)
    exact (c.open_target.eventually_mem h0t).and (hHu.and h₂)
  obtain ⟨B, hBsub, hBo, hB0⟩ := mem_nhds_iff.1 hB
  -- Since `f` is an embedding, the points of `Q` near `q₀` are cut out by an open `U ⊆ M`.
  obtain ⟨U, hUo, hfU⟩ := f.isEmbedding.isInducing.isOpen_iff.1
    (c.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_source hBo)
  obtain ⟨O₁, hO₁sub, hO₁o, h0O₁⟩ := mem_nhds_iff.1 (hHpb.and hH.eventually)
  set O := O₁ ∩ π' ⁻¹' B
  have hOo : IsOpen O := hO₁o.inter (hBo.preimage π'.continuous)
  set O' := e₀.source ∩ e₀ ⁻¹' O ∩ U
  have hO'o : IsOpen O' :=
    (e₀.contMDiffOn.continuousOn.isOpen_inter_preimage e₀.open_source hOo).inter hUo
  have hH0 : H 0 = f q₀ := by
    have h := (hBsub hB0).2.1
    rw [map_zero] at h
    rw [h, hu_def, comp_apply, hcs0]
  have he₀H0 : e₀ (f q₀) = 0 := hH0 ▸ hH.localInverse_left_inv hH.localInverse_mem_target
  refine ⟨e₀.restrOpen O' hO'o, ?_, ?_, ?_, ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    have hs : f q₀ ∈ e₀.source := hH0 ▸ hH.localInverse_mem_source
    refine ⟨hs, ⟨hs, by rw [mem_preimage, he₀H0]; exact ⟨h0O₁, by simpa using hB0⟩⟩, ?_⟩
    have : q₀ ∈ ⇑f ⁻¹' U := by
      rw [hfU]
      exact ⟨hq₀, by simpa [hc₀] using hB0⟩
    exact this
  · rw [PartialDiffeomorph.coe_restrOpen]
    exact he₀H0
  · -- `e₀` pulls `stdForm` back to `σ`, since `H ∘ e₀ = id` near `x` and `H^* σ = stdForm`.
    intro x hx v w
    rw [PartialDiffeomorph.restrOpen_source] at hx
    obtain ⟨hx₀, ⟨-, ⟨hxO₁, -⟩⟩, -⟩ := hx
    obtain ⟨hxpb, hxH⟩ := hO₁sub hxO₁
    rw [PartialDiffeomorph.coe_restrOpen]
    have hid : H ∘ e₀ =ᶠ[𝓝 x] id := by
      filter_upwards [e₀.open_source.mem_nhds hx₀] with y hy
      exact hH.localInverse_right_inv hy
    have key : σ.val x =
        TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) e₀ (stdForm (Fin n)).constSmooth.val x := by
      rw [← mpullback_id σ.val, ← hid.mpullback_eq,
        mpullback_comp_at (e₀.mdifferentiableAt (by simp) hx₀)
          (hxH.mdifferentiableAt (by simp))]
      ext a
      rw [mpullback_apply, hxpb, mpullback_apply]
    rw [SmoothBundleForm.eval₂_apply, key, mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply]
    exact SymplecticForm.eval₂_constSmooth_mfderiv_eq _ _ x v w
  · ext x
    simp only [mem_inter_iff, PartialDiffeomorph.restrOpen_source, mem_preimage,
      PartialDiffeomorph.coe_restrOpen, mem_range]
    constructor
    · -- A point `f q` of the source has `q` near `q₀`, and then `e₀ (f q) = ι (c q)`.
      rintro ⟨hx, q, rfl⟩
      refine ⟨hx, ?_⟩
      obtain ⟨-, -, hxU⟩ := hx
      have hq : q ∈ c.source ∩ c ⁻¹' B := by
        rw [← hfU]
        exact hxU
      obtain ⟨-, hHs, hts⟩ := hBsub hq.2
      refine ⟨c q, ?_⟩
      have hHq : H (ι (c q)) = f q := by
        rw [hHs, hu_def, comp_apply, PartialDiffeomorph.symm_toPartialEquiv, c.left_inv hq.1]
      rw [← hHq, hH.localInverse_left_inv hts]
    · -- A point `x` of the source with `e₀ x = ι s` is `H (ι s) = f (c⁻¹ s)`.
      rintro ⟨hx, s, hs⟩
      refine ⟨hx, c.symm s, ?_⟩
      obtain ⟨hx₀, ⟨-, ⟨-, hxB⟩⟩, -⟩ := hx
      have hsB : s ∈ B := by
        have h := hxB
        rwa [mem_preimage, ← hs, hπι] at h
      calc f (c.symm s) = H (ι s) := (hBsub hsB).2.1.symm
        _ = H (e₀ x) := by rw [hs]
        _ = x := hH.localInverse_right_inv hx₀

/-! ### The standard inclusions of the model subspaces -/

open StdSpace in
/-- `StdSpace (Fin k)` inside `StdSpace (Fin (k + m))`, on the first `k` coordinate pairs. -/
private noncomputable def stdInl (k m : ℕ) : StdSpace (Fin k) →L[ℝ] StdSpace (Fin (k + m)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv.sumCongr finSumFinEquiv)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sumEquiv (Fin k) (Fin m)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _))

private theorem x_stdInl {k m : ℕ} (z : StdSpace (Fin k)) :
    (stdInl k m z).x = Sum.elim z.x 0 ∘ finSumFinEquiv.symm := by
  simp [stdInl]

private theorem y_stdInl {k m : ℕ} (z : StdSpace (Fin k)) :
    (stdInl k m z).y = Sum.elim z.y 0 ∘ finSumFinEquiv.symm := by
  simp [stdInl]

private theorem stdInl_apply_inl_castAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin k) :
    stdInl k m z (Sum.inl (Fin.castAdd m i)) = z (Sum.inl i) := by
  simpa using congr_fun (x_stdInl (m := m) z) (Fin.castAdd m i)

private theorem stdInl_apply_inr_castAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin k) :
    stdInl k m z (Sum.inr (Fin.castAdd m i)) = z (Sum.inr i) := by
  simpa using congr_fun (y_stdInl (m := m) z) (Fin.castAdd m i)

private theorem stdInl_apply_inl_natAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin m) :
    stdInl k m z (Sum.inl (Fin.natAdd k i)) = 0 := by
  simpa using congr_fun (x_stdInl (m := m) z) (Fin.natAdd k i)

private theorem stdInl_apply_inr_natAdd {k m : ℕ} (z : StdSpace (Fin k)) (i : Fin m) :
    stdInl k m z (Sum.inr (Fin.natAdd k i)) = 0 := by
  simpa using congr_fun (y_stdInl (m := m) z) (Fin.natAdd k i)

private theorem stdForm_stdInl {k m : ℕ} (z w : StdSpace (Fin k)) :
    stdForm (Fin (k + m)) (stdInl k m z) (stdInl k m w) = stdForm (Fin k) z w := by
  simp [stdForm_apply, Fin.sum_univ_add, stdInl_apply_inl_castAdd, stdInl_apply_inr_castAdd,
    stdInl_apply_inl_natAdd, stdInl_apply_inr_natAdd]

private theorem injective_stdInl {k m : ℕ} : Injective (stdInl k m) := by
  intro z w h
  refine StdSpace.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
  · simpa [stdInl_apply_inl_castAdd] using congr_fun (congrArg StdSpace.x h) (Fin.castAdd m i)
  · simpa [stdInl_apply_inr_castAdd] using congr_fun (congrArg StdSpace.y h) (Fin.castAdd m i)

private theorem range_stdInl {k m : ℕ} :
    range (stdInl k m) = {z | ∀ j : Fin (k + m), k ≤ (j : ℕ) → z.x j = 0 ∧ z.y j = 0} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin m, Fin.natAdd k i = j :=
      ⟨⟨j - k, by omega⟩, Fin.ext (by simp; omega)⟩
    simp [stdInl_apply_inl_natAdd, stdInl_apply_inr_natAdd]
  · intro hz
    refine ⟨(StdSpace.equivProd (Fin k)).symm
      (fun i ↦ z.x (Fin.castAdd m i), fun i ↦ z.y (Fin.castAdd m i)), ?_⟩
    refine StdSpace.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_) <;>
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp [stdInl_apply_inl_castAdd]
    · simpa [stdInl_apply_inl_natAdd] using (hz (Fin.natAdd k i) (by simp)).1.symm
    · simp [stdInl_apply_inr_castAdd]
    · simpa [stdInl_apply_inr_natAdd] using (hz (Fin.natAdd k i) (by simp)).2.symm

/-! ### Symplectic, isotropic and Lagrangian submanifolds -/

variable [IsManifold J ∞ Q] [BoundarylessManifold J Q]

/-- **Darboux charts adapted to a symplectic submanifold.** Let `f : Q → M` be a smooth embedding
with symplectic tangent images, of dimension `2k`, into a manifold of dimension `2n` with a closed
nondegenerate two-form `σ`. Near each `f q₀` there is a chart `e` of `M` with `e (f q₀) = 0`
pulling `stdForm` back to `σ`, whose source meets the image of `f` exactly where the coordinates
`xⱼ` and `yⱼ` of `e` vanish for all `j ≥ k`.

Milestone: *Darboux charts adapted to submanifolds*. -/
theorem HasSymplecticTangentImages.exists_darbouxChart_inter_range_eq
    {hσ : σ.IsNondegenerate} {f : SmoothEmbedding J I ∞ Q M} (h : hσ.HasSymplecticTangentImages J f)
    (hcl : σ.IsClosed)
    (hn : finrank ℝ E = 2 * n) {k : ℕ} (hk : finrank ℝ E' = 2 * k) (q₀ : Q) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f =
        e.source ∩ e ⁻¹' {z | ∀ j : Fin n, k ≤ (j : ℕ) → z.x j = 0 ∧ z.y j = 0} := by
  have hinj (q : Q) : Injective (mfderiv J I f q) := f.isImmersion.mfderiv_injective (by simp) q
  have hkn : k ≤ n := by
    have := LinearMap.finrank_le_finrank_of_injective (hinj q₀)
    rw [finrank_tangentSpace, finrank_tangentSpace] at this
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  let L : E' ≃L[ℝ] StdSpace (Fin k) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_stdSpace, Fintype.card_fin, hk])
  have hL (a b : E') : (stdForm (Fin k)).transport L.symm.toLinearEquiv a b =
      stdForm (Fin (k + m)) ((stdInl k m).comp (L : E' →L[ℝ] StdSpace (Fin k)) a)
        ((stdInl k m).comp (L : E' →L[ℝ] StdSpace (Fin k)) b) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, stdForm_stdInl,
      SymplecticForm.transport_apply]
    simp
  -- A Darboux chart of `f^* σ` on `Q` modelled on `StdSpace (Fin k)` read through `L`.
  obtain ⟨c, hq₀, hc₀, hc⟩ := (h.isSymplectic_mpullback ⟨hcl, hσ⟩ f.contMDiff hinj)
    |>.exists_darbouxChart_of_symplecticForm ((stdForm (Fin k)).transport L.symm.toLinearEquiv) q₀
  obtain ⟨e, h₁, h₂, h₃, h₄⟩ := hσ.exists_darbouxChart_inter_range_eq_of_chart hcl hn f c hq₀ hc₀
    (ι := (stdInl k m).comp (L : E' →L[ℝ] StdSpace (Fin k)))
    (by rw [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
        exact injective_stdInl.comp L.injective) (by
      filter_upwards [c.open_target.mem_nhds (hc₀ ▸ c.map_source hq₀)] with s hs a b
      have hd : MDifferentiableAt 𝓘(ℝ, E') J c.symm s :=
        c.symm.mdifferentiableAt (by simp) (by simpa using hs)
      have hf := f.contMDiff.mdifferentiableAt (x := c.symm s) (by simp)
      have hinv (v : TangentSpace 𝓘(ℝ, E') s) :
          mvfderiv J c (c.symm s) (mfderiv 𝓘(ℝ, E') J c.symm s v) = v :=
        (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans
          (c.mfderiv_apply_mfderiv_symm_apply (by simp) hs v)
      rw [mfderiv_comp_apply s hf hd a, mfderiv_comp_apply s hf hd b,
        ← SmoothForm.eval₂_mpullback f f.contMDiff, hc (c.symm s) (c.map_target hs), hinv, hinv]
      exact hL a b)
  refine ⟨e, h₁, h₂, h₃, ?_⟩
  rw [h₄, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, range_comp,
    L.surjective.range_eq, image_univ,
    range_stdInl]

/-- **Darboux charts adapted to an isotropic submanifold.** Let `f : Q → M` be an isotropic smooth
embedding, of dimension `k`, into a manifold of dimension `2n` with a closed nondegenerate two-form
`σ`. Near each `f q₀` there is a chart `e` of `M` with `e (f q₀) = 0` pulling `stdForm` back to
`σ`, whose source meets the image of `f` exactly where the coordinates `y` of `e` vanish, and
so do the coordinates `xⱼ` for all `j ≥ k`.

Milestone: *Darboux charts adapted to submanifolds*. -/
theorem IsIsotropicMap.exists_darbouxChart_inter_range_eq
    {hσ : σ.IsNondegenerate} {f : SmoothEmbedding J I ∞ Q M} (h : hσ.IsIsotropicMap J f)
    (hcl : σ.IsClosed) (hn : finrank ℝ E = 2 * n) {k : ℕ} (hk : finrank ℝ E' = k) (q₀ : Q) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f =
        e.source ∩ e ⁻¹' {z | z.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → z.x j = 0} := by
  have hinj (q : Q) : Injective (mfderiv J I f q) := f.isImmersion.mfderiv_injective (by simp) q
  have hkn : k ≤ n := by
    have := h.two_mul_finrank_le (hinj q₀)
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  -- The model of `Q` is `Fin k → ℝ`, included as the first `k` coordinates `x`.
  let L : E' ≃L[ℝ] (Fin k → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hk])
  let ι₀ : (Fin k → ℝ) →ₗ[ℝ] StdSpace (Fin k) :=
    (StdSpace.equivProd (Fin k)).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
  let ι : E' →L[ℝ] StdSpace (Fin (k + m)) :=
    (stdInl k m).comp (LinearMap.toContinuousLinearMap (ι₀ ∘ₗ L.toLinearMap))
  have hι₀ : Injective ι₀ := fun a b hab ↦ by simpa [ι₀] using congrArg StdSpace.x hab
  have hιapp (a : E') : ι a = stdInl k m (ι₀ (L a)) := by
    simp only [ι, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  have hι : Injective ι := by
    rw [show (ι : E' → StdSpace (Fin (k + m))) = stdInl k m ∘ ι₀ ∘ L from funext hιapp]
    exact injective_stdInl.comp (hι₀.comp L.injective)
  have hstd (a b : E') : stdForm (Fin (k + m)) (ι a) (ι b) = 0 := by
    rw [hιapp, hιapp, stdForm_stdInl]
    simp [ι₀]
  have hrange : range ι = {z | z.y = 0 ∧ ∀ j : Fin (k + m), k ≤ (j : ℕ) → z.x j = 0} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨funext fun j ↦ ?_, fun j hj ↦ ?_⟩
      · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
        · simp [hιapp, stdInl_apply_inr_castAdd, ι₀]
        · simp [hιapp, stdInl_apply_inr_natAdd]
      · exact ((range_stdInl (k := k) (m := m)).subset ⟨_, (hιapp a).symm⟩ j hj).1
    · rintro ⟨hy, hx⟩
      obtain ⟨w, rfl⟩ : z ∈ range (stdInl k m) := by
        rw [range_stdInl]
        exact fun j hj ↦ ⟨hx j hj, congr_fun hy j⟩
      refine ⟨L.symm w.x, ?_⟩
      rw [hιapp, L.apply_symm_apply]
      congr 1
      refine StdSpace.ext (by simp [ι₀]) (funext fun i ↦ ?_)
      simpa [ι₀, stdInl_apply_inr_castAdd] using (congr_fun hy (Fin.castAdd m i)).symm
  obtain ⟨c, hq₀, hc₀⟩ := exists_partialDiffeomorph_apply_eq_zero (I := J) q₀
  obtain ⟨e, h₁, h₂, h₃, h₄⟩ := hσ.exists_darbouxChart_inter_range_eq_of_chart hcl hn f c hq₀ hc₀
    hι (by
      filter_upwards [c.open_target.mem_nhds (hc₀ ▸ c.map_source hq₀)] with s hs a b
      have hd : MDifferentiableAt 𝓘(ℝ, E') J c.symm s :=
        c.symm.mdifferentiableAt (by simp) (by simpa using hs)
      have hf := f.contMDiff.mdifferentiableAt (x := c.symm s) (by simp)
      rw [mfderiv_comp_apply s hf hd a, mfderiv_comp_apply s hf hd b,
        isIsotropicMap_iff.1 h]
      exact (hstd a b).symm)
  exact ⟨e, h₁, h₂, h₃, by rw [h₄, hrange]⟩

/-- **Darboux charts adapted to a Lagrangian submanifold.** Let `f : Q → M` be a Lagrangian smooth
embedding into a manifold of dimension `2n` with a closed nondegenerate two-form `σ`. Near each
`f q₀` there is a chart `e` of `M` with `e (f q₀) = 0` pulling `stdForm` back to `σ`, whose source
meets the image of `f` exactly where the coordinates `y` of `e` vanish.

Milestone: *Darboux charts adapted to submanifolds*. -/
theorem IsLagrangianMap.exists_darbouxChart_inter_range_eq
    {hσ : σ.IsNondegenerate} {f : SmoothEmbedding J I ∞ Q M} (h : hσ.IsLagrangianMap J f)
    (hcl : σ.IsClosed) (hn : finrank ℝ E = 2 * n) (q₀ : Q) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f = e.source ∩ e ⁻¹' {z | z.y = 0} := by
  have hk : finrank ℝ E' = n := by
    have := h.two_mul_finrank (f.isImmersion.mfderiv_injective (by simp) q₀)
    omega
  obtain ⟨e, h₁, h₂, h₃, h₄⟩ := h.isIsotropicMap.exists_darbouxChart_inter_range_eq hcl hn hk q₀
  refine ⟨e, h₁, h₂, h₃, ?_⟩
  rw [h₄]
  congr 2
  ext z
  simp

end TauCeti.SmoothTwoForm.IsNondegenerate
