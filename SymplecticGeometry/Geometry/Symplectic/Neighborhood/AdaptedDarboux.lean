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
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Darboux.Immersion
import TauCeti.Geometry.Symplectic.Manifold.Darboux
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Extend
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Topology.Maps.Embedding
import SymplecticGeometry.Geometry.Symplectic.Manifold.CharacteristicFoliation
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Darboux charts adapted to submanifolds

Take a smooth embedding `f : Q → M`, whose image need not be closed, into a symplectic manifold
`(M, σ)` with `dim M = 2n`. Near each point `f q₀` there is a Darboux chart
`e : M → StdSpace (Fin n)`, pulling `stdForm (Fin n)` (that is, `ω₀ = ∑ⱼ dxⱼ ∧ dyⱼ`) back to `σ`,
centred at `f q₀`, in which `Q` is a linear subspace `S`: the source of `e` meets the image of `f`
exactly where `e` takes values in `S`. With the coordinates `xⱼ = z.x j`, `yⱼ = z.y j`,
`j : Fin n`, the subspace `S` is given by

* `xⱼ = yⱼ = 0` for `k ≤ j`, if `Q` is a symplectic submanifold of dimension `2k`
  (`HasSymplecticTangentImages.exists_darbouxChart_inter_range_eq`);
* `y = 0` and `xⱼ = 0` for `k ≤ j`, if `Q` is an isotropic submanifold of dimension `k`
  (`IsIsotropicMap.exists_darbouxChart_inter_range_eq`);
* `y = 0`, if `Q` is a Lagrangian submanifold
  (`IsLagrangianMap.exists_darbouxChart_inter_range_eq`);
* `yⱼ = 0` for `j < k`, if `Q` is a coisotropic submanifold of dimension `2n - k`
  (`IsCoisotropicMap.exists_darbouxChart_inter_range_eq`). There the derivative of `e` also
  carries the symplectic orthogonal of each tangent space of `Q`, the tangent space of its
  characteristic foliation, onto the span of the first `k` vectors `∂/∂xⱼ`.

These names are in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, of Tau Ceti's
predicates on maps. All four come from `exists_darbouxChart_inter_range_eq_of_chart`: given a
chart `c` of `Q` with `c q₀ = 0` and an injective linear map `ι : E' → StdSpace (Fin n)` such
that `f ∘ c⁻¹` pulls `σ` back to the pull-back of `stdForm` along `ι`, the conclusion holds with
`S` the range of `ι`. Its proof extends `f ∘ c⁻¹` along `ι` to a local diffeomorphism `G` from a
neighbourhood of `0` in `StdSpace (Fin n)` into `M`
(`SymplecticGeometry.exists_localDiffeomorph_extend`), corrects `G` by Tau Ceti's relative Darboux
theorem along the linear immersion `ι`
(`TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq`) so that it
pulls `σ` back to `stdForm`, and inverts the result. The inverse is a restriction of the local
inverse, which still pulls `stdForm` back to `σ`
(`IsLocalDiffeomorphAt.mpullback_localInverse_apply_eq`), and is shrunk, `f` being an embedding,
until its source meets the image of `f` only along the range of `ι`
(`Topology.IsInducing.exists_isOpen_inter_range_eq`). For a symplectic `Q`, the chart `c` is a
Darboux chart of `f^* σ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart_of_symplecticForm`);
for an isotropic one both forms vanish along `Q`, and any chart with `c q₀ = 0` will do. For a
coisotropic `Q`, `c` is a chart in which the presymplectic form `f^* σ`, closed and of constant
rank, is pulled back from `stdForm` along a linear projection
(`IsCoisotropicMap.exists_partialDiffeomorph_eval₂_eq_stdForm`). Since
`e` pulls `ω₀` back to `σ` and its derivative carries each tangent space of `Q` onto `S`, it
carries their symplectic orthogonals onto the `ω₀`-orthogonal of `S`
(`TauCeti.SymplecticForm.IsSymplectomorphism.map_orthogonal`), which
`SymplecticGeometry.forall_stdForm_eq_zero_iff_y_eq_zero_and_x_eq_zero` computes. The linear
maps `ι` come from
`SymplecticGeometry.StdSpace.stdInl`, `SymplecticGeometry.StdSpace.stdInr` and
`SymplecticGeometry.StdSpace.ofX`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4,
  Exercise 3.4.19 (Darboux charts adapted to submanifolds), with Exercise 3.4.9 for the
  characteristic foliation of a coisotropic submanifold.
-/

public section

open Set Filter Function Module
open scoped Manifold ContDiff Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open SymplecticGeometry SymplecticGeometry.StdSpace

variable {E H M E' H' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Q] [ChartedSpace H' Q]
  {σ : SmoothTwoForm I M} {n : ℕ}

/-! ### Relative Darboux charts along a linear subspace of the model -/

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ E'] in
/-- Along the image of `ι`, near `0`, the pull-back of `σ` by `G` agrees with `stdForm` on
vectors tangent to that image, when `G ∘ ι = u` near `0` and `u` pulls `σ` back to the pull-back
of `stdForm` along `ι`. -/
private theorem eventually_compContinuousLinearMap_mpullback_eq {G : StdSpace (Fin n) → M}
    {W : Set (StdSpace (Fin n))} (hWo : IsOpen W) (hW0 : 0 ∈ W)
    (hGW : ∀ v ∈ W, ContMDiffAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ G v)
    {u : E' → M} {ι : E' →L[ℝ] StdSpace (Fin n)} (hGu : ∀ᶠ s in 𝓝 0, G (ι s) = u s)
    (hc : ∀ᶠ s in 𝓝 (0 : E'), ∀ a b : TangentSpace 𝓘(ℝ, E') s,
      σ.eval₂ (u s) (mfderiv 𝓘(ℝ, E') I u s a) (mfderiv 𝓘(ℝ, E') I u s b) =
        stdForm (Fin n) (ι a) (ι b)) :
    ∀ᶠ s in 𝓝 (0 : E'),
      (TauCeti.mpullback 𝓘(ℝ, StdSpace (Fin n)) I G σ.val (ι s)).compContinuousLinearMap
        (fderiv ℝ ι s) =
      ((stdForm (Fin n)).constSmooth.val (ι s)).compContinuousLinearMap (fderiv ℝ ι s) := by
  have hpull_flat (γ : StdSpace (Fin n) → StdSpace (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (s : E') :
      (γ (ι s)).compContinuousLinearMap (fderiv ℝ ι s) =
        TauCeti.mpullback 𝓘(ℝ, E') 𝓘(ℝ, StdSpace (Fin n)) ι γ s :=
    (congrFun (mpullback_eq_flat (ι : E' → StdSpace (Fin n)) γ) s).symm
  have hWι : ∀ᶠ s in 𝓝 (0 : E'), ι s ∈ W :=
    ι.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hWo.mem_nhds hW0)
  filter_upwards [hc, hGu.eventually_nhds, hWι] with s hcs hGus hsW
  refine (hpull_flat (TauCeti.mpullback _ I G σ.val) s).trans
    (Eq.trans ?_ (hpull_flat (stdForm (Fin n)).constSmooth.val s).symm)
  -- `hGus` says that `G ∘ ι` and `u` agree near `s`, which is `G ∘ ι =ᶠ[𝓝 s] u` by definition.
  rw [← mpullback_comp_at ι.mdifferentiableAt
    ((hGW _ hsW).mdifferentiableAt (by simp)), (show G ∘ ι =ᶠ[𝓝 s] u from hGus).mpullback_eq]
  ext v w
  rw [mpullback_apply_pair, mpullback_apply_pair, ContinuousLinearMap.mfderiv_eq,
    ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply]
  exact (hcs v w).trans (SymplecticForm.constSmooth_apply _ _ _ _).symm

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
  have hσ₀ : ContDiffOn ℝ (⊤ : ℕ∞) σ₀ W := by
    simpa [mpullback_id] using SmoothForm.contDiffOn_mpullback (stdForm (Fin n)).constSmooth
      hWo contMDiffOn_id
  have hdσ₀ (v : StdSpace (Fin n)) (_ : v ∈ W) : extDeriv σ₀ v = 0 := by
    simpa [mpullback_id] using SmoothForm.IsClosed.extDeriv_mpullback_eq_zero
      (SymplecticForm.isClosed_constSmooth (stdForm (Fin n))) (contMDiffAt_id (x := v))
  -- Both forms are nondegenerate at `ι 0 = 0`.
  have hnd₀ : ∀ a, (∀ b, σ₀ (ι 0) ![a, b] = 0) → a = 0 := fun a ha ↦
    (stdForm (Fin n)).separatingLeft a fun b ↦ (SymplecticForm.constSmooth_apply _ _ a b).symm.trans
      ((SmoothBundleForm.eval₂_apply _ _ a b).trans (ha b))
  have hnd₁ : ∀ a, (∀ b, σ₁ (ι 0) ![a, b] = 0) → a = 0 := by
    intro a ha
    have hinv := (show IsLocalDiffeomorphAt _ _ ∞ G (ι 0) by rwa [map_zero]).isInvertible_mfderiv
      (by simp)
    have h : mfderiv 𝓘(ℝ, StdSpace (Fin n)) I G (ι 0) a = 0 :=
      isNondegenerate_iff_separatingLeft.1 hσ (G (ι 0)) _ fun w ↦ by
        obtain ⟨b, rfl⟩ := hinv.surjective w
        rw [SmoothBundleForm.eval₂_apply, ← mpullback_apply_pair G σ.val (ι 0) a b]
        exact ha b
    exact hinv.injective (h.trans (map_zero _).symm)
  -- The relative Darboux theorem along `ι` gives `Φ` fixing the image of `ι` near `0`, with
  -- `Φ^* σ₁ = σ₀`.
  obtain ⟨Φ, h0Φι, hfix, hpb⟩ :=
    TauCeti.exists_partialDiffeomorph_fix_immersion_compContinuousLinearMap_fderiv_eq (r := ⊤)
      le_top hWo (by rwa [map_zero]) hσ₀
      (SmoothForm.contDiffOn_mpullback σ hWo fun v hv ↦ (hGW v hv).contMDiffWithinAt) hdσ₀
      (fun v hv ↦ SmoothForm.IsClosed.extDeriv_mpullback_eq_zero hcl ((hGW v hv).of_le (by simp)))
      (Eventually.of_forall fun _ ↦ ι.contDiff.contDiffAt) (by rwa [ι.fderiv])
      (eventually_compContinuousLinearMap_mpullback_eq hWo hW0 hGW hGu hc) hnd₀ hnd₁
  have hΦ0 : Φ 0 = 0 := by simpa using hfix.self_of_nhds
  have h0Φ : (0 : StdSpace (Fin n)) ∈ Φ.source := by simpa using h0Φι
  -- `H = G ∘ Φ` is a local diffeomorphism at `0` which pulls `σ` back to `σ₀`.
  refine ⟨G ∘ Φ, (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ h0Φ).comp (K := I) (P := M)
    (by rw [hΦ0]; exact hG), ?_, ?_⟩
  · have hWΦ : IsOpen (Φ.source ∩ Φ ⁻¹' W) := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hWo
    have hO : Φ.source ∩ Φ ⁻¹' W ∈ 𝓝 0 := hWΦ.mem_nhds ⟨h0Φ, by rwa [mem_preimage, hΦ0]⟩
    filter_upwards [hO] with v ⟨hv, hvW⟩
    rw [mpullback_comp_at (Φ.mdifferentiableAt (by simp) hv)
      ((hGW _ hvW).mdifferentiableAt (by simp)), ← hσ₁_def]
    exact (congrFun (mpullback_eq_flat (Φ : StdSpace (Fin n) → StdSpace (Fin n)) σ₁) v).trans
      (hpb v hv)
  · filter_upwards [hfix, hGu] with s h₁ h₂
    rw [comp_apply, h₁, h₂]

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ E'] in
/-- Let `H : StdSpace (Fin n) → M` be a local diffeomorphism at `0` which pulls `σ` back to
`stdForm` near `0` and agrees near `0` with `u : E' → M` along `ι`. Then some chart `e₀` of `M`,
a restriction of the local inverse of `H`, pulls `stdForm` back to `σ` on its source and carries
`u s` to `ι s` for `s` near `0`. -/
private theorem exists_partialDiffeomorph_apply_eq_of_mpullback_eq {H : StdSpace (Fin n) → M}
    (hH : IsLocalDiffeomorphAt 𝓘(ℝ, StdSpace (Fin n)) I ∞ H 0)
    (hHpb : ∀ᶠ v in 𝓝 0, TauCeti.mpullback 𝓘(ℝ, StdSpace (Fin n)) I H σ.val v =
      (stdForm (Fin n)).constSmooth.val v)
    {u : E' → M} {ι : E' →L[ℝ] StdSpace (Fin n)} (hHu : ∀ᶠ s in 𝓝 0, H (ι s) = u s) :
    ∃ e₀ : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      (∀ x ∈ e₀.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e₀ x v) (mvfderiv I e₀ x w)) ∧
      ∀ᶠ s in 𝓝 0, u s ∈ e₀.source ∧ e₀ (u s) = ι s := by
  set Λ := hH.localInverse
  obtain ⟨O, hOsub, hOo, h0O⟩ := mem_nhds_iff.1 hHpb
  have hOΛ : IsOpen (Λ.source ∩ Λ ⁻¹' O) := Λ.toOpenPartialHomeomorph.isOpen_inter_preimage hOo
  refine ⟨Λ.restrOpen _ hOΛ, fun x hx v w ↦ ?_, ?_⟩
  · -- `Λ` pulls `stdForm` back to `σ` at `x`, since `H^* σ = stdForm` at `Λ x`.
    rw [PartialDiffeomorph.restrOpen_source] at hx
    obtain ⟨hxΛ, -, hxO⟩ := hx
    rw [PartialDiffeomorph.coe_restrOpen, SmoothBundleForm.eval₂_apply,
      ← hH.mpullback_localInverse_apply_eq (by simp) hxΛ (hOsub hxO),
      mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply]
    exact SymplecticForm.eval₂_constSmooth_mfderiv_eq _ _ x v w
  · -- For `s` near `0`, `u s = H (ι s)` lies in the source of `Λ`, which sends it to `ι s ∈ O`.
    have hιt : ∀ᶠ s in 𝓝 (0 : E'), ι s ∈ Λ.target ∩ O :=
      ι.continuous.continuousAt.preimage_mem_nhds (by
        rw [map_zero]
        exact (Λ.open_target.inter hOo).mem_nhds ⟨hH.localInverse_mem_target, h0O⟩)
    have hHs : ∀ᶠ s in 𝓝 (0 : E'), H (ι s) ∈ Λ.source :=
      (hH.contMDiffAt.continuousAt.comp_of_eq ι.continuous.continuousAt
        (map_zero ι)).preimage_mem_nhds
        (Λ.open_source.mem_nhds (by simpa using hH.localInverse_mem_source))
    filter_upwards [hHu, hιt, hHs] with s h₁ h₂ h₃
    have hΛ : Λ (H (ι s)) = ι s := hH.localInverse_left_inv h₂.1
    rw [← h₁, PartialDiffeomorph.restrOpen_source, PartialDiffeomorph.coe_restrOpen]
    exact ⟨⟨h₃, h₃, by rw [mem_preimage, hΛ]; exact h₂.2⟩, hΛ⟩

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
  have h0t : (0 : E') ∈ c.target := hc₀ ▸ c.map_source hq₀
  have hcs0 : c.symm 0 = q₀ := hc₀ ▸ c.left_inv hq₀
  have hu : ∀ᶠ s in 𝓝 0, ContMDiffAt 𝓘(ℝ, E') I ∞ (f ∘ c.symm) s := by
    filter_upwards [c.open_target.mem_nhds h0t] with s hs
    exact f.contMDiff.contMDiffAt.comp s
      (c.symm.contMDiffOn.contMDiffAt (c.symm.open_source.mem_nhds hs))
  have hinj : Injective (mfderiv 𝓘(ℝ, E') I (f ∘ c.symm) 0) := by
    rw [mfderiv_comp 0 (f.contMDiff.mdifferentiableAt (by simp))
      (c.symm.mdifferentiableAt (by simp) (by simpa using h0t))]
    exact (f.isImmersion.mfderiv_injective (by simp) _).comp
      (c.symm.isInvertible_mfderiv (by simp) (by simpa using h0t)).injective
  -- Extend `f ∘ c⁻¹` along `ι`, then correct the extension to `H`, with `H^* σ = stdForm`.
  have hdim : finrank ℝ (StdSpace (Fin n)) = finrank ℝ E := by
    rw [finrank_stdSpace, Fintype.card_fin, hn]
  obtain ⟨G, hG, hGu⟩ := exists_localDiffeomorph_extend hι hu hinj hdim
  obtain ⟨H, hH, hHpb, hHu⟩ := exists_localDiffeomorph_mpullback_eq hσ hcl hG hι hGu hc
  -- A restriction `e₀` of the local inverse of `H` carries `f ∘ c⁻¹` to `ι` near `0`.
  obtain ⟨e₀, he₀σ, hfe₀⟩ := exists_partialDiffeomorph_apply_eq_of_mpullback_eq hH hHpb hHu
  -- Since `f` is an embedding, a smaller source meets the image of `f` only along `range ι`.
  obtain ⟨π, hπ⟩ := (ι : E' →ₗ[ℝ] StdSpace (Fin n)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hι)
  obtain ⟨U, hUo, hU0, hUsub, hU⟩ := f.isEmbedding.isInducing.exists_isOpen_inter_range_eq
    (c.symm.toOpenPartialHomeomorph.map_nhds_eq (by simpa using h0t)).ge
    e₀.toOpenPartialHomeomorph (LinearMap.toContinuousLinearMap π).continuous
    (fun s ↦ LinearMap.congr_fun hπ s) (by simpa using hfe₀)
  rw [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hcs0] at hU0
  have he₀q₀ : e₀ (f q₀) = 0 := by
    have h := hfe₀.self_of_nhds.2
    rwa [comp_apply, hcs0, map_zero] at h
  replace hUsub : U ⊆ e₀.source := by simpa using hUsub
  refine ⟨e₀.restrOpen U hUo, ?_, by rwa [PartialDiffeomorph.coe_restrOpen], fun x hx ↦ ?_, ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hUsub hU0, hU0⟩
  · rw [PartialDiffeomorph.restrOpen_source] at hx
    rw [PartialDiffeomorph.coe_restrOpen]
    exact he₀σ x hx.1
  · rw [PartialDiffeomorph.restrOpen_source, PartialDiffeomorph.coe_restrOpen,
      inter_eq_right.2 hUsub]
    simpa using hU

omit [FiniteDimensional ℝ E] [BoundarylessManifold I M] [FiniteDimensional ℝ E'] in
/-- Let `e` be a chart of `M` pulling `stdForm` back to `σ` whose source meets the image of a smooth
embedding `f` exactly where `e` takes values in the range of an injective linear map
`ι : E' → StdSpace (Fin n)`. At each point `f q` of the source, the derivative of `e` carries the
`σ`-orthogonal of the tangent image `df_q (T_q Q)` onto the `ω₀`-orthogonal of the range of `ι`. -/
private theorem image_mvfderiv_orthogonal_range_mfderiv {hσ : σ.IsNondegenerate}
    {e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞}
    (he : ∀ x ∈ e.source, ∀ v w : TangentSpace I x,
      σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w))
    (f : SmoothEmbedding J I ∞ Q M) {ι : E' →L[ℝ] StdSpace (Fin n)} (hι : Injective ι)
    (hrange : e.source ∩ range f = e.source ∩ e ⁻¹' range ι) {q : Q} (hq : f q ∈ e.source) :
    mvfderiv I e (f q) '' (hσ.symplecticFormAt (f q)).orthogonal
        (LinearMap.range (mfderiv J I f q).toLinearMap) =
      {v | ∀ z ∈ range ι, stdForm (Fin n) z v = 0} := by
  -- Near `q`, `e ∘ f` takes values in the range of `ι`, so it is `ι ∘ g` with `g = π ∘ e ∘ f`.
  obtain ⟨π, hπ⟩ := (ι : E' →ₗ[ℝ] StdSpace (Fin n)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hι)
  set π' := LinearMap.toContinuousLinearMap π
  have hev : e ∘ f =ᶠ[𝓝 q] ι ∘ (π' ∘ e ∘ f) := by
    filter_upwards [f.contMDiff.continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with q' hq'
    obtain ⟨-, s, hs⟩ := hrange.subset (⟨hq', q', rfl⟩ : f q' ∈ e.source ∩ range f)
    have hπs : π (ι s) = s := LinearMap.congr_fun hπ s
    simp [← hs, π', hπs]
  have hed := e.mdifferentiableAt (by simp) hq
  have hfd := f.contMDiff.mdifferentiableAt (x := q) (by simp)
  have hmap (v : TangentSpace J q) : mvfderiv I e (f q) (mfderiv J I f q v) ∈ range ι := by
    have hg : MDifferentiableAt J 𝓘(ℝ, E') (π' ∘ e ∘ f) q :=
      π'.mdifferentiableAt.comp q (hed.comp q hfd)
    rw [← mvfderiv_comp_apply q hed hfd, hev.mvfderiv_eq, ι.mvfderiv_comp_apply hg]
    exact mem_range_self _
  -- By dimensions, `de ∘ df` maps `T_q Q` onto the range of `ι`.
  have hrange' : LinearMap.range ((mvfderiv I e (f q)).toLinearMap ∘ₗ
      (mfderiv J I f q).toLinearMap) = LinearMap.range ι.toLinearMap := by
    refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, rfl⟩; exact hmap v) ?_
    have hinj : Injective ((mvfderiv I e (f q)).toLinearMap ∘ₗ (mfderiv J I f q).toLinearMap) := by
      rw [LinearMap.coe_comp]
      exact (e.bijective_mvfderiv (by simp) hq).1.comp
        (f.isImmersion.mfderiv_injective (by simp) q)
    rw [LinearMap.finrank_range_of_inj hinj, LinearMap.finrank_range_of_inj hι,
      finrank_tangentSpace]
  -- `de` is a linear symplectomorphism, so it carries `σ`-orthogonals to `ω₀`-orthogonals.
  set A := LinearEquiv.ofBijective (mvfderiv I e (f q)).toLinearMap
    (e.bijective_mvfderiv (by simp) hq)
  have hA : SymplecticForm.IsSymplectomorphism (hσ.symplecticFormAt (f q)) (stdForm (Fin n)) A :=
    SymplecticForm.isSymplectomorphism_iff.2 fun v w ↦
      (he _ hq v w).symm.trans (symplecticFormAt_apply hσ (f q) v w).symm
  rw [LinearMap.range_comp] at hrange'
  have h := congrArg (fun W : Submodule ℝ _ ↦ (W : Set (StdSpace (Fin n))))
    (hA.map_orthogonal (LinearMap.range (mfderiv J I f q).toLinearMap))
  rw [Submodule.map_coe] at h
  have hA' : (A : TangentSpace I (f q) →ₗ[ℝ] StdSpace (Fin n)) =
      (mvfderiv I e (f q)).toLinearMap :=
    LinearMap.ext fun v ↦ LinearEquiv.ofBijective_apply _ v
  rw [hA', hrange', ContinuousLinearMap.coe_coe] at h
  refine h.trans ?_
  ext v
  simp [SymplecticForm.mem_orthogonal_iff]

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
  let ι : E' →L[ℝ] StdSpace (Fin (k + m)) :=
    (stdInl k m).comp (LinearMap.toContinuousLinearMap (ofX (Fin k) ∘ₗ L.toLinearMap))
  have hιapp (a : E') : ι a = stdInl k m (ofX (Fin k) (L a)) := by
    simp only [ι, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  have hιF : ⇑ι = stdInl k m ∘ ofX (Fin k) ∘ L := funext hιapp
  have hι : Injective ι := by
    rw [hιF]
    exact injective_stdInl.comp (injective_ofX.comp L.injective)
  have hstd (a b : E') : stdForm (Fin (k + m)) (ι a) (ι b) = 0 := by
    rw [hιapp, hιapp, stdForm_stdInl, stdForm_ofX]
  have hrange : range ι = {z | z.y = 0 ∧ ∀ j : Fin (k + m), k ≤ (j : ℕ) → z.x j = 0} := by
    rw [hιF, ← comp_assoc, range_comp, L.surjective.range_eq, image_univ, range_stdInl_ofX]
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


/-! ### Coisotropic submanifolds -/

section Coisotropic

variable [J.Boundaryless]

omit [BoundarylessManifold I M] [BoundarylessManifold J Q] in
/-- For a coisotropic smooth embedding `f`, of dimension `k + 2r`, into a manifold of dimension
`2(k + r)` with a closed nondegenerate two-form `σ`, and any linear identification `L` of the
model of `Q` with `ℝᵏ × StdSpace (Fin r)`, some chart `c` of `Q` with `c q₀ = 0` reads `f^* σ`, near
`0`, as the pull-back of `stdForm (Fin r)` along the second component of `L`. -/
private theorem IsCoisotropicMap.exists_chart_eval₂_eq {hσ : σ.IsNondegenerate}
    {f : SmoothEmbedding J I ∞ Q M} (h : hσ.IsCoisotropicMap J f) (hcl : σ.IsClosed) {k r : ℕ}
    (hn : finrank ℝ E = 2 * (k + r))
    (L : E' ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r)) (q₀ : Q) :
    ∃ c : PartialDiffeomorph J 𝓘(ℝ, E') Q E' ∞, q₀ ∈ c.source ∧ c q₀ = 0 ∧
      ∀ᶠ s in 𝓝 (0 : E'), ∀ a b : TangentSpace 𝓘(ℝ, E') s,
        σ.eval₂ (f (c.symm s)) (mfderiv 𝓘(ℝ, E') I (f ∘ c.symm) s a)
          (mfderiv 𝓘(ℝ, E') I (f ∘ c.symm) s b) = stdForm (Fin r) (L a).2 (L b).2 := by
  have hk : finrank ℝ E' + k = finrank ℝ E := by
    rw [hn, L.toLinearEquiv.finrank_eq, Module.finrank_prod, finrank_euclideanSpace,
      finrank_stdSpace]
    simp
    ring
  obtain ⟨c, hcq, hc0, hc⟩ :=
    h.exists_partialDiffeomorph_eval₂_eq_stdForm f.isImmersion f.contMDiff hcl hk L q₀
  refine ⟨c, hcq, hc0, ?_⟩
  filter_upwards [c.open_target.mem_nhds (hc0 ▸ c.map_source hcq), hc] with s hs hcs a b
  have hcd : MDifferentiableAt 𝓘(ℝ, E') J c.symm s :=
    c.symm.mdifferentiableAt (by simp) (by simpa using hs)
  rw [mfderiv_comp_apply s (f.contMDiff.mdifferentiableAt (by simp)) hcd,
    mfderiv_comp_apply s (f.contMDiff.mdifferentiableAt (by simp)) hcd,
    ← SmoothForm.eval₂_mpullback f f.contMDiff]
  exact hcs a b

omit [BoundarylessManifold J Q] in
/-- `IsCoisotropicMap.exists_darbouxChart_inter_range_eq` when `n = k + r`. -/
private theorem IsCoisotropicMap.exists_darbouxChart_inter_range_eq_of_eq_add
    {hσ : σ.IsNondegenerate} {f : SmoothEmbedding J I ∞ Q M} (h : hσ.IsCoisotropicMap J f)
    (hcl : σ.IsClosed) {k r : ℕ} (hkr : n = k + r) (hn : finrank ℝ E = 2 * n)
    (hk : finrank ℝ E' = k + 2 * r) (q₀ : Q) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f = e.source ∩ e ⁻¹' {z | ∀ j : Fin n, (j : ℕ) < k → z.y j = 0} ∧
      ∀ q, f q ∈ e.source →
        mvfderiv I e (f q) '' (hσ.symplecticFormAt (f q)).orthogonal
          (LinearMap.range (mfderiv J I f q).toLinearMap) =
        {v | v.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → v.x j = 0} := by
  subst hkr
  let L : E' ≃L[ℝ] EuclideanSpace ℝ (Fin k) × StdSpace (Fin r) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hk]; omega)
  obtain ⟨c, hq₀, hc₀, hc⟩ := h.exists_chart_eval₂_eq hcl hn L q₀
  -- `ι` puts the leaf coordinates into the first `k` coordinates `x`, and the coordinates of the
  -- space of leaves into the last `r` coordinate pairs.
  let ι : E' →L[ℝ] StdSpace (Fin (k + r)) := LinearMap.toContinuousLinearMap
    (((stdInl k r).toLinearMap ∘ₗ ofX (Fin k) ∘ₗ
        (EuclideanSpace.equiv (Fin k) ℝ).toLinearMap ∘ₗ LinearMap.fst ℝ _ _ +
      (stdInr k r).toLinearMap ∘ₗ LinearMap.snd ℝ _ _) ∘ₗ L.toLinearMap)
  have hιapp (s : E') :
      ι s = stdInl k r (ofX (Fin k) (EuclideanSpace.equiv (Fin k) ℝ (L s).1)) +
        stdInr k r (L s).2 := by
    simp [ι]
  have hιF : ⇑ι = (fun p : (Fin k → ℝ) × StdSpace (Fin r) ↦
      stdInl k r (ofX (Fin k) p.1) + stdInr k r p.2) ∘
        Prod.map (EuclideanSpace.equiv (Fin k) ℝ) id ∘ L :=
    funext hιapp
  have hι : Injective ι := by
    rw [hιF]
    exact injective_stdInl_ofX_add_stdInr.comp
      (((EuclideanSpace.equiv (Fin k) ℝ).injective.prodMap injective_id).comp L.injective)
  have hrange : range ι = {z | ∀ j : Fin (k + r), (j : ℕ) < k → z.y j = 0} := by
    rw [hιF, range_comp, range_comp, L.surjective.range_eq, image_univ,
      ((EuclideanSpace.equiv (Fin k) ℝ).surjective.prodMap surjective_id).range_eq, image_univ,
      range_stdInl_ofX_add_stdInr]
  -- `ι` pulls `stdForm` back to the pull-back of `stdForm (Fin r)` along the second component.
  have hform (a b : E') : stdForm (Fin (k + r)) (ι a) (ι b) = stdForm (Fin r) (L a).2 (L b).2 := by
    rw [hιapp, hιapp, stdForm_stdInl_add_stdInr, stdForm_ofX, zero_add]
  obtain ⟨e, h₁, h₂, h₃, h₄⟩ := hσ.exists_darbouxChart_inter_range_eq_of_chart hcl hn f c hq₀ hc₀
    hι (by
      filter_upwards [hc] with s hs a b
      exact (hs a b).trans (hform a b).symm)
  refine ⟨e, h₁, h₂, h₃, by rw [h₄, hrange], fun q hq ↦ ?_⟩
  rw [image_mvfderiv_orthogonal_range_mfderiv h₃ f hι h₄ hq, hrange]
  ext v
  exact forall_stdForm_eq_zero_iff_y_eq_zero_and_x_eq_zero k v

omit [BoundarylessManifold J Q] in
/-- **Darboux charts adapted to a coisotropic submanifold.** Let `f : Q → M` be a coisotropic smooth
embedding, of dimension `2n - k`, into a manifold of dimension `2n` with a closed nondegenerate
two-form `σ`. Near each `f q₀` there is a chart `e` of `M` with `e (f q₀) = 0` pulling `stdForm`
back to `σ`, whose source meets the image of `f` exactly where the coordinates `yⱼ` of `e` vanish
for all `j < k`. Moreover, at each point `f q` of the source, the derivative of `e` carries the
symplectic orthogonal `(df_q (T_q Q))^σ`, the tangent space of the characteristic leaf, onto the
span of the first `k` vectors `∂/∂xⱼ`: the vectors with `y = 0` and `xⱼ = 0` for all `j ≥ k`.

Milestone: *Darboux charts adapted to submanifolds*. -/
theorem IsCoisotropicMap.exists_darbouxChart_inter_range_eq
    {hσ : σ.IsNondegenerate} {f : SmoothEmbedding J I ∞ Q M} (h : hσ.IsCoisotropicMap J f)
    (hcl : σ.IsClosed) (hn : finrank ℝ E = 2 * n) {k : ℕ} (hk : finrank ℝ E' = 2 * n - k)
    (q₀ : Q) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, StdSpace (Fin n)) M (StdSpace (Fin n)) ∞,
      f q₀ ∈ e.source ∧ e (f q₀) = 0 ∧
      (∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        σ.eval₂ x v w = stdForm (Fin n) (mvfderiv I e x v) (mvfderiv I e x w)) ∧
      e.source ∩ range f = e.source ∩ e ⁻¹' {z | ∀ j : Fin n, (j : ℕ) < k → z.y j = 0} ∧
      ∀ q, f q ∈ e.source →
        mvfderiv I e (f q) '' (hσ.symplecticFormAt (f q)).orthogonal
          (LinearMap.range (mfderiv J I f q).toLinearMap) =
        {v | v.y = 0 ∧ ∀ j : Fin n, k ≤ (j : ℕ) → v.x j = 0} := by
  -- A coisotropic submanifold has at least half the dimension, so `k ≤ n` unless `n = 0`.
  have hle := h.finrank_le_two_mul_finrank q₀
  by_cases hkn : k ≤ n
  · exact h.exists_darbouxChart_inter_range_eq_of_eq_add hcl (Nat.add_sub_cancel' hkn).symm hn
      (by omega) q₀
  · obtain rfl : n = 0 := by omega
    obtain ⟨e, h₁, h₂, h₃, h₄, h₅⟩ :=
      h.exists_darbouxChart_inter_range_eq_of_eq_add hcl (k := 0) (r := 0) rfl hn (by omega) q₀
    refine ⟨e, h₁, h₂, h₃, by simpa using h₄, fun q hq ↦ (h₅ q hq).trans ?_⟩
    -- Both sets are `{v | v.y = 0}`, since `Fin 0` is empty.
    ext v
    exact ⟨fun h ↦ ⟨h.1, fun j ↦ j.elim0⟩, fun h ↦ ⟨h.1, fun j ↦ j.elim0⟩⟩

end Coisotropic

end TauCeti.SmoothTwoForm.IsNondegenerate
