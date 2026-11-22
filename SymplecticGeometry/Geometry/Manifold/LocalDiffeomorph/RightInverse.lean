/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# First-order right inverses near a compact set, and correcting the ends of a family

Let `F` be a finite-dimensional real normed space and `M` a boundaryless manifold of the same
dimension. If `f, j : F → M` are smooth near a compact set `K`, agree on `K` with the same
derivative there, and `j` is injective on `K` with injective derivative along `K`, then `f` is an
injective local diffeomorphism near `K`, and `g = f⁻¹ ∘ j` is a smooth map near `K` with
`f ∘ g = j`, which is the identity, with derivative the identity, along `K`
(`SymplecticGeometry.exists_comp_eq_of_mfderiv_eq`).

Applied to the two end slices of a family `k'` over `[0, 1]` of maps `F → M`, this gives maps
`g₀` and `g₁`, and the family `k t = k' t ∘ ((1 - t) g₀ + t g₁)` agrees with `k'` along `K` to
first order and has prescribed ends on a neighbourhood of `K`
(`SymplecticGeometry.exists_contMDiffOn_forall_eq_mfderiv_eq`). This is the step of
McDuff–Salamon's Theorem A.2.1(iii) that fixes both ends of a family of embeddings.

## Main results

* `SymplecticGeometry.exists_comp_eq_of_mfderiv_eq`: a first-order right inverse of `f` against
  `j` near a compact set.
* `SymplecticGeometry.exists_contMDiffOn_forall_eq_mfderiv_eq`: correcting the ends of a family
  of maps along a compact set.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem A.2.1(iii).
-/

public section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A first-order right inverse near a compact set.** Let `M` be a boundaryless manifold of
the dimension of `F`, let `f, j : F → M` be smooth on an open `U ⊇ K`, with `K` compact, and let
`f` and `j` agree on `K` with the same derivative there, `j` being injective on `K` with
injective derivative along `K`. Then there is a map `g`, smooth on an open `W ⊇ K` and mapping it
into `U`, with `f ∘ g = j` on `W`, which is the identity with derivative the identity along
`K`. -/
theorem exists_comp_eq_of_mfderiv_eq [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) {K U : Set F} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f j : F → M}
    (hf : ContMDiffOn 𝓘(ℝ, F) I ∞ f U)
    (hj : ContMDiffOn 𝓘(ℝ, F) I ∞ j U) (hfj : ∀ z ∈ K, f z = j z)
    (hd : ∀ z ∈ K, mfderiv 𝓘(ℝ, F) I f z = mfderiv 𝓘(ℝ, F) I j z)
    (himm : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, F) I j z)) (hinj : InjOn j K) :
    ∃ g : F → F, ∃ W, IsOpen W ∧ K ⊆ W ∧
      ContDiffOn ℝ ∞ g W ∧ MapsTo g W U ∧ (∀ z ∈ W, f (g z) = j z) ∧ (∀ z ∈ K, g z = z) ∧
      ∀ z ∈ K, fderiv ℝ g z = ContinuousLinearMap.id ℝ _ := by
  -- `f` is a local diffeomorphism at each point of `K`, and injective on `K`.
  have hloc (z : F) (hz : z ∈ K) :
      IsLocalDiffeomorphAt 𝓘(ℝ, F) I ∞ f z :=
    isLocalDiffeomorphAt_of_injective_mfderiv hf hU (hKU hz) BoundarylessManifold.isInteriorPoint
      (by simp) (hd z hz ▸ himm z hz) hdim
  have hinjf : InjOn f K := fun x hx y hy h ↦ hinj hx hy (by rwa [← hfj x hx, ← hfj y hy])
  obtain ⟨V₁, hV₁o, hKV₁, hV₁inj, hV₁loc⟩ :=
    hinjf.exists_isOpen_superset_isLocalDiffeomorphOn hK hloc
  set V := V₁ ∩ U
  have hVo : IsOpen V := hV₁o.inter hU
  have hVinj : InjOn f V := hV₁inj.mono inter_subset_left
  have hVloc : IsLocalDiffeomorphOn 𝓘(ℝ, F) I ∞ f V :=
    fun x ↦ hV₁loc ⟨x, x.property.1⟩
  have hfV : IsOpen (f '' V) := hVloc.isLocalHomeomorphOn.isOpen_image hVo
  set g := invFunOn f V ∘ j
  set W := U ∩ j ⁻¹' (f '' V)
  have hmem (z : F) (hz : z ∈ W) : ∃ a ∈ V, f a = j z := hz.2
  have hgf (z : F) (hz : z ∈ W) : f (g z) = j z := invFunOn_eq (hmem z hz)
  have hKW : K ⊆ W := fun z hz ↦ ⟨hKU hz, z, ⟨hKV₁ hz, hKU hz⟩, hfj z hz⟩
  have hgK (z : F) (hz : z ∈ K) : g z = z := by
    simp only [g, comp_apply, ← hfj z hz]
    exact hVinj.leftInvOn_invFunOn ⟨hKV₁ hz, hKU hz⟩
  have hWo : IsOpen W := hj.continuousOn.isOpen_inter_preimage hU hfV
  have hg : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ g W :=
    (hVloc.contMDiffOn_invFunOn hVo hVinj).comp (hj.mono inter_subset_left) fun z hz ↦ hz.2
  refine ⟨g, W, hWo, hKW, contMDiffOn_iff_contDiffOn.1 hg,
    fun z hz ↦ (invFunOn_mem (hmem z hz)).2, hgf, hgK, fun z hz ↦ ?_⟩
  -- Differentiating `f ∘ g = j` at `z ∈ K`, where `g z = z`, gives `df ∘ dg = dj = df`.
  have hgd : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) g z :=
    (hg.contMDiffAt (hWo.mem_nhds (hKW hz))).mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, F) I f (g z) := by
    rw [hgK z hz]
    exact (hf.contMDiffAt (hU.mem_nhds (hKU hz))).mdifferentiableAt (by simp)
  have hcomp : f ∘ g =ᶠ[𝓝 z] j :=
    Filter.eventually_of_mem (hWo.mem_nhds (hKW hz)) fun y hy ↦ hgf y hy
  have hchain := mfderiv_comp z hfd hgd
  rw [hcomp.mfderiv_eq, ← hd z hz] at hchain
  have hfg : mfderiv 𝓘(ℝ, F) I f (g z) = mfderiv 𝓘(ℝ, F) I f z := by
    rw [hgK z hz]
  rw [hfg, mfderiv_eq_fderiv] at hchain
  ext1 v
  -- `tangentSpaceCast` and `NormedSpace.fromTangentSpace` in `hchain` are identities by definition.
  exact (hd z hz ▸ himm z hz) (by exact (congrArg (fun L ↦ L v) hchain).symm)

/-- **Correcting the ends of a family.** Let `M` be a boundaryless manifold of the dimension of
`F`, and let `k'` be a family of maps `F → M` over `[0, 1]`, jointly smooth on `[0, 1] × U` for an
open `U` containing a compact `K`. Let `j₀` and `j₁` be smooth on `U`, injective on `K` with
injective derivative along `K`, and let the slice of `k'` at time `0` (`1`) agree with `j₀`
(`j₁`) on `K`, with the same derivative there. Then there is a family `k`, jointly smooth on
`[0, 1] × W` for an open `W ⊇ K`, that agrees with `k'` on `K` at every time, with the same
derivative along `K`, and whose slices at times `0` and `1` are `j₀` and `j₁` on `W`. This is the
end correction of McDuff–Salamon, Theorem A.2.1(iii). -/
theorem exists_contMDiffOn_forall_eq_mfderiv_eq [FiniteDimensional ℝ E] [I.Boundaryless]
    [T2Space M] (hdim : Module.finrank ℝ F = Module.finrank ℝ E) {K U : Set F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {k' : unitInterval × F → M}
    (hk' : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) I ∞ k' (univ ×ˢ U))
    {j₀ j₁ : F → M} (hj₀ : ContMDiffOn 𝓘(ℝ, F) I ∞ j₀ U)
    (hj₁ : ContMDiffOn 𝓘(ℝ, F) I ∞ j₁ U)
    (h₀ : ∀ z ∈ K, k' (0, z) = j₀ z) (h₁ : ∀ z ∈ K, k' (1, z) = j₁ z)
    (hd₀ : ∀ z ∈ K, mfderiv 𝓘(ℝ, F) I (fun z ↦ k' (0, z)) z =
      mfderiv 𝓘(ℝ, F) I j₀ z)
    (hd₁ : ∀ z ∈ K, mfderiv 𝓘(ℝ, F) I (fun z ↦ k' (1, z)) z =
      mfderiv 𝓘(ℝ, F) I j₁ z)
    (himm₀ : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, F) I j₀ z))
    (himm₁ : ∀ z ∈ K, Injective (mfderiv 𝓘(ℝ, F) I j₁ z))
    (hinj₀ : InjOn j₀ K) (hinj₁ : InjOn j₁ K) :
    ∃ k : unitInterval × F → M, ∃ W, IsOpen W ∧ K ⊆ W ∧
      ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) I ∞ k (univ ×ˢ W) ∧
      (∀ t, ∀ z ∈ K, k (t, z) = k' (t, z)) ∧
      (∀ t, ∀ z ∈ K, mfderiv 𝓘(ℝ, F) I (fun z ↦ k (t, z)) z =
        mfderiv 𝓘(ℝ, F) I (fun z ↦ k' (t, z)) z) ∧
      (∀ z ∈ W, k (0, z) = j₀ z) ∧ ∀ z ∈ W, k (1, z) = j₁ z := by
  have hslice (t : unitInterval) :
      ContMDiffOn 𝓘(ℝ, F) I ∞ (fun z ↦ k' (t, z)) U :=
    hk'.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun z hz ↦ ⟨mem_univ _, hz⟩
  -- Right inverses `g₀`, `g₁` of the end slices against `j₀`, `j₁`, near `K`.
  obtain ⟨g₀, W₀, hW₀, hKW₀, hg₀, -, hg₀j, hg₀K, hg₀d⟩ :=
    exists_comp_eq_of_mfderiv_eq hdim hK hU hKU (hslice 0) hj₀ h₀ hd₀ himm₀ hinj₀
  obtain ⟨g₁, W₁, hW₁, hKW₁, hg₁, -, hg₁j, hg₁K, hg₁d⟩ :=
    exists_comp_eq_of_mfderiv_eq hdim hK hU hKU (hslice 1) hj₁ h₁ hd₁ himm₁ hinj₁
  -- The segment `G t = (1 - t) g₀ + t g₁`, which is the identity on `K`.
  set G : unitInterval × F → F :=
    fun p ↦ (1 - (p.1 : ℝ)) • g₀ p.2 + (p.1 : ℝ) • g₁ p.2
  have hGK (t : unitInterval) (z : F) (hz : z ∈ K) : G (t, z) = z := by
    simp only [G, hg₀K z hz, hg₁K z hz, ← add_smul, sub_add_cancel, one_smul]
  have hc : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ) ∞
      (fun p : unitInterval × F ↦ (p.1 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hW₀₁ : IsOpen (W₀ ∩ W₁) := hW₀.inter hW₁
  have hG : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ G
      (univ ×ˢ (W₀ ∩ W₁)) :=
    ((contMDiff_const.sub hc).contMDiffOn.smul ((contMDiffOn_iff_contDiffOn.2 hg₀).comp
      contMDiffOn_snd fun p (hp : p ∈ univ ×ˢ (W₀ ∩ W₁)) ↦ hp.2.1)).add
      (hc.contMDiffOn.smul ((contMDiffOn_iff_contDiffOn.2 hg₁).comp
      contMDiffOn_snd fun p (hp : p ∈ univ ×ˢ (W₀ ∩ W₁)) ↦ hp.2.2))
  -- A neighbourhood `W` of `K` on which `G t` stays in `U` at every time.
  obtain ⟨u, W, -, hW, hu, hKW, hWN⟩ := generalized_tube_lemma isCompact_univ hK
    (hG.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hW₀₁) hU)
    fun p (hp : p ∈ univ ×ˢ K) ↦ ⟨⟨mem_univ _, hKW₀ hp.2, hKW₁ hp.2⟩, by
      rw [mem_preimage, ← Prod.mk.eta (p := p), hGK _ _ hp.2]; exact hKU hp.2⟩
  have hWN' : univ ×ˢ W ⊆ univ ×ˢ (W₀ ∩ W₁) ∩ G ⁻¹' U :=
    (prod_mono hu subset_rfl).trans hWN
  have hG₀ (z : F) : G (0, z) = g₀ z := by simp [G]
  have hG₁ (z : F) : G (1, z) = g₁ z := by simp [G]
  refine ⟨fun p ↦ k' (p.1, G p), W, hW, hKW,
    hk'.comp (contMDiffOn_fst.prodMk (hG.mono fun p hp ↦ (hWN' hp).1))
      fun p hp ↦ ⟨mem_univ _, (hWN' hp).2⟩,
    fun t z hz ↦ by simp only [hGK t z hz], fun t z hz ↦ ?_,
    fun z hz ↦ by simp only [hG₀, hg₀j z (hWN' (mk_mem_prod (mem_univ 0) hz)).1.2.1],
    fun z hz ↦ by simp only [hG₁, hg₁j z (hWN' (mk_mem_prod (mem_univ 1) hz)).1.2.2]⟩
  -- Along `K`, the slice `k' t ∘ G t` has the derivative of `k' t`, since `d (G t) = id`.
  have hg₀z : DifferentiableAt ℝ g₀ z :=
    (hg₀.contDiffAt (hW₀.mem_nhds (hKW₀ hz))).differentiableAt (by simp)
  have hg₁z : DifferentiableAt ℝ g₁ z :=
    (hg₁.contDiffAt (hW₁.mem_nhds (hKW₁ hz))).differentiableAt (by simp)
  have hGf : HasFDerivAt (fun z ↦ G (t, z)) (ContinuousLinearMap.id ℝ (F)) z := by
    have h := (hg₀z.hasFDerivAt.const_smul (1 - (t : ℝ))).add
      (hg₁z.hasFDerivAt.const_smul (t : ℝ))
    rwa [hg₀d z hz, hg₁d z hz, ← add_smul, sub_add_cancel, one_smul] at h
  have hGd : fderiv ℝ (fun z ↦ G (t, z)) z = ContinuousLinearMap.id ℝ _ := hGf.fderiv
  have hGz : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F)
      (fun z ↦ G (t, z)) z :=
    hGf.differentiableAt.mdifferentiableAt
  have hk'z : MDifferentiableAt 𝓘(ℝ, F) I (fun z ↦ k' (t, z)) (G (t, z)) := by
    rw [hGK t z hz]
    exact ((hslice t).contMDiffAt (hU.mem_nhds (hKU hz))).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp (g := fun z ↦ k' (t, z)) z hk'z hGz
  have hk'G : mfderiv 𝓘(ℝ, F) I (fun z ↦ k' (t, z)) (G (t, z)) =
      mfderiv 𝓘(ℝ, F) I (fun z ↦ k' (t, z)) z := by
    rw [hGK t z hz]
  rw [hk'G, mfderiv_eq_fderiv, hGd] at hchain
  exact hchain

end SymplecticGeometry

end
