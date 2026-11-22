/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SymplecticGeometry.Geometry.Manifold.RegularValue.LevelCollar
public import SymplecticGeometry.Topology.VectorBundle.Orientation.ArgumentPrinciple
public import TauCeti.Geometry.Manifold.RegularValue.Fibre
public import TauCeti.Geometry.Manifold.Sard.EqualDimension
public import TauCeti.Topology.VectorBundle.Hom

/-!
# The argument principle on a split closed surface

Let `M` be a closed smooth surface with a homological orientation `oM`, and let `g : M → ℝ` be a
smooth function with regular value `0`. It splits `M` into `Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`,
which meet along the level set `C = g⁻¹(0)`. By `SymplecticGeometry.isCollared_inclusion_levelSet`,
`Σ₁` is a compact surface whose boundary `C` is collared and whose interior is the open set
`{g < 0}`, oriented by the restriction of `oM`: this is the setting of the boundary degree
(`TauCeti.HomologicalOrientation.boundaryDegree`).

Let `L` be an oriented real plane bundle over `M`, `τ` a frame of `L` over `Σ₁` (linear
isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, carrying the orientation of `L` to
`Complex.orientation`), and `s` a nowhere-zero continuous section of `L` over `Σ₂`. Then the Euler
number of `L` is the boundary degree on `Σ₁` of `τ s / |τ s|` on `C`
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`).

## Proof

Read in the frame, `s` is a nowhere-zero map `C → ℂ`. Extend it to `M` by Tietze's theorem, and
modify the extension away from `C` so that it has finitely many zeros in `Σ₁`, none of them on `C`
(`SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`): take a smooth approximation, subtract a
small regular value of it (Sard's theorem, `TauCeti.dense_isRegularValue`), whose fibre is finite
(`TauCeti.IsRegularValue.finite_preimage`), and interpolate back to the extension in a band
`{-c < g ≤ 0}` where the extension stays away from `0`. Pulled back through the frame and glued
with `s` along `C`, this gives a continuous section `t` of `L` over `M` with finitely many zeros,
all in `{g < 0}` (`SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero`).

Adding up the local indices of `t` at its zeros gives the Euler number
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`). The
argument principle on `Σ₁`
(`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`) identifies the sum of the
local indices of `t` restricted to `{g < 0}` with the boundary degree, and the local indices on
`{g < 0}` and on `M` agree
(`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`).

## Main results

* `SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`: a continuous map on a compact manifold,
  nonzero on a level set of `g`, can be changed off that level set so that it has finitely many
  zeros in `{g ≤ 0}`, all in `{g < 0}`.
* `SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero`: a nowhere-zero section over `Σ₂`
  extends, through a frame over `Σ₁`, to a section over `M` with finitely many zeros, all in
  `{g < 0}`.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`: the Euler
  number is the boundary degree of the section over `Σ₂` read in the frame over `Σ₁`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: the
  first Chern number of a bundle over a closed surface computed from frames over the two sides of
  a splitting.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11: the Euler class evaluated through the zeros of a section.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 (Sard's theorem) and Theorem 6.21 (smooth approximation).
-/

public section

open Bundle Metric Module Set Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- On a compact smooth boundaryless manifold modelled on `E`, let `g : M → ℝ` be continuous and
`h₀ : M → V` continuous and nonzero on the level set `g⁻¹(0)`, where `dim V = dim E`. Then some
continuous `h : M → V` agrees with `h₀` on `g⁻¹(0)` and has finitely many zeros in `{g ≤ 0}`, all
in `{g < 0}`. -/
theorem exists_eq_on_levelSet_finite_zeros (hdim : finrank ℝ E = finrank ℝ V) {g : M → ℝ}
    (hg : Continuous g) (h₀ : C(M, V)) (hh₀ : ∀ x, g x = 0 → h₀ x ≠ 0) :
    ∃ h : C(M, V), (∀ x, g x = 0 → h x = h₀ x) ∧ {x | g x ≤ 0 ∧ h x = 0}.Finite ∧
      ∀ x, g x ≤ 0 → h x = 0 → g x < 0 := by
  -- A margin `c > 0` such that `‖h₀‖ ≥ c` wherever `|g| < c`.
  obtain ⟨c, hc, hcg⟩ : ∃ c > 0, ∀ x, |g x| < c → c ≤ ‖h₀ x‖ := by
    rcases isEmpty_or_nonempty M with hM | hM
    · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    have hψ : Continuous fun x ↦ max ‖h₀ x‖ |g x| := (continuous_norm.comp h₀.continuous).max
      hg.abs
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty hψ.continuousOn
    refine ⟨max ‖h₀ x₀‖ |g x₀|, ?_, fun x hx ↦ ?_⟩
    · by_contra hle
      have h1 : ‖h₀ x₀‖ = 0 := le_antisymm ((le_max_left _ _).trans (not_lt.1 hle)) (norm_nonneg _)
      have h2 : g x₀ = 0 := abs_eq_zero.1 (le_antisymm ((le_max_right _ _).trans (not_lt.1 hle))
        (abs_nonneg _))
      exact hh₀ x₀ h2 (norm_eq_zero.1 h1)
    · have := hx₀ (mem_univ x)
      simp only [mem_ofPred_eq] at this
      rcases le_max_iff.1 this with h | h
      · exact h
      · exact absurd (h.trans_lt hx) (lt_irrefl _)
  -- A smooth approximation `h₁` within `c / 2` of `h₀`.
  obtain ⟨h₁, hh₁⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E) (n := ⊤)
    (t := fun x ↦ ball (h₀ x) (c / 2)) (fun x ↦ convex_ball _ _) fun x ↦
      ⟨h₀ x, (h₀.continuous.tendsto x).eventually (ball_mem_nhds (h₀ x) (half_pos hc)) |>.mono
        fun y hy ↦ mem_ball_comm.1 hy⟩
  -- A regular value `w` of `h₁` of norm less than `c / 2`, by Sard's theorem.
  obtain ⟨w, hwreg, hw⟩ := (TauCeti.dense_isRegularValue (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, V)) hdim
    (h₁.contMDiff.mdifferentiable (by simp))).exists_mem_open isOpen_ball
    ⟨0, mem_ball_self (half_pos hc)⟩
  have hfin : (h₁ ⁻¹' {w}).Finite :=
    TauCeti.IsRegularValue.finite_preimage (hy := hwreg) hdim h₁.contMDiff.continuous
  -- Interpolate between `h₀` near the level set and `h₁ - w` away from it.
  let lam : M → ℝ := fun x ↦ max 0 (min 1 (-g x / c))
  have hlam : Continuous lam :=
    continuous_const.max (continuous_const.min (hg.neg.div_const c))
  refine ⟨⟨fun x ↦ h₀ x + lam x • ((h₁ x - w) - h₀ x), h₀.continuous.add
    (hlam.smul ((h₁.contMDiff.continuous.sub continuous_const).sub h₀.continuous))⟩,
    fun x hx ↦ ?_, ?_⟩
  · simp [lam, hx]
  -- A zero with `g ≤ 0` lies where `g ≤ -c`, and is a zero of `h₁ - w` there.
  have key : ∀ x, g x ≤ 0 → h₀ x + lam x • ((h₁ x - w) - h₀ x) = 0 → g x ≤ -c ∧ h₁ x = w := by
    intro x hx h0
    by_cases hxc : g x ≤ -c
    · have hl : lam x = 1 := by
        have : 1 ≤ -g x / c := by rw [le_div_iff₀ hc]; linarith
        simp [lam, min_eq_left this]
      rw [hl, one_smul, add_sub_cancel, sub_eq_zero] at h0
      exact ⟨hxc, h0⟩
    · exfalso
      have habs : |g x| < c := by rw [abs_of_nonpos hx]; linarith
      have hl0 : 0 ≤ lam x := le_max_left _ _
      have hl1 : lam x ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hd : ‖(h₁ x - w) - h₀ x‖ < c := by
        have h1 : ‖h₁ x - h₀ x‖ < c / 2 := by simpa [dist_eq_norm] using hh₁ x
        have h2 : ‖w‖ < c / 2 := by simpa using hw
        calc ‖(h₁ x - w) - h₀ x‖ = ‖(h₁ x - h₀ x) - w‖ := by abel_nf
          _ ≤ ‖h₁ x - h₀ x‖ + ‖w‖ := norm_sub_le _ _
          _ < c := by linarith
      have : ‖h₀ x‖ < c := by
        have := congrArg norm (eq_neg_of_add_eq_zero_left h0)
        rw [norm_neg, norm_smul, Real.norm_of_nonneg hl0] at this
        rw [this]
        calc lam x * ‖(h₁ x - w) - h₀ x‖ ≤ 1 * ‖(h₁ x - w) - h₀ x‖ :=
              mul_le_mul_of_nonneg_right hl1 (norm_nonneg _)
          _ < c := by linarith
      exact absurd (hcg x habs) (not_le.2 this)
  refine ⟨hfin.subset fun x hx ↦ (key x hx.1 hx.2).2, fun x hx h0 ↦ ?_⟩
  linarith [(key x hx h0).1]

end Extension

section Section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {L : M → Type*}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L] {g : M → ℝ}

/-- On a compact boundaryless surface, let `g : M → ℝ` be continuous, `τ` a frame of a real plane
bundle `L` over `{g ≤ 0}` (linear isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space of
the restriction of `L`), and `s` a nowhere-zero continuous section of `L` over `{g ≥ 0}`. Then `s`
extends to a continuous section of `L` over `M` with finitely many zeros, all in `{g < 0}`. -/
theorem exists_section_eq_finite_setOf_eq_zero (hn : finrank ℝ E = 2) (hg : Continuous g)
    {τ : ∀ x : g ⁻¹' Iic 0, L x ≃L[ℝ] ℂ}
    (hτ : Continuous fun v : TotalSpace F
      ((⇑(⟨Subtype.val, continuous_subtypeVal⟩ : C(g ⁻¹' Iic 0, M))) *ᵖ L) ↦ τ v.proj v.snd)
    {s : ∀ x : g ⁻¹' Ici 0, L x}
    (hs : Continuous fun x : g ⁻¹' Ici 0 ↦ TotalSpace.mk' F (x : M) (s x)) (hs0 : ∀ x, s x ≠ 0) :
    ∃ t : ∀ x, L x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      (∀ x : g ⁻¹' Ici 0, t x = s x) ∧ {x | t x = 0}.Finite ∧ ∀ x, t x = 0 → g x < 0 := by
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- `s` read in the frame `τ` on the level set `g⁻¹(0)`.
  have hc₀ : Continuous fun y : g ⁻¹' {0} ↦ TotalSpace.mk' F (E := (⇑i₁) *ᵖ L)
      (⟨y, (y.property : g y = 0).le⟩ : g ⁻¹' Iic 0) (s ⟨y, (y.property : g y = 0).ge⟩) :=
    Pullback.continuous_iff.2 ⟨continuous_subtypeVal.subtype_mk _,
      hs.comp (continuous_subtypeVal.subtype_mk _)⟩
  -- Extend it to `M` (Tietze), then change it off the level set to have finitely many zeros in
  -- `{g ≤ 0}`.
  obtain ⟨h₀, hh₀⟩ := (⟨_, hτ.comp hc₀⟩ : C(g ⁻¹' {0}, ℂ)).exists_extension'
    (isClosed_singleton.preimage hg).isClosedEmbedding_subtypeVal
  have hh₀C (x : M) (hx : g x = 0) : h₀ x = τ ⟨x, hx.le⟩ (s ⟨x, hx.ge⟩) :=
    congrFun hh₀ ⟨x, hx⟩
  obtain ⟨h, hhC, hhfin, hhneg⟩ := exists_eq_on_levelSet_finite_zeros
    (by rw [hn, Complex.finrank_real_complex]) hg h₀ fun x hx ↦ by
      rw [hh₀C x hx]
      exact fun h ↦ hs0 _ ((τ _).map_eq_zero_iff.1 h)
  -- The section: `τ⁻¹ h` on `{g ≤ 0}` and `s` on `{g > 0}`.
  let t : ∀ x, L x := fun x ↦
    if hx : g x ≤ 0 then (τ ⟨x, hx⟩).symm (h x) else s ⟨x, (not_le.1 hx).le⟩
  have ht₁ (x : g ⁻¹' Iic 0) : t x = (τ x).symm (h x) := dite_eq_left x.property
  have ht₂ (x : g ⁻¹' Ici 0) : t x = s x := by
    by_cases hx : g x ≤ 0
    · have hx0 : g x = 0 := le_antisymm hx x.property
      simp only [t, dite_eq_left hx, hhC x hx0, hh₀C x hx0]
      exact (τ _).symm_apply_apply _
    · exact dite_eq_right hx
  have hZt (x : M) : t x = 0 ↔ g x ≤ 0 ∧ h x = 0 := by
    by_cases hx : g x ≤ 0
    · rw [ht₁ ⟨x, hx⟩, (τ _).symm.map_eq_zero_iff]
      exact ⟨fun h0 ↦ ⟨hx, h0⟩, And.right⟩
    · rw [ht₂ ⟨x, (not_le.1 hx).le⟩]
      exact ⟨fun h0 ↦ absurd h0 (hs0 _), fun h0 ↦ absurd h0.1 hx⟩
  refine ⟨t, ?_, ht₂, hhfin.subset fun x hx ↦ (hZt x).1 hx, fun x hx ↦
    hhneg x ((hZt x).1 hx).1 ((hZt x).1 hx).2⟩
  -- `τ⁻¹ h` is continuous on `{g ≤ 0}`, as the inverse of a frame is continuous.
  have hτ' : Continuous fun v : TotalSpace F ((⇑i₁) *ᵖ L) ↦
      TotalSpace.mk' ℂ (E := Bundle.Trivial (g ⁻¹' Iic 0) ℂ) v.proj (τ v.proj v.snd) :=
    (Bundle.Trivial.isInducing_toProd _ ℂ).continuous_iff.2
      ((Pullback.continuous_proj F L i₁).prodMk hτ)
  have hh : Continuous fun x : g ⁻¹' Iic 0 ↦
      TotalSpace.mk' ℂ (E := Bundle.Trivial (g ⁻¹' Iic 0) ℂ) x (h x) :=
    (Bundle.Trivial.isInducing_toProd _ ℂ).continuous_iff.2
      (continuous_id.prodMk (h.continuous.comp continuous_subtypeVal))
  have hτs : Continuous fun x : g ⁻¹' Iic 0 ↦
      TotalSpace.mk' F (E := (⇑i₁) *ᵖ L) x ((τ x).symm (h x)) :=
    (TauCeti.continuous_bundle_symm (F₁ := F) (E₁ := (⇑i₁) *ᵖ L) (F₂ := ℂ)
      (E₂ := Bundle.Trivial (g ⁻¹' Iic 0) ℂ) τ hτ').comp hh
  -- The section is continuous on the closed sets `{g ≤ 0}` and `{g ≥ 0}`, which cover `M`.
  refine continuousOn_univ.1 ?_
  rw [← show g ⁻¹' Iic 0 ∪ g ⁻¹' Ici 0 = univ from
    eq_univ_of_forall fun x ↦ (le_total (g x) 0).imp id id]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_Iic.preimage hg)
    (isClosed_Ici.preimage hg) <;> rw [continuousOn_iff_continuous_domRestrict]
  · convert (Pullback.continuous_lift F L i₁).comp hτs using 1
    funext x
    simp only [domRestrict_apply, Function.comp_apply, ht₁ x, Pullback.lift_mk, i₁,
      ContinuousMap.coe_mk]
  · convert hs using 1
    funext x
    simp only [domRestrict_apply, ht₂ x]

end Section

end SymplecticGeometry

namespace TauCeti.VectorBundleOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : M → Type}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L] {g : M → ℝ}

/-- **The argument principle on a split closed surface.** Let `M` be a closed smooth surface
oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into
`Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. Let `L` be a real plane bundle over `M`, oriented by `oL`, `τ`
a frame of `L` over `Σ₁` (linear isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, that
carry `oL` to `Complex.orientation`), and `s` a nowhere-zero continuous section of `L` over `Σ₂`.
Then the Euler number of `L` is the boundary degree on `Σ₁`, whose interior `{g < 0}` carries the
orientation restricted from `oM`, of any continuous `u` from the boundary `Σ₁ ∖ {g < 0}` of `Σ₁`
to the circle equal to `τ s / |τ s|` there. -/
theorem evalFundamentalClass_eulerClass_eq_boundaryDegree
    (oL : VectorBundleOrientation F L (Fin 2)) (hF : finrank ℝ F = 2)
    (oM : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g 0)
    {τ : ∀ x : g ⁻¹' Iic 0, L x ≃L[ℝ] ℂ}
    (hτ : Continuous fun v : TotalSpace F
      ((⇑(⟨Subtype.val, continuous_subtypeVal⟩ : C(g ⁻¹' Iic 0, M))) *ᵖ L) ↦ τ v.proj v.snd)
    (hτo : ∀ x, Orientation.map (Fin 2) (τ x).toLinearEquiv (oL x) = Complex.orientation)
    {s : ∀ x : g ⁻¹' Ici 0, L x}
    (hs : Continuous fun x : g ⁻¹' Ici 0 ↦ TotalSpace.mk' F (x : M) (s x)) (hs0 : ∀ x, s x ≠ 0)
    {u : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, Circle)}
    (hu : ∀ z hz, (u z : ℂ) = ‖τ z (s ⟨z, hz⟩)‖⁻¹ • τ z (s ⟨z, hz⟩)) :
    haveI : CompactSpace (g ⁻¹' Iic 0) :=
      isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
    (oM.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (oL.eulerClass hF)).down =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryDegree hn
        (IsOpenEmbedding.inclusion _
          ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
        ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 u := by
  have : CompactSpace (g ⁻¹' Iic 0) :=
    isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- A section `t` extending `s`, with finitely many zeros, all in `{g < 0}`.
  obtain ⟨t, ht, ht₂, hZ, hZneg⟩ :=
    SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero hn hg.continuous hτ hs hs0
  -- Adding up the local indices of `t` at its zeros gives the Euler number.
  rw [evalFundamentalClass_eulerClass_eq_sum_sectionIndex oL hF oM ht hn hZ]
  -- The argument principle on `{g ≤ 0}`, for the frame `τ` and the restriction of `t`.
  have hτo' (x : g ⁻¹' Iic 0) :
      Orientation.map (Fin 2) (τ x).toLinearEquiv ((oL.pullback i₁) x) = Complex.orientation := by
    rw [pullback_apply]
    exact hτo x
  have ht' : Continuous fun x : g ⁻¹' Iic 0 ↦ TotalSpace.mk' F (E := (⇑i₁) *ᵖ L) x (t x) :=
    Pullback.continuous_iff.2 ⟨continuous_id, ht.comp continuous_subtypeVal⟩
  -- A point of `{g ≤ 0}` off the interior `{g < 0}` lies in `{g ≥ 0}`.
  have hlt (x : g ⁻¹' Iic 0)
      (hx : x ∉ range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
        TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self))) :
      (x : M) ∈ g ⁻¹' Ici 0 :=
    mem_preimage.2 (mem_Ici.2 (not_lt.1 fun h' ↦ hx ⟨⟨x, h'⟩, rfl⟩))
  refine Eq.trans ?_ (sum_sectionIndex_eq_boundaryDegree (oL.pullback i₁) hF
    (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)) hn
    (IsOpenEmbedding.inclusion _
      ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
    ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
    (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 hτ hτo'
    (t := fun x ↦ t x) ht' (hZ.preimage Subtype.val_injective.injOn)
    (fun x hx ↦ ⟨⟨x, hZneg x hx⟩, rfl⟩) (u := u)
    (fun z ↦ by rw [ht₂ ⟨z, hlt z z.property⟩]; exact hu z _))
  -- Each local index on `{g < 0}` is the local index on `M` at the same point.
  symm
  -- The zeros of `t` on `{g < 0}` are its zeros on `M`, read in the fibres of a pull-back: the
  -- membership is stated through `have` since `rw` does not see the two fibres as equal.
  refine Finset.sum_nbij (fun y ↦ (y : M))
    (fun y hy ↦ hZ.mem_toFinset.2 (by have := (Set.Finite.mem_toFinset _).1 hy; exact this))
    Subtype.val_injective.injOn (fun z hz ↦ ?_) (fun y _ ↦ ?_)
  · have hz' : t z = 0 := (Set.Finite.mem_toFinset _).1 hz
    exact ⟨⟨z, hZneg z hz'⟩, (Set.Finite.mem_toFinset _).2 hz', rfl⟩
  refine sectionIndex_comap_eq_of_fiberwise oL hF oM _ hF
    (j := ⟨Subtype.val, continuous_subtypeVal⟩) _
    (φ := fun x ↦ ContinuousLinearEquiv.refl ℝ (L x)) ?_ (fun x ↦ ?_) _ ht (fun _ ↦ rfl) y
  · exact (Pullback.continuous_lift F L i₁).comp (Pullback.continuous_lift F _ _)
  · have hrefl : (ContinuousLinearEquiv.refl ℝ (L x)).toLinearEquiv = LinearEquiv.refl ℝ (L x) :=
      LinearEquiv.ext fun _ ↦ rfl
    rw [pullback_apply, pullback_apply, hrefl]
    exact Equiv.congr_fun (Orientation.map_refl _) _

end TauCeti.VectorBundleOrientation

end
