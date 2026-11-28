/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import TauCeti.Geometry.Diffeomorphism.Group
import SymplecticGeometry.Analysis.Calculus.BumpFunction.Radial
import SymplecticGeometry.Geometry.Diffeomorphism.SmoothFamily

/-!
# Cutting off a homotopy of clutching maps along the collar of a coordinate disc

Let `φ` be a coordinate disc of a space `M` (`SymplecticGeometry.CoordinateDisc`) whose
coordinate `φ.coord` is `Cⁿ` on the range of `φ`, as it is for the coordinate disc of a chart of
the maximal atlas (`CoordinateDisc.contMDiffOn_coord_ofChart`). Let `K` be a subgroup of the group
`TauCeti.Diff IF F N` of diffeomorphisms of a manifold `F`, and let `h : ℝ → M → K` be a family
whose uncurried maps `(t, x, v) ↦ h t x v` and `(t, x, v) ↦ (h t x)⁻¹ v` are `Cⁿ` on
`[0, 1] × A × F`, where `A` is the image under `φ` of the annulus `a < ‖z‖ < b`.

For radii `0 ≤ a'` and `a < a' < b'` chosen in advance, this file builds `k : M → K` whose
uncurried map and that of its inverse are `Cⁿ` on the image of the disc `‖z‖ < b`, which is `1`
off the image of the annulus `a' < ‖z‖ < b`, and which is `h 1 * (h 0)⁻¹` on the image of
`b' ≤ ‖z‖ < b` (`CoordinateDisc.exists_contMDiffOn_cutoff_homotopy`). On `A` it is
`k x = h (χ x) x * (h 0 x)⁻¹`, where `χ` is a smooth function of the radius `‖φ.coord x‖` that
rises from `0` to `1` between `a'` and `b'`; it comes from the radial cut-off
`SymplecticGeometry.exists_contDiff_norm_cutoff`.

This is the step that turns a homotopy of clutching maps into a change of chart: if the charts of
a bundle over the disc and over its complement differ on `A` by `h 0`, then composing the chart
over the disc with `k` leaves it unchanged near the centre and makes the two charts differ by
`h 1` near the outer edge of `A`. The file `ChernNumber/Gluing.lean` does the same for families
of symplectic matrices (`exists_extend_of_maslovIndex_eq_zero`), with an extension over the disc
in place of the cut-off.

## Main results

* `SymplecticGeometry.CoordinateDisc.exists_contMDiffOn_cutoff_homotopy`: the cut-off of a
  homotopy of `K`-valued maps along the collar of a coordinate disc.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.2, where sphere bundles over surfaces are classified by clutching.
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace CoordinateDisc

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {o : TauCeti.HomologicalOrientation M E 2}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} [ChartedSpace HM M]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {N : ℕ∞ω} {K : Subgroup (TauCeti.Diff IF F N)} {n : ℕ∞}

/-- **Cutting off a homotopy along the collar of a coordinate disc.** Let `φ` be a coordinate
disc whose coordinate is `Cⁿ` on the range of `φ`, let `0 ≤ a'` and `a < a' < b'`, and let
`h : ℝ → M → K` be a family of maps into a subgroup `K` of the diffeomorphisms of `F` whose
uncurried maps `(t, x, v) ↦ h t x v` and `(t, x, v) ↦ (h t x)⁻¹ v` are `Cⁿ` on `[0, 1] × A × F`,
for the image `A` of the annulus `a < ‖z‖ < b`. Then some `k : M → K` has `Cⁿ` uncurried maps
`(x, v) ↦ k x v` and `(x, v) ↦ (k x)⁻¹ v` on the image of the disc `‖z‖ < b` times `F`, is `1`
off the image of the annulus `a' < ‖z‖ < b`, and is `h 1 * (h 0)⁻¹` on the image of
`b' ≤ ‖z‖ < b`. -/
theorem exists_contMDiffOn_cutoff_homotopy (φ : CoordinateDisc o)
    (hφ : ContMDiffOn I 𝓘(ℝ, ℂ) n φ.coord (range φ)) {a a' b' b : ℝ} (ha' : 0 ≤ a')
    (haa' : a < a') (hab : a' < b') {h : ℝ → M → K}
    (hh : ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod IF) IF n
      (fun p : (ℝ × M) × F ↦ (h p.1.1 p.1.2 : TauCeti.Diff IF F N) p.2)
      ((Icc 0 1 ×ˢ (φ '' {z | a < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < b})) ×ˢ univ))
    (hh' : ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod IF) IF n
      (fun p : (ℝ × M) × F ↦ ((h p.1.1 p.1.2)⁻¹ : TauCeti.Diff IF F N) p.2)
      ((Icc 0 1 ×ˢ (φ '' {z | a < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < b})) ×ˢ univ)) :
    ∃ k : M → K,
      ContMDiffOn (I.prod IF) IF n (fun p : M × F ↦ (k p.1 : TauCeti.Diff IF F N) p.2)
        ((φ '' {z | ‖(z : ℂ)‖ < b}) ×ˢ univ) ∧
      ContMDiffOn (I.prod IF) IF n (fun p : M × F ↦ ((k p.1)⁻¹ : TauCeti.Diff IF F N) p.2)
        ((φ '' {z | ‖(z : ℂ)‖ < b}) ×ˢ univ) ∧
      (∀ x ∉ φ '' {z | a' < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < b}, k x = 1) ∧
      ∀ z : ball, b' ≤ ‖(z : ℂ)‖ → ‖(z : ℂ)‖ < b → k (φ z) = h 1 (φ z) * (h 0 (φ z))⁻¹ := by
  classical
  set A := φ '' {z | a < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < b}
  set A' := φ '' {z | a' < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < b}
  have hAr : A ⊆ range φ := image_subset_range _ _
  -- The cut-off `χ = 1 - ψ (‖φ.coord x‖)`, for a radial cut-off `ψ` that is `1` up to `a'` and `0`
  -- beyond `(a' + b') / 2`.
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0⟩ :=
    exists_contDiff_norm_cutoff ℂ ha' (show a' < (a' + b') / 2 by linarith)
  set χ : M → ℝ := fun x ↦ 1 - ψ ‖φ.coord x‖
  have hχ : ContMDiffOn I 𝓘(ℝ, ℝ) n χ (range φ) :=
    (contDiff_const.sub (hψ.of_le (WithTop.coe_le_coe.2 le_top))).contMDiff.comp_contMDiffOn hφ
  have hχ01 (x : M) : χ x ∈ Icc 0 1 := by
    obtain ⟨h₀, h₁⟩ := hψ01 ‖φ.coord x‖
    exact ⟨sub_nonneg.2 h₁, sub_le_self _ h₀⟩
  have hχz (z : ball) : χ (φ z) = 1 - ψ ‖(z : ℂ)‖ := by simp only [χ, coord_apply]
  have hχ0 (z : ball) (hz : ‖(z : ℂ)‖ ≤ a') : χ (φ z) = 0 := by
    rw [hχz, hψ1 _ (by rwa [abs_norm]), sub_self]
  have hχ1 (z : ball) (hz : b' ≤ ‖(z : ℂ)‖) : χ (φ z) = 1 := by
    rw [hχz, hψ0 _ (by rw [abs_norm]; linarith), sub_zero]
  -- The families `x ↦ h (c x) x` and their inverses, for a smooth `c : M → [0, 1]`.
  have hfam {c : M → ℝ} (hc : ContMDiffOn I 𝓘(ℝ, ℝ) n c A) (hc01 : ∀ x, c x ∈ Icc 0 1) :
      ContMDiffOn (I.prod IF) IF n
          (fun p : M × F ↦ (h (c p.1) p.1 : TauCeti.Diff IF F N) p.2) (A ×ˢ univ) ∧
        ContMDiffOn (I.prod IF) IF n
          (fun p : M × F ↦ ((h (c p.1) p.1)⁻¹ : TauCeti.Diff IF F N) p.2) (A ×ˢ univ) := by
    have hg : ContMDiffOn (I.prod IF) ((𝓘(ℝ, ℝ).prod I).prod IF) n
        (fun p : M × F ↦ ((c p.1, p.1), p.2)) (A ×ˢ univ) :=
      ((hc.comp contMDiffOn_fst fun p (hp : p ∈ A ×ˢ univ) ↦ hp.1).prodMk
        contMDiffOn_fst).prodMk contMDiffOn_snd
    have hmaps : MapsTo (fun p : M × F ↦ ((c p.1, p.1), p.2)) (A ×ˢ univ)
        ((Icc 0 1 ×ˢ A) ×ˢ univ) := fun p hp ↦ ⟨⟨hc01 _, hp.1⟩, trivial⟩
    exact ⟨hh.comp hg hmaps, hh'.comp hg hmaps⟩
  obtain ⟨hχs, hχs'⟩ := hfam (hχ.mono hAr) hχ01
  obtain ⟨h0s, h0s'⟩ := hfam (c := fun _ ↦ 0) contMDiffOn_const fun _ ↦ ⟨le_rfl, zero_le_one⟩
  -- The map `k`: `h (χ x) x * (h 0 x)⁻¹` on `A'`, and `1` elsewhere.
  set k : M → K := fun x ↦ if x ∈ A' then h (χ x) x * (h 0 x)⁻¹ else 1
  have hkA (x : M) (hx : x ∈ A) : k x = h (χ x) x * (h 0 x)⁻¹ := by
    by_cases hx' : x ∈ A'
    · simp only [k, hx', ite_true]
    · obtain ⟨z, hz, rfl⟩ := hx
      have hza : ‖(z : ℂ)‖ ≤ a' := not_lt.1 fun h' ↦ hx' ⟨z, ⟨h', hz.2⟩, rfl⟩
      simp only [k, hx', ite_false, hχ0 z hza, mul_inv_cancel]
  have hk1 (x : M) (hx : x ∉ A') : k x = 1 := by simp only [k, hx, ite_false]
  -- Near the centre, `k` is `1`.
  set U := φ '' {z | ‖(z : ℂ)‖ < a'}
  have hkU (x : M) (hx : x ∈ U) : k x = 1 := by
    refine hk1 x ?_
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hx
    rw [φ.injective hwz] at hw
    exact absurd hz.1 (not_lt.2 (le_of_lt hw))
  have hopen {s : Set ball} (hs : IsOpen s) : IsOpen (φ '' s) := φ.isOpenEmbedding.isOpenMap _ hs
  have hAo : IsOpen A := hopen ((isOpen_lt continuous_const continuous_subtypeVal.norm).inter
    (isOpen_lt continuous_subtypeVal.norm continuous_const))
  have hUo : IsOpen U := hopen (isOpen_lt continuous_subtypeVal.norm continuous_const)
  -- Smoothness on the disc, from smoothness on the open sets `U` and `A`, which cover it.
  have hcover : (φ '' {z | ‖(z : ℂ)‖ < b}) ×ˢ (univ : Set F) ⊆ U ×ˢ univ ∪ A ×ˢ univ := by
    rintro ⟨_, v⟩ ⟨⟨z, hz, rfl⟩, -⟩
    by_cases hza : ‖(z : ℂ)‖ < a'
    · exact Or.inl ⟨⟨z, hza, rfl⟩, trivial⟩
    · exact Or.inr ⟨⟨z, ⟨by linarith [not_lt.1 hza], hz⟩, rfl⟩, trivial⟩
  have hlocal {G : M → TauCeti.Diff IF F N} (hGU : EqOn G 1 U)
      (hGA : ContMDiffOn (I.prod IF) IF n (fun p : M × F ↦ G p.1 p.2) (A ×ˢ univ)) :
      ContMDiffOn (I.prod IF) IF n (fun p : M × F ↦ G p.1 p.2)
        ((φ '' {z | ‖(z : ℂ)‖ < b}) ×ˢ univ) :=
    ((Diffeomorph.contMDiffOn_apply_of_eqOn_one hGU).union_of_isOpen hGA
      (hUo.prod isOpen_univ) (hAo.prod isOpen_univ)).mono hcover
  refine ⟨k, hlocal (G := fun x ↦ k x)
      (fun x hx ↦ by simp only [hkU x hx, Subgroup.coe_one, Pi.one_apply]) ?_,
    hlocal (G := fun x ↦ ((k x)⁻¹ : K))
      (fun x hx ↦ by simp only [hkU x hx, inv_one, Subgroup.coe_one, Pi.one_apply]) ?_, hk1,
    fun z hz₁ hz₂ ↦ ?_⟩
  · refine (Diffeomorph.contMDiffOn_mul_apply (f := fun x ↦ h (χ x) x)
      (g := fun x ↦ (h 0 x : TauCeti.Diff IF F N)⁻¹) hχs h0s').congr fun q hq ↦ ?_
    rw [hkA q.1 hq.1, Subgroup.coe_mul, Subgroup.coe_inv]
  · refine (Diffeomorph.contMDiffOn_mul_apply (f := fun x ↦ h 0 x)
      (g := fun x ↦ (h (χ x) x : TauCeti.Diff IF F N)⁻¹) h0s hχs').congr fun q hq ↦ ?_
    rw [hkA q.1 hq.1, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [hkA _ ⟨z, ⟨by linarith, hz₂⟩, rfl⟩, hχ1 z hz₁]

end CoordinateDisc

end SymplecticGeometry

end
