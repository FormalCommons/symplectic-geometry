/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Neighborhood
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Extension
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Family
import TauCeti.Geometry.Manifold.Diffeomorph.Family
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Transport of functions along a family of isotopies

Let `k : Q × [0, 1] × P → M` be a smooth family of smooth isotopies of a boundaryless manifold `P`
into a boundaryless manifold `M` of the same finite dimension, over a parameter manifold `Q`, and
let `h : Q × [0, 1] × P → ℝ` be smooth. Near a compact `A ⊆ P`, and for parameters in a compact
`T ⊆ Q`, `h` is the pull-back along the slices of `k` of a smooth function `G` on `Q × M × [0, 1]`:
`G (q, k (q, s, y), s) = h (q, s, y)`. The function `G` vanishes outside a compact subset of any
given open neighbourhood of the track of `A`, and `G (q, ·, ·)` vanishes whenever `h (q, ·, ·)`
does (`ContMDiff.exists_contMDiff_family_comp_eventuallyEq`). The case of the parameter manifold
`unitInterval` is `ContMDiff.exists_contMDiff_unitInterval_family_comp_eventuallyEq`.

The proof follows that of `TauCeti.SmoothIsotopy.exists_contMDiff_comp_eventuallyEq`, with every
step carried out over the parameter:

1. Isotopy extension at every time with a parameter
   (`ContMDiff.exists_contMDiff_diffeomorph_family_forall_apply_eq`) gives diffeomorphisms
   `ψ q s` of `M`, jointly smooth, with `ψ q s (k (q, 0, x)) = k (q, s, x)` near `A`. Their
   inverses are jointly smooth by Tau Ceti's `Diffeomorph.contMDiff_symm_family`.
2. The graph `(q, x) ↦ (q, k (q, 0, x))` is a smooth embedding of a neighbourhood `V` of
   `T ×ˢ A` into `Q × M` (`TauCeti.exists_isOpen_isSmoothEmbedding_of_injOn`, with the
   differential of a graph from `MDifferentiableAt.injective_mfderiv_fst_prod_iff`), hence an
   injective local diffeomorphism (`Manifold.IsImmersion.isLocalDiffeomorph`), whose inverse is
   smooth on its image (`TauCeti.IsLocalDiffeomorphOn.contMDiffOn_invFunOn`).
3. With a cutoff `χ` on `Q × M` near the image of `T ×ˢ A` and a cutoff `ρ` on `M` near the
   track, `G (q, y, s) = ρ y · χ (q, z) · h (q, s, x)`, where `z = (ψ q s)⁻¹ y` and `(q, x)` is
   the preimage of `(q, z)` under the graph. The parameter of `h` is that of the point `(q, y)`,
   so `G (q, ·, ·)` vanishes with `h (q, ·, ·)`.

Tau Ceti's family inverse needs a boundaryless parameter, so the case of `unitInterval` first
extends the pair `(k, h)` in the parameter near `univ ×ˢ A`
(`ContMDiff.exists_contMDiffOn_extend_unitInterval`), runs them at a parameter `c q` with `c` the
identity on `[0, 1]` (`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`), as in the proof of
`ContMDiff.exists_contMDiff_diffeomorph_unitInterval_family_forall_apply_eq`, and applies the
first result with `Q = ℝ` and `T = [0, 1]`.

## Main results

* `ContMDiff.exists_contMDiff_family_comp_eventuallyEq`: transport of functions along a smooth
  family of isotopies over a boundaryless parameter manifold.
* `ContMDiff.exists_contMDiff_unitInterval_family_comp_eventuallyEq`: the same for a family of
  isotopies with a parameter in `unitInterval`.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 8, §1, Theorems 1.3 and 1.4.
-/

public section

noncomputable section

open Set Function Manifold Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E E' EQ H H' HQ P M Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace HQ]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} {IQ : ModelWithCorners ℝ EQ HQ}
  [TopologicalSpace P] [ChartedSpace H' P] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace Q] [ChartedSpace HQ Q]
  [I.Boundaryless] [J.Boundaryless] [IQ.Boundaryless]
  [IsManifold J ∞ P] [IsManifold I ∞ M] [IsManifold IQ ∞ Q]
  [T2Space M] [T2Space Q] [SigmaCompactSpace M] [SigmaCompactSpace Q]

/-- **Transport of functions along a family of isotopies.** Let `k : Q × [0, 1] × P → M` be
smooth, with `Q` and `M` finite-dimensional, Hausdorff, σ-compact boundaryless manifolds and `P`
boundaryless of the dimension of `M`, let `T ⊆ Q` and `A ⊆ P` be compact, with every slice
`k (q, s, ·)` for `q ∈ T` a smooth embedding, let `h : Q × [0, 1] × P → ℝ` be smooth, and let
`W ⊆ M` be open and contain `k (q, s, x)` for `q ∈ T` and `x ∈ A`. Then there are a smooth
`G : Q × M × [0, 1] → ℝ` and a compact `C ⊆ W` such that `G (q, y, s) = 0` for `y ∉ C`, such that
`G (q, k (q, s, y), s) = h (q, s, y)` for `q ∈ T`, every `s` and `y` near any point of `A`, and
such that `G (q, ·, ·) = 0` for every `q` with `h (q, ·, ·) = 0`. -/
theorem _root_.ContMDiff.exists_contMDiff_family_comp_eventuallyEq
    {k : Q × unitInterval × P → M} (hk : ContMDiff (IQ.prod ((𝓡∂ 1).prod J)) I ∞ k)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {T : Set Q} (hT : IsCompact T) {A : Set P}
    (hA : IsCompact A) (hemb : ∀ q ∈ T, ∀ s, IsSmoothEmbedding J I ∞ fun x ↦ k (q, s, x))
    {h : Q × unitInterval × P → ℝ} (hh : ContMDiff (IQ.prod ((𝓡∂ 1).prod J)) 𝓘(ℝ) ∞ h)
    {W : Set M} (hW : IsOpen W) (hAW : ∀ q ∈ T, ∀ s, ∀ x ∈ A, k (q, s, x) ∈ W) :
    ∃ (G : Q × M × unitInterval → ℝ) (C : Set M),
      ContMDiff (IQ.prod (I.prod (𝓡∂ 1))) 𝓘(ℝ) ∞ G ∧ IsCompact C ∧ C ⊆ W ∧
      (∀ q y s, y ∉ C → G (q, y, s) = 0) ∧
      (∀ q ∈ T, ∀ s, ∀ x ∈ A, (fun y ↦ G (q, k (q, s, y), s)) =ᶠ[𝓝 x] fun y ↦ h (q, s, y)) ∧
      ∀ q, (∀ s y, h (q, s, y) = 0) → ∀ y s, G (q, y, s) = 0 := by
  -- Without a point of `T ×ˢ A`, the zero function will do.
  by_cases hTA : (T ×ˢ A).Nonempty
  swap
  · exact ⟨0, ∅, contMDiff_const, isCompact_empty, empty_subset _, fun _ _ _ _ ↦ rfl,
      fun q hq _ x hx ↦ (hTA ⟨(q, x), hq, hx⟩).elim, fun _ _ _ _ ↦ rfl⟩
  obtain ⟨⟨q₀, x₀⟩, hq₀, hx₀⟩ := hTA
  -- `P` is Hausdorff and its model finite-dimensional, since a slice embeds it into `M`.
  have : T2Space P := (hemb q₀ hq₀ 0).isEmbedding.t2Space
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv
    ((hemb q₀ hq₀ 0).isImmersion.mfderiv_injective (by simp) x₀)
  have := Manifold.locallyCompact_of_finiteDimensional J (M := P)
  have : CompleteSpace EQ := FiniteDimensional.completeSpace ℝ EQ
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- Step 1: the diffeomorphisms `ψ q s` of isotopy extension, and their inverses.
  obtain ⟨A', hA', hAA'⟩ := exists_compact_superset hA
  obtain ⟨ψ, hψ, -, -, -, -, hψk⟩ := hk.exists_contMDiff_diffeomorph_family_forall_apply_eq hT hA'
    hemb
  have hψs : ContMDiff ((IQ.prod 𝓘(ℝ, ℝ)).prod I) I ∞
      fun z : (Q × ℝ) × M ↦ (ψ z.1.1 z.1.2).symm z.2 :=
    Diffeomorph.contMDiff_symm_family (f := fun p : Q × ℝ ↦ ψ p.1 p.2)
      (hψ.comp (contMDiff_fst.fst.prodMk (contMDiff_fst.snd.prodMk contMDiff_snd))) (by simp)
  -- Step 2: the graph `Φ₀` of the slice at time `0` embeds an open `V ⊇ T ×ˢ A`.
  let Φ₀ : Q × P → Q × M := fun p ↦ (p.1, k (p.1, 0, p.2))
  have hΦ₀ : ContMDiff (IQ.prod J) (IQ.prod I) ∞ Φ₀ :=
    contMDiff_fst.prodMk (hk.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)))
  obtain ⟨V, hTAV, -, hV⟩ := exists_isOpen_isSmoothEmbedding_of_injOn isOpen_univ
    hΦ₀.contMDiffOn (hT.prod hA) (subset_univ _)
    (fun p hp p' hp' hpp ↦ by
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 hpp
      obtain ⟨q, x⟩ := p
      obtain ⟨q', x'⟩ := p'
      obtain rfl : q = q' := h₁
      exact congrArg (Prod.mk q) ((hemb q hp.1 0).isEmbedding.injective h₂))
    fun p hp ↦ by
      have hdiff : MDifferentiableAt (IQ.prod J) I (fun x : Q × P ↦ k (x.1, 0, x.2)) p :=
        (hk.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd))).mdifferentiableAt
          (by simp)
      exact hdiff.injective_mfderiv_fst_prod_iff.2
        ((hemb p.1 hp.1 0).isImmersion.mfderiv_injective (by simp) p.2)
  have : Nonempty V := ⟨⟨(q₀, x₀), hTAV ⟨hq₀, hx₀⟩⟩⟩
  let f : V → Q × M := fun x ↦ Φ₀ x
  have hf : IsLocalDiffeomorph (IQ.prod J) (IQ.prod I) ∞ f :=
    hV.isImmersion.isLocalDiffeomorph (by simp [Module.finrank_prod, hd]) (by simp)
  have hinj : Injective f := hV.isEmbedding.injective
  let inv : Q × M → V := invFunOn f univ
  have hinv : ContMDiffOn (IQ.prod I) (IQ.prod J) ∞ (fun z ↦ ((inv z : V) : Q × P)) (f '' univ) :=
    contMDiff_subtypeVal.comp_contMDiffOn
      ((hf.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn isOpen_univ hinj.injOn)
  have hfo : IsOpen (f '' univ) := hf.isOpenMap _ isOpen_univ
  -- Step 3: the cutoffs `χ` near `Φ₀ '' (T ×ˢ A)` and `ρ` near the track of `A`.
  obtain ⟨χ, hχ, hχ1, -, hχf, -⟩ :=
    ((hT.prod hA).image hΦ₀.continuous).exists_contMDiff_one_nhds_tsupport_subset (IQ.prod I) hfo
      (by rintro _ ⟨p, hp, rfl⟩; exact ⟨⟨p, hTAV hp⟩, mem_univ _, rfl⟩)
  have hL : IsCompact (k '' (T ×ˢ univ ×ˢ A)) :=
    (hT.prod (isCompact_univ.prod hA)).image hk.continuous
  obtain ⟨ρ, hρ, hρ1, hρc, hρW, -⟩ := hL.exists_contMDiff_one_nhds_tsupport_subset I hW
    (by rintro _ ⟨⟨q, s, x⟩, ⟨hq, -, hx⟩, rfl⟩; exact hAW q hq s x hx)
  -- The function `(q, s, z) ↦ χ (q, z) · h (q, s, x)`, with `(q, x)` the preimage of `(q, z)`.
  let g : Q × unitInterval × M → ℝ := fun p ↦
    χ (p.1, p.2.2) * h (p.1, p.2.1, ((inv (p.1, p.2.2) : V) : Q × P).2)
  have hg : ContMDiff (IQ.prod ((𝓡∂ 1).prod I)) 𝓘(ℝ) ∞ g := by
    rintro ⟨q, s, z⟩
    have hpr : ContMDiff (IQ.prod ((𝓡∂ 1).prod I)) (IQ.prod I) ∞
        fun p : Q × unitInterval × M ↦ (p.1, p.2.2) := contMDiff_fst.prodMk contMDiff_snd.snd
    by_cases hz : (q, z) ∈ tsupport χ
    · have hw : ContMDiffAt (IQ.prod ((𝓡∂ 1).prod I)) J ∞
          (fun p : Q × unitInterval × M ↦ ((inv (p.1, p.2.2) : V) : Q × P).2) (q, s, z) :=
        contMDiffAt_snd.comp (q, s, z)
          (ContMDiffAt.comp (g := fun z ↦ ((inv z : V) : Q × P)) (q, s, z)
            (hinv.contMDiffAt (hfo.mem_nhds (hχf hz))) hpr.contMDiffAt)
      exact (hχ.contMDiffAt.comp _ hpr.contMDiffAt).mul (hh.contMDiffAt.comp _
        (contMDiffAt_fst.prodMk (contMDiffAt_snd.fst.prodMk hw)))
    · refine contMDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(hpr.continuous.tendsto (q, s, z)).eventually
        (notMem_tsupport_iff_eventuallyEq.1 hz)] with p hp
      simp only [g, show χ (p.1, p.2.2) = 0 from hp, zero_mul]
  refine ⟨fun p ↦ ρ p.2.1 * g (p.1, p.2.2, (ψ p.1 p.2.2).symm p.2.1), tsupport ρ,
    (hρ.comp contMDiff_snd.fst).mul (hg.comp (contMDiff_fst.prodMk (contMDiff_snd.snd.prodMk
      (hψs.comp ((contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd.snd)).prodMk
        contMDiff_snd.fst))))),
    hρc.isCompact, hρW, fun q y s hy ↦ by simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul],
    fun q hq s x hx ↦ ?_, fun q hq y s ↦ by simp only [g, hq, mul_zero]⟩
  have hqx : (q, x) ∈ T ×ˢ A := ⟨hq, hx⟩
  filter_upwards [isOpen_interior.mem_nhds (hAA' hx),
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds (hTAV hqx),
    ((hΦ₀.continuous.comp (continuous_const.prodMk continuous_id)).tendsto x).eventually
      (hχ1.filter_mono (nhds_le_nhdsSet (mem_image_of_mem Φ₀ hqx))),
    ((hk.continuous.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).tendsto
      x).eventually
      (hρ1.filter_mono (nhds_le_nhdsSet (mem_image_of_mem k
        (show (q, s, x) ∈ T ×ˢ univ ×ˢ A from ⟨hq, mem_univ s, hx⟩))))]
    with y hyA hyV hyχ hyρ
  have h₁ : (ψ q s).symm (k (q, s, y)) = k (q, 0, y) := by
    rw [← hψk q hq s y (interior_subset hyA), Diffeomorph.symm_apply_apply]
  have h₂ : inv (q, k (q, 0, y)) = ⟨(q, y), hyV⟩ :=
    hinj.injOn.leftInvOn_invFunOn (f := f) (mem_univ ⟨(q, y), hyV⟩)
  simp only [g, h₁, h₂]
  simp only [comp_apply, Φ₀, id] at hyχ hyρ
  rw [hyχ, hyρ, one_mul, one_mul]

/-- **Transport of functions along a family of isotopies over `[0, 1]`.** Let
`k : [0, 1] × [0, 1] × P → M` be smooth, with `M` a finite-dimensional, Hausdorff, σ-compact
boundaryless manifold and `P` boundaryless of the dimension of `M`, with every slice `k (a, s, ·)`
a smooth embedding, let `A ⊆ P` be compact, `h : [0, 1] × [0, 1] × P → ℝ` smooth, and `W ⊆ M`
open and containing `k (a, s, x)` for `x ∈ A`. Then there are a smooth
`G : [0, 1] × M × [0, 1] → ℝ` and a compact `C ⊆ W` such that `G (a, y, s) = 0` for `y ∉ C`, such
that `G (a, k (a, s, y), s) = h (a, s, y)` for every `a`, `s` and `y` near any point of `A`, and
such that `G (a, ·, ·) = 0` for every `a` with `h (a, ·, ·) = 0`. -/
theorem _root_.ContMDiff.exists_contMDiff_unitInterval_family_comp_eventuallyEq
    {k : unitInterval × unitInterval × P → M} (hk : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod J)) I ∞ k)
    (hd : Module.finrank ℝ E' = Module.finrank ℝ E) {A : Set P} (hA : IsCompact A)
    (hemb : ∀ a s, IsSmoothEmbedding J I ∞ fun x ↦ k (a, s, x))
    {h : unitInterval × unitInterval × P → ℝ}
    (hh : ContMDiff ((𝓡∂ 1).prod ((𝓡∂ 1).prod J)) 𝓘(ℝ) ∞ h)
    {W : Set M} (hW : IsOpen W) (hAW : ∀ a s, ∀ x ∈ A, k (a, s, x) ∈ W) :
    ∃ (G : unitInterval × M × unitInterval → ℝ) (C : Set M),
      ContMDiff ((𝓡∂ 1).prod (I.prod (𝓡∂ 1))) 𝓘(ℝ) ∞ G ∧ IsCompact C ∧ C ⊆ W ∧
      (∀ a y s, y ∉ C → G (a, y, s) = 0) ∧
      (∀ a s, ∀ x ∈ A, (fun y ↦ G (a, k (a, s, y), s)) =ᶠ[𝓝 x] fun y ↦ h (a, s, y)) ∧
      ∀ a, (∀ s y, h (a, s, y) = 0) → ∀ y s, G (a, y, s) = 0 := by
  -- Extend the pair `(k, h)` in the parameter near `univ ×ˢ A`, and shrink to a product
  -- `univ ×ˢ V`.
  obtain ⟨δ, hδ, U, hU, hAU, F, hF, hFkh⟩ :=
    (hk.prodMk hh).exists_contMDiffOn_extend_unitInterval (I := I.prod 𝓘(ℝ))
      (isCompact_univ.prod hA)
  obtain ⟨u, V, -, hV, hu, hAV, hVU⟩ := generalized_tube_lemma isCompact_univ hA hU hAU
  have hsV (s : unitInterval) (x : P) (hx : x ∈ V) : (s, x) ∈ U := hVU ⟨hu (mem_univ s), hx⟩
  let V' : TopologicalSpace.Opens P := ⟨V, hV⟩
  -- The families `k'` and `h'` over `ℝ`, run at a parameter `c q` equal to `q` on `[0, 1]`.
  obtain ⟨c, hc, hc_id, hc_mem, -⟩ :=
    SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo zero_le_one hδ
  have hF' : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡∂ 1).prod J)) (I.prod 𝓘(ℝ)) ∞
      fun p : ℝ × unitInterval × V' ↦ F (c p.1, p.2.1, p.2.2) :=
    hF.comp_contMDiff ((hc.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_snd.fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd.snd)))
      fun p ↦ ⟨by simpa only [zero_sub] using hc_mem p.1, hsV _ _ p.2.2.property⟩
  let k' : ℝ × unitInterval × V' → M := fun p ↦ (F (c p.1, p.2.1, p.2.2)).1
  let h' : ℝ × unitInterval × V' → ℝ := fun p ↦ (F (c p.1, p.2.1, p.2.2)).2
  have hk' : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡∂ 1).prod J)) I ∞ k' := contMDiff_fst.comp hF'
  have hh' : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡∂ 1).prod J)) 𝓘(ℝ) ∞ h' := contMDiff_snd.comp hF'
  have hFkh' (q : ℝ) (hq : q ∈ Icc 0 1) (s : unitInterval) (x : V') :
      F (c q, s, x) = (k (⟨q, hq⟩, s, x), h (⟨q, hq⟩, s, x)) := by
    rw [show c q = q from hc_id hq]
    exact hFkh ⟨q, hq⟩ (s, x) (hsV s x x.property)
  have hk'k (q : ℝ) (hq : q ∈ Icc 0 1) (s : unitInterval) (x : V') :
      k' (q, s, x) = k (⟨q, hq⟩, s, x) := by
    simp only [k', hFkh' q hq]
  have hh'h (q : ℝ) (hq : q ∈ Icc 0 1) (s : unitInterval) (x : V') :
      h' (q, s, x) = h (⟨q, hq⟩, s, x) := by
    simp only [h', hFkh' q hq]
  have hA' : IsCompact (Subtype.val ⁻¹' A : Set V') :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hA (by rw [Subtype.range_coe]; exact hAV)
  obtain ⟨G, C, hG, hC, hCW, hGC, hGk', hG0⟩ :=
    hk'.exists_contMDiff_family_comp_eventuallyEq hd isCompact_Icc hA' (fun q hq s ↦ by
        rw [show (fun x : V' ↦ k' (q, s, x)) = fun x : V' ↦ k (⟨q, hq⟩, s, x) from
          funext fun x ↦ hk'k q hq s x]
        exact (hemb ⟨q, hq⟩ s).comp_subtypeVal V')
      hh' hW fun q hq s x hx ↦ by rw [hk'k q hq]; exact hAW _ s x hx
  -- Restrict `G` to parameters in `[0, 1]`.
  refine ⟨fun p ↦ G (p.1, p.2), C, hG.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk
      contMDiff_snd), hC, hCW, fun a y s hy ↦ hGC a y s hy, fun a s x hx ↦ ?_,
    fun a ha y s ↦ hG0 a (fun s y ↦ by rw [hh'h a a.property]; exact ha s y) y s⟩
  have hx' := hGk' a a.property s ⟨x, hAV hx⟩ hx
  rw [EventuallyEq, ← map_nhds_subtypeVal_eq_nhds (hAV hx) (hV.mem_nhds (hAV hx)),
    eventually_map]
  filter_upwards [hx'] with y (hy : G (a, k' (a, s, y), s) = h' (a, s, y))
  rw [hk'k a a.property, hh'h a a.property] at hy
  exact hy

end TauCeti

end
