/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Glue
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Descent
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.LocalPullback
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The almost complex blowup

Let `M` be a smooth manifold modelled on `E = ℂⁿ⁺¹`, with a smooth almost complex structure `J`,
and let `c` be a chart of `M` at `p₀` (a `SymplecticGeometry.BlowupChart M p₀`) in the smooth
maximal atlas which is `J`-holomorphic on its source: `c` is pseudoholomorphic from `J` to the
standard structure of `E`. This file builds the almost complex structure `J̃` on the blowup
`SymplecticGeometry.Blowup c` of `M` at `p₀` along `c`
(`SymplecticGeometry.Blowup.almostComplexStructure`), following McDuff–Salamon, §7.1.

The structure is glued, with `TauCeti.SmoothAlmostComplexStructure.glue`, from two pieces:

* off the exceptional divisor, the pullback (Tau Ceti's
  `TauCeti.SmoothAlmostComplexStructure.localPullback`) of `J` along the blowdown, which is a
  diffeomorphism there (`SymplecticGeometry.Blowup.blowdownRealDiffeomorph`);
* on the range of `GluedAlong.inr`, the pullback along the map `SymplecticGeometry.Blowup.lift`
  to the model blowup of the almost complex structure of the complex manifold `BlowupModel n`.

They agree where both are defined: there the chart `c` composed with the blowdown is the blowdown
of the model composed with `lift`, both pieces make this map complex linear, and its derivative
is injective.

## Main results

* `SymplecticGeometry.Blowup.almostComplexStructure_apply_inl`: off the exceptional divisor,
  `J̃` is `(dπ)⁻¹ ∘ J ∘ dπ`, for the blowdown `π`.
* `SymplecticGeometry.Blowup.almostComplexStructure_lift`: on the range of `inr`, `J̃` is the
  pullback of multiplication by `i` along `lift`.
* `SymplecticGeometry.Blowup.mfderiv_blowdown_comp_almostComplexStructure`: off the exceptional
  divisor, `dπ ∘ J̃ = J ∘ dπ`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1 (the complex blowup).
-/

public section

open Set Function Topology TopologicalSpace
open scoped Manifold ContDiff TauCeti.ComplexManifold

noncomputable section

namespace SymplecticGeometry

namespace Blowup

open BlowupModel TauCeti TauCeti.SmoothAlmostComplexStructure

open GluedAlong (inl inr)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := n) M p₀)

/-! ### The cover by two open sets -/

/-- The complement of the exceptional divisor and the range of `inr`. -/
private def cover : Bool → Opens (Blowup c)
  | false => offDivisorOpens c
  | true => GluedAlong.rangeInr (gluingHomeomorph c)

private theorem mem_cover_true {z : Blowup c} :
    z ∈ cover c true ↔ z ∈ range (inr (gluingHomeomorph c)) :=
  GluedAlong.mem_rangeInr _

/-- The two open sets cover the blowup. -/
private theorem isOpenCover_cover : IsOpenCover (cover c) := by
  refine IsOpenCover.mk (eq_top_iff.2 fun z _ ↦ Opens.mem_iSup.2 ?_)
  rcases (Set.ext_iff.1 (GluedAlong.range_inl_union_range_inr (gluingHomeomorph c)) z).2
    (mem_univ z) with h | h
  · exact ⟨false, (mem_offDivisorOpens c).2 (by rwa [range_inl] at h)⟩
  · exact ⟨true, (mem_cover_true c).2 h⟩

variable [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]

/-! ### The two pieces -/

private theorem isLocalDiffeomorph_offDivisor :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun z : offDivisorOpens c ↦ (blowdownRealDiffeomorph c z : M)) :=
  (blowdownRealDiffeomorph c).isLocalDiffeomorph_subtypeVal_comp

private theorem isLocalDiffeomorph_rangeInr :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun z : GluedAlong.rangeInr (gluingHomeomorph c) ↦
        (GluedAlong.rangeInrDiffeomorph (isCompatible_real c hc.out) z : BlowupModel n)) :=
  (GluedAlong.rangeInrDiffeomorph (isCompatible_real c hc.out)).isLocalDiffeomorph_subtypeVal_comp

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M)

/-- The structure off the exceptional divisor: the pullback of `J` along the blowdown. -/
private def offDivisorStructure :
    SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (offDivisorOpens c) :=
  localPullback (isLocalDiffeomorph_offDivisor c) J

/-- The structure on the range of `inr`: the pullback along `lift` of the structure of the
complex manifold `BlowupModel n`. -/
private def rangeInrStructure :
    SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ)
      (GluedAlong.rangeInr (gluingHomeomorph c)) :=
  localPullback (isLocalDiffeomorph_rangeInr c)
    (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))

/-- The family of structures on the two open sets. -/
private def coverStructure :
    ∀ b, SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (cover c b)
  | false => offDivisorStructure c J
  | true => rangeInrStructure c

/-! ### Differentials on the two pieces -/

private theorem mfderiv_blowdown_offDivisorStructure (z : offDivisorOpens c)
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z
        (offDivisorStructure c J z v) =
      J (blowdown c z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z v) :=
  mfderiv_apply_localPullback_subtypeVal_comp (blowdownRealDiffeomorph c)
    (fun z ↦ (coe_blowdownRealDiffeomorph_apply c z).symm) J z v

private theorem mfderiv_lift_rangeInrStructure (z : GluedAlong.rangeInr (gluingHomeomorph c))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z
        (rangeInrStructure c z v) =
      ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n) (lift c z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z v) :=
  mfderiv_apply_localPullback_subtypeVal_comp
    (GluedAlong.rangeInrDiffeomorph (isCompatible_real c hc.out))
    (fun z ↦ (coe_rangeInrDiffeomorph_apply c z).symm) _ z v

variable {c J}

/-- The two pieces agree where both are defined. -/
private theorem offDivisorStructure_apply_eq
    (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
      c.source)
    {z : Blowup c} (h₀ : z ∈ offDivisorOpens c)
    (h₁ : z ∈ GluedAlong.rangeInr (gluingHomeomorph c)) (v : Fin (n + 1) → ℂ) :
    offDivisorStructure c J ⟨z, h₀⟩ v = rangeInrStructure c ⟨z, h₁⟩ v := by
  have hr : ∀ {w}, w ∈ GluedAlong.rangeInr (gluingHomeomorph c) →
      w ∈ range (inr (gluingHomeomorph c)) := fun hw ↦ by
    rwa [← SetLike.mem_coe, GluedAlong.coe_rangeInr] at hw
  have hsrc := blowdown_mem_source c (hr h₁)
  have hc' := c.toOpenPartialHomeomorph.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out hsrc
  have hπ := isLocalDiffeomorphAt_blowdown_real c ((mem_offDivisorOpens c).1 h₀)
  have hl := isLocalDiffeomorphAt_lift c (hr h₁)
  have hJ' := (hJ.isPseudoholomorphicWithinAt hsrc).isPseudoholomorphicAt_of_mem_nhds
    (c.open_source.mem_nhds hsrc)
  have hbdℂ : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
      BlowupModel.blowdown (lift c z) :=
    (BlowupModel.contMDiff_blowdown (n := n) ω).mdifferentiableAt (by simp)
  have hbd : MDifferentiableAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ)
      BlowupModel.blowdown (lift c z) :=
    ((BlowupModel.contMDiff_blowdown (n := n) ω).restrictScalars' ℝ).mdifferentiableAt
      (by simp)
  set A := mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) c (blowdown c z)
  set B := mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z
  set D := mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) BlowupModel.blowdown (lift c z)
  set L := mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z
  -- Near `z`, `c ∘ blowdown c` is `BlowupModel.blowdown ∘ lift c`.
  have hEq : c ∘ blowdown c =ᶠ[𝓝 z] BlowupModel.blowdown ∘ lift c := by
    filter_upwards [(GluedAlong.rangeInr (gluingHomeomorph c)).isOpen.mem_nhds h₁] with w hw
    exact (blowdown_lift c (blowdown_mem_source c (hr hw))).symm
  have hd : ∀ w, A (B w) = D (L w) := fun w ↦
    (mfderiv_comp_apply z (hc'.mdifferentiableAt (by simp)) (hπ.mdifferentiableAt (by simp))
      w).symm.trans ((DFunLike.congr_fun hEq.mfderiv_eq w).trans
        (mfderiv_comp_apply z hbd (hl.mdifferentiableAt (by simp)) w))
  -- Both sides are multiplication by `i` after `A ∘ B`. The vectors live in tangent spaces,
  -- which are `ℂⁿ⁺¹` only by definition; `id` gives them that type.
  have lhs : A (B (offDivisorStructure c J ⟨z, h₀⟩ v)) =
      Complex.I • @id (Fin (n + 1) → ℂ) (A (B v)) :=
    (congrArg A (mfderiv_blowdown_offDivisorStructure c J ⟨z, h₀⟩ v)).trans
      ((hJ'.mfderiv_apply_commute _).trans (ofComplexManifold_apply _ _))
  have rhs : A (B (rangeInrStructure c ⟨z, h₁⟩ v)) =
      Complex.I • @id (Fin (n + 1) → ℂ) (A (B v)) :=
    (hd _).trans ((congrArg D (mfderiv_lift_rangeInrStructure c ⟨z, h₁⟩ v)).trans
      ((hbdℂ.mfderiv_ofComplexManifold_apply _).trans
        ((ofComplexManifold_apply _ _).trans (congrArg _ (hd v).symm))))
  exact ((hc'.isInvertible_mfderiv (by simp)).injective.comp
    (hπ.isInvertible_mfderiv (by simp)).injective) (lhs.trans rhs.symm)

variable (c J)

private theorem agreeOnOverlaps_coverStructure
    (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
      c.source) :
    AgreeOnOverlaps (cover c) (coverStructure c J) := by
  rw [agreeOnOverlaps_iff]
  rintro (_ | _) (_ | _) z hi hj v
  · rfl
  · rw [Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply,
      Manifold.tangentSpaceOpenEquiv_symm_apply, Manifold.tangentSpaceOpenEquiv_symm_apply]
    exact offDivisorStructure_apply_eq hJ hi hj v
  · rw [Manifold.tangentSpaceOpenEquiv_apply, Manifold.tangentSpaceOpenEquiv_apply,
      Manifold.tangentSpaceOpenEquiv_symm_apply, Manifold.tangentSpaceOpenEquiv_symm_apply]
    exact (offDivisorStructure_apply_eq hJ hj hi v).symm
  · rfl

/-! ### The almost complex blowup -/

/-- **The almost complex blowup.** For a smooth almost complex structure `J` on `M` and a chart
`c` of the smooth atlas that is pseudoholomorphic on its source, from `J` to the standard structure
of `ℂⁿ⁺¹`, the almost complex structure `J̃` on the blowup `Blowup c`: off the exceptional
divisor it is the pullback of `J` by the blowdown (`almostComplexStructure_apply_inl`), and on the
range of `inr` the pullback by `lift c` of the structure of the complex manifold `BlowupModel n`
(`almostComplexStructure_lift`). -/
def almostComplexStructure
    (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
      c.source) :
    SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (Blowup c) :=
  glue (isOpenCover_cover c) (agreeOnOverlaps_coverStructure c J hJ)

variable (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
  c.source)

/-- Off the exceptional divisor, the differential of the blowdown is complex linear for the
almost complex blowup and `J`: `dπ (J̃ v) = J (dπ v)`. -/
theorem mfderiv_blowdown_almostComplexStructure_apply {z : Blowup c}
    (hz : z ∉ exceptionalDivisor c) (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z
        (almostComplexStructure c J hJ z v) =
      J (blowdown c z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z v) := by
  have hz' : z ∈ cover c false := (mem_offDivisorOpens c).2 hz
  rw [almostComplexStructure, glue_apply _ _ false z hz', Manifold.tangentSpaceOpenEquiv_apply,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  exact mfderiv_blowdown_offDivisorStructure c J ⟨z, hz'⟩ v

/-- Off the exceptional divisor, `dπ ∘ J̃ = J ∘ dπ` for the blowdown `π` and the almost complex
blowup `J̃`. -/
theorem mfderiv_blowdown_comp_almostComplexStructure {z : Blowup c}
    (hz : z ∉ exceptionalDivisor c) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z ∘L
        (almostComplexStructure c J hJ).toEndomorphism z =
      J.toEndomorphism (blowdown c z) ∘L
        mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z := by
  ext1 v
  exact mfderiv_blowdown_almostComplexStructure_apply c J hJ hz v

/-- Off the exceptional divisor, the almost complex blowup is the pullback of `J` by the
blowdown `π`: at `inl x`, `J̃ v = (dπ)⁻¹ (J (dπ v))`, where `dπ` is invertible. -/
theorem almostComplexStructure_apply_inl (x : puncturedOpens c)
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (inl (gluingHomeomorph c) x)) :
    almostComplexStructure c J hJ (inl (gluingHomeomorph c) x) v =
      ((isLocalDiffeomorphAt_blowdown_real c
          (inl_notMem_exceptionalDivisor c x)).mfderivToContinuousLinearEquiv (by simp)).symm
        (J (blowdown c (inl (gluingHomeomorph c) x))
          (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c)
            (inl (gluingHomeomorph c) x) v)) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, ← ContinuousLinearEquiv.coe_coe,
    IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe,
    mfderiv_blowdown_almostComplexStructure_apply c J hJ (inl_notMem_exceptionalDivisor c x)]

/-- On the range of `inr`, the domain of `lift c`, the differential of `lift c` is complex
linear for the almost complex blowup and the structure of the complex manifold `BlowupModel n`,
which is multiplication by `i` (`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold_apply`). -/
theorem almostComplexStructure_lift {z : Blowup c} (hz : z ∈ range (inr (gluingHomeomorph c)))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z
        (almostComplexStructure c J hJ z v) =
      ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n) (lift c z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z v) := by
  have hz' : z ∈ cover c true := (mem_cover_true c).2 hz
  rw [almostComplexStructure, glue_apply _ _ true z hz', Manifold.tangentSpaceOpenEquiv_apply,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  exact mfderiv_lift_rangeInrStructure c ⟨z, hz'⟩ v

end Blowup

end SymplecticGeometry

end
