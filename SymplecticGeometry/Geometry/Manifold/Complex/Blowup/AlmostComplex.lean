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
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  {U : Opens X} {V : Opens Y}

/-- Let `f : X → Y` agree on an open set `U` with a diffeomorphism `Ψ` from `U` onto an open set
`V`. Then the differential of `f` at a point of `U` is complex linear for the pullback of a
structure `K` of `Y` along `Ψ` (followed by the inclusion of `V`) and for `K`. -/
theorem mfderiv_apply_localPullback_subtypeVal_comp (Ψ : U ≃ₘ^∞⟮I, I⟯ V) {f : X → Y}
    (hf : ∀ x : U, f x = Ψ x) (K : SmoothAlmostComplexStructure I Y) (x : U)
    (v : TangentSpace I x) :
    mfderiv I I f x (localPullback Ψ.isLocalDiffeomorph_subtypeVal_comp K x v) =
      K (f x) (mfderiv I I f x v) := by
  have hfx : MDifferentiableAt I I f x :=
    (Ψ.isLocalDiffeomorphAt_of_coe_eq hf x).mdifferentiableAt (by simp)
  have h := ((hfx.hasMFDerivAt.comp x
    ((contMDiff_subtypeVal : ContMDiff I I 1 (Subtype.val : U → X)).mdifferentiableAt
      one_ne_zero).hasMFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u : U ↦ (hf u).symm)).mfderiv
  have hmf : ∀ w : TangentSpace I x,
      mfderiv I I (fun u : U ↦ (Ψ u : Y)) x w = mfderiv I I f x w := fun w ↦
    (DFunLike.congr_fun h w).trans (by
      simp only [comp_apply, Manifold.mfderiv_subtype_val, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply]
      -- `tangentSpaceCast` is the identity of the model space.
      exact (rfl))
  refine (hmf _).symm.trans ((mfderiv_localPullback_apply _ K x v).trans ?_)
  rw [hmf, hf x]

end TauCeti.SmoothAlmostComplexStructure

namespace SymplecticGeometry

namespace Blowup

open BlowupModel TauCeti TauCeti.SmoothAlmostComplexStructure

open GluedAlong (inl inr)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]

/-! ### The two pieces -/

/-- The range of `inr (gluingHomeomorph c)`, as an open set of the blowup. -/
private def rangeInrOpens : Opens (Blowup c) := (isLocalDiffeomorph_inr_real c).image

/-- The inverse of `inr` on its range, as a diffeomorphism onto the part of the model over the
target of `c`. -/
private def rangeInrDiffeomorph :
    rangeInrOpens c ≃ₘ^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ modelOpens c :=
  ((isLocalDiffeomorph_inr_real c).diffeomorphOfInjective (GluedAlong.inr_injective _)).symm

private theorem inr_rangeInrDiffeomorph (z : rangeInrOpens c) :
    inr (gluingHomeomorph c) (rangeInrDiffeomorph c z) = z :=
  (isLocalDiffeomorph_inr_real c).apply_diffeomorphOfInjective_symm _ z

private theorem coe_rangeInrDiffeomorph (z : rangeInrOpens c) :
    (rangeInrDiffeomorph c z : BlowupModel n) = lift c z := by
  conv_rhs => rw [← inr_rangeInrDiffeomorph c z, lift_inr]

/-- The blowdown sends the range of `inr` into the source of `c`. -/
private theorem blowdown_mem_source {z : Blowup c} (hz : z ∈ rangeInrOpens c) :
    blowdown c z ∈ c.source := by
  obtain ⟨y, rfl⟩ := hz
  rw [blowdown_inr]
  exact c.map_target ((mem_modelOpens c).1 y.property)

private theorem isLocalDiffeomorph_offDivisor :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun z : offDivisorOpens c ↦ (blowdownRealDiffeomorph c z : M)) :=
  (blowdownRealDiffeomorph c).isLocalDiffeomorph_subtypeVal_comp

private theorem isLocalDiffeomorph_rangeInr :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (fun z : rangeInrOpens c ↦ (rangeInrDiffeomorph c z : BlowupModel n)) :=
  (rangeInrDiffeomorph c).isLocalDiffeomorph_subtypeVal_comp

/-- The two open sets cover the blowup. -/
private def cover : Bool → Opens (Blowup c) := fun b ↦ cond b (rangeInrOpens c) (offDivisorOpens c)

private theorem isOpenCover_cover : IsOpenCover (cover c) := by
  refine IsOpenCover.mk (eq_top_iff.2 fun z _ ↦ Opens.mem_iSup.2 ?_)
  rcases GluedAlong.exists_inl_or_exists_inr _ z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨false, (mem_offDivisorOpens c).2 (inl_notMem_exceptionalDivisor c x)⟩
  · exact ⟨true, mem_range_self y⟩

variable (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M)

/-- The structure off the exceptional divisor: the pullback of `J` along the blowdown. -/
private def offDivisorStructure :
    SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (offDivisorOpens c) :=
  localPullback (isLocalDiffeomorph_offDivisor c) J

/-- The structure on the range of `inr`: the pullback along `lift` of the structure of the
complex manifold `BlowupModel n`. -/
private def rangeInrStructure :
    SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (rangeInrOpens c) :=
  localPullback (isLocalDiffeomorph_rangeInr c)
    (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n))

/-- The family of structures on the two open sets. -/
private def coverStructure : ∀ b, SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) (cover c b)
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

private theorem mfderiv_lift_rangeInrStructure (z : rangeInrOpens c)
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z
        (rangeInrStructure c z v) =
      ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n) (lift c z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (lift c) z v) :=
  mfderiv_apply_localPullback_subtypeVal_comp (rangeInrDiffeomorph c)
    (fun z ↦ (coe_rangeInrDiffeomorph c z).symm) _ z v

/-- On the range of `inr`, `lift` is a local diffeomorphism. -/
private theorem isLocalDiffeomorphAt_lift {z : Blowup c} (hz : z ∈ rangeInrOpens c) :
    IsLocalDiffeomorphAt 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (lift c) z :=
  (rangeInrDiffeomorph c).isLocalDiffeomorphAt_of_coe_eq
    (fun v ↦ (coe_rangeInrDiffeomorph c v).symm) ⟨z, hz⟩

variable {c J}

/-- The two pieces agree where both are defined. -/
private theorem offDivisorStructure_apply_eq
    (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
      c.source)
    {z : Blowup c} (h₀ : z ∈ offDivisorOpens c) (h₁ : z ∈ rangeInrOpens c)
    (v : Fin (n + 1) → ℂ) :
    offDivisorStructure c J ⟨z, h₀⟩ v = rangeInrStructure c ⟨z, h₁⟩ v := by
  have hsrc := blowdown_mem_source c h₁
  have hc' := c.toOpenPartialHomeomorph.isLocalDiffeomorphAt_of_mem_maximalAtlas hc.out hsrc
  have hπ := isLocalDiffeomorphAt_blowdown_real c ((mem_offDivisorOpens c).1 h₀)
  have hl := isLocalDiffeomorphAt_lift c h₁
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
    filter_upwards [(rangeInrOpens c).isOpen.mem_nhds h₁] with w hw
    exact (blowdown_lift c (blowdown_mem_source c hw)).symm
  have hd : ∀ w, A (B w) = D (L w) := fun w ↦
    (mfderiv_comp_apply z (hc'.mdifferentiableAt (by simp)) (hπ.mdifferentiableAt (by simp))
      w).symm.trans ((DFunLike.congr_fun hEq.mfderiv_eq w).trans
        (mfderiv_comp_apply z hbd (hl.mdifferentiableAt (by simp)) w))
  -- The vectors below live in tangent spaces, which are `ℂⁿ⁺¹` only by definition; `id` gives
  -- them that type, so that multiplication by `i` applies.
  have hD : ∀ u : Fin (n + 1) → ℂ,
      D (Complex.I • u) = Complex.I • @id (Fin (n + 1) → ℂ) (D u) := fun u ↦ by
    simp only [D, hbdℂ.mfderiv_modelWithCornersSelf_restrictScalars_apply (R := ℝ), id]
    exact (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) BlowupModel.blowdown
      (lift c z)).map_smul Complex.I u
  have lhs : A (B (offDivisorStructure c J ⟨z, h₀⟩ v)) =
      Complex.I • @id (Fin (n + 1) → ℂ) (A (B v)) :=
    (congrArg A (mfderiv_blowdown_offDivisorStructure c J ⟨z, h₀⟩ v)).trans
      ((hJ'.mfderiv_apply_commute _).trans (ofComplexManifold_apply _ _))
  have rhs : A (B (rangeInrStructure c ⟨z, h₁⟩ v)) =
      Complex.I • @id (Fin (n + 1) → ℂ) (A (B v)) :=
    (hd _).trans ((congrArg D ((mfderiv_lift_rangeInrStructure c ⟨z, h₁⟩ v).trans
      (ofComplexManifold_apply _ _))).trans ((hD _).trans (congrArg _ (hd v).symm)))
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
  have hz' : z ∈ cover c true := hz
  rw [almostComplexStructure, glue_apply _ _ true z hz', Manifold.tangentSpaceOpenEquiv_apply,
    Manifold.tangentSpaceOpenEquiv_symm_apply]
  exact mfderiv_lift_rangeInrStructure c ⟨z, hz'⟩ v

end Blowup

end SymplecticGeometry

end
