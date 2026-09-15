import OPAC016Imports
import OPAC016ComponentOrthogonal

/-! Actual coordinate projection from signed components.
Prepared for Shawn Calvin Snelling. This module does not assert the final kappa theorem. -/
namespace OPAC016

noncomputable def componentProjectedCoord {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) (a : ℝ) : Coord n :=
  coordVec i a - (a / (signedClassSize U (i, true) : ℝ)) • componentNormal U i

theorem componentProjectedCoord_mem {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) (a : ℝ) :
    componentProjectedCoord U i a ∈ U := by
  have hmem : componentProjectedCoord U i a ∈ Uᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hb : (signedClassSize U (i, true) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (signedClassSize_pos U (i, true)))
    rw [componentProjectedCoord, inner_sub_left, real_inner_smul_left,
      inner_componentNormal_of_mem_orthogonal U i hz]
    simp [coordVec, EuclideanSpace.inner_single_left]
    field_simp
    ring
  simpa only [U.orthogonal_orthogonal] using hmem

theorem starProjection_coord_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U) (a : ℝ) :
    U.starProjection (coordVec i a) = componentProjectedCoord U i a := by
  have hd : (a / (signedClassSize U (i, true) : ℝ)) • componentNormal U i ∈ Uᗮ :=
    Uᗮ.smul_mem _ (componentNormal_mem_orthogonal_of_rootSpanned hU hnfull)
  exact Submodule.eq_starProjection_of_mem_orthogonal'
    (componentProjectedCoord_mem U i a) hd (by simp [componentProjectedCoord])

theorem starProjection_coord_full {n : ℕ}
    {U : Submodule ℝ (Coord n)} (i : Fin n)
    (hfull : coordVec i 1 ∈ U) (a : ℝ) :
    U.starProjection (coordVec i a) = coordVec i a := by
  have hm : coordVec i a ∈ U := by
    have heq : a • coordVec i 1 = coordVec i a := by
      ext j
      by_cases hji : j = i <;> simp [coordVec, hji]
    rw [← heq]
    exact U.smul_mem a hfull
  exact U.starProjection_eq_self_iff.mpr hm

theorem starProjection_long_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U) (s : Bool) :
    U.starProjection (longRoot i s) =
      componentProjectedCoord U i (2 * rootSign s) := by
  exact starProjection_coord_nonfull hU i hnfull _

#print axioms componentProjectedCoord_mem
#print axioms starProjection_coord_nonfull
#print axioms starProjection_coord_full
#print axioms starProjection_long_nonfull
end OPAC016
