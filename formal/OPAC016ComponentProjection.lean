import Mathlib
import OPAC016Arithmetic
import OPAC016ComponentOrthogonal

/-!
Exact orthogonal projection of Type-C long-axis vertices from signed component data.
-/

namespace OPAC016

noncomputable def classProjectionCandidate {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) : Coord n :=
  longRoot i true -
    ((2 : ℝ) / (signedClassSize U (i, true) : ℝ)) • componentNormal U i

theorem classProjectionCandidate_mem {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) :
    classProjectionCandidate U i ∈ U := by
  have hc : classProjectionCandidate U i ∈ Uᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    rw [classProjectionCandidate, inner_sub_left, inner_longRoot,
      real_inner_smul_left, inner_componentNormal_of_mem_orthogonal U i hz]
    have hbpos : 0 < signedClassSize U (i, true) := signedClassSize_pos U (i, true)
    have hb : (signedClassSize U (i, true) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hbpos)
    simp [rootSign]
    field_simp [hb]
  simpa using hc

theorem starProjection_longRoot_true_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hU : RootSpanned U) (hnfull : coordVec i 1 ∉ U) :
    U.starProjection (longRoot i true) = classProjectionCandidate U i := by
  exact Submodule.eq_starProjection_of_mem_orthogonal'
    (classProjectionCandidate_mem U i)
    ((Uᗮ).smul_mem ((2 : ℝ) / (signedClassSize U (i, true) : ℝ))
      (componentNormal_mem_orthogonal_of_rootSpanned hU hnfull))
    (by simp [classProjectionCandidate])

theorem longRoot_mem_of_coord_full {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) (s : Bool)
    (hfull : coordVec i 1 ∈ U) : longRoot i s ∈ U := by
  have h := U.smul_mem (2 * rootSign s) hfull
  have heq : (2 * rootSign s) • coordVec i 1 = longRoot i s := by
    ext k
    by_cases hki : k = i <;>
      simp [longRoot, coordVec, hki]
  rw [← heq]
  exact h

theorem starProjection_longRoot_full {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) (s : Bool)
    (hfull : coordVec i 1 ∈ U) :
    U.starProjection (longRoot i s) = longRoot i s := by
  exact Submodule.starProjection_eq_self_iff.mpr
    (longRoot_mem_of_coord_full U i s hfull)

theorem longRoot_eq_sign_smul_true {n : ℕ} (i : Fin n) (s : Bool) :
    longRoot i s = rootSign s • longRoot i true := by
  ext k
  cases s <;> by_cases hki : k = i <;>
    simp [longRoot, coordVec, rootSign, hki]

theorem starProjection_longRoot_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hU : RootSpanned U) (hnfull : coordVec i 1 ∉ U) (s : Bool) :
    U.starProjection (longRoot i s) = rootSign s • classProjectionCandidate U i := by
  rw [longRoot_eq_sign_smul_true, map_smul,
    starProjection_longRoot_true_nonfull hU hnfull]

theorem componentNormal_apply_anchor {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hbal : signedBalancedAt U (i, true)) :
    componentNormal U i i = 1 := by
  have h := inner_componentNormal_signedCoordVec hbal i true
  have hrefl : signedConnected U (i, true) (i, true) := Relation.EqvGen.refl _
  rw [show signedCoordVec (i, true) = coordVec i 1 by
    ext k; simp [signedCoordVec, coordVec, rootSign]] at h
  simp [componentClassValue, hrefl, coordVec, EuclideanSpace.inner_single_right] at h
  exact h

theorem classProjectionCandidate_apply_anchor {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hnfull : coordVec i 1 ∉ U) :
    classProjectionCandidate U i i =
      balancedScore (signedClassSize U (i, true) : ℝ) := by
  have hbal := nonfull_anchor_balanced U i hnfull
  rw [classProjectionCandidate]
  simp [longRoot, rootSign, componentNormal_apply_anchor hbal, balancedScore]
  ring

end OPAC016
