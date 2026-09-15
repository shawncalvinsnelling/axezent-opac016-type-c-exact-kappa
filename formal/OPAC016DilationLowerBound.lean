import OPAC016CoordinateProjection

/-! Coordinate-function lower bounds for the exact Type-C dilation. -/
namespace OPAC016

def inducedPolytope {n : ℕ} (U : Submodule ℝ (Coord n)) : Set (Coord n) :=
  convexHull ℝ (inducedRoots U)

theorem componentNormal_apply_anchor {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hnfull : coordVec i 1 ∉ U) : componentNormal U i i = 1 := by
  have h := inner_componentNormal_signedCoordVec (nonfull_anchor_balanced U i hnfull) i true
  have hi : signedConnected U (i, true) (i, true) := Relation.EqvGen.refl _
  simpa [componentClassValue, hi, signedCoordVec, coordVec,
    EuclideanSpace.inner_single_right, rootSign] using h

theorem projected_long_anchor_coordinate {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U) :
    (U.starProjection (coordVec i 2)) i =
      2 - 2 / (signedClassSize U (i, true) : ℝ) := by
  rw [starProjection_coord_nonfull hU i hnfull]
  simp [componentProjectedCoord, componentNormal_apply_anchor hnfull]

theorem inducedRoot_coord_le_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hnfull : coordVec i 1 ∉ U) {α : Coord n}
    (hα : α ∈ inducedRoots U) : α i ≤ 1 := by
  rcases hα with ⟨hroot, hu⟩
  rcases hroot with hlong | hshort
  · rcases hlong with ⟨j, s, rfl⟩
    by_cases hij : i = j
    · subst j
      exact (hnfull (longRoot_forces_coordinate_line U i s hu 1)).elim
    · simp [longRoot, coordVec, hij]
  · rcases hshort with ⟨j, k, sj, sk, hjk, rfl⟩
    by_cases hij : i = j
    · subst j
      cases sj <;> cases sk <;> simp [shortRoot, coordVec, rootSign, hjk]
    · by_cases hik : i = k
      · subst k
        cases sj <;> cases sk <;> simp [shortRoot, coordVec, rootSign, hij]
      · simp [shortRoot, coordVec, hij, hik]

theorem inducedPolytope_coord_le_nonfull {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hnfull : coordVec i 1 ∉ U) {y : Coord n}
    (hy : y ∈ inducedPolytope U) : y i ≤ 1 := by
  have hsub : inducedRoots U ⊆ {x : Coord n | x i ≤ (1 : ℝ)} := by
    intro x hx
    exact inducedRoot_coord_le_nonfull hnfull hx
  have hlin : IsLinearMap ℝ (fun x : Coord n => x i) :=
    .mk (by intro x y; rfl) (by intro c x; rfl)
  exact (convexHull_min hsub (convex_halfSpace_le hlin 1)) hy

theorem nonfull_dilation_lower_bound {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U)
    {t : ℝ} (ht : 0 ≤ t) {y : Coord n} (hy : y ∈ inducedPolytope U)
    (heq : U.starProjection (coordVec i 2) = t • y) :
    2 - 2 / (signedClassSize U (i, true) : ℝ) ≤ t := by
  have hc := congrArg (fun v : Coord n => v i) heq
  rw [projected_long_anchor_coordinate hU i hnfull] at hc
  change 2 - 2 / (signedClassSize U (i, true) : ℝ) = t * y i at hc
  have hb := inducedPolytope_coord_le_nonfull hnfull hy
  nlinarith

end OPAC016

