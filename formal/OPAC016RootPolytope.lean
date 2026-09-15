import OPAC016Imports

/-!
Kernel-checked geometric layer for AXZ-OPAC-016.

The coordinate model is Mathlib's finite-dimensional EuclideanSpace, so the
same objects used for the convex-hull proof also carry the genuine inner
product needed by the later orthogonal-projection proof.
-/

namespace OPAC016

abbrev Coord (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordVec {n : ℕ} (i : Fin n) (a : ℝ) : Coord n :=
  PiLp.single 2 i a

@[simp] theorem coordVec_apply_self {n : ℕ} (i : Fin n) (a : ℝ) :
    coordVec i a i = a := by
  simp [coordVec]

@[simp] theorem coordVec_apply_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) (a : ℝ) :
    coordVec i a j = 0 := by
  simp [coordVec, h]

def rootSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem rootSign_sq (b : Bool) : rootSign b * rootSign b = 1 := by
  cases b <;> norm_num [rootSign]

def longRoot {n : ℕ} (i : Fin n) (s : Bool) : Coord n :=
  coordVec i (2 * rootSign s)

def shortRoot {n : ℕ} (i j : Fin n) (si sj : Bool) : Coord n :=
  coordVec i (rootSign si) + coordVec j (rootSign sj)

def longRoots (n : ℕ) : Set (Coord n) :=
  {x | ∃ i s, x = longRoot i s}

def shortRoots (n : ℕ) : Set (Coord n) :=
  {x | ∃ i j si sj, i ≠ j ∧ x = shortRoot i j si sj}

def typeCRoots (n : ℕ) : Set (Coord n) :=
  longRoots n ∪ shortRoots n

def typeCRootPolytope (n : ℕ) : Set (Coord n) :=
  convexHull ℝ (typeCRoots n)

def longRootPolytope (n : ℕ) : Set (Coord n) :=
  convexHull ℝ (longRoots n)

theorem longRoot_mem_longRoots {n : ℕ} (i : Fin n) (s : Bool) :
    longRoot i s ∈ longRoots n := by
  exact ⟨i, s, rfl⟩

theorem shortRoot_eq_midpoint {n : ℕ} (i j : Fin n) (si sj : Bool) :
    shortRoot i j si sj = midpoint ℝ (longRoot i si) (longRoot j sj) := by
  cases si <;> cases sj <;>
    ext k <;>
    rw [midpoint_eq_smul_add] <;>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [shortRoot, longRoot, coordVec, rootSign, hki, hkj] <;> ring

theorem shortRoot_mem_longRootPolytope {n : ℕ}
    (i j : Fin n) (si sj : Bool) :
    shortRoot i j si sj ∈ longRootPolytope n := by
  rw [shortRoot_eq_midpoint]
  apply (convex_convexHull ℝ (longRoots n)).midpoint_mem
  · exact subset_convexHull ℝ (longRoots n) (longRoot_mem_longRoots i si)
  · exact subset_convexHull ℝ (longRoots n) (longRoot_mem_longRoots j sj)

theorem typeCRoots_subset_longRootPolytope (n : ℕ) :
    typeCRoots n ⊆ longRootPolytope n := by
  intro x hx
  rcases hx with hx | hx
  · exact subset_convexHull ℝ (longRoots n) hx
  · rcases hx with ⟨i, j, si, sj, hij, rfl⟩
    exact shortRoot_mem_longRootPolytope i j si sj

theorem longRoots_subset_typeCRoots (n : ℕ) :
    longRoots n ⊆ typeCRoots n := by
  intro x hx
  exact Or.inl hx

theorem typeCRootPolytope_eq_longRootPolytope (n : ℕ) :
    typeCRootPolytope n = longRootPolytope n := by
  apply le_antisymm
  · exact convexHull_min (typeCRoots_subset_longRootPolytope n)
      (convex_convexHull ℝ (longRoots n))
  · exact convexHull_mono (longRoots_subset_typeCRoots n)

end OPAC016
