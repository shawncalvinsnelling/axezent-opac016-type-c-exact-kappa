import Mathlib
import OPAC016RootSpanned

/-!
Basic convex geometry of the induced subsystem root polytope.
-/

namespace OPAC016

noncomputable def inducedRootPolytope {n : ℕ} (U : Submodule ℝ (Coord n)) :
    Set (Coord n) :=
  convexHull ℝ (inducedRoots U)

@[simp] theorem neg_longRoot {n : ℕ} (i : Fin n) (s : Bool) :
    - longRoot i s = longRoot i (!s) := by
  ext k
  cases s <;> simp [longRoot, coordVec, rootSign]

@[simp] theorem neg_shortRoot {n : ℕ}
    (i j : Fin n) (si sj : Bool) :
    - shortRoot i j si sj = shortRoot i j (!si) (!sj) := by
  ext k
  cases si <;> cases sj <;> simp [shortRoot, coordVec, rootSign] <;> ring

theorem typeCRoots_neg_mem {n : ℕ} {α : Coord n}
    (hα : α ∈ typeCRoots n) : -α ∈ typeCRoots n := by
  rcases hα with hlong | hshort
  · rcases hlong with ⟨i, s, rfl⟩
    exact Or.inl ⟨i, !s, neg_longRoot i s⟩
  · rcases hshort with ⟨i, j, si, sj, hij, rfl⟩
    exact Or.inr ⟨i, j, !si, !sj, hij, neg_shortRoot i j si sj⟩

theorem inducedRoots_neg_mem {n : ℕ} {U : Submodule ℝ (Coord n)}
    {α : Coord n} (hα : α ∈ inducedRoots U) :
    -α ∈ inducedRoots U := by
  exact ⟨typeCRoots_neg_mem hα.1, U.neg_mem hα.2⟩

theorem inducedRootPolytope_neg_mem {n : ℕ} {U : Submodule ℝ (Coord n)}
    {x : Coord n} (hx : x ∈ inducedRootPolytope U) :
    -x ∈ inducedRootPolytope U := by
  let P : Set (Coord n) := inducedRootPolytope U
  have hP : Convex ℝ P := convex_convexHull ℝ (inducedRoots U)
  have hconv : Convex ℝ {y : Coord n | -y ∈ P} := by
    intro a ha b hb r s hr hs hrs
    change -(r • a + s • b) ∈ P
    rw [neg_add, neg_smul, neg_smul]
    exact hP ha hb hr hs hrs
  have hsub : inducedRoots U ⊆ {y : Coord n | -y ∈ P} := by
    intro y hy
    exact subset_convexHull ℝ (inducedRoots U) (inducedRoots_neg_mem hy)
  exact (convexHull_min hsub hconv) hx

theorem zero_mem_inducedRootPolytope {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hUnz : U ≠ ⊥) :
    (0 : Coord n) ∈ inducedRootPolytope U := by
  obtain ⟨α, hα⟩ := rootSpanned_nonzero_has_root hU hUnz
  have hp : α ∈ inducedRootPolytope U :=
    subset_convexHull ℝ (inducedRoots U) hα
  have hn : -α ∈ inducedRootPolytope U := inducedRootPolytope_neg_mem hp
  have hm := (convex_convexHull ℝ (inducedRoots U)).midpoint_mem hp hn
  simpa [midpoint_eq_smul_add] using hm

end OPAC016
