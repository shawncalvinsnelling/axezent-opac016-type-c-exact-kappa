import Mathlib
import OPAC016SignedComponents

/-!
Finite signed equivalence classes for the Type-C component decomposition.
-/

namespace OPAC016

noncomputable def signedClassFinset {n : ℕ} (U : Submodule ℝ (Coord n))
    (a : SignedCoord n) : Finset (SignedCoord n) := by
  classical
  exact Finset.univ.filter (fun b => signedConnected U a b)

@[simp] theorem mem_signedClassFinset {n : ℕ} {U : Submodule ℝ (Coord n)}
    {a b : SignedCoord n} :
    b ∈ signedClassFinset U a ↔ signedConnected U a b := by
  classical
  simp [signedClassFinset]

theorem anchor_mem_signedClassFinset {n : ℕ} (U : Submodule ℝ (Coord n))
    (a : SignedCoord n) : a ∈ signedClassFinset U a := by
  rw [mem_signedClassFinset]
  exact Relation.EqvGen.refl _

def signedClassSize {n : ℕ} (U : Submodule ℝ (Coord n))
    (a : SignedCoord n) : ℕ :=
  (signedClassFinset U a).card

theorem signedClassSize_pos {n : ℕ} (U : Submodule ℝ (Coord n))
    (a : SignedCoord n) : 0 < signedClassSize U a := by
  rw [signedClassSize]
  exact Finset.card_pos.mpr ⟨a, anchor_mem_signedClassFinset U a⟩

def signedBalancedAt {n : ℕ} (U : Submodule ℝ (Coord n))
    (a : SignedCoord n) : Prop :=
  ¬ signedConnected U a (a.1, !a.2)

theorem signedBalancedAt_no_opposite {n : ℕ} {U : Submodule ℝ (Coord n)}
    {a b : SignedCoord n} (hbal : signedBalancedAt U a)
    (hb : signedConnected U a b) :
    ¬ signedConnected U a (b.1, !b.2) := by
  intro hbo
  have hc := signedConnected_complement hb
  have hback : signedConnected U (b.1, !b.2) (a.1, !a.2) :=
    Relation.EqvGen.symm _ _ hc
  have : signedConnected U a (a.1, !a.2) :=
    Relation.EqvGen.trans _ _ _ hbo hback
  exact hbal this

theorem nonfull_anchor_balanced {n : ℕ} (U : Submodule ℝ (Coord n))
    (i : Fin n) (hnfull : coordVec i 1 ∉ U) :
    signedBalancedAt U (i, true) := by
  intro hunbal
  exact hnfull (unbalanced_forces_coordinate_line U i hunbal 1)

theorem coord_zero_of_coordVec_one_mem {n : ℕ} {U : Submodule ℝ (Coord n)}
    {i : Fin n} (hi : coordVec i 1 ∈ U) {z : Coord n} (hz : z ∈ Uᗮ) :
    z i = 0 := by
  have horth : @inner ℝ (Coord n) _ (coordVec i 1) z = 0 :=
    Submodule.inner_right_of_mem_orthogonal hi hz
  simpa [coordVec, EuclideanSpace.inner_single_left] using horth

theorem connected_anchor_true_to_full {n : ℕ} (U : Submodule ℝ (Coord n))
    (i j : Fin n) (s : Bool)
    (hconn : signedConnected U (i, true) (j, s))
    (hjfull : coordVec j 1 ∈ U) (a : ℝ) :
    coordVec i a ∈ U := by
  apply coordVec_mem_of_orthogonal_coord_zero U i
  intro z hz
  have hzj : z j = 0 := coord_zero_of_coordVec_one_mem hjfull hz
  have hval := signedConnected_value_eq hz hconn
  cases s <;> norm_num [signedValue, rootSign, hzj] at hval ⊢ <;> linarith

end OPAC016
