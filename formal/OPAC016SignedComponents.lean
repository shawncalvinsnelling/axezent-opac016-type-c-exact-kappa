import Mathlib
import OPAC016RootSpanned

/-!
Signed-component engine for the Type-C normal-form theorem.

A short root in `U` forces an equality between two signed coordinate values on
every vector in `Uᗮ`.  We encode those equalities as edges on `Fin n × Bool`
and use `Relation.EqvGen` for the signed connected components.
-/

namespace OPAC016

@[simp] theorem rootSign_not (b : Bool) : rootSign (!b) = -rootSign b := by
  cases b <;> norm_num [rootSign]

abbrev SignedCoord (n : ℕ) := Fin n × Bool

def signedValue {n : ℕ} (z : Coord n) (a : SignedCoord n) : ℝ :=
  rootSign a.2 * z a.1

def signedEdge {n : ℕ} (U : Submodule ℝ (Coord n))
    (a b : SignedCoord n) : Prop :=
  a.1 ≠ b.1 ∧ shortRoot a.1 b.1 a.2 (!b.2) ∈ U

def signedConnected {n : ℕ} (U : Submodule ℝ (Coord n))
    (a b : SignedCoord n) : Prop :=
  Relation.EqvGen (signedEdge U) a b

theorem inner_longRoot {n : ℕ} (i : Fin n) (s : Bool) (z : Coord n) :
    @inner ℝ (Coord n) _ (longRoot i s) z = 2 * rootSign s * z i := by
  simp [longRoot, coordVec, EuclideanSpace.inner_single_left, mul_assoc]

theorem inner_shortRoot {n : ℕ} (i j : Fin n) (si sj : Bool) (z : Coord n) :
    @inner ℝ (Coord n) _ (shortRoot i j si sj) z =
      rootSign si * z i + rootSign sj * z j := by
  rw [shortRoot, inner_add_left]
  simp [coordVec, EuclideanSpace.inner_single_left]

theorem signedEdge_value_eq {n : ℕ} {U : Submodule ℝ (Coord n)}
    {z : Coord n} (hz : z ∈ Uᗮ) {a b : SignedCoord n}
    (hab : signedEdge U a b) :
    signedValue z a = signedValue z b := by
  rcases hab with ⟨hne, hroot⟩
  have horth : @inner ℝ (Coord n) _
      (shortRoot a.1 b.1 a.2 (!b.2)) z = 0 :=
    Submodule.inner_right_of_mem_orthogonal hroot hz
  rw [inner_shortRoot, rootSign_not] at horth
  dsimp [signedValue]
  linarith

theorem signedConnected_value_eq {n : ℕ} {U : Submodule ℝ (Coord n)}
    {z : Coord n} (hz : z ∈ Uᗮ) {a b : SignedCoord n}
    (hab : signedConnected U a b) :
    signedValue z a = signedValue z b := by
  induction hab with
  | rel x y hxy => exact signedEdge_value_eq hz hxy
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem signedConnected_shortRoot_mem {n : ℕ} {U : Submodule ℝ (Coord n)}
    {a b : SignedCoord n} (hne : a.1 ≠ b.1)
    (hab : signedConnected U a b) :
    shortRoot a.1 b.1 a.2 (!b.2) ∈ U := by
  rw [← U.orthogonal_orthogonal, Submodule.mem_orthogonal']
  intro z hz
  have hval := signedConnected_value_eq hz hab
  rw [inner_shortRoot, rootSign_not]
  dsimp [signedValue] at hval
  linarith

theorem signedEdge_complement {n : ℕ} {U : Submodule ℝ (Coord n)}
    {a b : SignedCoord n} (hab : signedEdge U a b) :
    signedEdge U (a.1, !a.2) (b.1, !b.2) := by
  rcases hab with ⟨hne, hroot⟩
  refine ⟨hne, ?_⟩
  have hneg : shortRoot a.1 b.1 (!a.2) (!(!b.2)) =
      - shortRoot a.1 b.1 a.2 (!b.2) := by
    ext k
    cases a.2 <;> cases b.2 <;>
      by_cases hka : k = a.1 <;> by_cases hkb : k = b.1
    all_goals simp [shortRoot, coordVec, rootSign, hka, hkb] at *
    all_goals linarith
  rw [hneg]
  exact U.neg_mem hroot

theorem signedConnected_complement {n : ℕ} {U : Submodule ℝ (Coord n)}
    {a b : SignedCoord n} (hab : signedConnected U a b) :
    signedConnected U (a.1, !a.2) (b.1, !b.2) := by
  induction hab with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (signedEdge_complement hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z hxy hyz ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

theorem signed_unbalanced_coord_zero {n : ℕ} {U : Submodule ℝ (Coord n)}
    {i : Fin n} (hunbal : signedConnected U (i, true) (i, false))
    {z : Coord n} (hz : z ∈ Uᗮ) : z i = 0 := by
  have h := signedConnected_value_eq hz hunbal
  norm_num [signedValue, rootSign] at h
  linarith

theorem longRoot_coord_zero {n : ℕ} {U : Submodule ℝ (Coord n)}
    {i : Fin n} {s : Bool} (hroot : longRoot i s ∈ U)
    {z : Coord n} (hz : z ∈ Uᗮ) : z i = 0 := by
  have horth : @inner ℝ (Coord n) _ (longRoot i s) z = 0 :=
    Submodule.inner_right_of_mem_orthogonal hroot hz
  rw [inner_longRoot] at horth
  cases s <;> norm_num [rootSign] at horth ⊢ <;> linarith

theorem coordVec_mem_of_orthogonal_coord_zero {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n)
    (hzero : ∀ z ∈ Uᗮ, z i = 0) (a : ℝ) :
    coordVec i a ∈ U := by
  rw [← U.orthogonal_orthogonal]
  rw [Submodule.mem_orthogonal']
  intro z hz
  simp [coordVec, EuclideanSpace.inner_single_left, hzero z hz]

theorem longRoot_forces_coordinate_line {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) (s : Bool)
    (hroot : longRoot i s ∈ U) (a : ℝ) :
    coordVec i a ∈ U := by
  apply coordVec_mem_of_orthogonal_coord_zero U i
  intro z hz
  exact longRoot_coord_zero hroot hz

theorem unbalanced_forces_coordinate_line {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n)
    (hunbal : signedConnected U (i, true) (i, false)) (a : ℝ) :
    coordVec i a ∈ U := by
  apply coordVec_mem_of_orthogonal_coord_zero U i
  intro z hz
  exact signed_unbalanced_coord_zero hunbal hz

end OPAC016
