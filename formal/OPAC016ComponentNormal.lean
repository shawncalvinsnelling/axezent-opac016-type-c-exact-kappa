import Mathlib
import OPAC016SignedClass

/-!
Signed normal vectors for the Type-C component decomposition.

For a non-full anchor coordinate `i`, the equivalence class of `(i,true)` is
balanced.  Summing the corresponding signed coordinate vectors gives the
normal vector of that component.
-/

namespace OPAC016

open scoped BigOperators

noncomputable def signedCoordVec {n : ℕ} (a : SignedCoord n) : Coord n :=
  coordVec a.1 (rootSign a.2)

@[simp] theorem signedCoordVec_apply_self {n : ℕ} (a : SignedCoord n) :
    signedCoordVec a a.1 = rootSign a.2 := by
  simp [signedCoordVec]

@[simp] theorem signedCoordVec_apply_ne {n : ℕ} {a : SignedCoord n} {j : Fin n}
    (h : j ≠ a.1) : signedCoordVec a j = 0 := by
  simp [signedCoordVec, h]

@[simp] theorem signedCoordVec_flip {n : ℕ} (a : SignedCoord n) :
    signedCoordVec (a.1, !a.2) = - signedCoordVec a := by
  ext j
  by_cases h : j = a.1
  · subst j
    simp [signedCoordVec, rootSign_not]
  · simp [signedCoordVec, h, rootSign_not]

noncomputable def componentNormal {n : ℕ} (U : Submodule ℝ (Coord n))
    (i : Fin n) : Coord n :=
  ∑ a ∈ signedClassFinset U (i, true), signedCoordVec a

@[simp] theorem inner_signedCoordVec {n : ℕ} (a b : SignedCoord n) :
    @inner ℝ (Coord n) _ (signedCoordVec a) (signedCoordVec b) =
      if a.1 = b.1 then rootSign a.2 * rootSign b.2 else 0 := by
  simp [signedCoordVec, coordVec, EuclideanSpace.inner_single_left]

@[simp] theorem inner_signedCoordVec_self {n : ℕ} (a : SignedCoord n) :
    @inner ℝ (Coord n) _ (signedCoordVec a) (signedCoordVec a) = 1 := by
  simp [inner_signedCoordVec, rootSign_sq]

theorem inner_componentNormal_eq_sum {n : ℕ} (U : Submodule ℝ (Coord n))
    (i : Fin n) (z : Coord n) :
    @inner ℝ (Coord n) _ (componentNormal U i) z =
      ∑ a ∈ signedClassFinset U (i, true), signedValue z a := by
  rw [componentNormal, inner_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  simp [signedCoordVec, signedValue, coordVec, EuclideanSpace.inner_single_left,
    mul_comm]

theorem inner_componentNormal_of_mem_orthogonal {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) {z : Coord n} (hz : z ∈ Uᗮ) :
    @inner ℝ (Coord n) _ (componentNormal U i) z =
      (signedClassSize U (i, true) : ℝ) * z i := by
  rw [inner_componentNormal_eq_sum]
  have hterm : ∀ a ∈ signedClassFinset U (i, true), signedValue z a = z i := by
    intro a ha
    have hconn : signedConnected U (i, true) a := mem_signedClassFinset.mp ha
    have h := signedConnected_value_eq hz hconn
    simpa [signedValue, rootSign] using h
  calc
    (∑ a ∈ signedClassFinset U (i, true), signedValue z a)
        = ∑ a ∈ signedClassFinset U (i, true), z i := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hterm a ha
    _ = (signedClassFinset U (i, true)).card * z i := by
          simp [nsmul_eq_mul]
    _ = (signedClassSize U (i, true) : ℝ) * z i := by
          rfl

end OPAC016
