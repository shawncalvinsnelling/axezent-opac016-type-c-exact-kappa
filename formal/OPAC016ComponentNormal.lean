import Mathlib
import OPAC016SignedClass

/-!
Signed normal vectors for the Type-C component decomposition.

For a non-full anchor coordinate `i`, the equivalence class of `(i,true)` is
balanced. Summing the corresponding signed coordinate vectors gives the
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

theorem shortRoot_eq_signedCoordVec_sub {n : ℕ}
    (i j : Fin n) (si sj : Bool) (hij : i ≠ j) :
    shortRoot i j si sj =
      signedCoordVec (i, si) - signedCoordVec (j, !sj) := by
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [shortRoot, signedCoordVec, coordVec, rootSign_not, hij, hki, hkj] <;> ring

noncomputable def componentNormal {n : ℕ} (U : Submodule ℝ (Coord n))
    (i : Fin n) : Coord n :=
  ∑ a ∈ signedClassFinset U (i, true), signedCoordVec a

noncomputable def componentClassValue {n : ℕ} (U : Submodule ℝ (Coord n))
    (i j : Fin n) (s : Bool) : ℝ := by
  classical
  exact if signedConnected U (i, true) (j, s) then 1
    else if signedConnected U (i, true) (j, !s) then -1 else 0

@[simp] theorem inner_signedCoordVec {n : ℕ} (a b : SignedCoord n) :
    @inner ℝ (Coord n) _ (signedCoordVec a) (signedCoordVec b) =
      if a.1 = b.1 then rootSign a.2 * rootSign b.2 else 0 := by
  simp [signedCoordVec, coordVec, EuclideanSpace.inner_single_left]

@[simp] theorem inner_signedCoordVec_self {n : ℕ} (a : SignedCoord n) :
    @inner ℝ (Coord n) _ (signedCoordVec a) (signedCoordVec a) = 1 := by
  rw [inner_signedCoordVec]
  simp [rootSign_sq]

theorem inner_componentNormal_eq_sum {n : ℕ} (U : Submodule ℝ (Coord n))
    (i : Fin n) (z : Coord n) :
    @inner ℝ (Coord n) _ (componentNormal U i) z =
      ∑ a ∈ signedClassFinset U (i, true), signedValue z a := by
  simp only [componentNormal, sum_inner]
  apply Finset.sum_congr rfl
  intro a ha
  simp [signedCoordVec, signedValue, coordVec, EuclideanSpace.inner_single_left]

theorem inner_componentNormal_of_mem_orthogonal {n : ℕ}
    (U : Submodule ℝ (Coord n)) (i : Fin n) {z : Coord n} (hz : z ∈ Uᗮ) :
    @inner ℝ (Coord n) _ (componentNormal U i) z =
      (signedClassSize U (i, true) : ℝ) * z i := by
  rw [inner_componentNormal_eq_sum]
  have hterm : ∀ a ∈ signedClassFinset U (i, true), signedValue z a = z i := by
    intro a ha
    have hconn : signedConnected U (i, true) a := mem_signedClassFinset.mp ha
    have h := signedConnected_value_eq hz hconn
    simpa [signedValue, rootSign] using h.symm
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

theorem inner_componentNormal_signedCoordVec {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hbal : signedBalancedAt U (i, true)) (j : Fin n) (s : Bool) :
    @inner ℝ (Coord n) _ (componentNormal U i) (signedCoordVec (j, s)) =
      componentClassValue U i j s := by
  classical
  unfold componentClassValue
  rw [componentNormal, sum_inner]
  by_cases hs : signedConnected U (i, true) (j, s)
  · rw [if_pos hs]
    have hsmem : (j, s) ∈ signedClassFinset U (i, true) :=
      mem_signedClassFinset.mpr hs
    rw [Finset.sum_eq_single_of_mem (j, s) hsmem]
    · exact inner_signedCoordVec_self (j, s)
    · intro c hc hne
      rcases c with ⟨k, t⟩
      rw [inner_signedCoordVec]
      by_cases hkj : k = j
      · subst k
        rcases bool_eq_or_eq_not s t with hts | hts
        · subst t
          exact (hne rfl).elim
        · subst t
          have hcconn : signedConnected U (i, true) (j, !s) :=
            mem_signedClassFinset.mp hc
          have hno := signedBalancedAt_no_opposite hbal hs
          exact (hno hcconn).elim
      · simp [hkj]
  · rw [if_neg hs]
    by_cases hflip : signedConnected U (i, true) (j, !s)
    · rw [if_pos hflip]
      have hfmem : (j, !s) ∈ signedClassFinset U (i, true) :=
        mem_signedClassFinset.mpr hflip
      rw [Finset.sum_eq_single_of_mem (j, !s) hfmem]
      · rw [inner_signedCoordVec]
        cases s <;> norm_num [rootSign]
      · intro c hc hne
        rcases c with ⟨k, t⟩
        rw [inner_signedCoordVec]
        by_cases hkj : k = j
        · subst k
          rcases bool_eq_or_eq_not s t with hts | hts
          · subst t
            have hcconn : signedConnected U (i, true) (j, s) :=
              mem_signedClassFinset.mp hc
            exact (hs hcconn).elim
          · subst t
            exact (hne rfl).elim
        · simp [hkj]
    · rw [if_neg hflip]
      apply Finset.sum_eq_zero
      intro c hc
      rcases c with ⟨k, t⟩
      rw [inner_signedCoordVec]
      by_cases hkj : k = j
      · subst k
        rcases bool_eq_or_eq_not s t with hts | hts
        · subst t
          exact (hs (mem_signedClassFinset.mp hc)).elim
        · subst t
          exact (hflip (mem_signedClassFinset.mp hc)).elim
      · simp [hkj]

theorem inner_componentNormal_signedCoordVec_eq_of_connected {n : ℕ}
    {U : Submodule ℝ (Coord n)} {i : Fin n}
    (hbal : signedBalancedAt U (i, true)) {a b : SignedCoord n}
    (hab : signedConnected U a b) :
    @inner ℝ (Coord n) _ (componentNormal U i) (signedCoordVec a) =
      @inner ℝ (Coord n) _ (componentNormal U i) (signedCoordVec b) := by
  classical
  rcases a with ⟨ia, sa⟩
  rcases b with ⟨ib, sb⟩
  rw [inner_componentNormal_signedCoordVec hbal,
    inner_componentNormal_signedCoordVec hbal]
  unfold componentClassValue
  have hiff : signedConnected U (i, true) (ia, sa) ↔
      signedConnected U (i, true) (ib, sb) := by
    constructor
    · intro h
      exact Relation.EqvGen.trans _ _ _ h hab
    · intro h
      exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hab)
  have habc := signedConnected_complement hab
  have hiffc : signedConnected U (i, true) (ia, !sa) ↔
      signedConnected U (i, true) (ib, !sb) := by
    constructor
    · intro h
      exact Relation.EqvGen.trans _ _ _ h habc
    · intro h
      exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ habc)
  by_cases ha : signedConnected U (i, true) (ia, sa)
  · have hb := hiff.mp ha
    simp [ha, hb]
  · have hb : ¬ signedConnected U (i, true) (ib, sb) := by
      intro h
      exact ha (hiff.mpr h)
    by_cases hfa : signedConnected U (i, true) (ia, !sa)
    · have hfb := hiffc.mp hfa
      simp [ha, hb, hfa, hfb]
    · have hfb : ¬ signedConnected U (i, true) (ib, !sb) := by
        intro h
        exact hfa (hiffc.mpr h)
      simp [ha, hb, hfa, hfb]

end OPAC016
