import Mathlib
import OPAC016RootPolytope

/-!
Exact scope definitions for the AXZ-OPAC-016 theorem.

A subspace is root-spanned precisely when it is the real linear span of the
Type-C roots it actually contains.  The induced subsystem is literally the set
intersection `C_n ∩ U`; no surrogate or widened hypothesis is used.
-/

namespace OPAC016

variable {n : ℕ}

def inducedRoots (U : Submodule ℝ (Coord n)) : Set (Coord n) :=
  typeCRoots n ∩ (U : Set (Coord n))

def RootSpanned (U : Submodule ℝ (Coord n)) : Prop :=
  Submodule.span ℝ (inducedRoots U) = U

theorem inducedRoots_subset_subspace (U : Submodule ℝ (Coord n)) :
    inducedRoots U ⊆ U := by
  intro x hx
  exact hx.2

theorem inducedRoots_subset_typeCRoots (U : Submodule ℝ (Coord n)) :
    inducedRoots U ⊆ typeCRoots n := by
  intro x hx
  exact hx.1

theorem rootSpanned_iff_span_inter (U : Submodule ℝ (Coord n)) :
    RootSpanned U ↔ Submodule.span ℝ (typeCRoots n ∩ (U : Set (Coord n))) = U := by
  rfl

theorem span_inducedRoots_le (U : Submodule ℝ (Coord n)) :
    Submodule.span ℝ (inducedRoots U) ≤ U := by
  exact Submodule.span_le.2 (inducedRoots_subset_subspace U)

theorem rootSpanned_nonzero_has_root {U : Submodule ℝ (Coord n)}
    (hU : RootSpanned U) (hne : U ≠ ⊥) :
    (inducedRoots U).Nonempty := by
  by_contra h
  have hempty : inducedRoots U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hspan : Submodule.span ℝ (inducedRoots U) = ⊥ := by simp [hempty]
  rw [hU] at hspan
  exact hne hspan

end OPAC016
