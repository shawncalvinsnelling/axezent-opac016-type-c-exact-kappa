import OPAC016RootCertificate

/-! Complete geometric characterization of admissible Type-C dilation factors. -/
namespace OPAC016
open scoped BigOperators

theorem inducedRoots_neg {n : ℕ} {U : Submodule ℝ (Coord n)}
    {x : Coord n} (hx : x ∈ inducedRoots U) : -x ∈ inducedRoots U := by
  refine ⟨?_, U.neg_mem hx.2⟩
  rcases hx.1 with h | h
  · rcases h with ⟨i, s, rfl⟩
    left
    refine ⟨i, !s, ?_⟩
    ext j
    cases s <;> by_cases hji : j = i <;> simp [longRoot, coordVec, rootSign, hji]
  · rcases h with ⟨i, j, si, sj, hij, rfl⟩
    right
    refine ⟨i, j, !si, !sj, hij, ?_⟩
    ext k
    cases si <;> cases sj <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [shortRoot, coordVec, rootSign, hki, hkj, hij, Ne.symm hij]

theorem inducedPolytope_neg {n : ℕ} {U : Submodule ℝ (Coord n)}
    {x : Coord n} (hx : x ∈ inducedPolytope U) : -x ∈ inducedPolytope U := by
  have hsub : inducedRoots U ⊆ {y : Coord n | -y ∈ inducedPolytope U} := by
    intro y hy
    exact subset_convexHull ℝ (inducedRoots U) (inducedRoots_neg hy)
  have hc : Convex ℝ {y : Coord n | -y ∈ inducedPolytope U} :=
    (convex_convexHull ℝ (inducedRoots U)).linear_preimage
      (-(LinearMap.id : Coord n →ₗ[ℝ] Coord n))
  exact (convexHull_min hsub hc) hx

theorem zero_mem_inducedPolytope {n : ℕ} {U : Submodule ℝ (Coord n)}
    (hU : RootSpanned U) (hne : U ≠ ⊥) : (0 : Coord n) ∈ inducedPolytope U := by
  obtain ⟨x, hx⟩ := rootSpanned_nonzero_has_root hU hne
  have hp : x ∈ inducedPolytope U := subset_convexHull ℝ (inducedRoots U) hx
  have hm := (convex_convexHull ℝ (inducedRoots U)).midpoint_mem hp (inducedPolytope_neg hp)
  simpa [midpoint_eq_smul_add, inducedPolytope] using hm

def dilatedInduced {n : ℕ} (U : Submodule ℝ (Coord n)) (K : ℝ) : Set (Coord n) :=
  (fun y : Coord n => K • y) '' inducedPolytope U

theorem convex_dilatedInduced {n : ℕ} (U : Submodule ℝ (Coord n)) (K : ℝ) :
    Convex ℝ (dilatedInduced U K) := by
  exact (convex_convexHull ℝ (inducedRoots U)).linear_image
    (K • (LinearMap.id : Coord n →ₗ[ℝ] Coord n))

theorem dilatedInduced_neg {n : ℕ} {U : Submodule ℝ (Coord n)} {K : ℝ}
    {x : Coord n} (hx : x ∈ dilatedInduced U K) : -x ∈ dilatedInduced U K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨-y, inducedPolytope_neg hy, by simp⟩

theorem smul_mem_dilatedInduced {n : ℕ} {U : Submodule ℝ (Coord n)}
    (hU : RootSpanned U) (hne : U ≠ ⊥)
    {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) (hrK : r ≤ K)
    {y : Coord n} (hy : y ∈ inducedPolytope U) :
    r • y ∈ dilatedInduced U K := by
  have hz := (convex_convexHull ℝ (inducedRoots U)).smul_mem_of_zero_mem
    (zero_mem_inducedPolytope hU hne) hy
    (show r / K ∈ Set.Icc (0 : ℝ) 1 from
      ⟨div_nonneg hr hK.le, (div_le_one hK).mpr hrK⟩)
  refine ⟨(r / K) • y, hz, ?_⟩
  change K • ((r / K) • y) = r • y
  rw [smul_smul]
  congr 1
  field_simp

theorem projected_coord_singleton {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U)
    (i : Fin n) (hnfull : coordVec i 1 ∉ U)
    (hb : signedClassSize U (i, true) = 1) :
    U.starProjection (coordVec i 2) = 0 := by
  classical
  have he : classOthers U i = ∅ := Finset.card_eq_zero.mp (by simp [classOthers_card, hb])
  have hs := sum_classDifference U i
  have hd : coordVec i 1 - componentNormal U i = 0 := by simpa [he, hb] using hs.symm
  have hN := (sub_eq_zero.mp hd).symm
  rw [starProjection_coord_nonfull hU i hnfull]
  ext j
  by_cases hji : j = i <;> simp [componentProjectedCoord, hb, hN, coordVec, hji]

def AdmissibleDilation {n : ℕ} (U : Submodule ℝ (Coord n)) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ x ∈ typeCRootPolytope n, U.starProjection x ∈ dilatedInduced U K

theorem coordinate_upper_certificate {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥)
    {K : ℝ} (hK : 1 ≤ K)
    (hbK : ∀ i : Fin n, coordVec i 1 ∉ U →
      2 - 2 / (signedClassSize U (i, true) : ℝ) ≤ K)
    (i : Fin n) : U.starProjection (coordVec i 2) ∈ dilatedInduced U K := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  by_cases hf : coordVec i 1 ∈ U
  · rw [starProjection_coord_full i hf]
    have hm : coordVec i 2 ∈ U := by
      have he : (2 : ℝ) • coordVec i 1 = coordVec i 2 := by
        ext j
        by_cases hji : j = i <;> simp [coordVec, hji]
      rw [← he]
      exact U.smul_mem _ hf
    have hr : coordVec i 2 ∈ inducedRoots U :=
      ⟨Or.inl ⟨i, true, by simp [longRoot, rootSign]⟩, hm⟩
    have h := smul_mem_dilatedInduced hU hne hK0 zero_le_one hK
      (subset_convexHull ℝ (inducedRoots U) hr)
    simpa using h
  · have hbpos := signedClassSize_pos U (i, true)
    by_cases hb1 : signedClassSize U (i, true) = 1
    · rw [projected_coord_singleton hU i hf hb1]
      exact ⟨0, zero_mem_inducedPolytope hU hne, by simp⟩
    · have hb : 2 ≤ signedClassSize U (i, true) := by omega
      rw [projected_long_eq_score_average hU i hf hb]
      have hr : 0 ≤ 2 - 2 / (signedClassSize U (i, true) : ℝ) := by
        have h := balancedScore_ge_one (b := (signedClassSize U (i, true) : ℝ))
          (by exact_mod_cast hb)
        dsimp [balancedScore] at h
        simp only [mul_one_div] at h
        linarith
      exact smul_mem_dilatedInduced hU hne hK0 hr (hbK i hf)
        (componentRootAverage_mem hf hb)

theorem admissibleDilation_iff_coordinate_scores {n : ℕ}
    {U : Submodule ℝ (Coord n)} (hU : RootSpanned U) (hne : U ≠ ⊥) (K : ℝ) :
    AdmissibleDilation U K ↔
      1 ≤ K ∧ ∀ i : Fin n, coordVec i 1 ∉ U →
        2 - 2 / (signedClassSize U (i, true) : ℝ) ≤ K := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro i hi
    have hr : coordVec i 2 ∈ typeCRoots n :=
      Or.inl ⟨i, true, by simp [longRoot, rootSign]⟩
    obtain ⟨y, hy, heq⟩ := h.2 (coordVec i 2) (subset_convexHull ℝ (typeCRoots n) hr)
    exact nonfull_dilation_lower_bound hU i hi (by linarith [h.1]) hy heq.symm
  · rintro ⟨hK, hs⟩
    refine ⟨hK, ?_⟩
    have hc : Convex ℝ {x : Coord n | U.starProjection x ∈ dilatedInduced U K} :=
      (convex_dilatedInduced U K).linear_preimage U.starProjection.toLinearMap
    have hl : longRoots n ⊆ {x : Coord n | U.starProjection x ∈ dilatedInduced U K} := by
      intro x hx
      obtain ⟨i, s, rfl⟩ := hx
      have hp := coordinate_upper_certificate hU hne hK hs i
      cases s
      · have he : longRoot i false = - coordVec i 2 := by
          ext j
          by_cases hji : j = i <;> simp [longRoot, coordVec, rootSign, hji]
        change U.starProjection (longRoot i false) ∈ dilatedInduced U K
        rw [he, map_neg]
        exact dilatedInduced_neg hp
      · simpa [longRoot, rootSign] using hp
    intro x hx
    rw [typeCRootPolytope_eq_longRootPolytope] at hx
    exact (convexHull_min hl hc) hx

end OPAC016

