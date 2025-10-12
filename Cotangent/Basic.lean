import Mathlib

open Ideal

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ jacobson ⊥) :
    N.spanRank = (map (I • N).mkQ N).spanRank := by
  have smul_sup_eq : I • N ⊔ N = N := by rw [sup_eq_right]; exact smul_le_right
  apply le_antisymm
  · rw [FG.spanRank_le_iff_exists_span_set_card_le]
    rcases exists_span_set_card_eq_spanRank (map (I • N).mkQ N) with ⟨s, ⟨hscard, hsspan⟩⟩
    have hs_subset : s ⊆ (map (I • N).mkQ N) := by
      rw [← hsspan]
      exact subset_span
    -- pull back `s` from N / I to N to get a spanning set of N
    let pbv := fun (y : M ⧸ I • N) ↦ Classical.choose <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    let pbp := fun (y : M ⧸ I • N) ↦ Classical.choose_spec <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    have mkQ_pbv_cancel : (I • N).mkQ  ∘ pbv = id := by
      funext y
      exact pbp y
    use pbv '' s
    constructor
    · rw [← hscard]
      apply Cardinal.mk_image_le
    · apply le_antisymm
      · rw [Submodule.span_le]
        grw [hs_subset]
        haveI := comap_map_mkQ (I • N) N
        rw [smul_sup_eq] at this
        -- obtain a set version of `Submodule.comap_map_mkQ`
        apply_fun fun x ↦ (x : Set M) at this
        rw [Submodule.comap_coe, Submodule.map_coe] at this
        -- return to the goal
        rw [← this, ← Set.image_subset_iff, ← Set.image_comp, mkQ_pbv_cancel]
        simp
      · apply le_span_of_map_mkQ_le_map_mkQ_span_of_le_jacobson_bot hN hIjac
        rw [Submodule.map_span, ← Set.image_comp, mkQ_pbv_cancel]
        simp [hsspan]
  · rw [FG.spanRank_le_iff_exists_span_set_card_le]
    rcases exists_span_set_card_eq_spanRank N with ⟨s, ⟨hscard, hsspan⟩⟩
    use mkQ (I • N) '' s
    constructor
    · rw [← hscard]
      apply Cardinal.mk_image_le
    · rw [← Submodule.map_span, hsspan]

theorem tmp
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ jacobson ⊥) :
    N.spanRank = (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  haveI := spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hN hIjac
  -- #check Submodule (R ⧸ I) (map (I • N).mkQ N)
  sorry

end Submodule

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

open Submodule

theorem tmp' (hm : (maximalIdeal R).FG) :
    Module.rank R (CotangentSpace R) = (maximalIdeal R).spanRank := by
  rw [spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hm (maximalIdeal_le_jacobson _)]
  #check cotangentIdeal (maximalIdeal R)

  haveI : Submodule R (R ⧸ maximalIdeal R • maximalIdeal R) = Ideal (R ⧸ maximalIdeal R ^ 2) := by
    rw [smul_eq_mul]
    rw [pow_two]
    unfold Ideal
    sorry

  -- haveI : cotangentIdeal (maximalIdeal R) = Submodule.map (maximalIdeal R • maximalIdeal R).mkQ (maximalIdeal R) := by
  --   unfold cotangentIdeal

  --   rfl
  #check cotangentEquivIdeal
  #check rank_eq_spanRank_of_free
  #check pow_two
  #check rank_eq
  sorry

end IsLocalRing

#check IsLocalRing.CotangentSpace

#check IsLocalRing.finrank_cotangentSpace_eq_zero
