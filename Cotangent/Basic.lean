import Mathlib

namespace Submodule

/-
Should use
`Function.Surjective ⇑(Finsupp.linearCombination R v)`
to interpret spanning sets and span Rank
-/
#check LinearIndependent

section

open Cardinal

universe u
variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

#check FG.spanRank_le_iff_exists_span_set_card_le
#check Finsupp.range_linearCombination
theorem spanRank_le_iff_exists_linearCombination_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ (ι : Type u) (v : ι → M), #ι ≤ a ∧ p = LinearMap.range (Finsupp.linearCombination R v) := by
  rw [FG.spanRank_le_iff_exists_span_set_card_le]
  constructor
  · intro ⟨s, ⟨hscard, hsspan⟩⟩
    use s, (↑)
    constructor
    · exact hscard
    · rw [Finsupp.range_linearCombination, ← hsspan]
      simp
  · intro ⟨ι, v, hιcard, hple⟩
    use Set.range v
    constructor
    · grw [Cardinal.mk_range_le, hιcard]
    · rw [hple, Finsupp.range_linearCombination]
end

universe u
theorem spanRank_eq {R : Type*} {M N : Type u}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {M₁ : Submodule R M} {N₁ : Submodule R N} (e : M₁ ≃ₗ[R] N₁) :
    M₁.spanRank = N₁.spanRank := by
  apply le_antisymm
  · rw [FG.spanRank_le_iff_exists_span_set_card_le]
    symm at e
    #check N₁.generators
    #check N₁.generators_card
    #check N₁.span_generators
    sorry
  · sorry

theorem spanRank_eqₛₗ
    {R S : Type*} {M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [AddCommGroup N] [Module S N]
    {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] N)
    (M₁ : Submodule R M) (N₁ : Submodule S N)
    (inj : LinearMap.ker f ⊓ M₁ = ⊥) (surj : M₁.map f = N₁) :
    M₁.spanRank = N₁.spanRank := by
  sorry
#check LinearEquiv
theorem spanRank_eqₛₗ'
    {R S : Type*} {M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [AddCommGroup N] [Module S N]
    {σ : R →+* S} [RingHomSurjective σ]
    {M₁ : Submodule R M} {N₁ : Submodule S N}
    (f : M₁ →ₛₗ[σ] N₁) (inj : LinearMap.ker f = ⊥) (surj : LinearMap.range f = ⊤) :
    M₁.spanRank = N₁.spanRank := by

  #check LinearMap.restrict
  sorry


end Submodule

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
         {N : Submodule R M} {I : Ideal R}

noncomputable def quotientIdealSubmoduleEquivMap : (N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[R] (map (I • N).mkQ N) := by
  refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩
  · refine Submodule.liftQ _ ?_ ?_
    · exact {
        toFun x := by
          rcases x with ⟨x, hx⟩
          use ((I • N).mkQ x), x, hx
        map_add' := by simp
        map_smul' := by simp
      }
    · intro x hx
      rw [mem_smul_top_iff] at hx
      simp [hx]
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction' x using Submodule.Quotient.induction_on with x
    simp at hx ⊢
    rw [mem_smul_top_iff]
    exact hx
  · rintro ⟨_, ⟨x, hx, rfl⟩⟩
    use Quotient.mk ⟨x, hx⟩
    simp

#check TensorProduct.quotTensorEquivQuotSMul

end Submodule

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
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
      · rw [span_le]
        grw [hs_subset]
        haveI := comap_map_mkQ (I • N) N
        rw [smul_sup_eq] at this
        -- obtain a set version of `Submodule.comap_map_mkQ`
        apply_fun fun x ↦ (x : Set M) at this
        rw [comap_coe, map_coe] at this
        -- return to the goal
        rw [← this, ← Set.image_subset_iff, ← Set.image_comp, mkQ_pbv_cancel]
        simp
      · apply le_span_of_map_mkQ_le_map_mkQ_span_of_le_jacobson_bot hN hIjac
        rw [map_span, ← Set.image_comp, mkQ_pbv_cancel]
        simp [hsspan]
  · rw [FG.spanRank_le_iff_exists_span_set_card_le]
    rcases exists_span_set_card_eq_spanRank N with ⟨s, ⟨hscard, hsspan⟩⟩
    use mkQ (I • N) '' s
    constructor
    · rw [← hscard]
      apply Cardinal.mk_image_le
    · rw [← map_span, hsspan]

theorem tmp
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    (⊤ : Submodule R (N ⧸ (I • ⊤ : Submodule R N))).spanRank = N.spanRank := by
  rw [spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hN hIjac]
  sorry

end Submodule

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

open Submodule

-- def cotangentSubmodule (I : Ideal R) : Submodule R (R ⧸ I ^ 2) :=
--   map (I • (R ⧸ I)).mkQ (R ⧸ I ^ 2)

theorem tmp' (hm : (maximalIdeal R).FG) :
    Module.rank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanRank := by
  rw [spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hm (maximalIdeal_le_jacobson _)]
  rw [Submodule.rank_eq_spanRank_of_free]
  simp

  -- apply Submodule.spanRank_eq

  #check Ideal.cotangentEquivIdeal
  sorry

end IsLocalRing

#check IsLocalRing.CotangentSpace

#check IsLocalRing.finrank_cotangentSpace_eq_zero
