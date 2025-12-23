import Mathlib

namespace Submodule

open Cardinal

universe u
variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem exists_linearCombination_card_eq_spanRank (p : Submodule R M) :
    ∃ (ι : Type u) (v : ι → M),
    #ι = p.spanRank ∧ p = LinearMap.range (Finsupp.linearCombination R v) := by
  rcases exists_span_set_card_eq_spanRank p with ⟨s, hscard, hsspan⟩
  use s, (↑)
  constructor
  · exact hscard
  · rw [Finsupp.range_linearCombination, ← hsspan]
    simp

theorem spanRank_le_iff_exists_linearCombination_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ (ι : Type u) (v : ι → M),
    #ι ≤ a ∧ p = LinearMap.range (Finsupp.linearCombination R v) := by
  rw [FG.spanRank_le_iff_exists_span_set_card_le]
  constructor
  · intro ⟨s, hscard, hsspan⟩
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

end Submodule


namespace Submodule

universe u
variable
    {R S : Type*} {M N : Type u}
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [AddCommMonoid N] [Module S N]
    {M₁ : Submodule R M} {N₁ : Submodule S N}

theorem spanRank_le_spanRank_of_map_eq
    {σ : S →+* R} [RingHomSurjective σ] (f : N →ₛₗ[σ] M) (h_map : map f N₁ = M₁) :
    M₁.spanRank ≤ N₁.spanRank := by
  rcases exists_span_set_card_eq_spanRank N₁ with ⟨s, hscard, hsspan⟩
  rw [FG.spanRank_le_iff_exists_span_set_card_le]
  use f '' s
  constructor
  · rw [← hscard]
    exact Cardinal.mk_image_le
  · rw [span_image', hsspan, h_map]

theorem spanRank_le_spanRank_of_range_eq
    {σ : S →+* R} [RingHomSurjective σ] (f : N₁ →ₛₗ[σ] M) (h_range : LinearMap.range f = M₁) :
    M₁.spanRank ≤ N₁.spanRank := by
  -- obtain the spanning set of submodule `N₁`
  rcases exists_span_set_card_eq_spanRank N₁ with ⟨s, hscard, hsspan⟩
  have s_subset : s ⊆ N₁ := by rw [← hsspan]; exact subset_span
  rw [FG.spanRank_le_iff_exists_span_set_card_le]
  -- lift the set to a set of `N₁`
  lift s to Set N₁ using s_subset
  rw [Cardinal.mk_image_eq Subtype.val_injective] at hscard
  change span S (N₁.subtype '' s) = N₁ at hsspan
  rw [span_image] at hsspan
  apply_fun comap N₁.subtype at hsspan
  rw [comap_map_eq_of_injective (subtype_injective N₁) (span S s)] at hsspan
  simp only [comap_subtype_self] at hsspan
  -- transfer the lifted set via `f` to get a spanning set of `M₁`
  use f '' s
  constructor
  · grw [Cardinal.mk_image_le]; rw [hscard]
  · rw [span_image, hsspan, map_top, h_range]

theorem spanRank_le_spanRank_of_surjective
    {σ : S →+* R} [RingHomSurjective σ] (f : N₁ →ₛₗ[σ] M₁) (h_surj : Function.Surjective f) :
    M₁.spanRank ≤ N₁.spanRank := by
  apply spanRank_le_spanRank_of_range_eq (M₁.subtype.comp f)
  rw [LinearMap.range_comp, LinearMap.range_eq_top_of_surjective f h_surj, map_top, range_subtype]

theorem spanRank_eq_spanRank_of_linearEquiv'
    (σ : R →+* S) {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M₁ ≃ₛₗ[σ] N₁) : M₁.spanRank = N₁.spanRank :=
  le_antisymm
    (spanRank_le_spanRank_of_surjective e.symm.toLinearMap e.symm.surjective)
    (spanRank_le_spanRank_of_surjective e.toLinearMap e.surjective)

#check AddEquiv
#check rank_eq_of_equiv_equiv
theorem spanRank_eq_spanRank_of_addEquiv
    (σ : S →+* R) [RingHomSurjective σ] (e : N₁ ≃+ N₁) : M₁.spanRank = N₁.spanRank := by
  sorry

end Submodule

namespace Submodule

universe u
variable {R : Type*} {M N : Type u}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
variable {M₁ : Submodule R M} {N₁ : Submodule R N}

theorem spanRank_eq_spanRank_of_linearEquiv (e : M₁ ≃ₗ[R] N₁) : M₁.spanRank = N₁.spanRank :=
  spanRank_eq_spanRank_of_linearEquiv' _ e

end Submodule


namespace Submodule

universe u

theorem spanRank_eqₛₗ
    {R S : Type*} {M N : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [AddCommGroup N] [Module S N]
    {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] N)
    (M₁ : Submodule R M) (N₁ : Submodule S N)
    (inj : LinearMap.ker f ⊓ M₁ = ⊥) (surj : M₁.map f = N₁) :
    M₁.spanRank = N₁.spanRank := by
  sorry

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
         (N : Submodule R M) (I : Ideal R)

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

theorem tmp : (⊤ : Submodule R (N ⧸ (I • ⊤ : Submodule R N))).spanRank
    = (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  #check spanRank_eq_spanRank_of_addEquiv (Ideal.Quotient.mk I)
  apply spanRank_eq_spanRank_of_addEquiv (Ideal.Quotient.mk I)

  #check spanRank_eq_spanRank_of_linearEquiv (topEquiv : _ ≃ₗ[R] _)


  sorry

end Submodule


namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (map (I • N).mkQ N).spanRank := by
  have smul_sup_eq : I • N ⊔ N = N := by rw [sup_eq_right]; exact smul_le_right
  apply le_antisymm
  · rcases exists_span_set_card_eq_spanRank (map (I • N).mkQ N) with ⟨s, ⟨hscard, hsspan⟩⟩
    have hs_subset : s ⊆ map (I • N).mkQ N := by rw [← hsspan]; exact subset_span
    -- pull back `s` from N / I to N to get a spanning set of N
    -- [TODO] shall we use projective modules here?
    let pbv := fun (y : M ⧸ I • N) ↦ Classical.choose <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    let pbp := fun (y : M ⧸ I • N) ↦ Classical.choose_spec <|
      Set.Nonempty.preimage (Set.singleton_nonempty y) (mkQ_surjective (I • N))
    have mkQ_pbv_cancel : (I • N).mkQ  ∘ pbv = id := by
      funext y
      exact pbp y
    -- show the inequality via the pulled back set
    rw [FG.spanRank_le_iff_exists_span_set_card_le]
    use pbv '' s
    constructor
    · rw [← hscard]
      apply Cardinal.mk_image_le
    · apply le_antisymm
      · rw [span_le]
        grw [hs_subset]
        have := comap_map_mkQ (I • N) N
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
  · exact spanRank_le_spanRank_of_map_eq (mkQ (I • N)) (by dsimp)

theorem spanRank_eq_spanRank_quotient_ideal_submodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (⊤ : Submodule R (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  rw [spanRank_eq_spanRank_map_mkQ_of_le_jacobson_bot hN hIjac]
  apply spanRank_eq_spanRank_of_linearEquiv

  symm
  exact LinearEquiv.trans
    (Submodule.topEquiv : _ ≃ₗ[R] (N ⧸ (I • ⊤ : Submodule R N)))
    (quotientIdealSubmoduleEquivMap N I)

theorem spanRank_eq_spanRank_quotient_ring_quotient_ideal_submodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG) (hIjac : I ≤ Ideal.jacobson ⊥) :
    N.spanRank = (⊤ : Submodule (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N))).spanRank := by
  sorry

end Submodule


namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

open Submodule

theorem spanrank_maximalIdeal_eq_rank_cotangentSpace (hm : (maximalIdeal R).FG) :
    (maximalIdeal R).spanRank = Module.rank (ResidueField R) (CotangentSpace R) := by
  rw [spanRank_eq_spanRank_quotient_ring_quotient_ideal_submodule hm (maximalIdeal_le_jacobson _),
      Submodule.rank_eq_spanRank_of_free]

end IsLocalRing
