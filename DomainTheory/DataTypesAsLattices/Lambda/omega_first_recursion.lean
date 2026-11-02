module

public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem omega_first_recursion {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by
  let d := omegaComb (graph f)
  have hd : ∀ x, funOf d x = f (funOf x x) := by
    intro x
    simp [d, omegaComb.app, theorem_1_2.i hf]
  have hθ : funOf d d = f (funOf d d) := hd d
  refine subset_antisymm ?_ ((theorem_1_4 hf).2 _ hθ.symm)
  intro m hm

  let a := fix f
  have ha : f a = a := (theorem_1_4 hf).1
  have key : ∀ l, e l ⊆ d → funOf (e l) (e l) ⊆ a := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro hld k hk
      obtain ⟨n, hn, hp⟩ := hk
      have hnlt : n < l := (pair_le_left n k).trans_lt (e.mem_lt hp)
      have hnd : e n ⊆ d := subset_trans hn hld
      have hna : funOf (e n) (e n) ⊆ a := ih n hnlt hnd

      have : k ∈ funOf d (e n) := ⟨n, subset_rfl, hld hp⟩
      have : k ∈ f (funOf (e n) (e n)) := by
        rwa [hd] at this
      have : k ∈ f a := IsScottContinuous.monotone hf hna this
      rwa [ha] at this
  rw [funOf.diag_iUnion] at hm
  obtain ⟨l, hl, hml⟩ := Set.mem_iUnion.mp hm
  exact key l hl hml

end DomainTheory.DataTypesAsLattices
