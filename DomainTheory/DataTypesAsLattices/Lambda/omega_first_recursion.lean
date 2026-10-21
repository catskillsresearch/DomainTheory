/-ai
Scott's core induction shows that the self-application of the omega combinator of the graph of a Scott continuous map is the least fixed point of that map.

Let d be that omega combinator. Application of d rewrites, by the omega application law and Theorem 1.2 (i), as the map applied to a self-application, so the self-application of d is a fixed point and Theorem 1.4 places the least fixed point beneath it. For the other inclusion, let a be the least fixed point, so the map fixes a. Strong induction shows that if a finite set is contained in d, its self-application is contained in a: a pair code in that self-application has a strictly smaller index whose finite set is still contained in d, the inductive hypothesis puts that smaller self-application below a, the same code lies in the application of d to the smaller finite set and hence in the image under the map of that self-application, and monotonicity together with the fixed-point equation puts the value in a. The diagonal union formula for self-application then carries membership in the self-application of d into a.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_app
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_diag_iUnion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Scott's core induction proving that `ω(graph f)(ω(graph f))` is the
least fixed point of `f`. -/
theorem omega_first_recursion {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by
  let d := omegaComb (graph f)
  have hd : ∀ x, funOf d x = f (funOf x x) := by
    intro x
    simp [d, omegaComb_app, theorem_1_2_i hf]
  have hθ : funOf d d = f (funOf d d) := hd d
  refine subset_antisymm ?_ ((theorem_1_4 hf).2 _ hθ.symm)
  intro m hm
  -- Scott's argument: reduce to `e_l ⊆ d → e_l ⬝ e_l ⊆ a` with `a = fix f`.
  let a := fix f
  have ha : f a = a := (theorem_1_4 hf).1
  have key : ∀ l, e l ⊆ d → funOf (e l) (e l) ⊆ a := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro hld k hk
      obtain ⟨n, hn, hp⟩ := hk
      have hnlt : n < l := (pair_le_left n k).trans_lt (mem_e_lt hp)
      have hnd : e n ⊆ d := subset_trans hn hld
      have hna : funOf (e n) (e n) ⊆ a := ih n hnlt hnd
      -- `(n,k) ∈ e_l ⊆ d = λx. f(x x)`, so `k ∈ f(e n ⬝ e n)`
      have : k ∈ funOf d (e n) := ⟨n, subset_rfl, hld hp⟩
      have : k ∈ f (funOf (e n) (e n)) := by
        rwa [hd] at this
      have : k ∈ f a := isScottContinuous_monotone hf hna this
      rwa [ha] at this
  rw [funOf_diag_iUnion] at hm
  obtain ⟨l, hl, hml⟩ := Set.mem_iUnion.mp hm
  exact key l hl hml

end DomainTheory.DataTypesAsLattices
