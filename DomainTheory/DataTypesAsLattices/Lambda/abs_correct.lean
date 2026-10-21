/-ai
The combinatory interpretation of the abstraction of c in the variable i, in an environment rho, equals the graph of the map sending v to the interpretation of c in the environment updated by v at i.

The proof is by induction on c. If the variable equals i, the abstraction is S K K, and the identity law for S K K together with the environment update gives the graph of the updated interpretation. If the variable is different from i, the abstraction is K applied to that variable, and the first beta law for K leaves the interpretation unchanged by the update. Each constant is likewise K applied to itself, and the same beta law applies. For an application, the second beta law for S and the two inductive hypotheses reduce the claim to a congruence of graphs, and Theorem 1.2 (i), using continuity of combinatory interpretation under environment update, removes the graphs on each side.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta2
public import DomainTheory.DataTypesAsLattices.Lambda.SKK_eq_I
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb_update_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem abs_correct (i : ℕ) (c : Comb) (ρ : ℕ → Pomega) :
    ofComb (abs i c) ρ = graph (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ with
  | var j =>
    simp only [abs, ofComb]
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      simp only [ofComb]
      convert SKK_eq_I
      funext v
      simp [envSet, Function.update, hj]
    · rw [ite_eq_right hj]
      simp [ofComb, Kcomb_beta, envSet, Function.update, hj]
  | zero => simp [abs, ofComb, Kcomb_beta]
  | suc => simp [abs, ofComb, Kcomb_beta]
  | pred => simp [abs, ofComb, Kcomb_beta]
  | cond => simp [abs, ofComb, Kcomb_beta]
  | K => simp [abs, ofComb, Kcomb_beta]
  | S => simp [abs, ofComb, Kcomb_beta]
  | app u v iu iv =>
    simp only [abs, ofComb]
    rw [Scomb_beta2, iu, iv]
    congr 1
    funext x
    rw [theorem_1_2_i (ofComb_update_isScottContinuous u ρ i)]
    rw [theorem_1_2_i (ofComb_update_isScottContinuous v ρ i)]

end DomainTheory.DataTypesAsLattices
