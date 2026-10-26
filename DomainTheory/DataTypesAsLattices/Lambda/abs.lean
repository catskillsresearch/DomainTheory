
module

public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Lambda.SKK_eq_I
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def abs (i : ℕ) : Comb → Comb
  | .var j => if j = i then .app (.app .S .K) .K else .app .K (.var j)
  | .zero => .app .K .zero
  | .suc => .app .K .suc
  | .pred => .app .K .pred
  | .cond => .app .K .cond
  | .K => .app .K .K
  | .S => .app .K .S
  | .app u v => .app (.app .S (abs i u)) (abs i v)

namespace abs

theorem correct (i : ℕ) (c : Comb) (ρ : ℕ → Pomega) :
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
      simp [ofComb, Kcomb.beta, envSet, Function.update, hj]
  | zero => simp [abs, ofComb, Kcomb.beta]
  | suc => simp [abs, ofComb, Kcomb.beta]
  | pred => simp [abs, ofComb, Kcomb.beta]
  | cond => simp [abs, ofComb, Kcomb.beta]
  | K => simp [abs, ofComb, Kcomb.beta]
  | S => simp [abs, ofComb, Kcomb.beta]
  | app u v iu iv =>
    simp only [abs, ofComb]
    rw [Scomb.beta2, iu, iv]
    congr 1
    funext x
    rw [theorem_1_2.i (ofComb.update_isScottContinuous u ρ i)]
    rw [theorem_1_2.i (ofComb.update_isScottContinuous v ρ i)]

end abs

end DomainTheory.DataTypesAsLattices
