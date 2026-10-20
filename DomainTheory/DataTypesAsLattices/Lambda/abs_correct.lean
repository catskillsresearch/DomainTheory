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
