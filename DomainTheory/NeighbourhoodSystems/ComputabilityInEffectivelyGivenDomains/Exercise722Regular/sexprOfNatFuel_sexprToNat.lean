/-ai
Decoding the code of an expression with fuel strictly above that code returns the expression.

Induction on the expression. With no fuel the strict bound is impossible. For the universal expression and for a singleton, one unit of fuel and unpairing recover the constructor, and a singleton also inverts the encoding of its word. For a concatenation and for an intersection, each subexpression code is at most the paired code of the two subexpressions, that paired code is strictly below the whole code because the constructor tag is positive, and the inductive hypotheses at the smaller fuel reassemble the constructor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.snd_lt_pair_of_pos_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

theorem sexprOfNatFuel_sexprToNat (e : SExpr) :
    ∀ fuel, sexprToNat e < fuel → sexprOfNatFuel fuel (sexprToNat e) = some e := by
  induction e with
  | sigma =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair]
  | single σ =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel => simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, Encodable.encodek]
  | cat a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cat a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 2) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]
  | cap a b iha ihb =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ha : sexprToNat a < fuel := by
        have hinner : sexprToNat a ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.left_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      have hb : sexprToNat b < fuel := by
        have hinner : sexprToNat b ≤ Nat.pair (sexprToNat a) (sexprToNat b) := Nat.right_le_pair _ _
        have houter : Nat.pair (sexprToNat a) (sexprToNat b) < sexprToNat (.cap a b) := by
          simpa [sexprToNat] using snd_lt_pair_of_pos_fst (a := 3) (b := Nat.pair (sexprToNat a) (sexprToNat b)) (by omega)
        omega
      simp [sexprToNat, sexprOfNatFuel, Nat.unpair_pair, iha _ ha, ihb _ hb]

end Exercise722

end DomainTheory.NeighbourhoodSystems
