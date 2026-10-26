module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.3).** The modified boolean closure. -/
def boool : Pomega :=
  graph (fun u => condSet u (ofNat 0) (succSet topElem))

namespace boool

theorem map_isScottContinuous :
    IsScottContinuous (fun u => condSet u (ofNat 0) (succSet topElem)) :=
  condSet.isScottContinuous_left (ofNat 0) (succSet topElem)

theorem app (u : Pomega) :
    funOf boool u = condSet u (ofNat 0) (succSet topElem) :=
  beta map_isScottContinuous u

theorem expansive (u : Pomega) :
    u ⊆ condSet u (ofNat 0) (succSet topElem) := by
  intro k hk
  cases k with
  | zero => exact Or.inl ⟨rfl, hk⟩
  | succ k => exact Or.inr ⟨⟨k, Set.mem_univ k, rfl⟩, ⟨k, hk⟩⟩

theorem idem (u : Pomega) :
    condSet (condSet u (ofNat 0) (succSet topElem)) (ofNat 0) (succSet topElem) =
      condSet u (ofNat 0) (succSet topElem) := by
  by_cases h0 : 0 ∈ u
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = topElem := by
        ext n
        constructor
        · intro _; exact Set.mem_univ n
        · intro _
          cases n with
          | zero => exact Or.inl ⟨rfl, h0⟩
          | succ n => exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, hp⟩
      rw [hcu]
      ext n
      constructor
      · intro _; exact Set.mem_univ n
      · intro _
        cases n with
        | zero => exact Or.inl ⟨rfl, Set.mem_univ 0⟩
        | succ n =>
          exact Or.inr ⟨⟨n, Set.mem_univ n, rfl⟩, ⟨0, Set.mem_univ 1⟩⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = ofNat 0 := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨hn, _⟩ | ⟨_, ht⟩
          · exact hn
          · exact (hp ht).elim
        · intro hn
          exact Or.inl ⟨hn, h0⟩
      rw [hcu]
      ext n
      constructor
      · intro hn
        rcases hn with ⟨hn, _⟩ | ⟨_, ⟨k, hk⟩⟩
        · exact hn
        · simp [ofNat] at hk
      · intro hn
        exact Or.inl ⟨hn, rfl⟩
  · by_cases hp : ∃ k, k + 1 ∈ u
    · have hcu : condSet u (ofNat 0) (succSet topElem) = succSet topElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
          · exact (h0 hz).elim
          · exact hy
        · intro hy
          exact Or.inr ⟨hy, hp⟩
      rw [hcu]
      have h0' : 0 ∉ succSet topElem := by
        intro ⟨n, _, hn⟩
        omega
      have hp' : ∃ k, k + 1 ∈ succSet topElem :=
        ⟨0, ⟨0, Set.mem_univ 0, rfl⟩⟩
      ext n
      constructor
      · intro hn
        rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
        · exact (h0' hz).elim
        · exact hy
      · intro hy
        exact Or.inr ⟨hy, hp'⟩
    · have hcu : condSet u (ofNat 0) (succSet topElem) = botElem := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
          · exact (h0 hz).elim
          · exact (hp ht).elim
        · intro hn
          simp [botElem] at hn
      rw [hcu]
      ext n
      simp [condSet, botElem]

theorem isRetract : Retract boool := by
  constructor
  apply graph_ext
  intro u
  rw [app, app, idem]

end boool

end DomainTheory.DataTypesAsLattices
