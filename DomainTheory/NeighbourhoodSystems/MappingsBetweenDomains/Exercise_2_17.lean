module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section

structure SatisfiesRunEquations (g : ApproximableMap B B) : Prop where
  zero : ∀ x : B.Element, g.toElementMap (sigmaElt [false] x) = sigmaElt [false] (g.toElementMap x)
  oneOne : ∀ x : B.Element, g.toElementMap (sigmaElt [true, true] x) = g.toElementMap (sigmaElt [true] x)
  oneZero : ∀ x : B.Element, g.toElementMap (sigmaElt [true, false] x) = sigmaElt [false] x
  one : g.toElementMap (sigmaElt [true] B.bot) = B.bot
end

section

def del : Str → Str
  | [] => []
  | true :: t => del t
  | false :: t => false :: t
end

section
@[simp] theorem del_nil : del [] = [] := rfl
end

section
@[simp] theorem del_true (t : Str) : del (true :: t) = del t := rfl
end

section
@[simp] theorem del_false (t : Str) : del (false :: t) = false :: t := rfl
end

section

def out : Str → Str
  | [] => []
  | false :: t => false :: out t
  | true :: t => del t
end

section
@[simp] theorem out_nil : out [] = [] := rfl
end

section
@[simp] theorem out_false (t : Str) : out (false :: t) = false :: out t := rfl
end

section
@[simp] theorem out_true (t : Str) : out (true :: t) = del t := rfl
end

section

theorem del_append (s t : Str) : del s <+: del (s ++ t) := by
  induction s with
  | nil => simp
  | cons c s₀ ih =>
    cases c with
    | true => simpa using ih
    | false => exact ⟨t, rfl⟩
end

section

theorem out_append (σ t : Str) : out σ <+: out (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons c σ₀ ih =>
    cases c with
    | true => simpa using del_append σ₀ t
    | false =>
      simp only [List.cons_append, out_false]
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, by rw [List.cons_append, hu]⟩
end

section

theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t
end

end DomainTheory.NeighbourhoodSystems.Example24
