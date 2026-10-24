module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section
/- concordance: source L877 EXERCISE 2.17 equations for erase-ones -/
/-- **The four equations of Exercise 2.17.** `g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x` for
*every* `x : |B|`, plus the single value equation `g(1) = ⊥` (this last one is *not* quantified
over `x`: it pins down `g` at the single finite element `1⊥`, matching Scott's literal statement
"`g(1) = ⊥`"). -/
structure SatisfiesRunEquations (g : ApproximableMap B B) : Prop where
  zero : ∀ x : B.Element, g.toElementMap (sigmaElt [false] x) = sigmaElt [false] (g.toElementMap x)
  oneOne : ∀ x : B.Element, g.toElementMap (sigmaElt [true, true] x) = g.toElementMap (sigmaElt [true] x)
  oneZero : ∀ x : B.Element, g.toElementMap (sigmaElt [true, false] x) = sigmaElt [false] x
  one : g.toElementMap (sigmaElt [true] B.bot) = B.bot
end

section
/-- Inside the first run of `1`'s: swallow `1`'s; on the first `0`, emit it and copy the rest. -/
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
/-- The guaranteed output prefix: copy leading `0`'s; on the first `1`, eliminate the run via `del`.
-/
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
/-- `del` only grows under extension: `del s <+: del (s ++ t)`. -/
theorem del_append (s t : Str) : del s <+: del (s ++ t) := by
  induction s with
  | nil => simp
  | cons c s₀ ih =>
    cases c with
    | true => simpa using ih
    | false => exact ⟨t, rfl⟩
end

section
/-- `out` only grows under extension: `out σ <+: out (σ ++ t)`. -/
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
/-- **Prefix-monotonicity of the output.** Extending the input prefix can only extend the guaranteed
output: `σ <+: σ' → out σ <+: out σ'`. This is the heart of Definition 2.1(iii) for `g`. -/
theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t
end

end DomainTheory.NeighbourhoodSystems.Example24
