module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.mem_encSet
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.encSet_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

theorem comparable_of_agree : ∀ {τ τ' : Str},
    (∀ (i : ℕ) (b b' : Bool), τ[i]? = some b → τ'[i]? = some b' → b = b') → τ <+: τ' ∨ τ' <+: τ
  | [], _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _ => Or.inr (List.nil_prefix)
  | a :: s, a' :: s', hag => by
      have ha : a = a' := hag 0 a a' (by simp) (by simp)
      subst ha
      have hrec : ∀ (i : ℕ) (b b' : Bool), s[i]? = some b → s'[i]? = some b' → b = b' := by
        intro i b b' hb hb'
        exact hag (i + 1) b b' (by simpa using hb) (by simpa using hb')
      rcases comparable_of_agree hrec with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

end DomainTheory.NeighbourhoodSystems.Exercise317
