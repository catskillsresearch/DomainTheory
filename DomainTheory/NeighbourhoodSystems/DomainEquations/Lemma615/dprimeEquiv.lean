module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_exists
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_fst_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.isGen_snd_unique
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.mem_Dprime
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.toEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.ofEl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic.notation4

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- **The domain isomorphism `D ≅ D'`** (Scott's "inclusion-preserving one-one correspondence").
Built from `toEl`/`ofEl`; the inverse laws and order-reflection come from generator uniqueness. -/
def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

end ProjectionPair

end DomainTheory.NeighbourhoodSystems
